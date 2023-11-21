/* SPDX-License-Identifier: GPL-2.0-or-later */
/*
 * sss.c	"simplesockstat", simple socket statistics
 *
 * Based on the socket statistics tool included in iproute2
 * https://git.kernel.org/pub/scm/network/iproute2/iproute2.git
 *
 * Authors:	Alexey Kuznetsov, <kuznet@ms2.inr.ac.ru>
 *          Marvin Meiers
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <netinet/in.h>
#include <string.h>
#include <errno.h>
#include <arpa/inet.h>
#include <getopt.h>
#include <stdbool.h>
#include <limits.h>
#include <stdarg.h>
#include <time.h>

#include "ss_util.h"
#include "libnetlink.h"

#include <linux/tcp.h>
#include <linux/netdevice.h>	/* for MAX_ADDR_LEN */
#include <linux/tipc_sockets_diag.h>

static char version[] = "1.0";

#ifndef min
# define min(x, y) ({			\
	typeof(x) _min1 = (x);		\
	typeof(y) _min2 = (y);		\
	(void) (&_min1 == &_min2);	\
	_min1 < _min2 ? _min1 : _min2; })
#endif

#ifndef offsetof
# define offsetof(type, member) ((size_t) &((type *)0)->member)
#endif

#define ARRAY_SIZE(x) (sizeof(x) / sizeof((x)[0]))

typedef struct
{
    __u16 flags;
    __u16 bytelen;
    __s16 bitlen;
    /* These next two fields match rtvia */
    __u16 family;
    __u32 data[64];
} inet_prefix;

static const char *rt_addr_n2a_r(int af, int len,
                          const void *addr, char *buf, int buflen)
{
    switch (af) {
        case AF_INET:
        case AF_INET6:
            return inet_ntop(af, addr, buf, buflen);
        case AF_MPLS:
        case AF_PACKET:
            fprintf(stderr, "rt_addr_n2a_r: Protocols currently not supported\n");
            return "?";
        case AF_BRIDGE:
        {
            const union {
                struct sockaddr sa;
                struct sockaddr_in sin;
                struct sockaddr_in6 sin6;
            } *sa = addr;

            switch (sa->sa.sa_family) {
                case AF_INET:
                    return inet_ntop(AF_INET, &sa->sin.sin_addr,
                                     buf, buflen);
                case AF_INET6:
                    return inet_ntop(AF_INET6, &sa->sin6.sin6_addr,
                                     buf, buflen);
            }

            /* fallthrough */
        }
        default:
            return "???";
    }
}

static const char *format_host_r(int af, int len, const void *addr,
                          char *buf, int buflen)
{
    return rt_addr_n2a_r(af, len, addr, buf, buflen);
}

static const char *format_host(int af, int len, const void *addr)
{
    static char buf[256];

    return format_host_r(af, len, addr, buf, 256);
}

#define BUF_CHUNK (1024 * 1024)	/* Buffer chunk allocation size */
#define BUF_CHUNKS_MAX 5	/* Maximum number of allocated buffer chunks */
#define LEN_ALIGN(x) (((x) + 1) & ~1)

int preferred_family = AF_UNSPEC;
static int show_options;
static int show_mem;
static int show_tcpinfo;
static int show_header = 0;
static FILE *out_file = NULL;
static long current_time = 0;

enum col_id {
    COL_TIME,
    COL_NETID,
    COL_STATE,
    COL_RECVQ,
    COL_SENDQ,
    COL_ADDR,
    COL_SERV,
    COL_RADDR,
    COL_RSERV,
    COL_EXT,
    COL_PROC,
    COL_MAX
};

struct column {
    const char *header;
    int disabled;
};

static struct column columns[] = {
        {"Time",            0},
        {"Netid",           0},
        {"State",           0},
        {"Recv-Q",          0},
        {"Send-Q",          0},
        {"Local Address",  0},
        {"Port",            0},
        {"Peer Address",   0},
        {"Port",            0},
        {"Process",         0},
        {"",            0},
};

static struct column *current_field = columns;

/* Output buffer: chained chunks of BUF_CHUNK bytes. Each field is written to
 * the buffer as a variable size token. A token consists of a 16 bits length
 * field, followed by a string which is not NULL-terminated.
 *
 * A new chunk is allocated and linked when the current chunk doesn't have
 * enough room to store the current token as a whole.
 */
struct buf_chunk {
    struct buf_chunk *next;	/* Next chained chunk */
    char *end;		/* Current end of content */
    char data[0];
};

struct buf_token {
    uint16_t len;		/* Data length, excluding length descriptor */
    char data[0];
};

static struct {
    struct buf_token *cur;	/* Position of current token in chunk */
    struct buf_chunk *head;	/* First chunk */
    struct buf_chunk *tail;	/* Current chunk */
    int chunks;		/* Number of allocated chunks */
} buffer;

enum {
    TCP_DB,
    MAX_DB
};

#define INET_DBM ((1<<TCP_DB))

enum {
    SS_UNKNOWN,
    SS_ESTABLISHED,
    SS_SYN_SENT,
    SS_SYN_RECV,
    SS_FIN_WAIT1,
    SS_FIN_WAIT2,
    SS_TIME_WAIT,
    SS_CLOSE,
    SS_CLOSE_WAIT,
    SS_LAST_ACK,
    SS_LISTEN,
    SS_CLOSING,
    SS_MAX
};

#define SS_ALL ((1 << SS_MAX) - 1)
#define SS_CONN (SS_ALL & ~((1<<SS_LISTEN)|(1<<SS_CLOSE)|(1<<SS_TIME_WAIT)|(1<<SS_SYN_RECV)))

struct filter {
    int dbs;
    int states;
    uint64_t families;
    bool kill;
    struct rtnl_handle *rth_for_killing;
};

#define FAMILY_MASK(family) ((uint64_t)1 << (family))

static const struct filter default_dbs[MAX_DB] = {
        [TCP_DB] = {
                .states   = SS_CONN,
                .families = FAMILY_MASK(AF_INET),
        },
};

static const struct filter default_afs[AF_MAX] = {
        [AF_INET] = {
                .dbs    = INET_DBM,
                .states = SS_CONN,
        },
};

static struct filter current_filter;

static void filter_db_set(struct filter *f, int db, bool enable)
{
    if (enable) {
        f->states   |= default_dbs[db].states;
        f->dbs	    |= 1 << db;
    } else {
        f->dbs &= ~(1 << db);
    }
}

static void filter_af_set(struct filter *f, int af)
{
    f->states	   |= default_afs[af].states;
    f->families	   |= FAMILY_MASK(af);
    preferred_family    = af;
}

static int filter_af_get(struct filter *f, int af)
{
    return !!(f->families & FAMILY_MASK(af));
}

static void filter_states_set(struct filter *f, int states)
{
    if (states)
        f->states = states;
}

static void filter_merge_defaults(struct filter *f)
{
    int db;
    int af;

    for (db = 0; db < MAX_DB; db++) {
        if (!(f->dbs & (1 << db)))
            continue;

        if (!(default_dbs[db].families & f->families))
            f->families |= default_dbs[db].families;
    }
    for (af = 0; af < AF_MAX; af++) {
        if (!(f->families & FAMILY_MASK(af)))
            continue;

        if (!(default_afs[af].dbs & f->dbs))
            f->dbs |= default_afs[af].dbs;
    }
}

static FILE *generic_proc_open(const char *env, const char *name)
{
    const char *p = getenv(env);
    char store[128];

    if (!p) {
        p = getenv("PROC_ROOT") ? : "/proc";
        snprintf(store, sizeof(store)-1, "%s/%s", p, name);
        p = store;
    }

    return fopen(p, "r");
}
#define net_tcp_open()		generic_proc_open("PROC_NET_TCP", "net/tcp")

static unsigned long long cookie_sk_get(const uint32_t *cookie)
{
    return (((unsigned long long)cookie[1] << 31) << 1) | cookie[0];
}

struct sockstat {
    struct sockstat	   *next;
    unsigned int	    type;
    uint16_t	    prot;
    uint16_t	    raw_prot;
    inet_prefix	    local;
    inet_prefix	    remote;
    int		    lport;
    int		    rport;
    int		    state;
    int		    rq, wq;
    unsigned int ino;
    unsigned int uid;
    int		    refcnt;
    unsigned int	    iface;
    unsigned long long  sk;
    char *name;
    char *peer_name;
    __u32		    mark;
    __u64		    cgroup_id;
};

struct dctcpstat {
    unsigned int	ce_state;
    unsigned int	alpha;
    unsigned int	ab_ecn;
    unsigned int	ab_tot;
    bool		enabled;
};

struct tcpstat {
    struct sockstat	    ss;
    unsigned int	    timer;
    unsigned int	    timeout;
    int		    probes;
    char		    cong_alg[16];
    double		    rto, ato, rtt, rttvar;
    int		    qack, ssthresh, backoff;
    double		    send_bps;
    int		    snd_wscale;
    int		    rcv_wscale;
    int		    mss;
    int		    rcv_mss;
    int		    advmss;
    unsigned int	    pmtu;
    unsigned int	    cwnd;
    unsigned int	    lastsnd;
    unsigned int	    lastrcv;
    unsigned int	    lastack;
    double		    pacing_rate;
    double		    pacing_rate_max;
    double		    delivery_rate;
    unsigned long long  bytes_acked;
    unsigned long long  bytes_received;
    unsigned int	    segs_out;
    unsigned int	    segs_in;
    unsigned int	    data_segs_out;
    unsigned int	    data_segs_in;
    unsigned int	    unacked;
    unsigned int	    retrans;
    unsigned int	    retrans_total;
    unsigned int	    lost;
    unsigned int	    sacked;
    unsigned int	    fackets;
    unsigned int	    reordering;
    unsigned int	    not_sent;
    unsigned int	    delivered;
    unsigned int	    delivered_ce;
    unsigned int	    dsack_dups;
    unsigned int	    reord_seen;
    double		    rcv_rtt;
    double		    min_rtt;
    unsigned int 	    rcv_ooopack;
    unsigned int	    snd_wnd;
    int		    rcv_space;
    unsigned int        rcv_ssthresh;
    unsigned long long  busy_time;
    unsigned long long  rwnd_limited;
    unsigned long long  sndbuf_limited;
    unsigned long long  bytes_sent;
    unsigned long long  bytes_retrans;
    bool		    has_ts_opt;
    bool		    has_sack_opt;
    bool		    has_ecn_opt;
    bool		    has_ecnseen_opt;
    bool		    has_fastopen_opt;
    bool		    has_wscale_opt;
    bool		    app_limited;
    struct dctcpstat    *dctcp;
    struct tcp_bbr_info *bbr_info;
};

static const char *proto_name(int protocol)
{
    switch (protocol) {
        case 0:
            return "raw";
        case IPPROTO_UDP:
            return "udp";
        case IPPROTO_TCP:
            return "tcp";
        case IPPROTO_SCTP:
            return "sctp";
        case IPPROTO_DCCP:
            return "dccp";
        case IPPROTO_ICMPV6:
            return "icmp6";
    }

    return "???";
}

/* Allocate and initialize a new buffer chunk */
static struct buf_chunk *buf_chunk_new(void)
{
    struct buf_chunk *new = malloc(BUF_CHUNK);

    if (!new)
        abort();

    new->next = NULL;

    /* This is also the last block */
    buffer.tail = new;

    /* Next token will be stored at the beginning of chunk data area, and
	 * its initial length is zero.
	 */
    buffer.cur = (struct buf_token *)new->data;
    buffer.cur->len = 0;

    new->end = buffer.cur->data;

    buffer.chunks++;

    return new;
}

/* Return available tail room in given chunk */
static int buf_chunk_avail(struct buf_chunk *chunk)
{
    return BUF_CHUNK - offsetof(struct buf_chunk, data) -
           (chunk->end - chunk->data);
}

/* Update end pointer and token length, link new chunk if we hit the end of the
 * current one. Return -EAGAIN if we got a new chunk, caller has to print again.
 */
static int buf_update(int len)
{
    struct buf_chunk *chunk = buffer.tail;
    struct buf_token *t = buffer.cur;

    /* Claim success if new content fits in the current chunk, and anyway
	 * if this is the first token in the chunk: in the latter case,
	 * allocating a new chunk won't help, so we'll just cut the output.
	 */
    if ((len < buf_chunk_avail(chunk) && len != -1 /* glibc < 2.0.6 */) ||
        t == (struct buf_token *)chunk->data) {
        len = min(len, buf_chunk_avail(chunk));

        /* Total field length can't exceed 2^16 bytes, cut as needed */
        len = min(len, USHRT_MAX - t->len);

        chunk->end += len;
        t->len += len;
        return 0;
    }

    /* Content truncated, time to allocate more */
    chunk->next = buf_chunk_new();

    /* Copy current token over to new chunk, including length descriptor */
    memcpy(chunk->next->data, t, sizeof(t->len) + t->len);
    chunk->next->end += t->len;

    /* Discard partially written field in old chunk */
    chunk->end -= t->len + sizeof(t->len);

    return -EAGAIN;
}

/* Append content to buffer as part of the current field */
__attribute__((format(printf, 1, 2)))
static void out(const char *fmt, ...)
{
    struct column *f = current_field;
    va_list args;
    char *pos;
    int len;

    if (f->disabled)
        return;

    if (!buffer.head)
        buffer.head = buf_chunk_new();

again:	/* Append to buffer: if we have a new chunk, print again */

    pos = buffer.cur->data + buffer.cur->len;
    va_start(args, fmt);

    /* Limit to tail room. If we hit the limit, buf_update() will tell us */
    len = vsnprintf(pos, buf_chunk_avail(buffer.tail), fmt, args);
    va_end(args);

    if (buf_update(len))
        goto again;
}

/* Done with field: update buffer pointer, start new token after current one */
static void field_flush(struct column *f)
{
    struct buf_chunk *chunk;
    unsigned int pad;

    if (f->disabled)
        return;

    chunk = buffer.tail;
    pad = buffer.cur->len % 2;

    /* We need a new chunk if we can't store the next length descriptor.
	 * Mind the gap between end of previous token and next aligned position
	 * for length descriptor.
	 */
    if (buf_chunk_avail(chunk) - pad < sizeof(buffer.cur->len)) {
        chunk->end += pad;
        chunk->next = buf_chunk_new();
        return;
    }

    buffer.cur = (struct buf_token *)(buffer.cur->data +
                                      LEN_ALIGN(buffer.cur->len));
    buffer.cur->len = 0;
    buffer.tail->end = buffer.cur->data;
}

static int field_is_last(struct column *f)
{
    return f - columns == COL_MAX - 1;
}

/* Get the next available token in the buffer starting from the current token */
static struct buf_token *buf_token_next(struct buf_token *cur)
{
    struct buf_chunk *chunk = buffer.tail;

    /* If we reached the end of chunk contents, get token from next chunk */
    if (cur->data + LEN_ALIGN(cur->len) == chunk->end) {
        buffer.tail = chunk = chunk->next;
        return chunk ? (struct buf_token *)chunk->data : NULL;
    }

    return (struct buf_token *)(cur->data + LEN_ALIGN(cur->len));
}

/* Free up all allocated buffer chunks */
static void buf_free_all(void)
{
    struct buf_chunk *tmp;

    for (buffer.tail = buffer.head; buffer.tail; ) {
        tmp = buffer.tail;
        buffer.tail = buffer.tail->next;
        free(tmp);
    }
    buffer.head = NULL;
    buffer.chunks = 0;
}

static void render(void)
{
    struct buf_token *token;
    int line_started = 0;
    struct column *f;

    if (!buffer.head)
        return;

    token = (struct buf_token *)buffer.head->data;

    /* Ensure end alignment of last token, it wasn't necessarily flushed */
    buffer.tail->end += buffer.cur->len % 2;

    /* Rewind and replay */
    buffer.tail = buffer.head;

    f = columns;
    while (f->disabled)
        f++;

    while (token) {
        /* Print left delimiter only if we already started a line */
        if (line_started++ && !field_is_last(f))
            fprintf(out_file, ";");

        /* Print field content from token data with spacing */
        fwrite(token->data, 1, token->len, out_file);

        /* Go to next non-empty field, deal with end-of-line */
        do {
            if (field_is_last(f)) {
                fprintf(out_file, "\n");
                f = columns;
                line_started = 0;
            } else {
                f++;
            }
        } while (f->disabled);

        token = buf_token_next(token);
    }
    /* Deal with final end-of-line when the last non-empty field printed
	 * is not the last field.
	 */
    if (line_started)
        fprintf(out_file, "\n");

    buf_free_all();
    current_field = columns;
}

/* Move to next field, and render buffer if we reached the maximum number of
 * chunks, at the last field in a line.
 */
static void field_next(void)
{
    if (field_is_last(current_field) && buffer.chunks >= BUF_CHUNKS_MAX) {
        render();
        return;
    }

    field_flush(current_field);
    if (field_is_last(current_field))
        current_field = columns;
    else
        current_field++;
}

/* Walk through fields and flush them until we reach the desired one */
static void field_set(enum col_id id)
{
    while (id != current_field - columns)
        field_next();
}

/* Print header for all non-empty columns */
static void print_header(void)
{
    while (!field_is_last(current_field)) {
        if (!current_field->disabled)
            out("%s", current_field->header);
        field_next();
    }
}

static void sock_state_print(struct sockstat *s)
{
    const char *sock_name;
    static const char * const sstate_name[] = {
            "UNKNOWN",
            [SS_ESTABLISHED] = "ESTAB",
            [SS_SYN_SENT] = "SYN-SENT",
            [SS_SYN_RECV] = "SYN-RECV",
            [SS_FIN_WAIT1] = "FIN-WAIT-1",
            [SS_FIN_WAIT2] = "FIN-WAIT-2",
            [SS_TIME_WAIT] = "TIME-WAIT",
            [SS_CLOSE] = "UNCONN",
            [SS_CLOSE_WAIT] = "CLOSE-WAIT",
            [SS_LAST_ACK] = "LAST-ACK",
            [SS_LISTEN] =	"LISTEN",
            [SS_CLOSING] = "CLOSING",
    };

    switch (s->local.family) {
        case AF_UNIX:
            fprintf(stderr, "sock_state_print: Protocols currently not supported\n");
            sock_name = "???";
            break;
        case AF_INET:
        case AF_INET6:
            sock_name = proto_name(s->type);
            break;
        case AF_PACKET:
        case AF_NETLINK:
        case AF_TIPC:
        case AF_VSOCK:
        case AF_XDP:
            fprintf(stderr, "sock_state_print: Protocols currently not supported\n");
            sock_name = "???";
            break;
        default:
            sock_name = "unknown";
    }

    if (strcmp(sock_name, "sctp") == 0) {
        fprintf(stderr, "sock_state_print: SCTP currently not supported\n");
    } else {
        field_set(COL_NETID);
        out("Netid:%s", sock_name);
        field_set(COL_STATE);
        out("State:%s", sstate_name[s->state]);
    }

    field_set(COL_RECVQ);
    out("RecvQ:%d", s->rq);
    field_set(COL_SENDQ);
    out("SendQ:%d", s->wq);
    field_set(COL_ADDR);
}

static void sock_addr_print(const char *addr, char *delim, const char *port)
{
    out("Ip:%s%s", addr, delim);

    field_next();
    out("Port:%s", port);
    field_next();
}

static const char *print_ms_timer(unsigned int timeout)
{
    static char buf[64];
    int secs, msecs, minutes;

    secs = timeout/1000;
    minutes = secs/60;
    secs = secs%60;
    msecs = timeout%1000;
    buf[0] = 0;
    if (minutes) {
        msecs = 0;
        snprintf(buf, sizeof(buf)-16, "%dmin", minutes);
        if (minutes > 9)
            secs = 0;
    }
    if (secs) {
        if (secs > 9)
            msecs = 0;
        sprintf(buf+strlen(buf), "%d%s", secs, msecs ? "." : "sec");
    }
    if (msecs)
        sprintf(buf+strlen(buf), "%03dms", msecs);
    return buf;
}

static const char *resolve_service(int port)
{
    static char buf[128];

    if (port == 0) {
        buf[0] = '*';
        buf[1] = 0;
        return buf;
    }

    sprintf(buf, "%u", port);
    return buf;
}

static void inet_addr_print(const inet_prefix *a, int port,
                            unsigned int ifindex, bool v6only)
{
    char buf[1024];
    const char *ap = buf;

    if (a->family == AF_INET) {
        ap = format_host(AF_INET, 4, a->data);
    } else {
        if (!v6only &&
            !memcmp(a->data, &in6addr_any, sizeof(in6addr_any))) {
            buf[0] = '*';
            buf[1] = 0;
        } else {
            ap = format_host(a->family, 16, a->data);

            /* Numeric IPv6 addresses should be bracketed */
            if (strchr(ap, ':')) {
                snprintf(buf, sizeof(buf),
                         "[%s]", ap);
                ap = buf;
            }
        }
    }

    sock_addr_print(ap, "", resolve_service(port));
}

static void time_print(void)
{
    field_set(COL_TIME);
    out("Time:%ld", current_time);
}

static void inet_stats_print(struct sockstat *s, bool v6only)
{
    time_print();
    sock_state_print(s);

    inet_addr_print(&s->local, s->lport, s->iface, v6only);
    inet_addr_print(&s->remote, s->rport, 0, v6only);
}

static int proc_parse_inet_addr(char *loc, char *rem, int family, struct
        sockstat * s)
{
    s->local.family = s->remote.family = family;
    if (family == AF_INET) {
        sscanf(loc, "%x:%x", s->local.data, (unsigned *)&s->lport);
        sscanf(rem, "%x:%x", s->remote.data, (unsigned *)&s->rport);
        s->local.bytelen = s->remote.bytelen = 4;
        return 0;
    } else {
        sscanf(loc, "%08x%08x%08x%08x:%x",
               s->local.data,
               s->local.data + 1,
               s->local.data + 2,
               s->local.data + 3,
               &s->lport);
        sscanf(rem, "%08x%08x%08x%08x:%x",
               s->remote.data,
               s->remote.data + 1,
               s->remote.data + 2,
               s->remote.data + 3,
               &s->rport);
        s->local.bytelen = s->remote.bytelen = 16;
        return 0;
    }
    return -1;
}

static int proc_inet_split_line(char *line, char **loc, char **rem, char **data)
{
    char *p;

    if ((p = strchr(line, ':')) == NULL)
        return -1;

    *loc = p+2;
    if ((p = strchr(*loc, ':')) == NULL)
        return -1;

    p[5] = 0;
    *rem = p+6;
    if ((p = strchr(*rem, ':')) == NULL)
        return -1;

    p[5] = 0;
    *data = p+6;
    return 0;
}

/*
 * Display bandwidth in standard units
 * See: https://en.wikipedia.org/wiki/Data-rate_units
 * bw is in bits per second
 */
static char *sprint_bw(char *buf, double bw)
{
    // Always use numeric format
    sprintf(buf, "%.0f", bw);
//    if (numeric)
//        sprintf(buf, "%.0f", bw);
//    else if (bw >= 1e12)
//        sprintf(buf, "%.3gT", bw / 1e12);
//    else if (bw >= 1e9)
//        sprintf(buf, "%.3gG", bw / 1e9);
//    else if (bw >= 1e6)
//        sprintf(buf, "%.3gM", bw / 1e6);
//    else if (bw >= 1e3)
//        sprintf(buf, "%.3gk", bw / 1e3);
//    else
//        sprintf(buf, "%g", bw);

    return buf;
}

static void tcp_stats_print(struct tcpstat *s)
{
    char b1[64];

    if (s->has_ts_opt)
        out(";ts_opt:ts");
    else
        out(";ts_opt:-");
    if (s->has_sack_opt)
        out(";sack_opt:sack");
    else
        out(";sack_opt:-");
    if (s->has_ecn_opt)
        out(";ecn_opt:ecn");
    else
        out(";ecn_opt:-");
    if (s->has_ecnseen_opt)
        out(";ecnseen_opt:ecnseen");
    else
        out(";ecnseen_opt:-");
    if (s->has_fastopen_opt)
        out(";fastopen_opt:fastopen");
    else
        out(";fastopen_opt:-");
    if (s->cong_alg[0])
        out(";cong_alg:%s", s->cong_alg);
    else
        out(";cong_alg:-");
    if (s->has_wscale_opt)
        out(";wscale:%d,%d", s->snd_wscale, s->rcv_wscale);
    else
        out(";wscale:-");
    if (s->rto)
        out(";rto:%g", s->rto);
    else
        out(";rto:-");
    if (s->backoff)
        out(";backoff:%u", s->backoff);
    else
        out(";backoff:-");
    if (s->rtt)
        out(";rtt:%g/%g", s->rtt, s->rttvar);
    else
        out(";rtt:-");
    if (s->ato)
        out(";ato:%g", s->ato);
    else
        out(";ato:-");

    if (s->qack)
        out(";qack:%d", s->qack);
    else
        out(";qack:-");
    if (s->qack & 1)
        out(" bidir");

    if (s->mss)
        out(";mss:%d", s->mss);
    else
        out(";mss:-");
    if (s->pmtu)
        out(";pmtu:%u", s->pmtu);
    else
        out(";pmtu:-");
    if (s->rcv_mss)
        out(";rcvmss:%d", s->rcv_mss);
    else
        out(";rcvmss:-");
    if (s->advmss)
        out(";advmss:%d", s->advmss);
    else
        out(";advmss:-");
    if (s->cwnd)
        out(";cwnd:%u", s->cwnd);
    else
        out(";cwnd:-");
    if (s->ssthresh)
        out(";ssthresh:%d", s->ssthresh);
    else
        out(";ssthresh:-");

    if (s->bytes_sent)
        out(";bytes_sent:%llu", s->bytes_sent);
    else
        out(";bytes_sent:-");
    if (s->bytes_retrans)
        out(";bytes_retrans:%llu", s->bytes_retrans);
    else
        out(";bytes_retrans:-");
    if (s->bytes_acked)
        out(";bytes_acked:%llu", s->bytes_acked);
    else
        out(";bytes_acked:-");
    if (s->bytes_received)
        out(";bytes_received:%llu", s->bytes_received);
    else
        out(";bytes_received:-");
    if (s->segs_out)
        out(";segs_out:%u", s->segs_out);
    else
        out(";segs_out:-");
    if (s->segs_in)
        out(";segs_in:%u", s->segs_in);
    else
        out(";segs_in:-");
    if (s->data_segs_out)
        out(";data_segs_out:%u", s->data_segs_out);
    else
        out(";data_segs_out:-");
    if (s->data_segs_in)
        out(";data_segs_in:%u", s->data_segs_in);
    else
        out(";data_segs_in:-");

    if (s->dctcp && s->dctcp->enabled) {
        struct dctcpstat *dctcp = s->dctcp;

        out(";dctcp:(ce_state:%u,alpha:%u,ab_ecn:%u,ab_tot:%u)",
            dctcp->ce_state, dctcp->alpha, dctcp->ab_ecn,
            dctcp->ab_tot);
    } else if (s->dctcp) {
        out(";dctcp:fallback_mode");
    } else {
        out(";dctcp:-");
    }

    if (s->bbr_info) {
        __u64 bw;

        bw = s->bbr_info->bbr_bw_hi;
        bw <<= 32;
        bw |= s->bbr_info->bbr_bw_lo;

        out(";bbr:(bw:%sbps,mrtt:%g",
            sprint_bw(b1, bw * 8.0),
            (double)s->bbr_info->bbr_min_rtt / 1000.0);
        if (s->bbr_info->bbr_pacing_gain)
            out(",pacing_gain:%g",
                (double)s->bbr_info->bbr_pacing_gain / 256.0);
        if (s->bbr_info->bbr_cwnd_gain)
            out(",cwnd_gain:%g",
                (double)s->bbr_info->bbr_cwnd_gain / 256.0);
        out(")");
    } else {
        out(";bbr:-");
    }

    if (s->send_bps)
        out(";send:%sbps", sprint_bw(b1, s->send_bps));
    else
        out(";send:-");
    if (s->lastsnd)
        out(";lastsnd:%u", s->lastsnd);
    else
        out(";lastsnd:-");
    if (s->lastrcv)
        out(";lastrcv:%u", s->lastrcv);
    else
        out(";lastrcv:-");
    if (s->lastack)
        out(";lastack:%u", s->lastack);
    else
        out(";lastack:-");

    if (s->pacing_rate) {
        out(";pacing_rate:%sbps", sprint_bw(b1, s->pacing_rate));
        if (s->pacing_rate_max)
            out("/%sbps", sprint_bw(b1, s->pacing_rate_max));
        else
            out("/-");
    } else {
        out(";pacing_rate:-");
    }

    if (s->delivery_rate)
        out(";delivery_rate:%sbps", sprint_bw(b1, s->delivery_rate));
    else
        out(";delivery_rate:-");
    if (s->delivered)
        out(";delivered:%u", s->delivered);
    else
        out(";delivered:-");
    if (s->delivered_ce)
        out(";delivered_ce:%u", s->delivered_ce);
    else
        out(";delivered_ce:-");
    if (s->app_limited)
        out(";app_limited:app_limited");
    else
        out(";app_limited:-");

    if (s->busy_time) {
        out(";busy:%llums", s->busy_time / 1000);
        if (s->rwnd_limited)
            out(";rwnd_limited:%llums(%.1f%%)",
                s->rwnd_limited / 1000,
                100.0 * s->rwnd_limited / s->busy_time);
        else
            out(";rwnd_limited:-");
        if (s->sndbuf_limited)
            out(";sndbuf_limited:%llums(%.1f%%)",
                s->sndbuf_limited / 1000,
                100.0 * s->sndbuf_limited / s->busy_time);
        else
            out(";sndbuf_limited:-");
    } else {
        out(";busy:-;rwnd_limited:-;sndbuf_limited:-");
    }

    if (s->unacked)
        out(";unacked:%u", s->unacked);
    else
        out(";unacked:-");
    if (s->retrans || s->retrans_total)
        out(";retrans:%u/%u", s->retrans, s->retrans_total);
    else
        out(";retrans:-");
    if (s->lost)
        out(";lost:%u", s->lost);
    else
        out(";lost:-");
    if (s->sacked && s->ss.state != SS_LISTEN)
        out(";sacked:%u", s->sacked);
    else
        out(";sacked:-");
    if (s->dsack_dups)
        out(";dsack_dups:%u", s->dsack_dups);
    else
        out(";dsack_dups:-");
    if (s->fackets)
        out(";fackets:%u", s->fackets);
    else
        out(";fackets:-");
    if (s->reordering != 3)
        out(";reordering:%d", s->reordering);
    else
        out(";reordering:-");
    if (s->reord_seen)
        out(";reord_seen:%d", s->reord_seen);
    else
        out(";reord_seen:-");
    if (s->rcv_rtt)
        out(";rcv_rtt:%g", s->rcv_rtt);
    else
        out(";rcv_rtt:-");
    if (s->rcv_space)
        out(";rcv_space:%d", s->rcv_space);
    else
        out(";rcv_space:-");
    if (s->rcv_ssthresh)
        out(";rcv_ssthresh:%u", s->rcv_ssthresh);
    else
        out(";rcv_ssthresh:-");
    if (s->not_sent)
        out(";notsent:%u", s->not_sent);
    else
        out(";notsent:-");
    if (s->min_rtt)
        out(";minrtt:%g", s->min_rtt);
    else
        out(";minrtt:-");
    if (s->rcv_ooopack)
        out(";rcv_ooopack:%u", s->rcv_ooopack);
    else
        out(";rcv_ooopack:-");
    if (s->snd_wnd)
        out(";snd_wnd:%u", s->snd_wnd);
    else
        out(";snd_wnd:-");
}

static void tcp_timer_print(struct tcpstat *s)
{
    static const char * const tmr_name[] = {
            "off",
            "on",
            "keepalive",
            "timewait",
            "persist",
            "unknown"
    };

    if (s->timer) {
        if (s->timer > 4)
            s->timer = 5;
        out(";timer:(%s,%s,%d)",
            tmr_name[s->timer],
            print_ms_timer(s->timeout),
            s->retrans);
    }
}

static int tcp_show_line(char *line, const struct filter *f, int family)
{
    int rto = 0, ato = 0;
    struct tcpstat s = {};
    char *loc, *rem, *data;
    char opt[256];
    int n;
    int hz = sysconf(_SC_CLK_TCK);

    if (proc_inet_split_line(line, &loc, &rem, &data))
        return -1;

    int state = (data[1] >= 'A') ? (data[1] - 'A' + 10) : (data[1] - '0');

    if (!(f->states & (1 << state)))
        return 0;

    proc_parse_inet_addr(loc, rem, family, &s.ss);

    opt[0] = 0;
    n = sscanf(data, "%x %x:%x %x:%x %x %d %d %u %d %llx %d %d %d %u %d %[^\n]\n",
               &s.ss.state, &s.ss.wq, &s.ss.rq,
               &s.timer, &s.timeout, &s.retrans, &s.ss.uid, &s.probes,
               &s.ss.ino, &s.ss.refcnt, &s.ss.sk, &rto, &ato, &s.qack, &s.cwnd,
               &s.ssthresh, opt);

    if (n < 17)
        opt[0] = 0;

    if (n < 12) {
        rto = 0;
        s.cwnd = 2;
        s.ssthresh = -1;
        ato = s.qack = 0;
    }

    s.retrans   = s.timer != 1 ? s.probes : s.retrans;
    s.timeout   = (s.timeout * 1000 + hz - 1) / hz;
    s.ato	    = (double)ato / hz;
    s.qack	   /= 2;
    s.rto	    = (double)rto;
    s.ssthresh  = s.ssthresh == -1 ? 0 : s.ssthresh;
    s.rto	    = s.rto != 3 * hz  ? s.rto / hz : 0;
    s.ss.type   = IPPROTO_TCP;

    inet_stats_print(&s.ss, false);

    if (show_options)
        tcp_timer_print(&s);

    if (show_tcpinfo)
        tcp_stats_print(&s);

    return 0;
}

static int generic_record_read(FILE *fp,
                               int (*worker)(char*, const struct filter *, int),
                               const struct filter *f, int fam)
{
    char line[256];

    /* skip header */
    if (fgets(line, sizeof(line), fp) == NULL)
        goto outerr;

    while (fgets(line, sizeof(line), fp) != NULL) {
        int n = strlen(line);

        if (n == 0 || line[n-1] != '\n') {
            errno = -EINVAL;
            return -1;
        }
        line[n-1] = 0;

        if (worker(line, f, fam) < 0)
            return 0;
    }
outerr:

    return ferror(fp) ? -1 : 0;
}

static void print_skmeminfo(struct rtattr *tb[], int attrtype)
{
    const __u32 *skmeminfo;

    if (!tb[attrtype]) {
        if (attrtype == INET_DIAG_SKMEMINFO) {
            if (!tb[INET_DIAG_MEMINFO])
                return;

            const struct inet_diag_meminfo *minfo =
                    RTA_DATA(tb[INET_DIAG_MEMINFO]);

            out(";mem:(r%u,w%u,f%u,t%u)",
                minfo->idiag_rmem,
                minfo->idiag_wmem,
                minfo->idiag_fmem,
                minfo->idiag_tmem);
        }
        return;
    }

    skmeminfo = RTA_DATA(tb[attrtype]);

    out(";skmem:(r%u,rb%u,t%u,tb%u,f%u,w%u,o%u",
        skmeminfo[SK_MEMINFO_RMEM_ALLOC],
        skmeminfo[SK_MEMINFO_RCVBUF],
        skmeminfo[SK_MEMINFO_WMEM_ALLOC],
        skmeminfo[SK_MEMINFO_SNDBUF],
        skmeminfo[SK_MEMINFO_FWD_ALLOC],
        skmeminfo[SK_MEMINFO_WMEM_QUEUED],
        skmeminfo[SK_MEMINFO_OPTMEM]);

    if (RTA_PAYLOAD(tb[attrtype]) >=
        (SK_MEMINFO_BACKLOG + 1) * sizeof(__u32))
        out(",bl%u", skmeminfo[SK_MEMINFO_BACKLOG]);
    else
        out(",bl-");

    if (RTA_PAYLOAD(tb[attrtype]) >=
        (SK_MEMINFO_DROPS + 1) * sizeof(__u32))
        out(",d%u", skmeminfo[SK_MEMINFO_DROPS]);
    else
        out(",d-");

    out(")");
}

#define TCPI_HAS_OPT(info, opt) !!(info->tcpi_options & (opt))

static void tcp_show_info(const struct nlmsghdr *nlh, struct inet_diag_msg *r,
                          struct rtattr *tb[])
{
    double rtt = 0;
    struct tcpstat s = {};

    s.ss.state = r->idiag_state;

    print_skmeminfo(tb, INET_DIAG_SKMEMINFO);

    if (tb[INET_DIAG_INFO]) {
        struct tcp_info *info;
        int len = RTA_PAYLOAD(tb[INET_DIAG_INFO]);

        /* workaround for older kernels with less fields */
        if (len < sizeof(*info)) {
            info = alloca(sizeof(*info));
            memcpy(info, RTA_DATA(tb[INET_DIAG_INFO]), len);
            memset((char *)info + len, 0, sizeof(*info) - len);
        } else
            info = RTA_DATA(tb[INET_DIAG_INFO]);

        if (show_options) {
            s.has_ts_opt	   = TCPI_HAS_OPT(info, TCPI_OPT_TIMESTAMPS);
            s.has_sack_opt	   = TCPI_HAS_OPT(info, TCPI_OPT_SACK);
            s.has_ecn_opt	   = TCPI_HAS_OPT(info, TCPI_OPT_ECN);
            s.has_ecnseen_opt  = TCPI_HAS_OPT(info, TCPI_OPT_ECN_SEEN);
            s.has_fastopen_opt = TCPI_HAS_OPT(info, TCPI_OPT_SYN_DATA);
        }

        if (tb[INET_DIAG_CONG])
            strncpy(s.cong_alg,
                    rta_getattr_str(tb[INET_DIAG_CONG]),
                    sizeof(s.cong_alg) - 1);

        if (TCPI_HAS_OPT(info, TCPI_OPT_WSCALE)) {
            s.has_wscale_opt  = true;
            s.snd_wscale	  = info->tcpi_snd_wscale;
            s.rcv_wscale	  = info->tcpi_rcv_wscale;
        }

        if (info->tcpi_rto && info->tcpi_rto != 3000000)
            s.rto = (double)info->tcpi_rto / 1000;

        s.backoff	 = info->tcpi_backoff;
        s.rtt		 = (double)info->tcpi_rtt / 1000;
        s.rttvar	 = (double)info->tcpi_rttvar / 1000;
        s.ato		 = (double)info->tcpi_ato / 1000;
        s.mss		 = info->tcpi_snd_mss;
        s.rcv_mss	 = info->tcpi_rcv_mss;
        s.advmss	 = info->tcpi_advmss;
        s.rcv_space	 = info->tcpi_rcv_space;
        s.rcv_rtt	 = (double)info->tcpi_rcv_rtt / 1000;
        s.lastsnd	 = info->tcpi_last_data_sent;
        s.lastrcv	 = info->tcpi_last_data_recv;
        s.lastack	 = info->tcpi_last_ack_recv;
        s.unacked	 = info->tcpi_unacked;
        s.retrans	 = info->tcpi_retrans;
        s.retrans_total  = info->tcpi_total_retrans;
        s.lost		 = info->tcpi_lost;
        s.sacked	 = info->tcpi_sacked;
        s.fackets	 = info->tcpi_fackets;
        s.reordering	 = info->tcpi_reordering;
        s.rcv_ssthresh   = info->tcpi_rcv_ssthresh;
        s.cwnd		 = info->tcpi_snd_cwnd;
        s.pmtu		 = info->tcpi_pmtu;

        if (info->tcpi_snd_ssthresh < 0xFFFF)
            s.ssthresh = info->tcpi_snd_ssthresh;

        rtt = (double) info->tcpi_rtt;
        if (tb[INET_DIAG_VEGASINFO]) {
            const struct tcpvegas_info *vinfo
                    = RTA_DATA(tb[INET_DIAG_VEGASINFO]);

            if (vinfo->tcpv_enabled &&
                vinfo->tcpv_rtt && vinfo->tcpv_rtt != 0x7fffffff)
                rtt =  vinfo->tcpv_rtt;
        }

        if (tb[INET_DIAG_DCTCPINFO]) {
            struct dctcpstat *dctcp = malloc(sizeof(struct
                    dctcpstat));

            const struct tcp_dctcp_info *dinfo
                    = RTA_DATA(tb[INET_DIAG_DCTCPINFO]);

            dctcp->enabled	= !!dinfo->dctcp_enabled;
            dctcp->ce_state = dinfo->dctcp_ce_state;
            dctcp->alpha	= dinfo->dctcp_alpha;
            dctcp->ab_ecn	= dinfo->dctcp_ab_ecn;
            dctcp->ab_tot	= dinfo->dctcp_ab_tot;
            s.dctcp		= dctcp;
        }

        if (tb[INET_DIAG_BBRINFO]) {
            const void *bbr_info = RTA_DATA(tb[INET_DIAG_BBRINFO]);
            int len = min(RTA_PAYLOAD(tb[INET_DIAG_BBRINFO]),
                          sizeof(*s.bbr_info));

            s.bbr_info = calloc(1, sizeof(*s.bbr_info));
            if (s.bbr_info && bbr_info)
                memcpy(s.bbr_info, bbr_info, len);
        }

        if (rtt > 0 && info->tcpi_snd_mss && info->tcpi_snd_cwnd) {
            s.send_bps = (double) info->tcpi_snd_cwnd *
                         (double)info->tcpi_snd_mss * 8000000. / rtt;
        }

        if (info->tcpi_pacing_rate &&
            info->tcpi_pacing_rate != ~0ULL) {
            s.pacing_rate = info->tcpi_pacing_rate * 8.;

            if (info->tcpi_max_pacing_rate &&
                info->tcpi_max_pacing_rate != ~0ULL)
                s.pacing_rate_max = info->tcpi_max_pacing_rate * 8.;
        }
        s.bytes_acked = info->tcpi_bytes_acked;
        s.bytes_received = info->tcpi_bytes_received;
        s.segs_out = info->tcpi_segs_out;
        s.segs_in = info->tcpi_segs_in;
        s.data_segs_out = info->tcpi_data_segs_out;
        s.data_segs_in = info->tcpi_data_segs_in;
        s.not_sent = info->tcpi_notsent_bytes;
        if (info->tcpi_min_rtt && info->tcpi_min_rtt != ~0U)
            s.min_rtt = (double) info->tcpi_min_rtt / 1000;
        s.delivery_rate = info->tcpi_delivery_rate * 8.;
        s.app_limited = info->tcpi_delivery_rate_app_limited;
        s.busy_time = info->tcpi_busy_time;
        s.rwnd_limited = info->tcpi_rwnd_limited;
        s.sndbuf_limited = info->tcpi_sndbuf_limited;
        s.delivered = info->tcpi_delivered;
        s.delivered_ce = info->tcpi_delivered_ce;
        s.dsack_dups = info->tcpi_dsack_dups;
        s.reord_seen = info->tcpi_reord_seen;
        s.bytes_sent = info->tcpi_bytes_sent;
        s.bytes_retrans = info->tcpi_bytes_retrans;
        s.rcv_ooopack = info->tcpi_rcv_ooopack;
        s.snd_wnd = info->tcpi_snd_wnd;
        tcp_stats_print(&s);
        free(s.dctcp);
        free(s.bbr_info);
    }
    //TODO Ignore this for now
//    if (tb[INET_DIAG_MD5SIG]) {
//        struct tcp_diag_md5sig *sig = RTA_DATA(tb[INET_DIAG_MD5SIG]);
//        int len = RTA_PAYLOAD(tb[INET_DIAG_MD5SIG]);
//
//        out(" md5keys:");
//        print_md5sig(sig++);
//        for (len -= sizeof(*sig); len > 0; len -= sizeof(*sig)) {
//            out(",");
//            print_md5sig(sig++);
//        }
//    }
//    if (tb[INET_DIAG_ULP_INFO]) {
//        struct rtattr *ulpinfo[INET_ULP_INFO_MAX + 1] = { 0 };
//
//        parse_rtattr_nested(ulpinfo, INET_ULP_INFO_MAX,
//                            tb[INET_DIAG_ULP_INFO]);
//
//        if (ulpinfo[INET_ULP_INFO_NAME])
//            out(" tcp-ulp-%s",
//                rta_getattr_str(ulpinfo[INET_ULP_INFO_NAME]));
//
//        if (ulpinfo[INET_ULP_INFO_TLS]) {
//            struct rtattr *tlsinfo[TLS_INFO_MAX + 1] = { 0 };
//
//            parse_rtattr_nested(tlsinfo, TLS_INFO_MAX,
//                                ulpinfo[INET_ULP_INFO_TLS]);
//
//            tcp_tls_version(tlsinfo[TLS_INFO_VERSION]);
//            tcp_tls_cipher(tlsinfo[TLS_INFO_CIPHER]);
//            tcp_tls_conf("rxconf", tlsinfo[TLS_INFO_RXCONF]);
//            tcp_tls_conf("txconf", tlsinfo[TLS_INFO_TXCONF]);
//            tcp_tls_zc_sendfile(tlsinfo[TLS_INFO_ZC_RO_TX]);
//        }
//        if (ulpinfo[INET_ULP_INFO_MPTCP]) {
//            struct rtattr *sfinfo[MPTCP_SUBFLOW_ATTR_MAX + 1] =
//                    { 0 };
//
//            parse_rtattr_nested(sfinfo, MPTCP_SUBFLOW_ATTR_MAX,
//                                ulpinfo[INET_ULP_INFO_MPTCP]);
//            mptcp_subflow_info(sfinfo);
//        }
//    }
}

static void parse_diag_msg(struct nlmsghdr *nlh, struct sockstat *s)
{
    struct rtattr *tb[INET_DIAG_MAX+1];
    struct inet_diag_msg *r = NLMSG_DATA(nlh);

    parse_rtattr(tb, INET_DIAG_MAX, (struct rtattr *)(r+1),
                 nlh->nlmsg_len - NLMSG_LENGTH(sizeof(*r)));

    s->state	= r->idiag_state;
    s->local.family	= s->remote.family = r->idiag_family;
    s->lport	= ntohs(r->id.idiag_sport);
    s->rport	= ntohs(r->id.idiag_dport);
    s->wq		= r->idiag_wqueue;
    s->rq		= r->idiag_rqueue;
    s->ino		= r->idiag_inode;
    s->uid		= r->idiag_uid;
    s->iface	= r->id.idiag_if;
    s->sk		= cookie_sk_get(&r->id.idiag_cookie[0]);

    s->mark = 0;
    if (tb[INET_DIAG_MARK])
        s->mark = rta_getattr_u32(tb[INET_DIAG_MARK]);
    s->cgroup_id = 0;
    if (tb[INET_DIAG_CGROUP_ID])
        s->cgroup_id = rta_getattr_u64(tb[INET_DIAG_CGROUP_ID]);
    if (tb[INET_DIAG_PROTOCOL])
        s->raw_prot = rta_getattr_u8(tb[INET_DIAG_PROTOCOL]);
    else
        s->raw_prot = 0;

    if (s->local.family == AF_INET)
        s->local.bytelen = s->remote.bytelen = 4;
    else
        s->local.bytelen = s->remote.bytelen = 16;

    memcpy(s->local.data, r->id.idiag_src, s->local.bytelen);
    memcpy(s->remote.data, r->id.idiag_dst, s->local.bytelen);
}

static int inet_show_sock(struct nlmsghdr *nlh,
                          struct sockstat *s)
{
    struct rtattr *tb[INET_DIAG_MAX+1];
    struct inet_diag_msg *r = NLMSG_DATA(nlh);
    unsigned char v6only = 0;

    parse_rtattr(tb, INET_DIAG_MAX, (struct rtattr *)(r+1),
                 nlh->nlmsg_len - NLMSG_LENGTH(sizeof(*r)));

    if (tb[INET_DIAG_PROTOCOL])
        s->type = rta_getattr_u8(tb[INET_DIAG_PROTOCOL]);

    if (s->local.family == AF_INET6 && tb[INET_DIAG_SKV6ONLY])
        v6only = rta_getattr_u8(tb[INET_DIAG_SKV6ONLY]);

    inet_stats_print(s, v6only);

    if (show_options) {
        struct tcpstat t = {};

        t.timer = r->idiag_timer;
        t.timeout = r->idiag_expires;
        t.retrans = r->idiag_retrans;
        tcp_timer_print(&t);
    }

    if (show_mem || show_tcpinfo) {
        tcp_show_info(nlh, r, tb);
    }

    return 0;
}

static int tcpdiag_send(int fd, int protocol, struct filter *f)
{
    struct sockaddr_nl nladdr = { .nl_family = AF_NETLINK };
    struct {
        struct nlmsghdr nlh;
        struct inet_diag_req r;
    } req = {
            .nlh.nlmsg_len = sizeof(req),
            .nlh.nlmsg_flags = NLM_F_ROOT | NLM_F_MATCH | NLM_F_REQUEST,
            .nlh.nlmsg_seq = MAGIC_SEQ,
            .r.idiag_family = AF_INET,
            .r.idiag_states = f->states,
    };
    struct msghdr msg;
    struct iovec iov[3];
    int iovlen = 1;

    if (protocol == IPPROTO_TCP)
        req.nlh.nlmsg_type = TCPDIAG_GETSOCK;
    else if (protocol == IPPROTO_DCCP)
        req.nlh.nlmsg_type = DCCPDIAG_GETSOCK;
    else
        return -1;

    if (show_mem) {
        req.r.idiag_ext |= (1<<(INET_DIAG_MEMINFO-1));
        req.r.idiag_ext |= (1<<(INET_DIAG_SKMEMINFO-1));
    }

    if (show_tcpinfo) {
        req.r.idiag_ext |= (1<<(INET_DIAG_INFO-1));
        req.r.idiag_ext |= (1<<(INET_DIAG_VEGASINFO-1));
        req.r.idiag_ext |= (1<<(INET_DIAG_CONG-1));
    }

    iov[0] = (struct iovec){
            .iov_base = &req,
            .iov_len = sizeof(req)
    };

    msg = (struct msghdr) {
            .msg_name = (void *)&nladdr,
            .msg_namelen = sizeof(nladdr),
            .msg_iov = iov,
            .msg_iovlen = iovlen,
    };

    if (sendmsg(fd, &msg, 0) < 0) {
        close(fd);
        return -1;
    }

    return 0;
}

static int sockdiag_send(int family, int fd, int protocol, struct filter *f)
{
    struct sockaddr_nl nladdr = { .nl_family = AF_NETLINK };
    DIAG_REQUEST(req, struct inet_diag_req_v2 r);
    __u32	proto;
    struct msghdr msg;
    struct rtattr rta_proto;
    struct iovec iov[5];
    int iovlen = 1;

    if (family == PF_UNSPEC)
        return tcpdiag_send(fd, protocol, f);

    memset(&req.r, 0, sizeof(req.r));
    req.r.sdiag_family = family;
    req.r.sdiag_protocol = protocol;
    req.r.idiag_states = f->states;
    if (show_mem) {
        req.r.idiag_ext |= (1<<(INET_DIAG_MEMINFO-1));
        req.r.idiag_ext |= (1<<(INET_DIAG_SKMEMINFO-1));
    }

    if (show_tcpinfo) {
        req.r.idiag_ext |= (1<<(INET_DIAG_INFO-1));
        req.r.idiag_ext |= (1<<(INET_DIAG_VEGASINFO-1));
        req.r.idiag_ext |= (1<<(INET_DIAG_CONG-1));
    }

    iov[0] = (struct iovec){
            .iov_base = &req,
            .iov_len = sizeof(req)
    };

    /* put extended protocol attribute, if required */
    if (protocol > 255) {
        rta_proto.rta_type = INET_DIAG_REQ_PROTOCOL;
        rta_proto.rta_len = RTA_LENGTH(sizeof(proto));
        proto = protocol;
        iov[iovlen] = (struct iovec){ &rta_proto, sizeof(rta_proto) };
        iov[iovlen + 1] = (struct iovec){ &proto, sizeof(proto) };
        req.nlh.nlmsg_len += RTA_LENGTH(sizeof(proto));
        iovlen += 2;
    }

    msg = (struct msghdr) {
            .msg_name = (void *)&nladdr,
            .msg_namelen = sizeof(nladdr),
            .msg_iov = iov,
            .msg_iovlen = iovlen,
    };

    if (sendmsg(fd, &msg, 0) < 0) {
        close(fd);
        return -1;
    }

    return 0;
}

struct inet_diag_arg {
    struct filter *f;
    int protocol;
    struct rtnl_handle *rth;
};

static int kill_inet_sock(struct nlmsghdr *h, void *arg, struct sockstat *s)
{
    struct inet_diag_msg *d = NLMSG_DATA(h);
    struct inet_diag_arg *diag_arg = arg;
    struct rtnl_handle *rth = diag_arg->rth;

    DIAG_REQUEST(req, struct inet_diag_req_v2 r);

    req.nlh.nlmsg_type = SOCK_DESTROY;
    req.nlh.nlmsg_flags = NLM_F_REQUEST | NLM_F_ACK;
    req.nlh.nlmsg_seq = ++rth->seq;
    req.r.sdiag_family = d->idiag_family;
    req.r.sdiag_protocol = diag_arg->protocol;
    req.r.id = d->id;

    return rtnl_talk(rth, &req.nlh, NULL);
}

static int show_one_inet_sock(struct nlmsghdr *h, void *arg)
{
    int err;
    struct inet_diag_arg *diag_arg = arg;
    struct inet_diag_msg *r = NLMSG_DATA(h);
    struct sockstat s = {};

    if (!(diag_arg->f->families & FAMILY_MASK(r->idiag_family)))
        return 0;

    parse_diag_msg(h, &s);
    s.type = diag_arg->protocol;

    if (diag_arg->f->kill && kill_inet_sock(h, arg, &s) != 0) {
        if (errno == EOPNOTSUPP || errno == ENOENT) {
            /* Socket can't be closed, or is already closed. */
            return 0;
        } else {
            perror("SOCK_DESTROY answers");
            return -1;
        }
    }

    err = inet_show_sock(h, &s);
    if (err < 0)
        return err;

    return 0;
}

static int inet_show_netlink(struct filter *f, FILE *dump_fp, int protocol)
{
    int err = 0;
    struct rtnl_handle rth, rth2;
    int family = PF_INET;
    struct inet_diag_arg arg = { .f = f, .protocol = protocol };

    if (rtnl_open_byproto(&rth, 0, NETLINK_SOCK_DIAG))
        return -1;

    if (f->kill) {
        if (rtnl_open_byproto(&rth2, 0, NETLINK_SOCK_DIAG)) {
            rtnl_close(&rth);
            return -1;
        }
        arg.rth = &rth2;
    }

    rth.dump = MAGIC_SEQ;
    rth.dump_fp = dump_fp;
    if (preferred_family == PF_INET6)
        family = PF_INET6;

    /* extended protocol will use INET_DIAG_REQ_PROTOCOL,
	 * not supported by older kernels. On such kernel
	 * rtnl_dump will bail with rtnl_dump_error().
	 * Suppress the error to avoid confusing the user
	 */
    if (protocol > 255)
        rth.flags |= RTNL_HANDLE_F_SUPPRESS_NLERR;

again:
    if ((err = sockdiag_send(family, rth.fd, protocol, f)))
        goto Exit;

    if ((err = rtnl_dump_filter(&rth, show_one_inet_sock, &arg))) {
        if (family != PF_UNSPEC) {
            family = PF_UNSPEC;
            goto again;
        }
        goto Exit;
    }
    if (family == PF_INET && preferred_family != PF_INET) {
        family = PF_INET6;
        goto again;
    }

Exit:
    rtnl_close(&rth);
    if (arg.rth)
        rtnl_close(arg.rth);
    return err;
}

static int tcp_show_netlink_file(struct filter *f)
{
    FILE	*fp;
    char	buf[16384];
    int	err = -1;

    if ((fp = fopen(getenv("TCPDIAG_FILE"), "r")) == NULL) {
        perror("fopen($TCPDIAG_FILE)");
        return err;
    }

    while (1) {
        int err2;
        size_t status, nitems;
        struct nlmsghdr *h = (struct nlmsghdr *)buf;
        struct sockstat s = {};

        status = fread(buf, 1, sizeof(*h), fp);
        if (status != sizeof(*h)) {
            if (ferror(fp))
                perror("Reading header from $TCPDIAG_FILE");
            if (feof(fp))
                fprintf(stderr, "Unexpected EOF reading $TCPDIAG_FILE");
            break;
        }

        nitems = NLMSG_ALIGN(h->nlmsg_len - sizeof(*h));
        status = fread(h+1, 1, nitems, fp);

        if (status != nitems) {
            if (ferror(fp))
                perror("Reading $TCPDIAG_FILE");
            if (feof(fp))
                fprintf(stderr, "Unexpected EOF reading $TCPDIAG_FILE");
            break;
        }

        /* The only legal exit point */
        if (h->nlmsg_type == NLMSG_DONE) {
            err = 0;
            break;
        }

        if (h->nlmsg_type == NLMSG_ERROR) {
            struct nlmsgerr *err = (struct nlmsgerr *)NLMSG_DATA(h);

            if (h->nlmsg_len < NLMSG_LENGTH(sizeof(struct nlmsgerr))) {
                fprintf(stderr, "ERROR truncated\n");
            } else {
                errno = -err->error;
                perror("TCPDIAG answered");
            }
            break;
        }

        parse_diag_msg(h, &s);
        s.type = IPPROTO_TCP;

        err2 = inet_show_sock(h, &s);
        if (err2 < 0) {
            err = err2;
            break;
        }
    }

    fclose(fp);
    return err;
}

static int tcp_show(struct filter *f)
{
    FILE *fp = NULL;
    char *buf = NULL;
    int bufsize = 1024*1024;

    if (!filter_af_get(f, AF_INET) && !filter_af_get(f, AF_INET6))
        return 0;

    if (getenv("TCPDIAG_FILE"))
        return tcp_show_netlink_file(f);

    if (!getenv("PROC_NET_TCP") && !getenv("PROC_ROOT")
        && inet_show_netlink(f, NULL, IPPROTO_TCP) == 0)
        return 0;

    /* Sigh... We have to parse /proc/net/tcp... */
    while (bufsize >= 64*1024) {
        if ((buf = malloc(bufsize)) != NULL)
            break;
        bufsize /= 2;
    }
    if (buf == NULL) {
        errno = ENOMEM;
        return -1;
    }

    if ((fp = net_tcp_open()) == NULL)
        goto outerr;

    setbuffer(fp, buf, bufsize);
    if (generic_record_read(fp, tcp_show_line, f, AF_INET))
        goto outerr;
    fclose(fp);

    free(buf);
    return 0;

outerr:
    do {
        int saved_errno = errno;

        free(buf);
        if (fp)
            fclose(fp);
        errno = saved_errno;
        return -1;
    } while (0);
}

static void _usage(FILE *dest)
{
    fprintf(dest,
            "Usage: sss [ OPTIONS ]\n"
            "   -h, --help          this message\n"
            "   -V, --version       output version information\n"
            "   -a, --all           display all sockets\n"
            "   -l, --listening     display listening sockets\n"
            "   -o, --options       show timer information\n"
            "   -m, --memory        show socket memory usage\n"
            "   -i, --info          show internal TCP information\n"
            "\n"
            "   -H, --header        Print header line\n"
            "\n"
            "       --time          the time to run this tool for (see also interval)\n"
            "       --interval      interval between printing current statistics\n"
            "   -O, --out           write output to this file instead of stdout\n"
    );
}

static void help(void) __attribute__((noreturn));
static void help(void)
{
    _usage(stdout);
    exit(0);
}

static void usage(void) __attribute__((noreturn));
static void usage(void)
{
    _usage(stderr);
    exit(-1);
}

#define OPT_TIME 256
#define OPT_INTERVAL 257

static const struct option long_opts[] = {
        { "options", 0, 0, 'o' },
        { "memory", 0, 0, 'm' },
        { "info", 0, 0, 'i' },
        { "all", 0, 0, 'a' },
        { "listening", 0, 0, 'l' },
        { "version", 0, 0, 'V' },
        { "help", 0, 0, 'h' },
        { "header", 0, 0, 'H' },
        { "out", 1, 0, 'O' },
        { "time", 1, 0, OPT_TIME },
        { "interval", 1, 0, OPT_INTERVAL },
        { 0 }

};

static long parse_number(const char *str)
{
    char *endptr;
    long val;

    errno = 0;
    val = strtol(str, &endptr, 10);

    if (errno != 0) {
        perror("strtol");
        exit(EXIT_FAILURE);
    }

    if (str == endptr) {
        fprintf(stderr, "Unable to convert numeric argument\n");
        exit(EXIT_FAILURE);
    }

    return val;
}

int main(int argc, char *argv[])
{
    int ch;
    int state_filter = 0;
    long time = 100;
    long interval = 100;
    char *file_path = NULL;

    while ((ch = getopt_long(argc, argv,
                             "halomivVHO:",
                             long_opts, NULL)) != EOF) {
        switch (ch) {
            case 'o':
                show_options = 1;
                break;
            case 'm':
                show_mem = 1;
                break;
            case 'i':
                show_tcpinfo = 1;
                break;
            case 'a':
                state_filter = SS_ALL;
                break;
            case 'l':
                state_filter = (1 << SS_LISTEN) | (1 << SS_CLOSE);
                break;
            case 'v':
            case 'V':
                printf("simple socket statistics %s\n", version);
                exit(0);
            case 'H':
                show_header = 1;
                break;
            case 'O':
                file_path = optarg;
                break;
            case OPT_TIME:
                time = parse_number(optarg);
                break;
            case OPT_INTERVAL:
                interval = parse_number(optarg);
                break;
            case 'h':
                help();
            case '?':
            default:
                usage();
        }
    }

    if (time == 0 || interval == 0) {
        fprintf(stderr, "time/interval cannot be zero!\n");
        exit(EXIT_FAILURE);
    }

    // Show only tcp sockets and ipv4 by default
    filter_db_set(&current_filter, TCP_DB, true);
    filter_af_set(&current_filter, AF_INET);

    filter_states_set(&current_filter, state_filter);
    filter_merge_defaults(&current_filter);

    if (current_filter.dbs == 0) {
        fprintf(stderr, "ss: no socket tables to show with such filter.\n");
        exit(0);
    }
    if (current_filter.families == 0) {
        fprintf(stderr, "ss: no families to show with such filter.\n");
        exit(0);
    }
    if (current_filter.states == 0) {
        fprintf(stderr, "ss: no socket states to show with such filter.\n");
        exit(0);
    }

    if (!(current_filter.dbs & (current_filter.dbs - 1)))
        columns[COL_NETID].disabled = 1;

    if (!(current_filter.states & (current_filter.states - 1)))
        columns[COL_STATE].disabled = 1;

    if (show_header)
        print_header();

    fflush(stdout);

    long repetitions = (time + interval - 1) / interval;

    struct timespec tspec;
    tspec.tv_sec = interval / 1000;
    tspec.tv_nsec = (interval % 1000) * 1000000;

    if (file_path == NULL) {
        out_file = stdout;
    } else {
        out_file = fopen(file_path, "w");
        if (out_file == NULL) {
            fprintf(stderr, "Could not open file. Fallback to stdout.\n");
            out_file = stdout;
        }
    }

    current_time = 0;
    for (long i = 0; i < repetitions - 1; ++i) {
        tcp_show(&current_filter);
        render();
        if (show_header)
            print_header();
        nanosleep(&tspec, NULL);
        current_time += interval;
    }
    tcp_show(&current_filter);
    render();

    if (out_file != stdout) {
        fclose(out_file);
    }

    return 0;
}
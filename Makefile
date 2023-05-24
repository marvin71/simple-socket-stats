CC:=gcc

CCOPTS = -O2 -pipe
WFLAGS := -Wall -Wstrict-prototypes  -Wmissing-prototypes
WFLAGS += -Wmissing-declarations -Wold-style-definition -Wformat=2

CFLAGS := $(WFLAGS) $(CCOPTS) $(CFLAGS)

SSSOBJ=sss.o libnetlink.o
TARGETS=sss

.PHONY: all clean

all: $(TARGETS)

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

sss: $(SSSOBJ)
	$(CC) $^ $(LDFLAGS) $(LDLIBS) -o $@

clean:
	rm -f *.o $(TARGETS)

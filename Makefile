CFLAGS += -Wall -W -pedantic -std=c99
# CFLAGS += -Wall -W -pedantic -std=c89
CFLAGS += -I. -O2
LDLIBS += -lsqlite3

all: iokit_tool_10 iokit_tool kext_tool_10 kext_tool rtti_tool knonce

iokit_tool: iokit_tool.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

iokit_tool_10: iokit_tool_10.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

kext_tool_10: kext_tool_10.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

kext_tool: kext_tool.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

rtti_tool: rtti_tool.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

knonce: kernel/knonce.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

clean:
	rm -f iokit_tool_10 iokit_tool kext_tool_10 kext_tool rtti_tool knonce
	rm -rf *.dSYM

# EOF

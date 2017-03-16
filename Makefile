CFLAGS += -Wall -W -pedantic -std=c99
#CFLAGS += -Wall -W -pedantic -std=c89
CFLAGS += -I. -O2
LDLIBS += -lsqlite3

iokit_tool: iokit_tool.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

iokit_tool_10: iokit_tool_10.c
	$(CC) -o $@ $(CFLAGS) $^ $(LDLIBS) -lstdc++

COQFLAGS = -Q theories CodegenOptimizations
COQC = coqc

SOURCES = $(wildcard theories/*.v)
OBJECTS = $(SOURCES:.v=.vo)

all: $(OBJECTS)

theories/%.vo: theories/%.v
	$(COQC) $(COQFLAGS) $<

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob

.PHONY: all clean

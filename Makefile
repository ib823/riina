COQC = coqc
COQFLAGS = -Q 02_FORMAL/coq TERAS

SOURCES = $(shell find 02_FORMAL/coq -name '*.v' | sort)
OBJECTS = $(SOURCES:.v=.vo)

all: $(OBJECTS)

%.vo: %.v
$(COQC) $(COQFLAGS) $

clean:
find 02_FORMAL/coq -name '*.vo' -delete
find 02_FORMAL/coq -name '*.glob' -delete
find 02_FORMAL/coq -name '*.aux' -delete
find 02_FORMAL/coq -name '.*.aux' -delete

.PHONY: all clean

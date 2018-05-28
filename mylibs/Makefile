
COQ = coqc
COQDOC = coqdoc -g

VFILES = $(wildcard *.v)

%.vo: %.v
	$(COQ) $<

%.glob: %.vo
	@true

%.html: %.v %.vo
	$(COQDOC) $<


doc: $(VFILES:.v=.glob)
	$(COQDOC) -toc $(VFILES)

clean :
	rm -f $(VFILES:.v=.vo)
	rm -f .*.aux
	rm -f *.crashcoqide
	rm -f *.glob
	rm -f *.html
	rm -f coqdoc.css
	rm -f lia.cache
	rm -f .lia.cache

.PHONY: clean
.PRECIOUS: %.vo %.glob


MYLIBSDIR = .

.DEFAULT_GOAL := mylibs

all: mylibs doc

mylibs: $(VFILES:.v=.vo)

include mylibs.mk


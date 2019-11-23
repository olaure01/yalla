
COQ = coqc -R $(OLLIBSDIR) "" -R $(YALLADIR) ""
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



OLLIBSDIR = ../ollibs
YALLADIR  = ../yalla

.DEFAULT_GOAL := all

all: yallaneeded microyalla

yallaneeded:
	cd $(YALLADIR) && $(MAKE) microyallaneeded

microyalla: $(VFILES:.v=.vo)

nano_macro_ll.vo: nano_macro_ll.v nanoll.vo

nano_macro_ill.vo: nano_macro_ill.v nanoill.vo

micro_macro_ll.vo: micro_macro_ll.v microll.vo

micro_macro_ill.vo: micro_macro_ill.v microill.vo

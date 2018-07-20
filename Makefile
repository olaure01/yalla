
COQDOC = coqdoc -g -toc

OLLIBSDIR = ollibs
YALLADIR  = yalla
YALLAHTMLDIR   = yalla_html

YALLAHTMLFILE   = yalla_html.tgz
OLLIBSVFILES = Bool_more.v Injective.v Surjective.v nattree.v List_more.v Permutation_more.v CyclicPerm.v Permutation_solve.v CPermutation_solve.v genperm.v fmsetlist.v fmsetoidlist.v
YALLAVFILES  = $(wildcard $(YALLADIR)/*.v)

all: ollibs yalla doc

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

yalla:
	cd $(YALLADIR) && $(MAKE)

doc:
	cd $(OLLIBSDIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@
	cd $(YALLADIR) && $(COQDOC) $(addprefix ../$(OLLIBSDIR)/,$(OLLIBSVFILES)) $(addprefix ../,$(YALLAVFILES))

htmlfiles: doc
	rm -f $(YALLAHTMLFILE)
	mkdir $(YALLAHTMLDIR)
	cp $(YALLADIR)/*.html $(YALLAHTMLDIR)/
	cp $(YALLADIR)/coqdoc.css $(YALLAHTMLDIR)/
	tar czf $(YALLAHTMLFILE) $(YALLAHTMLDIR)
	rm -rf $(YALLAHTMLDIR)

clean:
	cd $(OLLIBSDIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@

.PHONY: ollibs yalla clean


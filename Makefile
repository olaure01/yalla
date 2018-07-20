
COQDOC = coqdoc -g -toc

OLLIBSDIR = ollibs
YALLADIR  = yalla
YALLAARCHDIR   = yalla_lib
YALLAHTMLDIR   = yalla_html

YALLAARCHFILE = yalla.tgz
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

arch_yalla:
	rm -f $(YALLAARCHFILE)
	mkdir $(YALLAARCHDIR)
	mkdir $(YALLAARCHDIR)/$(OLLIBSDIR)
	mkdir $(YALLAARCHDIR)/$(YALLADIR)
	cp README $(YALLAARCHDIR)/
	cp Makefile $(YALLAARCHDIR)/
	cp $(OLLIBSDIR)/README_yalla $(YALLAARCHDIR)/$(OLLIBSDIR)/README
	cp $(OLLIBSDIR)/Makefile $(YALLAARCHDIR)/$(OLLIBSDIR)/
	cp $(OLLIBSDIR)/ollibs.mk $(YALLAARCHDIR)/$(OLLIBSDIR)/
	cp $(addprefix $(OLLIBSDIR)/,$(OLLIBSVFILES)) $(YALLAARCHDIR)/$(OLLIBSDIR)/
	cp $(YALLADIR)/README $(YALLAARCHDIR)/$(YALLADIR)/
	cp $(YALLADIR)/RELEASE_NOTES $(YALLAARCHDIR)/$(YALLADIR)/
	cp $(YALLADIR)/Makefile $(YALLAARCHDIR)/$(YALLADIR)/
	cp $(YALLADIR)/*.v $(YALLAARCHDIR)/$(YALLADIR)/
	tar czf $(YALLAARCHFILE) $(YALLAARCHDIR)
	rm -rf $(YALLAARCHDIR)

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


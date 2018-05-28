
COQDOC = coqdoc -g -toc

MYLIBSDIR = mylibs
YALLADIR  = yalla
YALLAARCHDIR   = yalla_lib
YALLAHTMLDIR   = yalla_html

YALLAARCHFILE = yalla.tgz
YALLAHTMLFILE   = yalla_html.tgz
MYLIBSVFILES = Bool_more.v Injective.v Surjective.v nattree.v List_more.v Permutation_more.v CyclicPerm.v Permutation_solve.v CPermutation_solve.v genperm.v fmsetlist.v fmsetoidlist.v
YALLAVFILES  = $(wildcard $(YALLADIR)/*.v)

all: mylibs yalla doc

mylibs:
	cd $(MYLIBSDIR) && $(MAKE)

yalla:
	cd $(YALLADIR) && $(MAKE)

doc:
	cd $(MYLIBSDIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@
	cd $(YALLADIR) && $(COQDOC) $(addprefix ../$(MYLIBSDIR)/,$(MYLIBSVFILES)) $(addprefix ../,$(YALLAVFILES))

arch_yalla:
	rm -f $(YALLAARCHFILE)
	mkdir $(YALLAARCHDIR)
	mkdir $(YALLAARCHDIR)/$(MYLIBSDIR)
	mkdir $(YALLAARCHDIR)/$(YALLADIR)
	cp README $(YALLAARCHDIR)/
	cp Makefile $(YALLAARCHDIR)/
	cp $(MYLIBSDIR)/README_yalla $(YALLAARCHDIR)/$(MYLIBSDIR)/README
	cp $(MYLIBSDIR)/Makefile $(YALLAARCHDIR)/$(MYLIBSDIR)/
	cp $(MYLIBSDIR)/mylibs.mk $(YALLAARCHDIR)/$(MYLIBSDIR)/
	cp $(addprefix $(MYLIBSDIR)/,$(MYLIBSVFILES)) $(YALLAARCHDIR)/$(MYLIBSDIR)/
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
	cd $(MYLIBSDIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@

.PHONY: mylibs yalla clean


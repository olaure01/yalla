
COQDOC = coqdoc -g -toc

MYLIBSDIR = mylibs
YALLADIR  = yalla
YALLAARCHDIR   = yalla_lib

YALLAARCHFILE = yalla.tgz
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
	cp $(YALLADIR)/Makefile $(YALLAARCHDIR)/$(YALLADIR)/
	cp $(YALLADIR)/*.v $(YALLAARCHDIR)/$(YALLADIR)/
	tar czf $(YALLAARCHFILE) $(YALLAARCHDIR)
	rm -rf $(YALLAARCHDIR)

clean:
	cd $(MYLIBSDIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@

.PHONY: mylibs yalla clean


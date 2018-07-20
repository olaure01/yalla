
COQDOC = coqdoc -g -toc

OLLIBSDIR = ollibs
YALLADIR  = yalla
YALLAHTMLDIR   = yalla_html

YALLAHTMLFILE   = yalla_html.tgz
OLLIBSVFILES = $(wildcard $(OLLIBSDIR)/*.v)
YALLAVFILES  = $(wildcard $(YALLADIR)/*.v)

all: ollibs yalla doc

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

yalla:
	cd $(YALLADIR) && $(MAKE)

doc:
	cd $(OLLIBSDIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@
	cd $(YALLADIR) && $(COQDOC) $(addprefix ../,$(OLLIBSVFILES)) $(addprefix ../,$(YALLAVFILES))

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


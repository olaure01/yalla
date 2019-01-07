
COQDOC = coqdoc -g -toc

OLLIBSDIR = ollibs
MICROYALLADIR  = microyalla
YALLADIR  = yalla
YALLAHTMLDIR   = yalla_html

YALLAHTMLFILE   = yalla_html.tgz
OLLIBSVFILES = $(wildcard $(OLLIBSDIR)/*.v)
MICROYALLAVFILES  = $(wildcard $(MICROYALLADIR)/*.v)
YALLAVFILES  = $(wildcard $(YALLADIR)/*.v)

all: ollibs microyalla yalla doc

ollibs:
	cd $(OLLIBSDIR) && $(MAKE)

microyalla:
	cd $(MICROYALLADIR) && $(MAKE)

yalla:
	cd $(YALLADIR) && $(MAKE)

doc:
	cd $(OLLIBSDIR) && $(MAKE) $@
	cd $(MICROYALLADIR) && $(MAKE) $@
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
	cd $(MICROYALLADIR) && $(MAKE) $@
	cd $(YALLADIR) && $(MAKE) $@

.PHONY: ollibs microyalla yalla clean


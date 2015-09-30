# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrReals
SUBDIRS  := collections
INCFLAGS := -R collections/src SsrCollections -R 3rdparty $(NAME) -R src $(NAME)
COQFILES := \
	3rdparty/bigenough.v \
	3rdparty/polyorder.v \
	3rdparty/polyrcf.v \
	3rdparty/cauchyreals.v \
	3rdparty/realalg.v \
	3rdparty/complex.v \
	src/funtype.v \
	src/reals.v \
	src/dedekind.v \
	src/realanalysis.v \
	src/sandbox.v

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
.PHONY: dist

DISTDIR = alternate-reals
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(TAROPT) $(DISTDIR)
	rm -rf $(DISTDIR)

# --------------------------------------------------------------------
this-clean::
	rm -f src/*.vo src/*.d src/*.glob

this-distclean::
	rm -f $(shell find . -name '*~')

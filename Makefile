# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrReals
SUBDIRS  :=
INCFLAGS :=
INCFLAGS += -R finmap $(NAME) -R src $(NAME)
COQFILES := \
	finmap/finmap.v \
	finmap/xfinmap.v \
	src/boolp.v \
	src/reals.v \
	src/dedekind.v \
	src/discrete.v \
	src/realseq.v \
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
this-distclean::
	rm -f $(shell find . -name '*~')

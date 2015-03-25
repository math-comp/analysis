# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrReals
SUBDIRS  :=
INCFLAGS := -R src $(NAME)
COQFILES := src/reals.v

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
	rm src/*.vo src/*.d src/*.glob

this-distclean::
	rm -f $(shell find . -name '*~')

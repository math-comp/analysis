# -*- Makefile -*-

# --------------------------------------------------------------------
include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
.PHONY: dist

DISTDIR = mathcomp-analysis
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(TAROPT) $(DISTDIR)
	rm -rf $(DISTDIR)

# --------------------------------------------------------------------
.PHONY: count

COQFILES := $(shell grep '.v$$' _CoqProject)

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'

# --------------------------------------------------------------------
this-distclean::
	rm -f $(shell find . -name '*~')

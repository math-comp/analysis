# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrReals
INCFLAGS := -R src $(NAME)
COQFILES := \
	src/xfinmap.v \
	src/boolp.v \
	src/xsets.v \
	src/reals.v \
	src/dedekind.v \
	src/discrete.v \
	src/realseq.v \
	src/realsum.v \
	src/distr.v \
	src/coupling.v \
	src/filters.v

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

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'

# --------------------------------------------------------------------
this-clean::
	rm -f $(COQFILES:%.v=%.aux)

this-distclean::
	rm -f $(shell find . -name '*~')

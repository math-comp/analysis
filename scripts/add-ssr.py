#! /usr/bin/env python

# (c) Copyright 2012--2014 - Pierre-Yves Strub

# --------------------------------------------------------------------
import sys, os, re, codecs, shutil, itertools as it

# --------------------------------------------------------------------
def flatten(s):
    return list(it.chain.from_iterable(s))

# --------------------------------------------------------------------
def isssrmodname(modname):
    return os.path.dirname(modname) == ''

# --------------------------------------------------------------------
_depcache = dict()

def _dependencies(libdir, modname):
    if isssrmodname(modname) and modname in _depcache:
        return _depcache[modname]['direct']

    reqre = re.compile(r'^Require(?: (?:Import|Export)) (.*)\.')

    filename = modname + '.v'
    if isssrmodname(modname):
        filename = os.path.join(libdir, filename)

    with codecs.open(filename, 'r', 'latin-1') as input:
        contents = input.read()
    contents = [x.strip() for x in contents.splitlines()]
    contents = [re.sub(r'\s+', ' ', x) for x in contents]
    modules  = flatten(map(reqre.findall, contents))
    modules  = set(flatten(x.split() for x in modules))
    modules  = \
        [x for x in modules \
             if os.path.exists(os.path.join(libdir, x + '.v'))]

    if not isssrmodname(modname):
        return set(modules)

    _depcache[modname] = dict(direct = set(modules), all = None)

    return _depcache[modname]['direct']

# --------------------------------------------------------------------
def _alldependencies(libdir, modname):
    if modname.endswith('.v'):
        modname = os.path.splitext(modname)[0]

    proceeds = set()
    alldeps  = set()
    stack    = [modname]

    if isssrmodname(modname):
        alldeps.add(modname)

    while stack:
        thismodname = stack.pop()
        thisdeps    = _depcache.get(modname, {}).get('all', None)

        if thisdeps is not None:
            alldeps .update(thisdeps)
            proceeds.update(thisdeps)
            continue

        thisdeps = _dependencies(libdir, thismodname)

        alldeps.update(thisdeps); proceeds.add(thismodname)
        stack.extend(list(thisdeps.difference(proceeds)))

    return alldeps

# --------------------------------------------------------------------
def _differ(file1, file2):
    return open(file1, 'rb').read() != open(file2, 'rb').read()

# --------------------------------------------------------------------
def _main(libdir, *modnames):
    allmods = [_alldependencies(libdir, x) for x in modnames]
    allmods = set(flatten(allmods))
    lname   = max(map(len, allmods) + [0])

    print >>sys.stderr, 'Copying: %s' % ', '.join(sorted(allmods))
    for modname in allmods:
        srcname = os.path.join(libdir, modname + '.v')
        dstname = modname + '.v'

        if not os.path.exists(dstname) or _differ(srcname, dstname):
            shutil.copy(srcname, dstname)
            print >>sys.stderr, "[%*s]: copied" % (lname, modname)
        else:
            print >>sys.stderr, "[%*s]: up-to-date" % (lname, modname)

    if os.path.exists('Makefile'):
        os.utime('Makefile', None)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main(sys.argv[1], *sys.argv[2:])

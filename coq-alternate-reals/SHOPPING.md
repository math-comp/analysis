### Differentials
 
- URL: <https://github.com/wangpengmit/ssmatrix-theory>
- Internship with G. Gonthier (Wang Peng, MIT) in 2014
	* <https://people.csail.mit.edu/wangpeng/>
- Last commit more than 1 year ago
- No relations with reals
- Contents:
	* right-modules, bi-modules, etc...
	* ring of n-ary functions
		+ functions are represented as elements of an abstract ring
		+ with gradient, Jacobian, etc...
	* abstract derivation over a ring R with result in a R-(bi)-module V:
		+ `d (a * b) = d a *: b + a :* d b`
		+ Then extension to a linear operator
	* mxdiff: lifting of differential to matrices
		+ only contains that `mapmx` preserves the differential 
		+ some results about tensorial product
	* mxmodule
		+ deals with matrices over a bi-module
		+ equip M[R]_(m,n) with a bi-module structure
		+ define the tensorial product
- Questions:
	* status w.r.t. the integration of the library in ssreflect?
	* why separating the first property to the linearity?
	* why using a column (w.r.t. row) vector in the mixin of `nfun`?

### RStruct

- URL: <https://github.com/Sobernard/Struct>
- Structure for equipping the Coq reals with SSR algebraic structures)
	* See: https://github.com/Sobernard/Struct
	* Going to be captured by this repository development

### Topology

- URL: <svn://scm.gforge.inria.fr/svnroot/marelledocs/proofs/topology>
- Based on Rstruct
- Contents
	* a bit about set theory (with bool/Prop reflection)
		+ going to be captured by Cyril's library
	* topology (opened-based)
		+ Convergence, continuity, compacity (T2 space)
		+ Basic properties about the aforementioned defs.
		+ Bolzano-Weierstrass theorem
	* metric spaces
		+ defs + balls
		+ links between topology-based and metric-based definitions
	* topology over matrices (only defs)

### Perron-Froebenius Theorem

- URL: <svn://scm.gforge.inria.fr/svnroot/marelledocs/proofs/interval/PF>
- Based on `topology` (contains a documented copy of `topology`)
	* some additions: D+ (`D : numDomainType`), normed matrix-based space
	* more core properties, more factorized
	* proof of the Perron-Froebenius Theorem

### Anaysis over R^n

- URL: <svn://scm.gforge.inria.fr/svnroot/marelledocs/proofs/kantorovich>
- Contents
	* use a very old version of ssreflect
	* redefine everything from scratch (e.g. R^n)
	* proof that R^n is complete
	* some facts about derivability

{ mathcomp-analysis, interval, version ? null }:
(mathcomp-analysis.overrideAttrs (o:
  { propagatedBuildInputs = o.propagatedBuildInputs ++ [ interval ]; }
)).override {single = true; inherit version;}

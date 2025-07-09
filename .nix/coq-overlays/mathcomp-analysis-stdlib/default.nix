{
  lib,
  mkCoqDerivation,
  mathcomp-analysis,
  mathcomp-reals-stdlib,
  stdlib,
  interval,
  version ? null,
}:

mkCoqDerivation {

  pname = "mathcomp-analysis-stdlib";
  repo = "analysis";
  owner = "math-comp";

  release."1.12.0".sha256 = "sha256-PF10NlZ+aqP3PX7+UsZwgJT9PEaDwzvrS/ZGzjP64Wo=";

  defaultVersion = mathcomp-analysis.version;

  propagatedBuildInputs = [ mathcomp-analysis mathcomp-reals-stdlib stdlib interval ];

  meta = {
    description = "Compatibility between Analysis library and Stdlib";
    maintainers = [ lib.maintainers.cohencyril ];
    license = lib.licenses.cecill-c;
  };

}

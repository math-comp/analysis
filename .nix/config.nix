{
  pname = "mathcomp-analysis";
  overrides = {
    coq = "8.11";
    coqPackages = {
      mathcomp = "1.11.0";
      mathcomp-real-closed = "1.1.1";
      mathcomp-finmap = "1.5.0";
    };
  };
}

{
  format = "1.0.0";
  coq-attribute = "mathcomp-analysis";
  pname = "analysis";
  namespace = "mathcomp.analysis";
  realpath = "theories";
  select = "mc-1.12-coq-8.13";
  tasks."mc-1.12-coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    mathcomp.override.version = "1.12.0"; };
  tasks."mc-1.12-coq-8.12".coqPackages = {
    coq.override.version = "8.12";
    mathcomp.override.version = "1.12.0"; };
  tasks."mc-1.12-coq-8.11".coqPackages = {
    coq.override.version = "8.11";
    mathcomp.override.version = "1.12.0";};
  tasks."mc-master-coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    mathcomp.override.version = "master"; };
  tasks."mc-master-coq-8.12".coqPackages = {
    coq.override.version = "8.12";
    mathcomp.override.version = "master"; };
  tasks."mc-master-coq-8.11".coqPackages = {
    coq.override.version = "8.11";
    mathcomp.override.version = "master";};
}

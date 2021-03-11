{
  format = "1.0.0";
  coq-attribute = "mathcomp-analysis";
  pname = "analysis";
  namespace = "mathcomp.analysis";
  realpath = "theories";
  select = "coq-8.13";
  tasks."coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    mathcomp.override.version = "1.12.0";
    mathcomp-real-closed.override.version = "1.1";
    mathcomp-finmap.override.version = "1.5";
    hierarchy-builder.override.version = "1.0.0";
    coq-elpi.override.version = "1.8.1"; };
  tasks."coq-8.12".coqPackages = {
    coq.override.version = "8.12";
    mathcomp.override.version = "1.12.0"; };
  tasks."coq-8.11+multinomials".coqPackages = {
    coq.override.version = "8.11";
    mathcomp.override.version = "1.11.0";
    multinomials.ci.job = "all"; };
}

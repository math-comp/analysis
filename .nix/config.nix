let
  mc-master = {
    mathcomp.override.version = "master";
    mathcomp-finmap.override.version = "master";
    mathcomp-bigenough.override.version = "master";
    mathcomp-real-closed.override.version = "master";};
  mc-1-12 = { mathcomp.override.version = "1.12.0";};
in
{
  format = "1.0.0";
  attribute = "mathcomp-analysis";
  pname = "analysis";
  select = "mc-1.12-coq-8.13";
  tasks."mc-1.12-coq-8.13".coqPackages = {
    coq.override.version = "8.13"; } // mc-1-12;
  tasks."mc-1.12-coq-8.12".coqPackages = {
    coq.override.version = "8.12"; } // mc-1-12;
  tasks."mc-1.12-coq-8.11".coqPackages = {
    coq.override.version = "8.11"; } // mc-1-12;
  tasks."mc-master-coq-8.13".coqPackages = {
    coq.override.version = "8.13"; } // mc-master;
  tasks."mc-master-coq-8.12".coqPackages = {
    coq.override.version = "8.12"; } // mc-master;
  tasks."mc-master-coq-8.11".coqPackages = {
    coq.override.version = "8.11"; } // mc-master;
}

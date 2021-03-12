# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.
{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci-matrix ? false,  ci-job ? null,
  override ? {}, ocaml-override ? {}, global-override ? {},
  ci ? (!isNull ci-job),  inNixShell ? null
}@args:
let auto = fetchGit {
  url = "https://github.com/coq-community/coq-nix-toolbox.git";
  ref = "master";
  rev = import ./.nix/coq-nix-toolbox.nix;
}; in
(import auto ({src = ./.;} // args)).nix-auto


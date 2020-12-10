# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to
# regenerate.
{
  config-file ? ./.nix/config.nix,
  config ? {},
  withEmacs ? false,
  print-env ? false,
  do-nothing ? false,
  update-nixpkgs ? false,
  ci ? false,
}@args:
let do-nothing = (args.do-nothing or false) || update-nixpkgs; in
with builtins;
let result = (import ./.nix/auto-config.nix {inherit config config-file;}); in
with result;
with selected-instance.pkgs.coqPackages.lib;
if trivial.inNixShell then
  with selected-instance; this-pkg.overrideAttrs (old: {
    inherit json_input;
    shellHook = result.shellHook
      + optionalString print-env "nixEnv"
      + optionalString update-nixpkgs "updateNixPkgs";
    currentdir = "./.";
    coq_version = pkgs.coqPackages.coq.coq-version;
    inherit (result.config) nixpkgs logpath realpath;

    buildInputs = optionals (!do-nothing)
      (old.buildInputs or [] ++ optional withEmacs pkgs.emacs);

    propagatedBuildInputs = optionals (!do-nothing)
      (old.propagatedBuildInputs or []);
  })
else
  if ci then map (b: b.ci-coqpkgs) instances
  else selected-instance.this-pkg

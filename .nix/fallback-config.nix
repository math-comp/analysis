# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.

# HOWEVER, we encourage you to copy paste it to `config.nix`
# in the same subdirectory .nix and extend it as needed.

{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  coq-attribute = "mathcomp-analysis";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
  # coq-shell-attribute = "mathcomp-analysis";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  pname = "analysis";

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `medleys` set
  ## defaults to "default"
  # select = "default";

  ## write one `medleys.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well
  # medleys.default = {

  ## You can override Coq and other Coq coqPackages
  ## throught the following attribute
  # coqPackages.coq.override.version = "8.11";

  ## In some cases, light overrides are not available/enough
  ## in which case you can use either
  # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
  ## or a "long" overlay to put in `.nix/coq-overlays
  ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
  ## to automatically retrieve the one from nixpkgs
  ## if it exists and is correctly named/located

  ## You can override Coq and other Coq coqPackages
  ## throught the following attribute
  ## If <ocaml-pkg> does not support lights overload,
  ## you may use `overrideAttrs` or long overlays
  ## located in `.nix/ocaml-overlays`
  ## (there is no automation for this one)
  #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

  ## You can also override packages from the nixpkgs toplevel
  # <nix-pkg>.override.overrideAttrs = o: <overrides>;
  ## Or put an overlay in `.nix/overlays`

  ## you may mark a package as a CI job as follows
  #  coqPackages.<another-pkg>.ci.job = "test";
  ## It can then be built throught
  ## nix-build --argstr ci "default" --arg ci-job "test";

  # }
}
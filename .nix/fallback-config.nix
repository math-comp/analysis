# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.

# *However*, you may copy paste it to `config.nix`
# in the same subdirectory .nix and extend it as needed.
# Note that this would completely deactivate this file.

{
  ## DO NOT CHANGE THE format
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  attribute = "mathcomp-analysis";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
  # shell-attribute = "mathcomp-analysis";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  pname = "analysis";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  #buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  coqproject = "_CoqProject";

  ## Select a task to build by default in the following `tasks` set
  ## It will be used when typing nix-shell or nix-build without argument
  ## defaults to "default"
  select = "coq-8.13";
  tasks."coq-8.13" = {};

  tasks."coq-8.13" = {
      coqPackages."coq".override.version = "8.13";
      coqPackages."coq".job = "_excluded";
      coqPackages."mathcomp".override.version = "1.12.0";
      coqPackages."mathcomp".job = "_excluded";
      coqPackages."mathcomp-real-closed".override.version = "1.1";
      coqPackages."mathcomp-real-closed".job = "_excluded";
      coqPackages."mathcomp-finmap".override.version = "1.5";
      coqPackages."mathcomp-finmap".job = "_excluded";
      coqPackages."hierarchy-builder".override.version = "1.0.0";
      coqPackages."hierarchy-builder".job = "_excluded";
      coqPackages."coq-elpi".override.version = "1.9.3";
      coqPackages."coq-elpi".job = "_excluded";
  };
  tasks."coq-8.12" = {
      coqPackages."coq".override.version = "8.12";
      coqPackages."coq".job = "_excluded";
      coqPackages."mathcomp".override.version = "1.12.0";
      coqPackages."mathcomp".job = "_excluded";
  };
  tasks."coq-8.11+multinomials" = {
      coqPackages."coq".override.version = "8.11";
      coqPackages."coq".job = "_excluded";
      coqPackages."mathcomp".override.version = "1.12.0";
      coqPackages."mathcomp".job = "_excluded";
      coqPackages."multinomials".override.version = "1.5.4";
      coqPackages."multinomials".job = "_excluded";
  };
}

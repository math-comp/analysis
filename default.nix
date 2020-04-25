{
  nixpkgs ? (fetchTarball https://github.com/CohenCyril/nixpkgs/archive/mathcomp-1.11.tar.gz),
  config ? (pkgs: {}),
  withEmacs ? false,
  print-env ? false,
  package ? "analysis",
  src ? (config.${package}.version or ./.),
}:
with builtins;
let
  cfg-fun = if isFunction config then config else (_: config);
  pkgs = import nixpkgs {
    config.packageOverrides = pkgs: with pkgs.lib; {
      coqPackages = with pkgs; {
        "8.7" = coqPackages_8_7;
        "8.8" = coqPackages_8_8;
        "8.9" = coqPackages_8_9;
        "8.10" = coqPackages_8_10;
        "8.11" = coqPackages_8_11;
        "default" = coqPackages_8_11;
      }.${(cfg-fun pkgs).coq or "default"}.overrideScope'
        (self: super:
          let
            cfg = cfg-fun (pkgs // {coqPackages = self;});
            mathcomp-full-config = lib.recursiveUpdate super.mathcomp-extra-config {
                for-package = {
                  mathcomp-fast = version: {
                    propagatedBuildInputs = with self; ([ mathcomp ] ++ mathcomp-extra-fast);
                  };
                  mathcomp-full = version: {
                    propagatedBuildInputs = with self; ([ mathcomp ] ++ mathcomp-extra-all);
                  };
                };
              };
          in {
            mathcomp-extra-config = lib.recursiveUpdate mathcomp-full-config {
              for-package = mapAttrs
                (name: value: version: recursiveUpdate (value version) cfg)
                (filterAttrs (name: _: !elem name [ "mathcomp" ]) cfg);
            };
            mathcomp = if cfg?mathcomp then self.mathcomp_ cfg.mathcomp else self.mathcomp_ "1.11.0+beta1";
          });
    };
  };

  mathcompnix = ./.;

  shellHook = ''
    nixEnv () {
      echo "Here is your work environement"
      echo "buildInputs:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "propagatedBuildInputs:"
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option --arg config '{coq = \"x.y\"; math-comp = \"x.y.z\";}' to nix-shell to change coq and/or math-comp versions"
    }
    cachixEnv () {
      echo "Pushing environement to cachix"
      for x in $buildInputs; do printf "  "; echo $x | cachix push math-comp; done
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cachix push math-comp; done
    }
    nixDefault () {
      cat $mathcompnix/default.nix
    }
  ''
  + pkgs.lib.optionalString print-env "nixEnv";

  emacs = with pkgs; emacsWithPackages
    (epkgs: with epkgs.melpaStablePackages; [proof-general]);

  pkg = with pkgs;
    if elem package
      [ "mathcomp" "ssreflect" "mathcomp-ssreflect" "mathcomp-fingroup"
        "mathcomp-algebra" "mathcomp-solvable" "mathcomp-field" "mathcomp-character" ]
    then coqPackages.${package}
    else (coqPackages.mathcomp-extra package src);
in
if pkgs.lib.trivial.inNixShell then pkg.overrideAttrs (old: {
  inherit shellHook mathcompnix;
  buildInputs = (old.buildInputs or []) ++ pkgs.lib.optional withEmacs emacs;
}) else pkg

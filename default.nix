{
  nixpkgs ? (fetchTarball https://github.com/CohenCyril/nixpkgs/archive/d53b12e0fc3b8941dfcf28e097600aec3b7b5c0e.tar.gz),
  coq-version ? "8.10",
  mc-version ? "1.11.0+beta1",
  withEmacs ? false,
  print-env ? false,
  config ? pkgs: coqPackages: {},
  name ? (config {} {}).name or "analysis",
  src ? (config {} {}).src or ./.,
}:
let
  pkgs = import nixpkgs {
    config.packageOverrides = pkgs: with pkgs; {
      coqPackages = {
        "8.7" = coqPackages_8_7;
        "8.8" = coqPackages_8_8;
        "8.9" = coqPackages_8_9;
        "8.10" = coqPackages_8_10;
        "8.11" = coqPackages_8_11;
      }.${coq-version}.overrideScope'
        (self: super:
          let mathcomp-full-config = lib.recursiveUpdate super.mathcomp-extra-config {
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
              for-package = {
                ${name} = version:
                  lib.recursiveUpdate ((mathcomp-full-config.for-package.${name}
                    or (version: {})) version) (config pkgs self);
              };
            };
            mathcomp = self.mathcomp_ mc-version;
          });
    };
  };

  current-config = config pkgs pkgs.coqPackages;

  mathcompnix = ./.;

  shellHook = ''
    nixEnv () {
      echo "Here is your work environement:"
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
      echo "you can pass option '--argstr mc-version \"x.y.z\"' to nix-shell to change mathcomp versions"
    }
    cachixEnv () {
      echo "Pushing environement to cachix"
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cachix push math-comp; done
    }
    nixDefault () {
      cat $mathcompnix/default.nix
    }
  ''
  + pkgs.lib.optionalString print-env "nixEnv";

  emacs = with pkgs; emacsWithPackages
    (epkgs: with epkgs.melpaStablePackages; [proof-general]);

  package = with pkgs; (coqPackages.mathcomp-extra name src);
in
if pkgs.lib.trivial.inNixShell then package.overrideAttrs (old: {
  inherit shellHook mathcompnix;
  buildInputs = (old.buildInputs or []) ++ pkgs.lib.optional withEmacs emacs;
}) else package

{
  nixpkgs ? (fetchTarball https://github.com/CohenCyril/nixpkgs/archive/mathcomp-1.11.tar.gz),
  config ? (pkgs: {}),
  withEmacs ? false,
  print-env ? false,
  package ? "mathcomp-analysis"
}:
with builtins;
let
  cfg-fun = if isFunction config then config else (pkgs: config);
  pkgs = import nixpkgs {
    overlays = [ (pkgs: super-pkgs: with pkgs.lib;
      let coqPackages = with pkgs; {
        "8.7" = coqPackages_8_7;
        "8.8" = coqPackages_8_8;
        "8.9" = coqPackages_8_9;
        "8.10" = coqPackages_8_10;
        "8.11" = coqPackages_8_11;
        "default" = coqPackages_8_10;
      }.${(cfg-fun pkgs).coq or "default"}.overrideScope'
        (self: super:
          let
            all-pkgs = pkgs // { coqPackages = self; };
            cfg = { ${package} = ./.; } // {
              mathcomp-fast = {
                src = ./.;
                propagatedBuildInputs = with self; ([ mathcomp ] ++ mathcomp-extra-fast);
              };
              mathcomp-full = {
                src = ./.;
                propagatedBuildInputs = with self; ([ mathcomp ] ++ mathcomp-extra-all);
              };
            } // (cfg-fun all-pkgs);
          in {
            # mathcomp-extra-config = lib.recursiveUpdate super.mathcomp-extra-config {
            #   for-coq-and-mc.${self.coq.coq-version}.${self.mathcomp.version} =
            #     removeAttrs cfg ["mathcomp" "coq"];
            # };
            mathcomp = if cfg?mathcomp then self.mathcomp_ cfg.mathcomp else super.mathcomp_ "1.11.0+beta1";
          } // mapAttrs
            (package: version: coqPackages.mathcomp-extra package version)
            (removeAttrs cfg ["mathcomp" "coq"])
        ); in {
          coqPackages = coqPackages.filterPackages coqPackages.coq coqPackages;
          coq = coqPackages.coq;
          mc-clean = src: {
            version = baseNameOf src;
            src = cleanSourceWith {
              src = cleanSource src;
              filter = path: type: let baseName = baseNameOf (toString path); in ! (
                # Filter out editor backup / swap files.
                hasPrefix ".git" baseName ||
                hasSuffix ".aux" baseName ||
                hasSuffix ".d" baseName ||
                hasSuffix ".vo" baseName ||
                hasSuffix ".glob" baseName ||
                elem baseName ["Makefile.coq" "Makefile.coq.conf" ".mailmap"]
              );
            };
          };
        })];
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

  pkg = with pkgs; coqPackages.${package} or (coqPackages.current-mathcomp-extra package);
in
if pkgs.lib.trivial.inNixShell then pkg.overrideAttrs (old: {
  inherit shellHook mathcompnix;
  buildInputs = (old.buildInputs or []) ++ pkgs.lib.optional withEmacs emacs;
}) else pkg

{
  nixpkgs ? (if builtins.pathExists ./.nix/nixpkgs.nix then import ./.nix/nixpkgs.nix
             # else fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/502845c3e31ef3de0e424f3fcb09217df2ce6df6.tar.gz),
             else null),
  config ? (if builtins.pathExists ./.nix/config.nix then import ./.nix/config.nix else {}),
  withEmacs ? false,
  print-env ? false,
  do-nothing ? false,
  pname ? config.pname or "generic"
}:
with builtins;
with (import nixpkgs {}).lib;
let
  mk-overlays = path:
    if !pathExists path then self: {}
    else self: mapAttrs (x: _v:
      let overlays = import (path + "/${x}");
          args = functionArgs overlays;
      in overlays (intersectAttrs args self)) (readDir path);
  coq-overlays = mk-overlays ./.nix/coq-overlays;
  ocaml-overlays = mk-overlays ./.nix/ocaml-overlays;
  overlays = [ (self: super: mk-overlays ./.nix/overlays self) ] ++ [
    (self-pkgs: super-pkgs: {
      coqPackages = super-pkgs.coqPackages.overrideScope' (
        coqPackages: super-coqPackages:
        let pkgs = self-pkgs // {inherit coqPackages;}; in
        coq-overlays (pkgs // coqPackages));

      ocamlPackages = super-pkgs.ocamlPackages.overrideScope' (
        ocamlPackages: super-ocamlPackages:
        let pkgs = self-pkgs // {inherit ocamlPackages;}; in
        ocaml-overlays (pkgs // ocamlPackages));
    })];
  pkgs = import nixpkgs { inherit overlays; };
  default-coq-derivation = makeOverridable pkgs.coqPackages.mkCoqDerivation {
    pname = "generic";
    version = "0.0.0";
    src = "./.";
  };
  locate = pkgs: pname:
    if pkgs.coqPackages?${pname}   then pkgs.coqPackages.${pname} else
    if pkgs.ocamlPackages?${pname} then pkgs.ocamlPackages.${pname} else
    if pkgs?${pname} then pkgs.${pname} else default-coq-derivation.override { inherit pname; };
  this-pkg = (locate pkgs pname).overrideAttrs (o: { src = config.${pname}.src or ./.; });
  shellHook = ''
    nixEnv () {
      echo "Here is your work environement"
      echo "buildInputs:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "propagatedBuildInputs:"
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option --arg config '{coq = \"x.y\"; ...}' to nix-shell to change packages versions"
    }

    printEnv () {
      for x in $buildInputs; do echo $x; done
      for x in $propagatedBuildInputs; do echo $x; done
    }

    cachixEnv () {
      echo "Pushing environement to cachix"
      printEnv | cachix push math-comp
    }

    nixDefault () {
      cat $currentdir/default.nix
    } > default.nix

    updateNixPkgs (){
      HASH=$(git ls-remote https://github.com/NixOS/nixpkgs-channels refs/heads/nixpkgs-unstable | cut -f1);
      URL=https://github.com/NixOS/nixpkgs-channels/archive/$HASH.tar.gz
      SHA256=$(nix-prefetch-url --unpack $URL)
      echo "fetchTarball {
        url = $URL;
        sha256 = \"$SHA256\";
      }" > .nix/nixpkgs.nix
    }
    updateNixPkgsMaster (){
      HASH=$(git ls-remote https://github.com/NixOS/nixpkgs refs/heads/master | cut -f1);
      URL=https://github.com/NixOS/nixpkgs/archive/$HASH.tar.gz
      SHA256=$(nix-prefetch-url --unpack $URL)
      echo "fetchTarball {
        url = $URL;
        sha256 = \"$SHA256\";
      }" > .nix/nixpkgs.nix
    }
  ''
  + pkgs.lib.optionalString print-env "nixEnv";

  currentdir = ./.;
  emacs = with pkgs; emacsWithPackages
    (epkgs: with epkgs.melpaStablePackages; [proof-general]);
in
# if pkgs.lib.trivial.inNixShell then this-pkg.overrideAttrs (old: {
#   inherit shellHook currentdir;

#   buildInputs = if do-nothing then []
#                 else (old.buildInputs ++
#                 (if pkgs.lib.trivial.inNixShell then pkgs.lib.optional withEmacs pkgs.emacs
#                  else []));

#   propagatedBuildInputs = if do-nothing then [] else old.propagatedBuildInputs;

# }) else this-pkg
this-pkg
{
  nixpkgs ? (if builtins.pathExists ./.nix/nixpkgs.nix then import ./.nix/nixpkgs.nix
             # else fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/502845c3e31ef3de0e424f3fcb09217df2ce6df6.tar.gz),
             else null),
  config ? {},
  withEmacs ? false,
  print-env ? false,
  do-nothing ? false,
  pname ? null,
  version ? null,
  ci ? false,
}@args:
with builtins;
with (import nixpkgs {}).lib;
let
  the-config = (if builtins.pathExists ./.nix/config.nix then import ./.nix/config.nix else {}) // config;
  full-pname = "coqPackages.${args.pname or the-config.pname or "generic"}";
  ppath = splitString "." full-pname;
  pname = last ppath;
  mk-overlays = path: callPackage:
    if !pathExists path then {}
    else mapAttrs (x: _v: callPackage (path + "/${x}") {}) (readDir path);
  coq-overlays = mk-overlays ./.nix/coq-overlays;
  ocaml-overlays = mk-overlays ./.nix/ocaml-overlays;
  override-version = x: v: x.override { version = v; };
  version-overrides = (setAttrByPath ppath ./.) // (the-config.overrides or {});
  overrides = self: super: mapAttrs (n: v: override-version super.${n} v)
    (removeAttrs version-overrides [ "coqPackages" "ocamlPackages" ]);
  ocaml-overrides = self: super: mapAttrs (n: v: override-version super.${n} v)
    (version-overrides.ocamlPackages or {});
  coq-overrides = self: super: mapAttrs 
    (n: v: if super?${n} then override-version super.${n} v else default-coq-derivation)
    (version-overrides.coqPackages or {});
  overlays = [
    (self: _super: mk-overlays ./.nix/overlays self.callPackage)
    (_self: super:  { ocamlPackages = super.ocamlPackages.overrideScope' (
                        self: _super: ocaml-overlays self.callPackage); })
    (_self: super:  { coqPackages = super.coqPackages.overrideScope' (
                        self: _super: coq-overlays self.callPackage); })
    overrides
    (_self: super:  { ocamlPackages = super.ocamlPackages.overrideScope' ocaml-overrides; })
    (_self: super:  { coqPackages = super.coqPackages.overrideScope' coq-overrides; })
  ];
  pkgs = import nixpkgs { inherit overlays; };
  default-coq-derivation = makeOverridable pkgs.coqPackages.mkCoqDerivation
    { inherit pname; version = ./.; };
  this-pkg = attrByPath ppath default-coq-derivation pkgs;

  shellHook = readFile ./.nix/shellHook.sh + pkgs.lib.optionalString print-env "nixEnv";

  currentdir = ./.;
  emacs = with pkgs; emacsWithPackages
    (epkgs: with epkgs.melpaStablePackages; [proof-general]);

  coqpkgs = let coqpkgs = pkgs.coqPackages; in coqpkgs.filterPackages pkgs coqpkgs;
in
if pkgs.lib.trivial.inNixShell then this-pkg.overrideAttrs (old: {
  inherit shellHook currentdir nixpkgs;
  overrides = toJSON (removeAttrs version-overrides [ "coqPackages" "ocamlPackages" ]);
  coq_overrides = toJSON (version-overrides.coqPackages or {});
  ocaml_overrides = toJSON (version-overrides.ocamlPackages or {});

  buildInputs = if do-nothing then []
                else (old.buildInputs or [] ++
                (if pkgs.lib.trivial.inNixShell then pkgs.lib.optional withEmacs pkgs.emacs
                 else []));

  propagatedBuildInputs = if do-nothing then [] else old.propagatedBuildInputs or [];

}) else if ci then coqpkgs else this-pkg

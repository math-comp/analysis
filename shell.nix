{withEmacs ? false,
 nixpkgs ?  (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/82b54d490663b6d87b7b34b9cfc0985df8b49c7d.tar.gz";
  sha256 = "12gpsif48g5b4ys45x36g4vdf0srgal4c96351m7gd2jsgvdllyf";
}),
coq-version ? "8.10",
print-env ? false
}:
with import nixpkgs {};
let
  pgEmacs = emacsWithPackages (epkgs:
    with epkgs.melpaStablePackages; [proof-general]);
  myCoqPackages = {
    default = coqPackages_8_9;
    "8.7" = coqPackages_8_7;
    "8.8" = coqPackages_8_8;
    "8.9" = coqPackages_8_9;
    "8.10" = coqPackages_8_10;
    "8.11" = coqPackages_8_11;
    }."${coq-version}";
  coq = myCoqPackages.coq;
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with myCoqPackages;
    [ mathcomp mathcomp-finmap mathcomp-bigenough
      mathcomp-multinomials mathcomp-real-closed ])
                ++ lib.optional withEmacs pgEmacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}

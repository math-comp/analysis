{withEmacs ? false,
 nixpkgs ? (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/d80148928b12ffa9c6cc320e107515aa7b7c7994.tar.gz";
  sha256 = "0590i3p14f668h0il81bh8m64l1ccl7nmdpv59y865db1wyq3a8c";
}),
coq-version ? "default",
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
    }."${coq-version}";
  coq = myCoqPackages.coq;
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with myCoqPackages;
    [mathcomp mathcomp-finmap mathcomp-bigenough mathcomp-real-closed])
                ++ lib.optional withEmacs pgEmacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}

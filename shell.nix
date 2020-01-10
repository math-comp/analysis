{withEmacs ? false,
 nixpkgs ? (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/c4196cca9acd1c51f62baf10fcbe34373e330bb3.tar.gz";
  sha256 = "0jsisiw8yckq96r5rgdmkrl3a7y9vg9ivpw12h11m8w6rxsfn5m5";
}),
coq-version ? "8.9",
mc ? {url = "https://github.com/math-comp/math-comp"; ref = "master";},
print-env ? false
}:
let
  config.packageOverrides = pkgs:
    with pkgs; {
      coqPackages =
        let coqPackages = (with pkgs;{
              "8.7" = coqPackages_8_7;
              "8.8" = coqPackages_8_8;
              "8.9" = coqPackages_8_9;
              "8.10" = coqPackages_8_10;
            }."${coq-version}");
        in
        coqPackages.overrideScope' (self: super: {
          mathcomp = super.mathcomp.overrideMathcomp (o: {
            version = "dev";
            name = "coq${super.coq.coq-version}-mathcomp-dev";
            src = fetchGit mc;
          });
        });
      emacs = emacsWithPackages (epkgs:
        with epkgs.melpaStablePackages; [proof-general]);
    };
in
with import nixpkgs {inherit config;};
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with coqPackages;
    [mathcomp mathcomp-finmap mathcomp-bigenough
     mathcomp-multinomials mathcomp-real-closed coqeal])
                ++ lib.optional withEmacs emacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}

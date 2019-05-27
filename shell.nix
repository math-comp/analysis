{withEmacs ? false}:
with import (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/650a295621b27c4ebe0fa64a63fd25323e64deb3.tar.gz";
  sha256 = "0rxjkfiq53ibz0rzggvnp341b6kgzgfr9x6q07m2my7ijlirs2da";
}) {};
let
  emacsWithPackages = (emacsPackagesNgGen emacs).emacsWithPackages;
  pgEmacs = emacsWithPackages (epkgs:
    with epkgs.melpaStablePackages; [proof-general]);
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ] ++ (with coqPackages; [mathcomp mathcomp-finmap mathcomp-bigenough])
                ++ lib.optional withEmacs pgEmacs;
}

#! /usr/bin/bash

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
b  echo "fetchTarball {
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
printOverrides (){
    echo overrides: $overrides
    echo ocaml-overrides: $ocaml_overrides
    echo coq-overrides: $coq_overrides
}
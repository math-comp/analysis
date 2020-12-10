#! /usr/bin/bash

printNixEnv () {
  echo "Here is your work environement"
  echo "buildInputs:"
  for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
  echo "propagatedBuildInputs:"
  for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
  echo "you can pass option --arg config '{coq = \"x.y\"; ...}' to nix-shell to change packages versions"
}
catNixEnv () {
  for x in $buildInputs; do echo $x; done
  for x in $propagatedBuildInputs; do echo $x; done
}

upateNixDefault () {
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

printNixOverrides (){
    echo overrides: $overrides
    echo ocaml-overrides: $ocaml_overrides
    echo coq-overrides: $coq_overrides
}

initNixConfig (){
  F=./.nix/config.nix;
  if [[ -f $F ]]
    then echo "$F already exists"; exit 1
    else if [[ -n "$1" ]]
      then echo "{" > $F
           echo "  pname = \"$1\";" >> $F
           echo "}" >> $F
      else echo "usage: initNixConfig pname"; exit 2
    fi
  fi
}

fetchCoqOverlay (){
  F=$nixpkgs/pkgs/development/coq-modules/$1/default.nix
  D=./.nix/coq-overlays/$1/
  echo $F
  if [[ -n "$1" ]]
    then mkdir -p $D; cp $F $D; chmod u+w ${D}default.nix
    else echo "usage: fetchCoqOverlay pname"; exit 1
  fi
}
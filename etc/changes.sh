#!/usr/bin/env bash
set -e
shopt -s nullglob

if [ "$DEBUG" = 1 ]; then
  set -x
fi

show_help(){
    cat <<EOF
Usage: changes [-h|-?|--help] [[-s|--since] Commit] [-r|--raw] [--cd]
               file*
EOF
}

die() {
    printf '%s\n' "$1" >&2
    exit 1
}

while :; do
    case $1 in
        -h|-\?|--help)
            show_help    # Display a usage synopsis.
            exit 0
            ;;
        -s|--since)
            shift
            COMMIT=$1
            shift
            ;;
        -r|--raw)
            RAW=1
            shift
            ;;
        --cd)
            CD=1
            shift
            ;;
        *)
            if ! [ "$*" ]; then break
            else FILES=$*; break
            fi
            ;;

    esac
done

if ! [ "$FILES" ]; then FILES=**/*.v; fi
if ! [ "$COMMIT" ]; then COMMIT="master"; fi

D=$(mktemp -d)

if [ "$RAW" ]; then echo $D; fi

VERNAC="Definition Notation Lemma Theorem Corollary"
ALLV=$(echo $VERNAC | sed "s/ /_/g")

touchp() { mkdir -p "$(dirname "$1")" && touch "$1" ; }

get_change() {
  STATUS=$1
  shift
  BODYGREPVERNAC=$(echo $* | sed "s/ /|/g")
  BODYSEDVERNAC=$(echo $* | sed "s/ /\\\|/g")
  GREPVERNAC="($BODYGREPVERNAC)"
  SEDVERNAC="\($BODYSEDVERNAC\)"
  (grep -Ee "^$STATUS *$GREPVERNAC " || true) |\
  sed "s/^$STATUS *$SEDVERNAC \+\\([^ \\:({\\[\"]*\\).*/\\2/" |\
  sed "/^\$/d" |\
  (grep -Ev -e "_(subproof|subdef)" || true)
}

for f in $FILES; do
  touchp $D/diffs/$f
  git diff "$COMMIT" -- $f > $D/diffs/$f
done

store_change() {
  SUB=$(echo $* | sed "s/ /_/g")
  touchp $D/additions/$SUB/$f
  touchp $D/deletions/$SUB/$f
  cat $D/diffs/$f | get_change "\+" "$*" > $D/additions/$SUB/$f
  cat $D/diffs/$f | get_change "-" "$*" > $D/deletions/$SUB/$f
}

for f in $FILES; do
  for v in $VERNAC; do store_change $v; done
  store_change $VERNAC
done

cat $D/additions/$ALLV/**/* > $D/all_additions
cat $D/deletions/$ALLV/**/* > $D/all_deletions

strictify() {
  touchp $D/strict_additions/$1/$f
  touchp $D/strict_deletions/$1/$f
  touchp $D/changes/$1/$f
  grep -Fxv -f $D/all_deletions $D/additions/$1/$f >\
       $D/strict_additions/$1/$f || true
  grep -Fxv -f $D/all_additions $D/deletions/$1/$f >\
       $D/strict_deletions/$1/$f || true
  grep -Fx -f  $D/all_deletions $D/additions/$1/$f >\
       $D/changes/$1/$f || true
}

for f in $FILES; do
  for v in $VERNAC; do strictify $v; done
  strictify $ALLV
done

cat $D/changes/$ALLV/**/* > $D/all_changes

len() { wc -l $1 | cut -d" " -f 1; }

pp() {
  LEN=$(len $1)
  if [ $LEN == 1 ]; then echo "\`$(cat $1)\`"
  else
  cat $1 | awk "(NR < $LEN) {printf (\"\`%s\`, \", \$1)}
                (NR == $LEN) {printf (\"and \`%s\`.\n\", \$1)}" ORS=" "
  fi
}

class() {
  if [ $1 == 1 ]; then
      echo $2 | sed "s/Definition/Definition/;s/Notation/Notation/;
      s/Lemma/Lemma/;s/Theorem/Theorem/;s/Corollary/Corollary/;"
  else
      echo $2 | sed "s/Definition/definitions/;s/Notation/notations/;
      s/Lemma/lemmas/;s/Theorem/theorems/;s/Corollary/corollaries/;"
  fi
}

if [ "$RAW" ]; then
  echo "=========================================="
  echo "ADDITIONS:"
  cat $D/all_additions
  echo "=========================================="
  echo "DELETIONS:"
  cat $D/all_deletions
  echo "=========================================="
else
  echo "### Added"
  echo ""
  for f in $FILES; do
    if [ -s $D/strict_additions/$ALLV/$f ]; then
       echo "- in file \`$(basename $f)\`"
       for v in $VERNAC; do
         if [ -s $D/strict_additions/$v/$f ]; then
           LEN=$(len $D/strict_additions/$v/$f)
           echo "  + new $(class $LEN $v) $(pp $D/strict_additions/$v/$f)"
         fi
       done
    fi
  done
  echo ""
  echo "### Removed"
  echo ""
  for f in $FILES; do
    if [ -s $D/strict_deletions/$ALLV/$f ]; then
       echo "- in file \`$(basename $f)\`"
       for v in $VERNAC; do
         if [ -s $D/strict_deletions/$v/$f ]; then
           LEN=$(len $D/strict_deletions/$v/$f)
           echo "  + removed $(class $LEN $v) $(pp $D/strict_deletions/$v/$f)"
         fi
       done
    fi
  done
  echo ""
  echo "### Potentially changed"
  echo ""
  pp $D/all_changes

fi

if [ "$CD" ]; then cd $D; exec $SHELL; fi

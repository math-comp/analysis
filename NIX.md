# Developing math-comp/analysis with nix.

1. Install nix:
  - To install it on a single-user unix system where you have admin
    rights, just type:

    > sh <(curl https://nixos.org/nix/install)

    You should run this under your usual user account, not as
    root. The script will invoke `sudo` as needed.

    For other configurations (in particular if multiple users share
    the machine) or for nix uninstallation, go to the [appropriate
    section of the nix
    manual](https://nixos.org/nix/manual/#ch-installing-binary).

    You may experience installation errors at this stage.
    For example, the installation may stop with the following
    error message:

    > ...
    > installing 'nix-2.2.2'
    > error: cloning builder process: Operation not permitted
    > error: unable to start build process
    > ...

    On Debian, this can be solved by the following command:

    > sudo sysctl kernel.unprivileged_userns_clone=1

    (Checked with Debian 9.9.)

  - You need to set several environment variables before you proceed to step 2:

    > . /home/username/.nix-profile/etc/profile.d/nix.sh

    or **log out and log in again**.

  - Step 1. only need to be done once on a same machine.

2. Open a new terminal. Navigate to the root of the mathcomp-analysis repository. Then type:
   > nix-shell

   - This will download and build the required packages, wait until
     you get a shell.
   - You need to type this command every time you open a new terminal.
   - You can call `nixEnv` after you start the nix shell to see your
     work environemnet (or call `nix-shell` with option `--arg
     print-env true`).

3. You are now in the correct work environment. You can do
   > make

   and do whatever you are accustomed to do with Coq.

   This is providing that the environment variable COQBIN does not
   point to conflicting binaries. Check with:

   > echo $COQBIN

   If wrongly set, do:

   > which coqtop
   /nix/store/blahblah/bin/
   > export COQBIN=/nix/store/blahblah/bin/

4. In particular, you can edit files using `emacs` or `coqide`.

   - If you were already using emacs with proof general, make sure you
     empty your `coq-prog-name` variables and any other proof general
     options that used to be tied to a previous local installation of
     Coq.

     Proof general will rely on the file `_CoqProject`, so you want to
     make sure that your `.emacs` configuration has not overwritten
     the `coq-project-filename` either.

   - If you do not have emacs installed, but want to use it, you can
     go back to step 2. and call `nix-shell` with the following option
     > nix-shell --arg withEmacs true

     in order to get a temporary installation of emacs and
     proof-general.  Make sure you add `(require 'proof-site)` to your
     `$HOME/.emacs`.

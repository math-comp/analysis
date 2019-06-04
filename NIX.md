# Developing math-comp/analysis with nix.

1. Install nix:
  - To install it on a single-user unix system where you have admin
    rights, just type:

    > sh <(curl https://nixos.org/nix/install)

    You should run this under your usual user account, not as
    root. The script will invoke `sudo` as needed.

    See [Troubleshooting](#error-when-installing-nix) in case of error.

    For other configurations (in particular if multiple users share
    the machine) or for nix uninstallation, go to the
    [appropriate section of the nix manual](https://nixos.org/nix/manual/#ch-installing-binary).

  - You need to set several environment variables before you proceed to step 2.
    The simplest way to do so is to **log out from your session and log in again**.

    See [Troubleshooting](#source-without-logging-out) if you prefer
    not to terminate your session.

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

   See [Troubleshooting](#error-when-executing-make) in case of error.

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

# Troubleshooting

## Error when installing nix

You may experience errors when installing nix.  If the installation
stops with an error message similar to the following one

> ...
> installing 'nix-2.2.2'
> error: cloning builder process: Operation not permitted
> error: unable to start build process
> ...

it may be fixed by the following command (tested with Debian 9.9):

> sudo sysctl kernel.unprivileged_userns_clone=1

## Error when executing make

If the environment variable COQBIN is set, it is likely to point
to the wrong binaries. If set, do:

> export COQBIN=$(which coqtop | xargs dirname)/

## Source without Logging out

Nix needs the user to set several environment variables and
the nix installer appends a command for this purpose to the user's `.profile`.
The Nix environment variables can actually be set from within any
shell by sourcing the appropriate file:

> . ${HOME}/.nix-profile/etc/profile.d/nix.sh

# Minimal set of build requirements for Verus
#
# Open a shell which has access to nothing but these requirements using
#    nix-shell --pure tools/shell.nix
# from the root of the repository.

{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    nativeBuildInputs = with pkgs; [
      git
      python3
      openssh
      cmake
      ninja
      pkg-config
      openssl
      libiconv
      curl
      libgit2_1_3_0 # Interestingly, libgit2 at the moment (at version 1.4.3.x) ends up in a segfault, but 1.3.0 works fine.
    ];
}

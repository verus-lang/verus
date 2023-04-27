# Minimal set of build requirements for Verus
#
# Open a shell which has access to nothing but these requirements using
#    nix-shell --pure tools/shell.nix
# from the root of the repository.

{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    nativeBuildInputs = with pkgs; [
      rustup
      unzip
      wget
    ];
}

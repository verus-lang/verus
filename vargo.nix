{
  pkgs
}:  pkgs.rustPlatform.buildRustPackage {
  pname = "vargo";
  version = "0.1.0";

  src = pkgs.lib.cleanSource ./tools/vargo;
  cargoLock.lockFile = ./tools/vargo/Cargo.lock; # yes, this does not use the rust toolchain

  patches = [ ./vargo.diff ];
  # it references a file outside the vargo dir which is just a headache... don't forget to update it if needed
  # oh and maybe just remove the entire "toolchain-check"! (although I'd prefer if that worked with the specified Cargo.lock)

  meta = {
    description = "Verus is a tool for verifying the correctness of code written in Rust.";
    homepage = "https://github.com/verus-lang/verus";
    license = pkgs.lib.licenses.mit;
  };
}

# docs for packaging this:
# https://m7.rs/blog/2022-11-01-package-a-rust-app-with-nix/index.html

# TODO
# * [x] deal with hardcoded path
# * [x] the dependency z3
# * [ ] verus as a package (not doable yet, since verus calls rustup and that means internet access during the build phase, which is not possible in nix)
# * [x] vargo as a package (technically doable with a cargo)
# * [ ] pick right z3 dependency automagically (not super simple when all we have the url in the script...)


# How to use (if you have the nix package manager installed. These days, I recommend [Lix](https://lix.systems).)
# 1. `nix develop` This will drop you in a shell environment where all dependencies are (should be) available
# afterwards, when running this the first time, continue the installation:
# 2. in ./source/: `vargo build --release` (building verus)
# 3. run `PATH=source/target-verus/release:$PATH (this adds verus to the path)

{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = {
    nixpkgs,
    self,
    ...
  }: let
    supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
    forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
    nixpkgsFor = forAllSystems (system: import nixpkgs { inherit system; });

    overrides = (builtins.fromTOML (builtins.readFile ./rust-toolchain.toml));
  in {
    packages = forAllSystems (system: let
      pkgs = nixpkgsFor.${system};
    in {
      vargo = import ./vargo.nix { inherit pkgs; };
    });

    # enter a dev shell with `nix develop
    devShells = forAllSystems (system: let
      pkgs = nixpkgsFor.${system};
      libPath = with pkgs; lib.makeLibraryPath [
        # load external libraries that you need in your rust project here
      ];
    in {
      default = pkgs.mkShell {
        RUSTC_VERSION = overrides.toolchain.channel;
        # https://github.com/rust-lang/rust-bindgen#environment-variables
        LIBCLANG_PATH = pkgs.lib.makeLibraryPath [ pkgs.llvmPackages_latest.libclang.lib ];

        # Add precompiled library to rustc search path
        RUSTFLAGS = (builtins.map (a: ''-L ${a}/lib'') [
        # add libraries here (e.g. pkgs.libvmi)
        ]);
        LD_LIBRARY_PATH = libPath;
        # Add glibc, clang, glib, and other headers to bindgen search path
        BINDGEN_EXTRA_CLANG_ARGS =
        # Includes normal include path
          (builtins.map (a: ''-I"${a}/include"'') [
            # add dev libraries here (e.g. pkgs.libvmi.dev)
            pkgs.glibc.dev
          ])
          # Includes with special directory paths
          ++ [
            ''-I"${pkgs.llvmPackages_latest.libclang.lib}/lib/clang/${pkgs.llvmPackages_latest.libclang.version}/include"''
            ''-I"${pkgs.glib.dev}/include/glib-2.0"''
            ''-I${pkgs.glib.out}/lib/glib-2.0/include/''
          ];

        packages = [
          pkgs.z3_4_12
          pkgs.clang
          pkgs.llvmPackages.bintools
          pkgs.rustup
          pkgs.cvc5
          (import ./vargo.nix { inherit pkgs; })
        ];
        shellHook = ''
          export PATH=$PATH:''${CARGO_HOME}/bin
          export PATH=$PATH:''${RUSTUP_HOME}/toolchains/$RUSTC_VERSION-x86_64-unknown-linux-gnu/bin/
          export VERUS_Z3_PATH=$(which z3)
        '';
      };
    });

    # this only works if you have rustup installed system wide
    # invoke as `nix run .#vargo`
    apps = forAllSystems (system: {
      vargo = {
        type = "app";
        program = "${self.packages.${system}.vargo}/bin/vargo";
      };
    });
  };
}

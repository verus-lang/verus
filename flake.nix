# TODO
# * [x] deal with hardcoded path
# * [x] the dependency z3
# * [ ] remove duplicates
# * [ ] verus as an app (which checks whether verus was build beforehand, otherwise instructs user to call the vargo app)
# * [ ] think about command names
# * [x] vargo as a package (technically doable with a cargo)

# MAYBE LATER
# * [ ] pick right z3 dependency automagically (not super simple when all we have the url in the script...)
# * [ ] verus as a package (not doable yet, since verus calls rustup and that means internet access during the build phase, which is not possible in nix)

# How to use (if you have the nix package manager installed. These days, I recommend [Lix](https://lix.systems).)
# ===============================
#
# How to use the devshell (meant for developping on vargo or verus itself)
# `nix develop` This will drop you in a shell environment where all dependencies are (should be) available
#
# How to call vargo:
# `cd src && nix run .#vargo-br`
#
# How to call verus;
# TODO

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
          pkgs.cvc5
          pkgs.singular

          pkgs.clang
          pkgs.llvmPackages.bintools
          pkgs.rustup
          (import ./vargo.nix { inherit pkgs; })
        ];
        shellHook = ''
          export PATH=$PATH:''${CARGO_HOME}/bin
          export PATH=$PATH:''${RUSTUP_HOME}/toolchains/$RUSTC_VERSION-x86_64-unknown-linux-gnu/bin/
          export PATH=$(realpath .)/source/target-verus/release:$PATH
          export VERUS_Z3_PATH=$(which z3)
          export VERUS_CVC5_PATH=$(which cvc5)
          export VERUS_SINGULAR_PATH=$(which Singular) # what exactly does it need on the path?
        '';
      };
    });

    # this only works if you have rustup installed system wide
    # invoke as `nix run .#vargo`
    apps = forAllSystems (system: let
      pkgs = nixpkgsFor.${system};
      libPath = with pkgs; lib.makeLibraryPath [
        # load external libraries that you need in your rust project here
      ];
      # todo put these vars inside
      RUSTC_VERSION = overrides.toolchain.channel; # TODO das hier wird noch gar nicht genutzt so
#         https://github.com/rust-lang/rust-bindgen#environment-variables
      LIBCLANG_PATH = pkgs.lib.makeLibraryPath [ pkgs.llvmPackages_latest.libclang.lib ];

#         Add precompiled library to rustc search path
      RUSTFLAGS = (builtins.map (a: ''-L ${a}/lib'') [
#           add libraries here (e.g. pkgs.libvmi)
      ]);
      LD_LIBRARY_PATH = libPath;
#       Add glibc, clang, glib, and other headers to bindgen search path
      BINDGEN_EXTRA_CLANG_ARGS =
#         Includes normal include path
        (builtins.map (a: ''-I"${a}/include"'') [
#         add dev libraries here (e.g. pkgs.libvmi.dev)
        pkgs.glibc.dev
      ])
#         Includes with special directory paths
      ++ [
        ''-I"${pkgs.llvmPackages_latest.libclang.lib}/lib/clang/${pkgs.llvmPackages_latest.libclang.version}/include"''
        ''-I"${pkgs.glib.dev}/include/glib-2.0"''
          ''-I${pkgs.glib.out}/lib/glib-2.0/include/''
      ];
      vargoWithRustup = pkgs.writeShellApplication {
        name = "vargo";
        runtimeInputs = [
          pkgs.z3_4_12
          pkgs.cvc5
          pkgs.singular

          pkgs.clang
          pkgs.llvmPackages.bintools
          pkgs.rustup
          (import ./vargo.nix { inherit pkgs; })
        ];


        text = ''
          VERUS_Z3_PATH=$(which z3)
          export VERUS_Z3_PATH


          export PATH=$PATH:~/.cargo/bin
          export PATH=$PATH:~/.rutup/toolchains/${RUSTC_VERSION}-x86_64-unknown-linux-gnu/bin/


          vargo build --release
        '';
      };
      in {
        vargo-br = {
          type = "app";
          program = "${vargoWithRustup}/bin/vargo";
        };
    });
  };
}

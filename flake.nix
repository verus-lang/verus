{
  description = "Flake for verus";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = { self, nixpkgs, rust-overlay }:
    let
      inherit (nixpkgs) lib;
      systems = [
        "x86_64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
        "x86_64-windows"
      ];
      eachDefaultSystem = f: builtins.foldl' lib.attrsets.recursiveUpdate { }
        (map f systems);

      # Set Z3_SOURCE_BUILD=1 or CVC5_SOURCE_BUILD=1 to build from source.
      # Requires --impure flag: nix build --impure .#verus
      z3SourceBuild = (builtins.getEnv "Z3_SOURCE_BUILD") == "1";
      cvc5SourceBuild = (builtins.getEnv "CVC5_SOURCE_BUILD") == "1";
    in
    eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        formatter = pkgs.nixpkgs-fmt;
        linters = [ pkgs.statix vargo verusfmt ];
        rust-bin = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

        # Inline rustup
        rustup = pkgs.stdenvNoCC.mkDerivation {
          name = "rustup";
          src = ./tools/nix;
          strictDeps = true;
          buildInputs = [ pkgs.python3 ];
          preferLocalBuild = true;
          postPatch = ''
            substituteInPlace rustup.py \
              --subst-var-by rustVersion "${rust-bin.version}"
          '';
          installPhase = ''
            runHook preInstall
            install -Dm755 rustup.py -T $out/bin/rustup
            runHook postInstall
          '';
          meta = {
            description = "Spoof rustup";
            mainProgram = "rustup";
            maintainers = with lib.maintainers; [ stephen-huan jakeginesin ];
          };
        };

        version = self.rev or "dirty";
        meta = {
          homepage = "https://github.com/verus-lang/verus";
          description = "Verified Rust for low-level systems code";
          license = lib.licenses.mit;
          maintainers = with lib.maintainers; [ stephen-huan jakeginesin ];
          platforms = systems;
        };

        vargo = pkgs.rustPlatform.buildRustPackage (finalAttrs: {
          pname = "vargo";
          inherit version;
          src = ./tools;
          sourceRoot = "tools/vargo";
          cargoLock = {
            lockFile = ./tools/vargo/Cargo.lock;
          };
          meta = meta // { mainProgram = "vargo"; };
        });

        verus = pkgs.rustPlatform.buildRustPackage {
          pname = "verus";
          inherit version;
          srcs = [ ./source ./tools ./dependencies ];
          sourceRoot = "source";
          cargoLock = {
            lockFile = ./source/Cargo.lock;
            outputHashes = {
              "smt2parser-0.6.1" = "sha256-AKBq8Ph8D2ucyaBpmDtOypwYie12xVl4gLRxttv5Ods=";
              "getopts-0.2.21" = "sha256-N/QJvyOmLoU5TabrXi8i0a5s23ldeupmBUzP8waVOiU=";
            };
          };
          nativeBuildInputs = [ pkgs.makeBinaryWrapper rust-bin rustup vargo z3 ];
          buildInputs = [ rustup z3 ];
          buildPhase = ''
            runHook preBuild
            ln -s ${lib.getExe z3} ./z3
            ln -sf ${./rust-toolchain.toml} ../rust-toolchain.toml
            vargo build --release
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            mkdir -p $out
            cp -r target-verus/release -T $out
            mkdir -p $out/bin
            ln -s $out/verus $out/bin/verus
            ln -s $out/rust_verify $out/bin/rust_verify
            ln -s $out/cargo-verus $out/bin/cargo-verus
            ln -s $out/z3 $out/bin/z3
            wrapProgram $out/bin/verus --prefix PATH : ${lib.makeBinPath [ rustup rust-bin z3 cvc5 ]}
            runHook postInstall
          '';
          doCheck = false;
          passthru = { inherit vargo; };
          meta = meta // { mainProgram = "verus"; };
        };

        verusfmt = pkgs.rustPlatform.buildRustPackage (finalAttrs: {
          pname = "verusfmt";
          version = "0.6.1";

          src = pkgs.fetchFromGitHub {
            owner = "verus-lang";
            repo = "verusfmt";
            tag = "v${finalAttrs.version}";
            hash = "sha256-+NHI2dvCxEGVIUF9zO2aVvVbPSLRtsHFCIHU4cfRzUY=";
          };

          cargoHash = "sha256-8r8PzBrYZWibeFDh2nENctEEkigUzQeD9uD0Jl/Nv5U=";

          nativeCheckInputs = [ pkgs.cargo pkgs.rustfmt ];

          doCheck = true;

          meta = {
            homepage = "https://github.com/verus-lang/verusfmt";
            description = "An Opinionated Formatter for Verus";
            license = lib.licenses.mit;
            mainProgram = "verusfmt";
            maintainers = with lib.maintainers; [ stephen-huan ];
            platforms = [
              "x86_64-linux"
              "x86_64-darwin"
              "aarch64-darwin"
              "x86_64-windows"
            ];
          };
        });

        # --- z3 ---

        z3Version = "4.12.5";

        z3Filename = {
          x86_64-linux = "z3-${z3Version}-x64-glibc-2.31";
          aarch64-linux = "z3-${z3Version}-arm64-glibc-2.35";
          x86_64-darwin = "z3-${z3Version}-x64-osx-11.7.10";
          aarch64-darwin = "z3-${z3Version}-arm64-osx-11.0";
          # x86_64-windows = "z3-${z3Version}-x64-win";
        }.${system} or (throw "Unsupported system for prebuilt z3: ${system}");

        z3PrebuiltHash = {
          x86_64-linux = "sha256-kHWanLxL180OPiDSvrxXjgyd/sKFHVgX5/SFfL+pJJs=";
          aarch64-linux = "sha256-+kPQBHmKI7HyCp7oSFNAm321hXwyonSSVXTTvo4tVSA=";
          x86_64-darwin = "sha256-SfDKEz5p75HGM4lkyQUNPBnQZKtU9cTch6KkTeN94+E=";
          aarch64-darwin = "sha256-Dkrqjn56UIZcNYKDFZkn2QVLWou4Vf0NjKIITSsweeU=";
        }.${system} or "sha256-kHWanLxL180OPiDSvrxXjgyd/sKFHVgX5/SFfL+pJJs="; # default to x86_64-linux

        z3Prebuilt = pkgs.stdenvNoCC.mkDerivation {
          pname = "z3";
          version = z3Version;
          src = pkgs.fetchzip {
            url = "https://github.com/Z3Prover/z3/releases/download/z3-${z3Version}/${z3Filename}.zip";
            hash = z3PrebuiltHash;
          };
          dontBuild = true;
          installPhase = ''
            runHook preInstall
            mkdir -p $out/bin
            cp bin/z3 $out/bin/z3
            chmod +x $out/bin/z3
            runHook postInstall
          '' + lib.optionalString pkgs.stdenvNoCC.isLinux ''
            patchelf --set-interpreter "$(cat ${pkgs.stdenv.cc}/nix-support/dynamic-linker)" $out/bin/z3 || true
          '';
          nativeBuildInputs = lib.optionals pkgs.stdenvNoCC.isLinux [ pkgs.patchelf pkgs.autoPatchelfHook ];
          buildInputs = lib.optionals pkgs.stdenvNoCC.isLinux [ pkgs.stdenv.cc.cc.lib ];
          meta = {
            description = "Z3 theorem prover (prebuilt binary)";
            mainProgram = "z3";
            platforms = systems;
          };
        };

        z3Source = pkgs.z3.overrideAttrs (finalAttrs: previousAttrs: {
          version = z3Version;
          src = pkgs.fetchFromGitHub {
            owner = "Z3Prover";
            repo = "z3";
            tag = "z3-${finalAttrs.version}";
            sha256 = "sha256-Qj9w5s02OSMQ2qA7HG7xNqQGaUacA1d4zbOHynq5k+A=";
          };
          patches = [];
          NIX_CFLAGS_COMPILE = "-Wno-template-body -Wno-error=maybe-uninitialized -Wno-error=uninitialized";
          # to fix error at InstallCheck time
          postFixup = (previousAttrs.postFixup or "") + ''
            if [ -f $dev/lib/pkgconfig/z3.pc ]; then
              sed -i 's|''${exec_prefix}//|/|g' $dev/lib/pkgconfig/z3.pc
            fi
          '';
        });

        z3 = if z3SourceBuild then z3Source else z3Prebuilt;

        # --- cvc5 ---

        cvc5Version = "1.1.2";

        cvc5Filename = {
          x86_64-linux = "cvc5-Linux-static";
          aarch64-linux = "cvc5-Linux-static";
          x86_64-darwin = "cvc5-macOS-static";
          aarch64-darwin = "cvc5-macOS-arm64-static";
        }.${system} or (throw "Unsupported system for prebuilt cvc5: ${system}");

        cvc5PrebuiltHash = {
          x86_64-linux = "sha256-BLJHO87BFnjBctzla/W2VSJtXBHv7WvC7/RsksIxE2Q=";
          aarch64-linux = "sha256-NR9F9IQK7z6y/NKnshofzxH2V6vMU2glP0KudKw+fTo=";
          x86_64-darwin = "sha256-Cg/K89SL2c3G/wPco8T5yL0BlLar0gQtpgikcsWewX8=";
          aarch64-darwin = "sha256-Cg/K89SL2c3G/wPco8T5yL0BlLar0gQtpgikcsWewX8=";
        }.${system} or "sha256-BLJHO87BFnjBctzla/W2VSJtXBHv7WvC7/RsksIxE2Q="; # default to x86_64-linux

        cvc5Prebuilt = pkgs.stdenvNoCC.mkDerivation {
          pname = "cvc5";
          version = cvc5Version;
          src = pkgs.fetchzip {
            url = "https://github.com/cvc5/cvc5/releases/download/cvc5-${cvc5Version}/${cvc5Filename}.zip";
            hash = cvc5PrebuiltHash;
          };
          dontBuild = true;
          installPhase = ''
            runHook preInstall
            mkdir -p $out/bin
            cp bin/cvc5 $out/bin/cvc5
            chmod +x $out/bin/cvc5
            runHook postInstall
          '' + lib.optionalString pkgs.stdenvNoCC.isLinux ''
            patchelf --set-interpreter "$(cat ${pkgs.stdenv.cc}/nix-support/dynamic-linker)" $out/bin/cvc5 || true
          '';
          nativeBuildInputs = lib.optionals pkgs.stdenvNoCC.isLinux [ pkgs.patchelf pkgs.autoPatchelfHook ];
          buildInputs = lib.optionals pkgs.stdenvNoCC.isLinux [ pkgs.stdenv.cc.cc.lib ];
          meta = {
            description = "cvc5 SMT solver (prebuilt binary)";
            mainProgram = "cvc5";
            platforms = systems;
          };
        };

        cvc5' = pkgs.cvc5.override {
          cadical = pkgs.cadical.overrideAttrs (old: rec {
            version = "2.0.0";
            src = pkgs.fetchFromGitHub {
              owner = "arminbiere";
              repo = "cadical";
              tag = "rel-${version}";
              hash = "sha256-qoeEM9SdpuFuBPeQlCzuhPLcJ+bMQkTUTGiT8QdU8rc=";
            };
          });
        };
        cvc5Source = cvc5'.overrideAttrs (finalAttrs: previousAttrs: {
          version = cvc5Version;
          src = pkgs.fetchFromGitHub {
            owner = "cvc5";
            repo = "cvc5";
            tag = "cvc5-${finalAttrs.version}";
            hash = "sha256-v+3/2IUslQOySxFDYgTBWJIDnyjbU2RPdpfLcIkEtgQ=";
          };
        });

        cvc5 = if cvc5SourceBuild then cvc5Source else cvc5Prebuilt;
      in
      {
        packages.${system} = rec {
          default = verus;
          inherit rust-bin rustup vargo verus verusfmt z3 cvc5;
        };
        formatter.${system} = pkgs.writeShellApplication {
          name = "formatter";
          runtimeInputs = [ verusfmt ] ++ lib.singleton formatter;
          text = ''
            nixpkgs-fmt "$@"
            vargo fmt
          '';
        };
        checks.${system}.lint = pkgs.stdenvNoCC.mkDerivation {
          name = "lint";
          src = ./.;
          doCheck = true;
          nativeCheckInputs = linters ++ lib.singleton formatter;
          checkPhase = ''
            statix check
            vargo fmt -- --check
          '';
          installPhase = "touch $out";
        };
        devShells.${system}.default = (pkgs.mkShellNoCC.override {
          stdenv = pkgs.stdenvNoCC.override {
            initialPath = [ pkgs.coreutils ];
          };
        }) {
          packages = [
            rust-bin
            rustup
            vargo
            verus
            verusfmt
            z3
            cvc5
          ];
        };
      }
    );
}

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
    in
    eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        formatter = pkgs.nixpkgs-fmt;
        linters = [ pkgs.statix ];
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
          cargoHash = "sha256-hxEH8qurjEDiXX2GGfZF4FTKaMz2e7O1rKHsb+ywnvc=";
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
            wrapProgram $out/bin/verus --prefix PATH : ${lib.makeBinPath [ rustup rust-bin z3 ]}
            runHook postInstall
          '';
          doCheck = false;
          passthru = { inherit vargo; };
          meta = meta // { mainProgram = "verus"; };
        };

        z3 = pkgs.z3.overrideAttrs (finalAttrs: previousAttrs: {
          version = "4.12.5";
          src = pkgs.fetchFromGitHub {
            owner = "Z3Prover";
            repo = "z3";
            tag = "z3-${finalAttrs.version}";
            sha256 = "sha256-Qj9w5s02OSMQ2qA7HG7xNqQGaUacA1d4zbOHynq5k+A=";
          };
        });
      in
      {
        packages.${system} = rec {
          default = verus;
          inherit rust-bin rustup vargo verus;
        };
        formatter.${system} = formatter;
        checks.${system}.lint = pkgs.stdenvNoCC.mkDerivation {
          name = "lint";
          src = ./.;
          doCheck = true;
          nativeCheckInputs = linters ++ lib.singleton formatter;
          checkPhase = ''
            nixpkgs-fmt --check .
            statix check
          '';
          installPhase = "touch $out";
        };
        apps.${system} = {
          update = {
            type = "app";
            program = lib.getExe (pkgs.writeShellApplication {
              name = "update";
              runtimeInputs = [ pkgs.nix-update ];
              text = lib.concatMapStringsSep "\n"
                (package: "nix-update --flake ${package} || true")
                (builtins.attrNames self.packages.${system});
            });
          };
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
          ];
        };
      }
    );
}

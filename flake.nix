{
  description = "RIINA — Rigorous Immutable Invariant, No Assumptions";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      pkgsFor = system: import nixpkgs {
        inherit system;
        overlays = [ rust-overlay.overlays.default ];
      };
    in
    {
      packages = forAllSystems (system:
        let pkgs = pkgsFor system; in {
          default = pkgs.rustPlatform.buildRustPackage {
            pname = "riinac";
            version = "0.2.0";
            src = ./03_PROTO;
            cargoLock.lockFile = ./03_PROTO/Cargo.lock;
            meta = with pkgs.lib; {
              description = "RIINA compiler — formally verified, zero-trust programming language";
              homepage = "https://github.com/ib823/proof";
              license = licenses.mpl20;
              mainProgram = "riinac";
            };
          };
        }
      );

      devShells = forAllSystems (system:
        let pkgs = pkgsFor system; in {
          default = pkgs.mkShell {
            buildInputs = with pkgs; [
              (rust-bin.stable."1.84.0".default)
              coq
              gcc
            ];
            shellHook = ''
              echo "RIINA dev shell — Rust $(rustc --version), Coq $(coqc --version | head -1)"
            '';
          };
        }
      );
    };
}

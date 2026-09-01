# This file is part of midnight-zkir.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

{
  description = "Midnight zkir";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    fenix.url = "github:nix-community/fenix";
    inclusive.url = "github:input-output-hk/nix-inclusive";
  };

  outputs = {
    self,
    nixpkgs,
    utils,
    fenix,
    inclusive,
    ...
  }:
    utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
        pkgsStatic = pkgs.pkgsStatic;
        mkShell = pkgs.mkShell.override {
          stdenv = pkgs.clangStdenv;
        };
        rustWorkspaceSrc = inclusive.lib.inclusive ./. [
          ./Cargo.toml
          ./Cargo.lock
          ./zkir
          ./zkir-wasm
        ];
        rust = fenix.packages.${system};
        zkir-version = (builtins.fromTOML (builtins.readFile ./zkir/Cargo.toml)).package.version;
        mkZkir = { pname, crate }: ({
            "x86_64-linux" = pkgsStatic;
            "x86_64-darwin" = pkgs;
            "aarch64-linux" = pkgsStatic;
            "aarch64-darwin" = pkgs;
        }.${system}.makeRustPlatform {
          rustc = self.packages.${system}.rust-build-toolchain;
          cargo = self.packages.${system}.rust-build-toolchain;
        }).buildRustPackage rec {
            inherit pname;
            version = (builtins.fromTOML (builtins.readFile ./${pname}/Cargo.toml)).package.version;
            src = rustWorkspaceSrc;
            cargoLock.lockFile = ./Cargo.lock;
            cargoLock.allowBuiltinFetchGit = true;

            MIDNIGHT_PP = "${self.packages.${system}.public-params}";

            buildInputs = [
              self.packages.${system}.public-params
            ];
            cargoBuildFlags = "--package ${crate} --features binary";
            nativeBuildInputs = [
              self.packages.${system}.rust-build-toolchain
            ];
            doCheck = false;
          };
      in
        rec {
          packages.rust-build-toolchain = rust.combine [
            rust.stable.rustc
            rust.targets.wasm32-unknown-unknown.stable.rust-std
            rust.targets.aarch64-unknown-linux-musl.stable.rust-std
            rust.targets.aarch64-unknown-linux-gnu.stable.rust-std
            rust.targets.x86_64-unknown-linux-musl.stable.rust-std
            rust.targets.x86_64-unknown-linux-gnu.stable.rust-std
            rust.complete.cargo
            rust.complete.rustfmt
            rust.stable.clippy
          ];
          packages.rust-dev-toolchain = rust.combine [
            rust.stable.rustc
            rust.targets.wasm32-unknown-unknown.stable.rust-std
            rust.targets.aarch64-unknown-linux-musl.stable.rust-std
            rust.targets.aarch64-unknown-linux-gnu.stable.rust-std
            rust.targets.x86_64-unknown-linux-musl.stable.rust-std
            rust.targets.x86_64-unknown-linux-gnu.stable.rust-std
            rust.complete.cargo
            rust.complete.rustfmt
            rust.stable.clippy
            rust.stable.rust-docs
            rust.stable.rust-src
            rust.stable.rust-analyzer
          ];

          packages.default = packages.zkir;

          packages.zkir = mkZkir { pname = "zkir"; crate = "midnight-zkir"; };

          packages.test-artifacts = pkgs.stdenvNoCC.mkDerivation {
            pname = "midnight-zkir-test-artifacts";
            version = zkir-version;
            src = inclusive.lib.inclusive ./zkir-precompiles [./zkir-precompiles];
            MIDNIGHT_PP = "${packages.public-params}";
            nativeBuildInputs = [
              pkgs.jq
              packages.public-params
              packages.zkir
            ];
            buildPhase = ''
              for contract in *; do
                mv "$contract" "$contract-tmp"
                mkdir -p "$contract/keys"
                mv $contract-tmp "$contract/zkir"
                VERSION=$(jq -s '.[0].version.major' $contract/zkir/*.zkir)
                if [[ "$VERSION" == "3" ]]; then
                  ${packages.zkir}/bin/zkir compile-many "$contract/zkir" "$contract/keys"
                elif [[ "$VERSION" == "2" ]]; then
                  # The v2 toolchain was removed in the crate consolidation, so
                  # v2 fixtures ship with an empty keys/ directory; only their
                  # zkir sources and precomputed hashes remain usable.
                  :
                else
                  # Without this the loop would fall through, leaving an empty
                  # keys/ directory and still exiting 0, so a contract whose
                  # version no zkir here can compile would silently vanish from
                  # MIDNIGHT_LEDGER_TEST_STATIC_DIR instead of failing the build.
                  echo "error: contract '$contract' declares unsupported zkir major version '$VERSION'" >&2
                  exit 1
                fi
              done
            '';
            installPhase = ''
              mkdir $out
              for contract in *; do
                cp -a "$contract" "$out/$contract"
              done
            '';
          };

          packages.public-params = let
              param-for = k: "https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_midnight_2p${builtins.toString k}";
          in pkgs.stdenvNoCC.mkDerivation {
            pname = "midnight-testing-public-parameters";
            version = "0.1.0";

            srcs = [
              (pkgs.fetchurl { url = param-for 0; hash = "sha256-WbMLMRSjTMu/tZk3bhePuNmzNmyuIXTC8dog51hH+CM="; })
              (pkgs.fetchurl { url = param-for 1; hash = "sha256-u+BP48cNDBOER8sIa0ut3DDLi7KgBBFLwC5vc5UWKA4="; })
              (pkgs.fetchurl { url = param-for 2; hash = "sha256-gOFVaPoaARfbiTI5vn+l40przDqMO/p3CVNLnLiOtsE="; })
              (pkgs.fetchurl { url = param-for 3; hash = "sha256-S+gnpkchk9+A2PCLSyWoW670Nv3Rll2Jtq+J9OxOmeI="; })
              (pkgs.fetchurl { url = param-for 4; hash = "sha256-Iy9AH60Qx934go0qpMhcZQbF2gl5WZjOyuufdfyPato="; })
              (pkgs.fetchurl { url = param-for 5; hash = "sha256-ChySKfMV/Bho/yX2aPuDrsTQn08jpwa1GXxpLGGdcsY="; })
              (pkgs.fetchurl { url = param-for 6; hash = "sha256-zyrWvn0P7fW+wqqjX2vkrKMwU9dCaP31qlT8sokept8="; })
              (pkgs.fetchurl { url = param-for 7; hash = "sha256-6CrokMCAGINV83/q/+kTclhM2BBhUILZFD1N7ART/Z0="; })
              (pkgs.fetchurl { url = param-for 8; hash = "sha256-kJtwdVHqrqeYKOiDzeb8RqsVmGw7HXkb7UYsnigFyTM="; })
              (pkgs.fetchurl { url = param-for 9; hash = "sha256-uQCfEJi87//sPEYas6XjoX9+VZnw8Ixw/NxVqJInvL0="; })
              (pkgs.fetchurl { url = param-for 10; hash = "sha256-RrIpCTPL7Uw3iInkupcfGpKIgzH/sJRmrNT/YaHiy0I="; })
              (pkgs.fetchurl { url = param-for 11; hash = "sha256-mQFYnXlW/1i+DYVWmy9FW3e1jDdYAm/7W75IBwALltE="; })
              (pkgs.fetchurl { url = param-for 12; hash = "sha256-7wjrP89i349yxRXP+gJ+aBgItTDLAW7qEEEVVF721cg="; })
              (pkgs.fetchurl { url = param-for 13; hash = "sha256-0zJJEJacTMVBQ7gEW2SeXDpL1ft7j4X+G3cPZAzhyAM="; })
              (pkgs.fetchurl { url = param-for 14; hash = "sha256-/CUwFoheyDDpeAjJ7JILtcq1whr1kDgKbLXrBTjiskQ="; })
              (pkgs.fetchurl { url = param-for 15; hash = "sha256-ckx8PXeRSLsRPH7pwDSy8n2xbmvfMV/ekBBam60Asd4="; })
              (pkgs.fetchurl { url = param-for 16; hash = "sha256-Cch3IW1libNwJj4Yr0CgMKkBtBp6fDfvWMmQHbQfBcY="; })
              (pkgs.fetchurl { url = param-for 17; hash = "sha256-Sp72x8Bhmqt07t5EsT51PjulRQigLdO3EGqUmqu3O3Q="; })
            ];

            dontUnpack = true;

            buildPhase = "";

            installPhase = ''
              mkdir $out
              for src in $srcs; do
                name=$(echo $src | sed -e 's/^.*-//')
                cp $src $out/$name
              done
              ls -lh $out
            '';
          };

          devShells.default = mkShell {
            packages = [
              packages.rust-dev-toolchain
              pkgs.jq
              pkgs.clang
              pkgs.cargo-hack
              pkgs.cargo-audit
              pkgs.cargo-nextest
              pkgs.wasm-pack
              pkgs.wasm-bindgen-cli_0_2_108
            ];
            buildInputs = [packages.public-params];

            # This is required to build blst for wasm. This will not affect
            # Native build outputs of this flake, though it does make native
            # builds *from this devshell* marginally less secure.
            # The stack protector tries to pull in OS code that doesn't exist.
            hardeningDisable = ["zerocallusedregs" "stackprotector"];

            MIDNIGHT_PP = "${packages.public-params}";
            MIDNIGHT_LEDGER_TEST_STATIC_DIR = "${packages.test-artifacts}";
          };
        }
    );
}

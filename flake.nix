{
  description = "Synthetic Computability Theory in Rocq";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    # Pinned to the same revision as ../commutative-kleene-algebra so the
    # Rocq toolchain (Rocq 9.0.1, Equations 1.3.1+9.0, stdpp 1.12.0) matches.
    nixpkgs.url = "github:NixOS/nixpkgs/c5296fdd05cfa2c187990dd909864da9658df755";
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import an internal flake module: ./other.nix
        # To import an external flake module:
        #   1. Add foo to inputs
        #   2. Add foo as a parameter to the outputs function
        #   3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };

        packages.default = pkgs.coqPackages.coq-synthetic-computability;

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
            pkgs.rocqPackages.vsrocq-language-server
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

      };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        overlays.default = final: prev: {
          coqPackages = prev.coqPackages.overrideScope (final: prev: {
            coq-synthetic-computability = prev.mkCoqDerivation {
              pname = "coq-synthetic-computability";
              version = ./.;
              # equations ships an OCaml findlib plugin (rocq-equations.plugin);
              # mlPlugin pulls in ocaml + findlib so OCAMLPATH is populated
              # and Rocq can locate the plugin at compile time.
              mlPlugin = true;
              propagatedBuildInputs = [
                final.coq
                final.equations
                final.stdpp
              ];
              # Rocq 9.0 reads dependency paths from ROCQPATH; the nixpkgs coq
              # setup hook still exports COQPATH and Rocq prints a deprecation
              # warning.  Translate once before any phase runs.
              preConfigure = ''
                if [ -n "''${COQPATH-}" ]; then
                  export ROCQPATH="$COQPATH"
                  unset COQPATH
                fi
              '';
              # The upstream theories/Makefile generates _CoqProject via
              # `git ls-files`, which does not work when the source is copied
              # out of the git tree by Nix.  Regenerate it from `find` and
              # produce Makefile.coq directly; subsequent phases use that.
              preBuild = ''
                pushd theories
                cp _CoqProject.in _CoqProject
                find . -name '*.v' -type f \
                  ! -path './Models/*' \
                  ! -path './ArithmeticHierarchy/*' \
                  | sed 's|^\./||' | sort >> _CoqProject
                coq_makefile -f _CoqProject -o Makefile.coq
                popd
              '';
              makeFlags = [ "-C" "theories" "-f" "Makefile.coq" ];
            };
          });
        };

      };
    };
}

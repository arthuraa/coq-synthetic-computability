{
  description = "Synthetic Computability Theory in Rocq";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    # Pinned to the same revision as ../commutative-kleene-algebra so the
    # Rocq toolchain (Rocq 9.0.1, Equations 1.3.1+9.0, stdpp 1.12.0) matches.
    nixpkgs.url = "github:NixOS/nixpkgs/c5296fdd05cfa2c187990dd909864da9658df755";
    # Sources for the Rocq MCP server and its one missing Python dependency.
    # Neither project is a flake; the overlay below packages them as proper
    # Nix derivations.
    rocq-mcp.url = "github:LLM4Rocq/rocq-mcp";
    rocq-mcp.flake = false;
    pytanque.url = "github:LLM4Rocq/pytanque";
    pytanque.flake = false;
    # Needed by theories/Models (T_L, LMuRecursion, etc. depend on
    # Undecidability.L.*). The rocq-9.0 branch's own _CoqProject comments out
    # most of L/ (including Functions/{Encoding,Eval}.v) -- empirically this
    # is NOT a real Rocq-9 incompatibility, just a build wired without
    # MetaRocq; see the postPatch/propagatedBuildInputs below (a no-op here,
    # since the fork already has L/ uncommented natively -- kept so this
    # flake still works standalone against a plain upstream checkout too).
    # Pinned to jstrattonsmith/coq-library-undecidability's enable-L-nix-9.0
    # branch (0 commits ahead/behind uds-psl/coq-library-undecidability's
    # rocq-9.0 otherwise, checked 2026-08-31) so this and
    # ../commutative-kleene-algebra always resolve the same source. Downstream
    # flakes should set
    # `inputs.coq-synthetic-computability.inputs.coq-library-undecidability.follows`
    # to avoid a second, possibly-drifted copy.
    coq-library-undecidability.url = "github:jstrattonsmith/coq-library-undecidability/enable-L-nix-9.0";
    coq-library-undecidability.flake = false;
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, rocq-mcp, pytanque, coq-library-undecidability, ... }:
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
        packages.rocq-mcp = pkgs.rocq-mcp;

        # Default shell: lean, for humans editing the development.
        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
            pkgs.rocqPackages.vsrocq-language-server
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

        # AI-agent shell: extends `default` with rocq-mcp and the tools it
        # drives (`pet` is already on PATH via coq-lsp; `coqc` via Coq;
        # dune is used by rocq-mcp to detect dune workspaces).  Use this
        # when configuring an MCP client.
        devShells.ai = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.rocq-mcp
            pkgs.dune_3
          ];
          inputsFrom = [
            self'.devShells.default
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
                final.coq-library-undecidability
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
                  ! -path './ArithmeticHierarchy/*' \
                  | sed 's|^\./||' | sort >> _CoqProject
                coq_makefile -f _CoqProject -o Makefile.coq
                popd
              '';
              makeFlags = [ "-C" "theories" "-f" "Makefile.coq" ];
            };
            # rocq-9.0's own _CoqProject comments out most of theories/L/
            # (including Functions/{Encoding,Eval}.v, needed by our
            # Models/CT.v). Empirically (tested in an isolated worktree
            # against this exact commit) all 69 L/ files compile cleanly
            # under Rocq 9.0.1 once the MetaRocq packages below are on the
            # loadpath -- the exclusion was a build-wiring gap upstream, not
            # a real incompatibility. So: un-comment those lines and add the
            # deps they need.
            coq-library-undecidability = prev.mkCoqDerivation {
              pname = "coq-library-undecidability";
              version = coq-library-undecidability.outPath;
              # L/Tactics/Extract.v needs the equations OCaml findlib plugin.
              mlPlugin = true;
              propagatedBuildInputs = [
                final.coq
                final.equations
                final.metarocq-template-rocq
                final.metarocq-utils
                final.metarocq-common
                final.metarocq-pcuic
                final.metarocq-template-pcuic
                final.metarocq-safechecker
                final.metarocq-erasure
              ];
              postPatch = ''
                sed -i -E 's/^#(L\/.*\.v)$/\1/' theories/_CoqProject
              '';
            };
          });

          # Extend python311Packages with the bits needed by rocq-mcp.
          python311 = prev.python311.override (old: {
            packageOverrides = prev.lib.composeExtensions
              (old.packageOverrides or (_: _: { }))
              (pyFinal: pyPrev: {
                # fastmcp 3.x needs py-key-value-aio >= 0.4.4; nixpkgs ships
                # 0.3.0 from when the upstream was a monorepo.  In 0.4.x the
                # repo flattened into a single package, so override both
                # source and layout (no more sourceRoot / py-key-value-shared
                # dependency).
                py-key-value-aio = pyPrev.py-key-value-aio.overridePythonAttrs (old: {
                  version = "0.4.4";
                  src = final.fetchFromGitHub {
                    owner = "strawgate";
                    repo = "py-key-value";
                    tag = "0.4.4";
                    hash = "sha256-JznZW3FOKlhZD42Ng108tNB4bNiEad7QBiu8RmflTXM=";
                  };
                  sourceRoot = null;
                  dependencies = [ pyFinal.beartype pyFinal.typing-extensions ];
                  # The upstream test suite exercises many backends we
                  # don't ship (aerospike, dynamodb, elasticsearch, etc.).
                  doCheck = false;
                  disabledTestPaths = [ ];
                  disabledTests = [ ];
                });

                # New package: griffelib (used by fastmcp 3.x for introspection).
                griffelib = pyFinal.buildPythonPackage rec {
                  pname = "griffelib";
                  version = "2.0.2";
                  pyproject = true;
                  src = final.fetchPypi {
                    inherit pname version;
                    hash = "sha256-PPILO8Rw6Ddj/78jbgB2sSEbrBvGfeE9r0lGQPLecH4=";
                  };
                  build-system = [
                    pyFinal.hatchling
                    pyFinal.pdm-backend
                    pyFinal.uv-dynamic-versioning
                  ];
                  # griffelib installs under the "griffe" top-level name.
                  pythonImportsCheck = [ "griffe" ];
                  doCheck = false;
                };

                # New package: uncalled-for.
                uncalled-for = pyFinal.buildPythonPackage rec {
                  pname = "uncalled_for";
                  version = "0.3.1";
                  pyproject = true;
                  src = final.fetchPypi {
                    inherit pname version;
                    hash = "sha256-XkEqxnCPBLVr71hntdz2aQ685OtzFgWNnFB4dJK7S8o=";
                  };
                  build-system = [ pyFinal.hatchling pyFinal.hatch-vcs ];
                  # hatch-vcs needs a version; the sdist doesn't carry git
                  # tags, so hand it the version explicitly.
                  env.SETUPTOOLS_SCM_PRETEND_VERSION = version;
                  env.HATCH_BUILD_HOOK_VERSION = version;
                  pythonImportsCheck = [ "uncalled_for" ];
                  doCheck = false;
                };

                # Upgrade fastmcp from 2.14.3 to 3.2.4.
                fastmcp = pyPrev.fastmcp.overridePythonAttrs (old: rec {
                  version = "3.2.4";
                  src = final.fetchPypi {
                    pname = "fastmcp";
                    inherit version;
                    hash = "sha256-CD7LdbRKQWnn/A9jL5S3gb2w/4d8azW5h3y7Vm/U1NE=";
                  };
                  dependencies = [
                    pyFinal.authlib
                    pyFinal.cyclopts
                    pyFinal.exceptiongroup
                    pyFinal.griffelib
                    pyFinal.httpx
                    pyFinal.jsonref
                    pyFinal.jsonschema-path
                    pyFinal.mcp
                    pyFinal.openapi-pydantic
                    pyFinal.opentelemetry-api
                    pyFinal.packaging
                    pyFinal.platformdirs
                    pyFinal.py-key-value-aio
                    pyFinal.pydantic
                    pyFinal.pyperclip
                    pyFinal.python-dotenv
                    pyFinal.pyyaml
                    pyFinal.rich
                    pyFinal.uncalled-for
                    pyFinal.uvicorn
                    pyFinal.watchfiles
                    pyFinal.websockets
                  ]
                  ++ pyFinal.py-key-value-aio.optional-dependencies.filetree
                  ++ pyFinal.py-key-value-aio.optional-dependencies.keyring
                  ++ pyFinal.py-key-value-aio.optional-dependencies.memory
                  ++ pyFinal.pydantic.optional-dependencies.email;
                  doCheck = false;
                  disabledTests = [ ];
                  disabledTestPaths = [ ];
                });

                # New package: pytanque (LLM4Rocq's Python client for petanque).
                pytanque = pyFinal.buildPythonPackage {
                  pname = "pytanque";
                  version = "0.2.2";
                  pyproject = true;
                  src = pytanque;
                  build-system = [ pyFinal.setuptools ];
                  dependencies = [
                    pyFinal.typing-extensions
                    pyFinal.requests
                  ];
                  pythonImportsCheck = [ "pytanque" ];
                  doCheck = false;
                };

              });
          });
          python311Packages = final.python311.pkgs;

          # rocq-mcp is an application, not a Python library, so it lives
          # at the top of the overlay (pythonPackages rejects non-toPythonModule
          # attrs).  It still uses buildPythonApplication under the hood.
          rocq-mcp = final.python311Packages.buildPythonApplication {
            pname = "rocq-mcp";
            version = "0.2.0";
            pyproject = true;
            src = rocq-mcp;
            # Upstream pins pytanque via a git URL; rewrite it to a plain
            # name so the wheel builder picks up our packaged pytanque.
            postPatch = ''
              substituteInPlace pyproject.toml \
                --replace-fail \
                  "pytanque @ git+https://github.com/LLM4Rocq/pytanque" \
                  "pytanque"
            '';
            build-system = [ final.python311Packages.setuptools ];
            dependencies = [
              final.python311Packages.fastmcp
              final.python311Packages.pytanque
            ];
            doCheck = false;
            pythonImportsCheck = [ "rocq_mcp" ];
          };
        };

      };
    };
}

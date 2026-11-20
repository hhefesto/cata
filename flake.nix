{
  description = "cata: Haskell, Agda and specs in, checked Bend 2 out, by fixed rules";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # Bend 2, upstream's; nothing it does not check is ever patched into it.
  inputs.bend2 = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # agda2bend's Bend side: its fold of Agda into Bend (Agda2Bend/Cata.bend),
  # the Bend syntax tree, printer and S-expression reader (ToBend/) and Sys.bend,
  # which cata shares.  Built in as bend/a2b (a git-ignored link in a checkout).
  inputs.agda2bend = {
    url = "github:hhefesto/agda2bend";
    flake = false;
  };

  outputs =
    { self, nixpkgs, bend2, agda2bend }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
      pkgsFor = system: import nixpkgs { inherit system; };
      # the pinned bend command, telemetry off
      bendFor =
        pkgs:
        pkgs.writeShellScriptBin "bend" ''
          export BEND_NO_TELEMETRY=1
          exec ${bend2.packages.${pkgs.stdenv.hostPlatform.system}.default}/bin/bend "$@"
        '';
      # The Haskell front end (tools/hs-export, its FORMAT.md): GHC's
      # typechecked syntax of one module as S-expressions.  It decides
      # nothing; all translation is Bend's.
      # What a Bend build may see: cata's .bend sources, and agda2bend's Bend side
      # as bend/a2b.
      bendSrc = nixpkgs.lib.fileset.toSource {
        root = ./.;
        fileset = nixpkgs.lib.fileset.fileFilter (f: f.hasExt "bend") ./bend;
      };
      # A Bend 2 program compiled to a native binary (C via clang).
      bendBinary =
        pkgs: name: entry:
        pkgs.runCommand name { nativeBuildInputs = [ (bendFor pkgs) ]; } ''
          export HOME=$TMPDIR
          cp -r ${bendSrc}/bend src
          chmod -R u+w src
          cp -r ${agda2bend}/bend src/a2b
          chmod -R u+w src/a2b
          mkdir -p $out/bin
          bend src/${entry} -o $out/bin/${name}
        '';
      hsExportFor =
        pkgs:
        (
          pkgs.haskellPackages.callCabal2nix "hs-export" (nixpkgs.lib.fileset.toSource {
            root = ./tools/hs-export;
            fileset = ./tools/hs-export;
          }) { }
        );
    in
    {
      packages = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          bend = bendFor pkgs;
          # `hs-export OUT.sexp FILE.hs`.  GHC's API needs its libdir at run
          # time; ghc-paths bakes in the ghc this was built with.
          hs-export = hsExportFor pkgs;
          # `survey OUT FILE.sexp...`: which bindings of hs-export's modules fall
          # in cata hs's first version, and why the others do not
          # (bend/Survey.bend)
          survey = bendBinary pkgs "survey" "Survey.bend";
          # `spec OUT FILE.sexp...`: a package's exports with pattern synonyms
          # inlined, views made plain and constrained defs specialised at their
          # callers' types (bend/Spec.bend); survey, fold and law read its output
          spec = bendBinary pkgs "spec" "Spec.bend";
          # `fold OUT FILE.sexp...`: step 2's fold into checked Bend (bend/Fold.bend)
          fold = bendBinary pkgs "fold" "Fold.bend";
          # `law OUT FILE.sexp...`: the fold with GHC's example laws
          # (bend/Law.bend; GHC names the ghc, the .#ghc below)
          law = bendBinary pkgs "law" "Law.bend";
          # The example laws' oracle (bend/Law.bend): GHC's interpreter runs
          # each original Haskell function on the inputs cata lists.  The same
          # GHC hs-export is built with.
          ghc = pkgs.haskellPackages.ghc;
          # The same GHC with telomare master's library dependencies
          # (telomare.cabal's build-depends): its package db is the
          # -package-db for hs-export --package, and its ghc law's GHC, when
          # telomare goes through cata as a package.
          ghc-telomare = pkgs.haskellPackages.ghcWithPackages (
            p: with p; [
              binary
              bytestring
              containers
              data-fix
              deepseq
              dlist
              filepath
              megaparsec
              memory
              mtl
              recursion-schemes
              transformers
              lens
              cryptonite
              utf8-string
              validity
              genvalidity
              free
            ]
          );
          default = self.packages.${system}.hs-export;
        }
      );

      devShells = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          default = pkgs.mkShell {
            packages = [
              (bendFor pkgs)
              (pkgs.haskellPackages.ghcWithPackages (p: [ p.ghc-paths p.mtl ]))
              pkgs.cabal-install
            ];
          };
        }
      );
    };
}

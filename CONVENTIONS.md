# Haskell programming conventions

  * Indentation uses spaces, not tabs.  Indentation is two spaces.

  * All top-level definitions and in a Haskell source file must be accompanied
    by a type declaration.

  * All major definitions and type declarations in a Haskell source file must
    be accompanied by Haddock documentation explaining their purpose.

  * GHC extensions must be enabled on a per-file basis (i.e. using a LANGUAGE
    pragma at the top of a file), rather than using global flags passed to GHC
    in the Mosquito.cabal file.

  * The following naming conventions are adopted:

      * Names of theorems are suffixed with T (e.g. reflexivityT)
      * Names of rules are suffixed with R (e.g. alphaR)
      * Names of constants are suffixed with C (e.g. trueC)
      * Names of defining theorems for constants are suffixed with D (e.g. trueD)
      * Names of local edits are suffixed with L (e.g. symmetryL)
      * Names of pretactics are suffixed with P (e.g. symmetryP)
      * Names of conversions and conversionals are suffixed with Conv (e.g.
        replaceEverywhereConv)

  * Every record must have accompanying first class labels generated using
    Data.Label.  See src/Mosquito/Kernel/Term.hs for an example.

  * For abstract types exported from a module consider exporting a non-abstract
    view type with accompanying view function.  See src/Mosquito/Kernel/Term.hs
    for examples.  Note the pattern in Term.hs is to supply both a series of
    monadic deconstruction functions for abstract types and view types.  For some
    types, multiple view types may be provided.

  * The Show typeclass is for printing "as is".  The Pretty typeclass is for pretty
    printing.  Do not use Show for pretty printing.
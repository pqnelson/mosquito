# About

Mosquito is an experimental LCF-style implementation of higher-order logic (HOL)
using Haskell as a metalanguage.  Mosquito is written in a pure, largely total,
and stateless style, as befitting an implementation of HOL in idiomatic Haskell.

As with all LCF-style implementations, the correctness of the entire system is
underpinned by the correctness of the system's `kernel'.  This kernel can be found
in the src/Mosquito/Kernel/ directory and consists of two files: QualifiedNames.hs
and Term.hs, the latter being the most interesting of the two files.  If you
believe that Term.hs correctly implements higher-order logic, and you believe that
your implementation of GHC correctly keeps the Theorem type in Term.hs abstract,
then you may conclude that the entire system is correct, as the only way to construct
a derivation in Mosquito's logic is via the inference rules implemented in Term.hs.

Mosquito supports both backward and forward proof.  Forward proof is supported
directly via appeal to the implementation of the HOL inference rules in Term.hs.
Backward proof is supported via an (experimental) implementation of tactics.  These,
and the proof state that tactics act upon, can be found in src/Mosquito/ProofState.
Examples of their use can be found in src/Mosquito/Theories/Boolean.hs.

# License

Mosquito is licensed under the BSD 3 clause open source license.  Please see the
enclosed LICENSE files for details.
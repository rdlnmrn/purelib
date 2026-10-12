module

public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Theorem 110: cyclic quadrilateral spreads

The six subtended spreads are finite field scalars.  Their four triangle
views are stored as explicit `SpreadTriple` certificates; Theorem 110 is then
exactly two applications of the Two spread triples theorem.

For an actual displayed cyclic quadrilateral on a non-null circle,
`normalizedCyclicSubtendedSpreads` constructs those six scalars as
`Q(A_i,A_j)/(4*K)` and derives every triple certificate from the finite
Subtended spread theorem.  The nonzero circle quadrance is visible because
over a general finite field a null circle can have null chords, for which the
book's spread quotients are not defined.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

set_option genInjectivity false in
/-- Six subtended spreads with their four triangle-relation certificates.

Each diagonal is retained together with the two spread triples formed by the corresponding pairs of side spreads; the
record uses explicit field scalars throughout. -/
structure CyclicSubtendedSpreads (K : Type*)
  [Algebra.Field.ExplicitField K] where
  /-- The subtended spread associated with the first and second vertices. -/ r₁₂ : K
  /-- The subtended spread associated with the second and third vertices. -/ r₂₃ : K
  /-- The subtended spread associated with the third and fourth vertices. -/ r₃₄ : K
  /-- The subtended spread associated with the first and fourth vertices. -/ r₁₄ : K
  /-- The subtended spread associated with the first diagonal. -/ r₁₃ : K
  /-- The subtended spread associated with the second diagonal. -/ r₂₄ : K
  /-- The first two side spreads and the first diagonal form a spread triple. -/ firstDiagonalAtFourth :
    TripleSpread.SpreadTriple r₁₂ r₂₃ r₁₃
  /-- The opposite two side spreads and the first diagonal form a spread triple. -/ firstDiagonalAtSecond :
    TripleSpread.SpreadTriple r₃₄ r₁₄ r₁₃
  /-- The side spreads at the first vertex and the second diagonal form a spread triple. -/ secondDiagonalAtThird :
    TripleSpread.SpreadTriple r₁₂ r₁₄ r₂₄
  /-- The side spreads at the third vertex and the second diagonal form a spread triple. -/ secondDiagonalAtFirst :
    TripleSpread.SpreadTriple r₂₃ r₃₄ r₂₄

constructive_injectivity CyclicSubtendedSpreads

end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end

module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Odd.Presentation
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib.Algebra.Field.Finite.Odd.Presentation

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Field-specific claims between the numbered results

The paper makes several mathematical assertions in the prose surrounding
Theorems 24 and 29.  This module records them explicitly.  Ordered and
rational claims are proved directly from finite coordinates.  The assertion
that every half-spread value occurs over a finite field is computed from an
explicit finite carrier and cached square table, with no choice-derived
enumeration or witness.
-/

namespace Purelib.Algebra.Field.Finite.Odd

variable {K : Type*} [ExplicitField K]

/-! ## Ordered half-spread interval -/

/-! ## Finite-field half-spread boundary -/

set_option genInjectivity false in
/-- Three displayed scalars whose squared sum is the indexed value.

The record retains each coordinate and the exact sum-of-squares equality. -/
structure ThreeSquares.ThreeSquareRepresentation (value : K) where
  /-- The first retained coordinate. -/ t : K
  /-- The second retained coordinate. -/ r : K
  /-- The third retained coordinate. -/ s : K
  /-- The three coordinate squares sum to the indexed value. -/ equation : t ^ 2 + r ^ 2 + s ^ 2 = value

constructive_injectivity ThreeSquares.ThreeSquareRepresentation

namespace ThreeSquares.ThreeSquareRepresentation

open Purelib.Algebra.Field.Finite.Odd.ThreeSquares
/-- Read a three-square representation as its retained three-coordinate vector. -/
def vector (representation :
  ThreeSquareRepresentation (K := K) value) :
    Vector K :=
  ⟨representation.t, representation.r, representation.s⟩

/-- The retained vector has quadrance equal to the represented value. -/
theorem vector_quadrance
    (representation : ThreeSquareRepresentation (K := K) value) :
    representation.vector.quadrance = value := by
  unfold vector Vector.quadrance Vector.dot
  calc
    representation.t * representation.t +
          representation.r * representation.r +
          representation.s * representation.s =
        representation.t ^ 2 + representation.r ^ 2 +
          representation.s ^ 2 := by ring1
    _ = value := representation.equation

end ThreeSquares.ThreeSquareRepresentation

open Purelib.Algebra.Field.Finite.Odd.ThreeSquares in
set_option genInjectivity false in
/-- An executable three-square representation for every requested scalar.

Each result retains its three coordinates and their exact sum-of-squares certificate. -/
structure ThreeSquares.ThreeSquareAlgorithm (K : Type*) [ExplicitField K] where
  /-- Construct retained coordinates and their three-square certificate for the requested value. -/ represent : (value :
    K) → ThreeSquareRepresentation value

constructive_injectivity ThreeSquares.ThreeSquareAlgorithm

open Purelib.Algebra.Field.Finite.Odd.ThreeSquares in
/-- Extend the finite two-square construction to a three-square algorithm.

The first two retained coordinates represent the target, and the third coordinate is zero. -/
def Presentation.FiniteOddFieldPresentation.threeSquareAlgorithm
    (presentation : FiniteOddFieldPresentation K) : ThreeSquareAlgorithm K where
  represent := fun value => by
    let pair := presentation.twoSquareRepresentation value
    refine
      { t := pair.first
        r := pair.second
        s := 0
        equation := ?_ }
    calc
      pair.first ^ 2 + pair.second ^ 2 + (0 : K) ^ 2 =
          pair.first ^ 2 + pair.second ^ 2 := by ring1
      _ = value := pair.equation
end Purelib.Algebra.Field.Finite.Odd

end

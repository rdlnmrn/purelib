module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Inverse
import Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Pulling finite CCL comparisons back to the original coordinate

Raw-parser predicates are stated at the current affine tail, whereas the
winding boxes live in the original polynomial coordinate.  This module
precomposes every Hermitian comparison with a finite decoder homography and
clears its denominator by a positive squared norm.  It also supplies the
explicit adjugate chart used to recover the unique parser tail.
-/

namespace Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A nonsingular parser state represents the input at its adjugate inverse tail when the inverse denominator and
retained constraints hold. -/
theorem represents_of_inverse_tail
    (state : Data.CCL.Encoding.Parser.State) (input : Basic.Canonical)
    (determinantNonzero : Matrix2.BoundaryAdjugate.determinant state.matrix ≠ 0)
    (inverseDenominator : Homography.Basic.denominator (Matrix2.BoundaryAdjugate.adjugate state.matrix) input ≠ 0)
    (holds : state.Holds (Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate state.matrix) input)) :
    Parser.Semantics.State.Represents state input (Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate
      state.matrix) input) := by
  refine ⟨Homography.denominator_inverse_tail_ne state.matrix input
      determinantNonzero inverseDenominator, ?_, holds⟩
  exact (Homography.homographic_adjugate_inverse state.matrix input determinantNonzero
    inverseDenominator).symm

end Purelib.Data.CCL.Encoding.Parser

end

section
@[expose] public section

/-!
# Finite Hermitian formulas for one raw CCL bit

Before a completed sector, the proposed child is just the next parser-state
formula at the unchanged affine tail.  On the third sector bit, the formula
checks the selected completed block and excludes its zero residual.  The
result is exactly the constructive one-bit semantic decision.
-/

namespace Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- A represented input has nonzero adjugate inverse denominator whenever the retained parser matrix is nonsingular. -/
theorem inverseDenominator_of_represents
    (state : Data.CCL.Encoding.Parser.State) (input tail : Basic.Canonical)
    (determinantNonzero :
      Matrix2.BoundaryAdjugate.determinant state.matrix ≠ 0)
    (represented : Parser.Semantics.State.Represents state input tail) :
    Homography.Basic.denominator (Matrix2.BoundaryAdjugate.adjugate state.matrix) input ≠
      0 := by
  have inverseDenominator :=
    Homography.adjugate_denominator_homographic_ne
      state.matrix tail determinantNonzero represented.1
  rw [represented.2.1]
  exact inverseDenominator

/-- The adjugate homography recovers the exact tail of a nonsingular retained parser representation. -/
theorem inverseTail_eq
    (state : Data.CCL.Encoding.Parser.State) (input tail : Basic.Canonical)
    (determinantNonzero :
      Matrix2.BoundaryAdjugate.determinant state.matrix ≠ 0)
    (represented : Parser.Semantics.State.Represents state input tail) :
    Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate state.matrix) input =
      tail := by
  calc
    Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate state.matrix) input =
        Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate state.matrix)
          (Homography.Basic.homographic state.matrix tail) := congrArg
            (Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate state.matrix))
            represented.2.1
    _ = tail :=
      Homography.homographic_adjugate_forward_inverse
        state.matrix tail determinantNonzero represented.1

/-- Any represented input of a nonsingular parser state is represented by its exact adjugate inverse tail. -/
theorem represents_inverse_tail_of_represented
    (state : Data.CCL.Encoding.Parser.State) (input : Basic.Canonical)
    (determinantNonzero :
      Matrix2.BoundaryAdjugate.determinant state.matrix ≠ 0)
    (represented : ∃ tail, Parser.Semantics.State.Represents state input tail) :
    Parser.Semantics.State.Represents state input
      (Homography.Basic.homographic (Matrix2.BoundaryAdjugate.adjugate state.matrix)
        input) := by
  rcases represented with ⟨tail, tailRepresents⟩
  have inverseDenominator := inverseDenominator_of_represents state input
    tail determinantNonzero tailRepresents
  apply represents_of_inverse_tail state input
    determinantNonzero inverseDenominator
  rw [inverseTail_eq state input tail determinantNonzero tailRepresents]
  exact tailRepresents.2.2
end Purelib.Data.CCL.Encoding.Parser

end

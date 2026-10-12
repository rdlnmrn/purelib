module
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Shear.Integral.Dual
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Vector.IntCast
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.LinearAlgebra.Alternating.UnitPivot

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra.Vector

section
@[expose] public section

/-!
# Exact evaluation of an integral normal form

The dual coordinate changes retain the original bilinear value. The final
normal form evaluates to an explicit finite list of handle determinants.
-/

namespace Purelib.LinearAlgebra.Alternating.Reduction

variable {K : Type*} [CommRing K] {n : Nat}

section Reduction

/-- Apply each inverse-transpose shear in reduction order.

The retained integral shear coefficients act on vectors over the supplied commutative ring. -/
def dualForward : {matrix :
  SquareMatrix.IntegralMatrix n} → {raw : List (Handle.Basic.PivotIndices n)} →
    Reduction matrix raw → Data.Vector K n → Data.Vector K n
  | _, _, .nil _, values => values
  | _, _, .cons step tail, values => tail.dualForward (step.change.dual values)

/-- Apply the transpose shears in reverse reduction order.

The retained integral shear coefficients act on vectors over the supplied commutative ring. -/
def dualBackward : {matrix :
  SquareMatrix.IntegralMatrix n} → {raw : List (Handle.Basic.PivotIndices n)} →
    Reduction matrix raw → Data.Vector K n → Data.Vector K n
  | _, _, .nil _, values => values
  | _, _, .cons step tail, values => step.change.transpose (tail.dualBackward values)

variable {matrix : SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}

/-- The backward dual change undoes the forward dual change. -/
theorem dualBackward_dualForward (reduction :
  Reduction matrix raw) (values : Data.Vector K n) :
    reduction.dualBackward (reduction.dualForward values) = values := by
  induction reduction generalizing values with
  | nil => rfl
  | cons step tail ih =>
      change step.change.transpose (tail.dualBackward (tail.dualForward (step.change.dual values))) = values
      rw [ih, step.change.transpose_dual]

/-- The forward dual change undoes the backward dual change. -/
theorem dualForward_dualBackward (reduction :
  Reduction matrix raw) (values : Data.Vector K n) :
    reduction.dualForward (reduction.dualBackward values) = values := by
  induction reduction generalizing values with
  | nil => rfl
  | cons step tail ih =>
      change tail.dualForward (step.change.dual (step.change.transpose (tail.dualBackward values))) = values
      rw [step.change.dual_transpose, ih]

/-- The retained dual coordinate changes preserve the original bilinear value through the reduction. -/
theorem pairing_dual (reduction :
  Reduction matrix raw) (left right : Data.Vector K n) :
    Bilinear.Integral.pairing matrix left right = Bilinear.Integral.pairing reduction.output (reduction.dualForward
      left) (reduction.dualForward right) := by
  induction reduction generalizing left right with
  | nil => rfl
  | cons step tail ih =>
      calc
        _ = Bilinear.Integral.pairing step.output (step.change.dual left) (step.change.dual right) := by
          rw [step.output_eq]
          exact step.change.pairing_dual _ left right
        _ = _ := ih _ _

end Reduction
end Purelib.LinearAlgebra.Alternating.Reduction

end

section
@[expose] public section

/-!
# Integer weights of the actual transformed cycle rows

The inverse of the dual coordinate map is the transpose of the ordinary
basis change. Applying it to coordinate unit vectors therefore constructs
integer rows for linear combinations of cycles. Pairing those rows with the
original values evaluates the corresponding row of the final handle form.
-/

namespace Purelib.LinearAlgebra.Alternating.Reduction

variable {K : Type*} [CommRing K] {n : Nat}

/-- Casting integral coordinates commutes with the retained backward dual change. -/
theorem cast_dualBackward {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (reduction : Reduction matrix raw) (values : Data.Vector Int n) :
    IntCast.castVector (K := K) (reduction.dualBackward values) = reduction.dualBackward (IntCast.castVector values) :=
      by
  induction reduction generalizing values with
  | nil => rfl
  | cons step tail ih =>
      change IntCast.castVector (step.change.transpose (tail.dualBackward values)) =
        step.change.transpose (tail.dualBackward (IntCast.castVector values))
      rw [step.change.cast_transpose, ih]
end Purelib.LinearAlgebra.Alternating.Reduction

end

section
@[expose] public section

/-!
# Constructive integral row spanning from a retained unit normal form

Only the finitely many unused-coordinate kernel tests are required.
Transform the requested row, solve each disjoint unit handle, and apply
the retained transpose changes backwards. All coefficients are integers;
there is no field division, search, quotient, or choice of a preimage.
-/

namespace Purelib.LinearAlgebra.Alternating.Reduction

variable {n : Nat}

/-- Move a backward dual change from integral values to a forward change of their weights. -/
theorem weighted_dualBackward {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (reduction : Reduction matrix raw) (weights values : Data.Vector Int n) :
    Weighted.weighted weights (reduction.dualBackward values) = Weighted.weighted (reduction.forward weights) values :=
      by
  induction reduction generalizing weights with
  | nil => rfl
  | cons step tail ih =>
      change Weighted.weighted weights (step.change.transpose (tail.dualBackward values)) = _
      rw [step.change.weighted_transpose, ih]
      rfl

/-- Simultaneous forward changes of weights and dual values preserve their weighted sum. -/
theorem weighted_dualForward {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (reduction : Reduction matrix raw) (weights values : Data.Vector Int n) :
    Weighted.weighted (reduction.forward weights) (reduction.dualForward values) = Weighted.weighted weights values :=
      by
  rw [← reduction.weighted_dualBackward, reduction.dualBackward_dualForward]
end Purelib.LinearAlgebra.Alternating.Reduction

end

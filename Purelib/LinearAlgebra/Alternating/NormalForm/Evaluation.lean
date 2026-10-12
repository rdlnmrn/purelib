module
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Reconstruction
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Pairing
public import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Vector.IntCast
import Purelib.LinearAlgebra.Vector.Unit
import Mathlib.Algebra.Ring.Defs
public import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.LinearAlgebra.Alternating.Reduction.Dual

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

namespace Purelib.LinearAlgebra.Alternating.NormalForm

variable {K : Type*} [CommRing K] {n : Nat}

/-- Evaluate the original integral form through the retained dual reduction and handle pairing.

Both vectors undergo the same cached dual coordinate change over the supplied commutative ring. -/
theorem pairing {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)} (normal : NormalForm
  matrix raw)
    (left right : Data.Vector K n) :
    Bilinear.Integral.pairing matrix left right = Handle.Pairing.handlePairing raw (normal.reduction.dualForward left)
      (normal.reduction.dualForward right) := open Purelib.LinearAlgebra in by
  rw [normal.reduction.pairing_dual]
  unfold Bilinear.Integral.pairing
  have entries (row column : Fin n) : (normal.reduction.output row column : K) = (Handle.Basic.handleEntry raw row
    column : K) := by
    rw [normal.entries]
  rw [Bilinear.Matrix.Basic.bilinear_congr entries, Handle.Pairing.handleEntry_pairing]

end Purelib.LinearAlgebra.Alternating.NormalForm

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

namespace Purelib.LinearAlgebra.Alternating.NormalForm

variable {K : Type*} [CommRing K] {n : Nat}

/-- A retained integral cycle row evaluates as its handle unit against the dual-transformed vector. -/
theorem cycleRow_pairing {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (normal : NormalForm matrix raw) (row : Fin n) (values : Data.Vector K n) :
    Bilinear.Integral.pairing matrix (IntCast.castVector (normal.reduction.cycleRows row)) values =
      Handle.Pairing.handlePairing raw (Unit.unitVector row) (normal.reduction.dualForward values) := by
  rw [normal.reduction.cycleRows_apply, normal.reduction.cast_dualBackward, Unit.cast_unitVector,
    normal.pairing, normal.reduction.dualForward_dualBackward]
end Purelib.LinearAlgebra.Alternating.NormalForm

end

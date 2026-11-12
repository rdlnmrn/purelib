module

public import Purelib.LinearAlgebra.Matrix.NormalForm.Attempt
public import Purelib.Algebra.Field.ExplicitField

/-!
# Automatic rectangular reduction over an explicit field

The same finite unit-pivot attempt engine receives the singleton containing
the actual selected coefficient's computed inverse. Its retained failed-test
alternative is impossible, so every field input returns its cached normal form.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.NormalForm

open Purelib.Algebra.Field
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [ExplicitField K]

/-- A field inverse candidate cannot exhaust the retained nonzero pivot stage. -/
private theorem field_exhaustion_impossible {rows columns : Nat}
    {matrix : Rectangular K (rows + 1) (columns + 1)}
    (selection : Pivot.Selection matrix)
    (receipt : Purelib.Algebra.Ring.Unit.Exhausted (Blocks.head selection.pivoted)
      [(Blocks.head selection.pivoted)⁻¹]) : False :=
  receipt.all_failed _ (List.Mem.head [])
    (ExplicitField.mul_inv_cancel _ selection.head_nonzero)

/-- Every retained field reduction history has a complete normal-form readback. -/
theorem Reduction.field_readback_complete : {rows columns : Nat} →
    {matrix : Rectangular K rows columns} →
    (history : Reduction (fun value => [value⁻¹]) matrix) → history.normal? ≠ none
  | _, _, _, .zero _ _ => by intro impossible; dsimp only [Reduction.normal?] at impossible; cases impossible
  | _, _, _, .exhausted _ selection receipt => (field_exhaustion_impossible selection receipt).elim
  | _, _, _, .pivot _ selection _ step _ following => by
      intro impossible
      dsimp only [Reduction.normal?] at impossible
      cases reading : following.normal? with
      | none => exact Reduction.field_readback_complete following reading
      | some normal => rw [reading] at impossible; cases impossible

variable [DecidableEq K]

/-- Compute both inverse coordinate changes and the actual diagonal reduction of any rectangle.

The shared finite attempt engine uses the same original row-ordered pivot
scan and one checked computed inverse per selected nonzero coefficient. Every
stage retains its exact original rectangle and Schur residual; the complete
cached normal form is returned without reconstructing the reduction history.
No rank, basis or search-success premise is supplied by the caller.
-/
@[expose] def compute {rows columns : Nat} (matrix : Rectangular K rows columns) : NormalForm matrix :=
  match attemptWith (fun value => [value⁻¹]) matrix with
  | .complete normal _ _ => normal
  | .incomplete history agreement => (Reduction.field_readback_complete history agreement).elim

end Purelib.LinearAlgebra.Matrix.NormalForm

end

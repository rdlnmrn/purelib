module

public import Purelib.LinearAlgebra.Matrix.NormalForm.Reduction
public import Purelib.LinearAlgebra.Matrix.Pivot.Selection
public import Purelib.Algebra.Ring.Unit
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained finite unit-pivot attempts

The original row-ordered pivot scan selects a nonzero coefficient. A finite
ordered inverse-candidate scan either supplies its checked unit or retains
its failed products. Every successful step retains the actual Schur residual;
a complete attempt also caches its normal form, linked to the same history.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.NormalForm

open Purelib.Algebra.Ring
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] {rows columns : Nat}

/-- Read back one original retained pivot selection without materializing its table again. -/
@[expose] def ofSelection {matrix : Rectangular K (rows + 1) (columns + 1)}
    (selection : Pivot.Selection matrix) (normal : NormalForm selection.pivoted) : NormalForm matrix :=
  ofPivot selection.entry.row selection.entry.column (ofEq selection.pivoted_eq normal)

set_option genInjectivity false in
/-- A finite reduction history retains each actual rectangle, candidate test and Schur step.

A zero stage certifies the original current table zero. Exhaustion identifies
one selected coefficient and exactly its failed finite candidate list, leaving
the current residual unresolved. A successful step retains that same selection,
its accepted inverse receipt and the actual smaller residual history.
-/
inductive Reduction (candidates : K → List K) :
    {rows columns : Nat} → Rectangular K rows columns → Type _ where
  /-- Retain the actual current rectangle with pointwise complete vanishing. -/
  | zero {rows columns : Nat} (matrix : Rectangular K rows columns) (vanishing : ∀ row column, matrix row column = 0) :
      Reduction candidates matrix
  /-- Retain the actual unresolved rectangle and all failed tests at its selected coefficient. -/
  | exhausted {rows columns : Nat} (matrix : Rectangular K (rows + 1) (columns + 1))
      (selection : Pivot.Selection matrix)
      (receipt : Unit.Exhausted (Blocks.head selection.pivoted)
        (candidates (Blocks.head selection.pivoted))) : Reduction candidates matrix
  /-- Retain one accepted unit pivot, its actual Schur residual and its following history. -/
  | pivot {rows columns : Nat} (matrix : Rectangular K (rows + 1) (columns + 1))
      (selection : Pivot.Selection matrix)
      (receipt : Unit.Found (Blocks.head selection.pivoted)
        (candidates (Blocks.head selection.pivoted)))
      (step : Schur.UnitReduction selection.pivoted)
      (inverse_eq : step.leadingInverse = receipt.inverse)
      (following : Reduction candidates step.residual) : Reduction candidates matrix

constructive_injectivity Reduction

namespace Reduction

/-- Reconstruct a normal form from retained successful steps, or report the retained unresolved stage.

This readback uses the original cached steps. The execution API separately
retains its already-produced normal form and proves agreement with this view;
consumers do not need to replay this reconstruction to obtain that result.
-/
@[expose] def normal? {candidates : K → List K} :
    {rows columns : Nat} → {matrix : Rectangular K rows columns} →
      Reduction candidates matrix → Option (NormalForm matrix)
  | _, _, _, .zero matrix vanishing => some (ofZero matrix vanishing)
  | _, _, _, .exhausted _ _ _ => none
  | _, _, _, .pivot _ selection _ step _ following =>
      match following.normal? with
      | none => none
      | some normal => some (ofSelection selection (ofUnitReduction step normal))

/-- Count the actual successful original unit-pivot reductions in a retained history. -/
@[expose] def pivotCount {candidates : K → List K} :
    {rows columns : Nat} → {matrix : Rectangular K rows columns} → Reduction candidates matrix → Nat
  | _, _, _, .zero _ _ => 0
  | _, _, _, .exhausted _ _ _ => 0
  | _, _, _, .pivot _ _ _ _ _ following => following.pivotCount + 1

/-- Count the actual cached scalar candidate products, including a final exhausted stage. -/
@[expose] def testCount {candidates : K → List K} :
    {rows columns : Nat} → {matrix : Rectangular K rows columns} → Reduction candidates matrix → Nat
  | _, _, _, .zero _ _ => 0
  | _, _, _, .exhausted _ _ receipt => receipt.count
  | _, _, _, .pivot _ _ receipt _ _ following => receipt.count + following.testCount

end Reduction

set_option genInjectivity false in
/-- A finite unit-pivot attempt returns a cached certified normal form or its unresolved history.

The complete case links the retained result to the same original reduction
steps. The incomplete case retains a terminal failed finite candidate scan and
all prior successful reductions, with no nonunit or global impossibility claim.
-/
inductive Attempt (candidates : K → List K) (matrix : Rectangular K rows columns) where
  /-- Retain the computed normal form and its original complete reduction history. -/
  | complete (normal : NormalForm matrix) (history : Reduction candidates matrix)
      (agreement : history.normal? = some normal)
  /-- Retain the actual unresolved stage and every preceding successful reduction. -/
  | incomplete (history : Reduction candidates matrix) (agreement : history.normal? = none)

constructive_injectivity Attempt

namespace Attempt

/-- Project the original retained history from either finite attempt outcome. -/
@[expose] def history {candidates : K → List K} {matrix : Rectangular K rows columns} :
    Attempt candidates matrix → Reduction candidates matrix
  | .complete _ history _ => history
  | .incomplete history _ => history

/-- Project the already-produced normal form without reconstructing its retained history. -/
@[expose] def normal? {candidates : K → List K} {matrix : Rectangular K rows columns} :
    Attempt candidates matrix → Option (NormalForm matrix)
  | .complete normal _ _ => some normal
  | .incomplete _ _ => none

/-- The cached result agrees with readback through the same original retained reductions. -/
theorem normal?_eq {candidates : K → List K} {matrix : Rectangular K rows columns}
    (result : Attempt candidates matrix) : result.normal? = result.history.normal? := by
  cases result with
  | complete normal history agreement => exact agreement.symm
  | incomplete history agreement => exact agreement.symm

end Attempt

variable [DecidableEq K]

/-- Attempt rectangular reduction using the original pivot scan and finite coefficient requests.

Each stage materializes its selected original rectangle once, caches every
actual candidate product once, and performs one original Schur reduction only
when a tested inverse succeeds. Recursion removes one original row and column.
Both complete and unresolved outcomes retain the ordered actual execution.
-/
@[expose] def attemptWith (candidates : K → List K) : {rows columns : Nat} →
    (matrix : Rectangular K rows columns) → Attempt candidates matrix
  | 0, _, matrix => .complete (ofZero matrix (fun row => Fin.elim0 row))
      (.zero matrix (fun row => Fin.elim0 row)) rfl
  | _ + 1, 0, matrix => .complete (ofZero matrix (fun _ column => Fin.elim0 column))
      (.zero matrix (fun _ column => Fin.elim0 column)) rfl
  | rows + 1, columns + 1, matrix =>
      match Pivot.scan (fun row column => matrix row column) with
      | .zero zero => .complete (ofZero matrix zero) (.zero matrix zero) rfl
      | .found row column nonzero =>
          let selection := Pivot.Selection.build matrix ⟨row, column, nonzero⟩
          match Unit.scan (Blocks.head selection.pivoted) (candidates (Blocks.head selection.pivoted)) with
          | .exhausted receipt => .incomplete (.exhausted matrix selection receipt) rfl
          | .found receipt =>
              let step := Schur.UnitReduction.build selection.pivoted receipt.inverse receipt.unit
              match attemptWith candidates step.residual with
              | .complete normal following agreement =>
                  .complete (ofSelection selection (ofUnitReduction step normal))
                    (.pivot matrix selection receipt step rfl following) (by
                      change (match following.normal? with
                        | none => none
                        | some normal => some (ofSelection selection (ofUnitReduction step normal))) = _
                      rw [agreement])
              | .incomplete following agreement =>
                  .incomplete (.pivot matrix selection receipt step rfl following) (by
                    change (match following.normal? with
                      | none => none
                      | some normal => some (ofSelection selection (ofUnitReduction step normal))) = none
                    rw [agreement])
termination_by structural rows _ _ => rows

/-- Attempt rectangular reduction with the same explicit finite inverse-candidate pool at every stage.

Failure identifies the actual selected coefficient, residual rectangle and
ordered failed products. It leaves other candidates and other possible pivot
choices unresolved, rather than claiming that no normal form exists.
-/
@[expose] def attempt (matrix : Rectangular K rows columns) (candidates : List K) :
    Attempt (fun _ => candidates) matrix := attemptWith (fun _ => candidates) matrix

end Purelib.LinearAlgebra.Matrix.NormalForm

end

module

public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Data.Gaussian.Norm.Components.Maximum
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field

/-! # Rational variation of original finite polynomial-cell paths

The fold reads only each retained cell displacement in its original order.
Append and indexed-flatten readbacks retain every occurrence; no polynomial,
integral sample or cached observation is reconstructed.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
open Purelib.Data.Gaussian
open Purelib.Data.List.OfFn.Basic (ofFn_succ)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

/-- Fold the maximum-coordinate variation of the same original ordered physical cell displacements. -/
def variation (path : PathModel) : Rational :=
  path.cells.foldr (fun cell total => Norm.Components.maximum cell.displacement + total) 0

/-- Appending two original cell lists adds their retained rational variations. -/
theorem variation_append (first last : List CellModel) :
    (PathModel.mk (first ++ last)).variation =
      (PathModel.mk first).variation + (PathModel.mk last).variation := by
  induction first with
  | nil => exact (Data.Rat.Fraction.Field.zero_add _).symm
  | cons head tail ih =>
      change Norm.Components.maximum head.displacement + (PathModel.mk (tail ++ last)).variation =
        (Norm.Components.maximum head.displacement + (PathModel.mk tail).variation) + (PathModel.mk last).variation
      exact (congrArg (fun value : Rational => Norm.Components.maximum head.displacement + value) ih).trans
        (Data.Rat.Fraction.Field.add_assoc _ _ _).symm

/-- An indexed view reads the same original cells' variation in its exact bounded occurrence order. -/
theorem variation_ofFn {count : Nat} (cells : Fin count → CellModel) :
    (PathModel.mk (List.ofFn cells)).variation =
      sumFin (fun index => Norm.Components.maximum (cells index).displacement) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rewrite [ofFn_succ, sumFin_succ]
      change Norm.Components.maximum (cells 0).displacement +
        (PathModel.mk (List.ofFn (fun index => cells index.succ))).variation = _
      exact congrArg (fun value : Rational => Norm.Components.maximum (cells 0).displacement + value)
        (ih (fun index => cells index.succ))

/-- The same ordered flattened block lists retain the sum of their original physical variations. -/
theorem variation_flatten_ofFn {count : Nat} (blocks : Fin count → List CellModel) :
    (PathModel.mk (List.ofFn blocks).flatten).variation =
      sumFin (fun index => (PathModel.mk (blocks index)).variation) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rewrite [ofFn_succ, sumFin_succ]
      change (PathModel.mk (blocks 0 ++ (List.ofFn (fun index => blocks index.succ)).flatten)).variation = _
      exact (variation_append _ _).trans
        (congrArg (fun value : Rational => (PathModel.mk (blocks 0)).variation + value)
          (ih (fun index => blocks index.succ)))

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

end

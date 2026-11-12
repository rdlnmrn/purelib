module

public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic

/-!
# Indexed readback of the original finite Gaussian path integral sample

The retained list order and each actual cell integral sample agree with the
original finite-index sum. This is an exact arithmetic readback of an existing
finite path model, not an identification with a geometric integral.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib.Algebra
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

universe u

/-- The original integral sample of a mapped cell list is the finite sum of those identical bounded entries. -/
theorem integralSample_map_eq_sumFin {Alpha : Type u} (entries : List Alpha) (cell : Alpha → CellModel) :
    (PathModel.mk (entries.map cell)).integralSample =
      FiniteSum.Fin.sumFin (fun index : Fin entries.length =>
        (cell (entries[index.val]'index.isLt)).integralSample) := by
  induction entries with
  | nil => rfl
  | cons first remaining inductionHypothesis =>
      rewrite [FiniteSum.Fin.sumFin_succ]
      change (cell first).integralSample + (PathModel.mk (remaining.map cell)).integralSample =
        (cell first).integralSample +
          FiniteSum.Fin.sumFin
            (fun index : Fin remaining.length => (cell (remaining[index.val]'index.isLt)).integralSample)
      exact congrArg (fun value : Canonical => (cell first).integralSample + value) inductionHypothesis

/-- The retained original cell list's actual integral sample is the same ordered finite-index sum. -/
theorem integralSample_eq_sumFin (path : PathModel) :
    path.integralSample =
      FiniteSum.Fin.sumFin (fun index : Fin path.cells.length =>
        (path.cells[index.val]'index.isLt).integralSample) := by
  cases path with
  | mk cells =>
      induction cells with
      | nil => rfl
      | cons first remaining inductionHypothesis =>
          rewrite [FiniteSum.Fin.sumFin_succ]
          change first.integralSample + (PathModel.mk remaining).integralSample =
            first.integralSample +
              FiniteSum.Fin.sumFin
                (fun index : Fin remaining.length => (remaining[index.val]'index.isLt).integralSample)
          exact congrArg (fun value : Canonical => first.integralSample + value) inductionHypothesis

/-- An indexed view of actual stored cells has the integral sum of those SAME original cell samples. -/
theorem integralSample_ofFn_eq_sumFin {count : Nat} (cells : Fin count → CellModel) :
    (PathModel.mk (List.ofFn cells)).integralSample =
      FiniteSum.Fin.sumFin (fun index => (cells index).integralSample) := by
  induction count with
  | zero => rfl
  | succ count previous =>
      rewrite [Data.List.OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      change (cells 0).integralSample + (PathModel.mk (List.ofFn (fun index => cells index.succ))).integralSample = _
      exact congrArg (fun value : Canonical => (cells 0).integralSample + value)
        (previous (fun index => cells index.succ))

/-- The SAME ordered flattened child-cell lists retain the finite sum of their original block integral samples. -/
theorem integralSample_flatten_ofFn {count : Nat} (blocks : Fin count → List CellModel) :
    (PathModel.mk (List.ofFn blocks).flatten).integralSample =
      FiniteSum.Fin.sumFin (fun index => (PathModel.mk (blocks index)).integralSample) := by
  induction count with
  | zero => rfl
  | succ count previous =>
      rewrite [Data.List.OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      change (PathModel.mk (blocks 0 ++ (List.ofFn (fun index => blocks index.succ)).flatten)).integralSample = _
      rewrite [integralSample_mk_append, previous (fun index => blocks index.succ)]
      rfl

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

end

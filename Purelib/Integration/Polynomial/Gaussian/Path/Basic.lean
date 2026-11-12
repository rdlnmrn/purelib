module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Fold
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Integration.Polynomial.Gaussian.Cell in
set_option genInjectivity false in
/-- An ordered finite list of original Gaussian polynomial integration cells.

The carrier retains each cell's endpoints, polynomial, allowance and observations without imposing a separate
endpoint-joining condition. -/
structure PathModel where
  /-- The retained ordered original Gaussian polynomial cells. -/ cells : List Basic.CellModel

constructive_injectivity PathModel

namespace PathModel

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
/-- Sum the original cell integral samples in retained list order. -/
def integralSample (path :
  PathModel) : Basic.Canonical :=
  path.cells.foldr (fun cell total => cell.integralSample + total) 0

open Purelib.Data.Gaussian in
/-- The original ordered path integral is the Gaussian list sum of those SAME retained cell integral samples. -/
theorem integralSample_eq_gaussianSum (path : PathModel) :
    path.integralSample = Norm.Sum.Basic.gaussianSum
      (path.cells.map (fun cell => cell.integralSample)) := by
  cases path with
  | mk cells =>
    induction cells with
    | nil => rfl
    | cons head remaining inductionHypothesis =>
      change head.integralSample + (PathModel.mk remaining).integralSample =
        head.integralSample + Norm.Sum.Basic.gaussianSum
          (remaining.map (fun cell => cell.integralSample))
      exact congrArg (head.integralSample + ·) inductionHypothesis

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- A singleton Gaussian path has its original cell's exact integral sample. -/
@[simp] theorem singleton_integralSample (cell :
  Basic.CellModel) :
    (mk [cell]).integralSample = cell.integralSample := by
  unfold integralSample
  simp only [List.foldr_cons, List.foldr_nil]
  exact Basic.add_zero _

open Purelib.Integration.Polynomial in
/-- Concatenate the exact two original ordered cell lists. -/
def concat (first second :
  PathModel) : PathModel :=
  ⟨first.cells ++ second.cells⟩

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Polynomial in
/-- Concatenating Gaussian paths adds their original integral samples. -/
theorem integralSample_concat (first second :
  PathModel) :
    (first.concat second).integralSample =
      first.integralSample + second.integralSample := by
  unfold concat integralSample
  rw [Fold.foldr_append]
  induction first.cells with
  | nil => exact (Basic.zero_add _).symm
  | cons cell remaining inductionHypothesis =>
      simp only [List.foldr_cons]
      rw [inductionHypothesis]
      exact (Basic.add_assoc _ _ _).symm

open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The path built from appended cell lists has the sum of the two original path samples. -/
@[simp] theorem integralSample_mk_append
    (first second : List Basic.CellModel) :
    (mk (first ++ second)).integralSample =
      (mk first).integralSample +
        (mk second).integralSample := by
  exact integralSample_concat (mk first)
    (mk second)

/-- Move the retained head cell to the end, preserving every original ordered cell occurrence. -/
def rotateHead (path : PathModel) : PathModel :=
  match path.cells with
  | [] => path
  | first :: remaining => ⟨remaining ++ [first]⟩

/-- A cyclic head rotation preserves the exact sum of the original finite cell samples. -/
theorem integralSample_rotateHead (path : PathModel) : path.rotateHead.integralSample = path.integralSample := by
  cases path with
  | mk cells =>
    cases cells with
    | nil => rfl
    | cons first remaining =>
      change (mk (remaining ++ [first])).integralSample = first.integralSample + (mk remaining).integralSample
      rewrite [integralSample_mk_append, singleton_integralSample]
      exact Canonical.add_comm _ _
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end

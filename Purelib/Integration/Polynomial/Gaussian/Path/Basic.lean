module

import Purelib.Data.Gaussian.Basic
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

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
/-- Sum the original cell integral samples in retained list order. -/
def integralSample (path :
  Gaussian.Path.Basic.PathModel) : Basic.Canonical :=
  path.cells.foldr (fun cell total => cell.integralSample + total) 0

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- A singleton Gaussian path has its original cell's exact integral sample. -/
@[simp] theorem singleton_integralSample (cell :
  Basic.CellModel) :
    (Gaussian.Path.Basic.PathModel.mk [cell]).integralSample = cell.integralSample := by
  unfold Gaussian.Path.Basic.PathModel.integralSample
  simp only [List.foldr_cons, List.foldr_nil]
  exact Basic.add_zero _

open Purelib.Integration.Polynomial in
/-- Concatenate the exact two original ordered cell lists. -/
def concat (first second :
  Gaussian.Path.Basic.PathModel) : Gaussian.Path.Basic.PathModel :=
  ⟨first.cells ++ second.cells⟩

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Polynomial in
/-- Concatenating Gaussian paths adds their original integral samples. -/
theorem integralSample_concat (first second :
  Gaussian.Path.Basic.PathModel) :
    (first.concat second).integralSample =
      first.integralSample + second.integralSample := by
  unfold Gaussian.Path.Basic.PathModel.concat Gaussian.Path.Basic.PathModel.integralSample
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
    (Gaussian.Path.Basic.PathModel.mk (first ++ second)).integralSample =
      (Gaussian.Path.Basic.PathModel.mk first).integralSample +
        (Gaussian.Path.Basic.PathModel.mk second).integralSample := by
  exact Gaussian.Path.Basic.PathModel.integralSample_concat (Gaussian.Path.Basic.PathModel.mk first)
    (Gaussian.Path.Basic.PathModel.mk second)
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end

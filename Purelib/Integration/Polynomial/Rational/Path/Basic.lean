module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Fold
public import Purelib.Integration.Polynomial.Rational.Cell.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Path.Basic

open Purelib.Integration.Polynomial in
set_option genInjectivity false in
/-- An ordered finite list of rational polynomial integration cells.

The list retains its original orientations and observations; this record alone imposes no endpoint-joining condition. -/
structure PathModel where
  /-- The retained ordered polynomial cell occurrences. -/ cells : List Rational.Cell.Basic.CellModel

constructive_injectivity PathModel

namespace PathModel

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial
/-- Sum the original cell integral samples in retained list order. -/
def integralSample (path :
  Rational.Path.Basic.PathModel) : Basic.Canonical :=
  path.cells.foldr (fun cell total => cell.integralSample + total) 0

/-- A singleton path's integral sample is its original cell sample. -/
@[simp] theorem singleton_integralSample (cell :
  Rational.Cell.Basic.CellModel) :
    (Rational.Path.Basic.PathModel.mk [cell]).integralSample = cell.integralSample := by
  unfold Rational.Path.Basic.PathModel.integralSample
  simp only [List.foldr_cons, List.foldr_nil]
  exact Basic.add_zero _

end

open Purelib.Integration.Polynomial in
/-- Concatenate the exact two ordered cell lists into one path model. -/
def concat (first second :
  Rational.Path.Basic.PathModel) : Rational.Path.Basic.PathModel :=
  ⟨first.cells ++ second.cells⟩

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Polynomial in
/-- Concatenating paths adds their original integral samples. -/
theorem integralSample_concat (first second :
  Rational.Path.Basic.PathModel) :
    (first.concat second).integralSample =
      first.integralSample + second.integralSample := by
  unfold Rational.Path.Basic.PathModel.concat Rational.Path.Basic.PathModel.integralSample
  rw [Fold.foldr_append]
  induction first.cells with
  | nil => exact (Basic.zero_add _).symm
  | cons cell remaining induction =>
      simp only [List.foldr_cons]
      rw [induction]
      exact (Basic.add_assoc _ _ _).symm
end PathModel

end Purelib.Integration.Polynomial.Rational.Path.Basic

end

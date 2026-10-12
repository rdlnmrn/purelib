module

import Purelib.Integration.Polynomial.Rational.Cell.Basic
public import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Polynomial.Ascending.Rational.Antiderivative
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.Integral
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Integration.Polynomial.Rational.Cell.Basic (CellModel)

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

namespace Purelib.Integration.Polynomial.Rational.Antiderivative

/-! ## Supplied finite antiderivatives -/

open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A primitive certificate for the exact retained polynomial integration cell.

Its derivative equals the original cell polynomial, and its endpoint difference multiplied by the same displacement
equals the retained integral sample. -/
structure CellAntiderivative (cell :
  CellModel) where
  /-- The retained rational coefficient primitive polynomial. -/ primitive : Rational.Basic.CoefficientPolynomial
  /-- The primitive derivative equals the exact original cell polynomial. -/ derivative_eq :
    Rational.Derivative.derivative primitive = cell.polynomial
  /-- The original displacement times primitive endpoint difference equals that cell's integral sample. -/ endpoint_eq :
    cell.displacement *
        (Rational.GaussianEvaluation.eval primitive 1 -
          Rational.GaussianEvaluation.eval primitive 0) =
      cell.integralSample

constructive_injectivity CellAntiderivative

namespace CellAntiderivative

open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Construct the original cell's primitive with zero integration constant and exact endpoint identity. -/
def canonical (cell :
  CellModel) : Rational.Antiderivative.CellAntiderivative cell :=
  { primitive := Rational.Antiderivative.antiderivative 0
      cell.polynomial
    derivative_eq :=
      Rational.Antiderivative.derivative_antiderivative 0
        cell.polynomial
    endpoint_eq := by
      unfold CellModel.integralSample
        Rational.Integral.definiteIntegral
      rfl }

end CellAntiderivative

open Purelib.Integration.Polynomial in
set_option genInjectivity false in
/-- An ordered list of cells paired dependently with their own retained primitive certificates. -/
structure PathAntiderivative where
  /-- The ordered cells paired with primitive certificates indexed by those exact cells. -/ entries : List (Sigma fun
    cell : CellModel => CellAntiderivative cell)

constructive_injectivity PathAntiderivative

namespace PathAntiderivative

open Purelib.Integration.Polynomial in
/-- Read the original cell occurrences from the dependent primitive-certificate list. -/
def path (certificate :
  Rational.Antiderivative.PathAntiderivative) : Rational.Path.Basic.PathModel :=
  ⟨certificate.entries.map Sigma.fst⟩

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Sum each original cell displacement times its own primitive endpoint difference. -/
def differenceSample (certificate :
  Rational.Antiderivative.PathAntiderivative) : Basic.Canonical :=
  certificate.entries.foldr
    (fun entry total =>
      entry.1.displacement *
          (Rational.GaussianEvaluation.eval entry.2.primitive 1 -
            Rational.GaussianEvaluation.eval entry.2.primitive 0) +
        total)
    0

open Purelib.Integration.Polynomial in
/-- The retained primitive-difference sum equals the exact readback path's integral sample. -/
theorem
  differenceSample_eq_integralSample
    (certificate : Rational.Antiderivative.PathAntiderivative) :
    certificate.differenceSample = certificate.path.integralSample := by
  unfold Rational.Antiderivative.PathAntiderivative.differenceSample Rational.Antiderivative.PathAntiderivative.path
    Rational.Path.Basic.PathModel.integralSample
  induction certificate.entries with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [List.foldr_cons, List.map_cons]
      rw [entry.2.endpoint_eq, induction]

end PathAntiderivative

end Purelib.Integration.Polynomial.Rational.Antiderivative

end

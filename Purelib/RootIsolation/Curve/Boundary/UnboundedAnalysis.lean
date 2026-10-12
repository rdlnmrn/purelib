module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Boundary.Description
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Decision
public import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic

section

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Total analysis of a described CCL boundary

Parameterized boundaries are sent directly to the cleared-gcd/Sturm event
classifier.  Finite zero sets are evaluated pointwise, and a universal form
is retained explicitly.  This is the finite dispatch layer between formula
provenance and equality ownership.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Unbounded

set_option genInjectivity false in
/-- Total finite analysis corresponding to each kind of boundary
description. -/
inductive Outcome (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    {reference : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {form :
      Geometry.Projective.Hermitian.HermitianForm} :
    Geometry.Projective.Hermitian.Boundary.BoundaryDescription reference form → Type where
  /-- Retain the primary chart's finite root-event analysis and a corresponding analysis for every companion chart. -/ |
    curve
      (source : Geometry.Projective.Hermitian.Chart.CurveSource reference form)
      (analysis : Curve.Event.Analysis p
        source.primary.curve)
      (companionAnalysis : ∀ companion,
        companion ∈ source.companions →
          Curve.Event.Analysis p companion.curve) :
      Purelib.RootIsolation.Curve.Boundary.Unbounded.Outcome p (.curve source)
  /-- Retain the complete finite boundary point list and its exact computed polynomial evaluations. -/ | finite (points
    : List Gaussian.Basic.Canonical)
      (complete : ∀ value, form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ form.eval value)
      (evaluations : List (Dense.Gaussian.Evaluation.EvaluatedPoint p))
      (evaluations_eq : evaluations = Dense.Gaussian.Evaluation.evaluatePoints p points) :
      Purelib.RootIsolation.Curve.Boundary.Unbounded.Outcome p (.finite points complete nonnegative)
  /-- Retain the proof that the original boundary form vanishes at every displayed point. -/ | universal (zero : ∀
    value, form.eval value = 0) :
      Purelib.RootIsolation.Curve.Boundary.Unbounded.Outcome p (.universal zero)

constructive_injectivity Outcome

set_option genInjectivity false in
/-- A boundary description paired with its executed analysis. -/
structure AnalyzedBoundary
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (form : Geometry.Projective.Hermitian.HermitianForm) where
  /-- The original boundary description, indexed by its reference matrix and Hermitian form. -/ description :
    Geometry.Projective.Hermitian.Boundary.BoundaryDescription reference form
  /-- The executed finite analysis of this exact retained boundary description. -/ outcome :
    Curve.Boundary.Unbounded.Outcome p description

constructive_injectivity AnalyzedBoundary

/-- Execute the complete finite analysis. -/
def analyze
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    (description : Geometry.Projective.Hermitian.Boundary.BoundaryDescription reference form) :
    Curve.Boundary.Unbounded.AnalyzedBoundary p reference form := by
  cases description with
  | curve source =>
      exact ⟨.curve source,
        .curve source
          (Curve.Event.analyze p source.primary.curve)
          (fun companion _member =>
            Curve.Event.analyze p companion.curve)⟩
  | finite points complete nonnegative =>
      exact ⟨.finite points complete nonnegative,
        .finite points complete nonnegative (Dense.Gaussian.Evaluation.evaluatePoints p points) rfl⟩
  | universal zero =>
      exact ⟨.universal zero, .universal zero⟩

end Purelib.RootIsolation.Curve.Boundary.Unbounded

end

end

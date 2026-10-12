module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Boundary.Description
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Decision
public import Purelib.RootIsolation.Curve.Chart.Analysis

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Geometry.Projective.Hermitian.Boundary (BoundaryDescription)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.RootIsolation.Curve.Boundary

set_option genInjectivity false in
/-- Finite bounded analysis corresponding to every kind of boundary
description.  Curve cases retain the executed chart list; finite and
universal zero sets retain their exact pointwise analysis. -/
inductive Outcome
    (p : CoefficientPolynomial) (box : Box) (denominatorMargin :
      Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    {reference : GaussianMatrix} {form :
      HermitianForm} :
    BoundaryDescription reference form → Type
  /-- The original parameterized boundary with its actual bounded chart analyses and construction equality. -/ | curve
    (source : Geometry.Projective.Hermitian.Chart.CurveSource reference form)
      (analyses : List
        (Sigma fun chart : Geometry.Projective.Hermitian.Chart.BoundedChart form => Curve.Chart.BoundedAnalysis p box
          chart))
      (analyses_eq : analyses =
        Curve.Chart.analyzeCharts p source box denominatorMargin marginPositive) :
      Outcome p box denominatorMargin marginPositive (.curve source)
  /-- The complete original finite zero set with its retained polynomial evaluations and nonnegative-form certificate.
  -/
  | finite (points : List Gaussian.Basic.Canonical)
      (complete : ∀ value, form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ form.eval value)
      (evaluations : List
        (Dense.Gaussian.Evaluation.EvaluatedPoint p))
      (evaluations_eq : evaluations =
        Dense.Gaussian.Evaluation.evaluatePoints p points) :
      Outcome p box denominatorMargin marginPositive
        (.finite points complete nonnegative)
  /-- The original boundary form vanishes at every displayed point. -/ | universal (zero : ∀ value, form.eval value = 0)
    :
      Outcome p box denominatorMargin marginPositive (.universal zero)

constructive_injectivity Outcome

set_option genInjectivity false in
/-- A boundary description paired with the finite analyses of precisely the
bounded charts relevant to the current box. -/
structure AnalyzedBoundary
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix) (form :
      HermitianForm)
    (box : Box) (denominatorMargin : Fraction.Rational) where
  /-- The retained denominator margin is strictly positive. -/ marginPositive : 0 < denominatorMargin
  /-- The original reference-indexed boundary description. -/ description :
    BoundaryDescription reference form
  /-- The finite analysis outcome for that exact retained boundary description. -/ outcome : Outcome p
    box denominatorMargin marginPositive description

constructive_injectivity AnalyzedBoundary

/-- Generate and execute all bounded analyses for one described boundary. -/
@[expose] def analyze
    (p : CoefficientPolynomial) (box : Box)
    (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    {reference : GaussianMatrix} {form :
      HermitianForm}
    (description :
      BoundaryDescription reference form) :
    AnalyzedBoundary p reference form box denominatorMargin := by
  cases description with
  | curve source =>
      exact
        { marginPositive := marginPositive
          description := .curve source
          outcome := .curve source
            (Curve.Chart.analyzeCharts p source box denominatorMargin marginPositive) rfl }
  | finite points complete nonnegative =>
      exact
        { marginPositive := marginPositive
          description := .finite points complete nonnegative
          outcome := .finite points complete nonnegative
            (Dense.Gaussian.Evaluation.evaluatePoints p points) rfl }
  | universal zero =>
      exact
        { marginPositive := marginPositive
          description := .universal zero
          outcome := .universal zero }

end Purelib.RootIsolation.Curve.Boundary

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Analysis

set_option genInjectivity false in
/-- A genuinely parameterized boundary is the only unresolved result that
may leave the finite-boundary loop.  Universal boundaries are equality-owned
by structural inspection, while finite zero sets are exhausted by winding
point exclusion. -/
structure CurveBoundary
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix)
    (current : Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (atom : Geometry.Projective.Hermitian.Atom) where
  /-- The original parameterized source of the retained atom's boundary form. -/ source :
    Geometry.Projective.Hermitian.Chart.CurveSource
    reference atom.form
  /-- The actual bounded-chart analyses for the original current box. -/ analyses : List (Sigma fun chart :
    Geometry.Projective.Hermitian.Chart.BoundedChart atom.form =>
      Curve.Chart.BoundedAnalysis p current chart)
  /-- The retained analyses equal the original bounded chart-analysis construction. -/ analyses_eq : analyses =
    Curve.Chart.analyzeCharts p source current
      denominatorMargin marginPositive

constructive_injectivity CurveBoundary

end Purelib.RootIsolation.Curve.Boundary.Analysis

end

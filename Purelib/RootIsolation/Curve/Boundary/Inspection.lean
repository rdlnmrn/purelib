module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Boundary.Description
import Purelib.Geometry.Projective.Hermitian.Box.Sign
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
public import Purelib.Geometry.Projective.Hermitian.Formula.Description
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Decision
public import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Rational.Box.Refinement

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.Geometry.Projective.Hermitian.Boundary (BoundaryDescription)
open Purelib.Geometry.Projective.Hermitian.Formula (BoundaryFormula)
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
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace Purelib.RootIsolation.Curve.Boundary

/-! ## Structural owner inspection -/

set_option genInjectivity false in
/-- A non-universal boundary that still requires polynomial/curve handling.
Universal zero forms are converted directly into equality-owned atom
stability and therefore never appear here. -/
inductive RemainingBoundary
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix) (current : Box)
    (denominatorMargin : Fraction.Rational) (marginPositive : 0 < denominatorMargin) :
    Atom → Type where
  /-- An unresolved parameterized atom boundary with its exact retained bounded chart analyses. -/ | curve (atom :
    Atom)
      (source : Geometry.Projective.Hermitian.Chart.CurveSource
        reference atom.form)
      (analyses : List (Sigma fun chart :
        Geometry.Projective.Hermitian.Chart.BoundedChart atom.form =>
          Curve.Chart.BoundedAnalysis p current chart))
      (analyses_eq : analyses =
        Curve.Chart.analyzeCharts p source current
          denominatorMargin marginPositive) :
      RemainingBoundary p reference current denominatorMargin marginPositive
        atom
  /-- An unresolved finite atom zero set with its complete membership and original polynomial evaluations. -/ | finite
    (atom : Atom) (points : List Canonical)
      (complete : ∀ value, atom.form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ atom.form.eval value)
      (evaluations : List
        (Dense.Gaussian.Evaluation.EvaluatedPoint p))
      (evaluations_eq : evaluations =
        Dense.Gaussian.Evaluation.evaluatePoints p points) :
      RemainingBoundary p reference current denominatorMargin marginPositive
        atom

constructive_injectivity RemainingBoundary

set_option genInjectivity false in
/-- Formula inspection that immediately applies exact equality ownership to
every universal atom it encounters. -/
inductive OwnerInspection
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix)
    (bounding current : Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (refines : current.Refines bounding)
    (sample : Canonical) (sampleInside : current.Contains sample)
    (formOverrides : List
      (Geometry.Projective.Hermitian.Formula.Box.FormOverride current)) :
    BoundaryFormula → Type where
  /-- The original formula has a retained stability certificate on the current box. -/ | stable {formula :
    BoundaryFormula} (result : Geometry.Projective.Hermitian.Formula.Box.Stable
    bounding current formula) :
      OwnerInspection p reference bounding current denominatorMargin
        marginPositive refines sample sampleInside formOverrides formula
  /-- The first unresolved original atom retains its formula membership, failed stability checks and complete finite or
    curve analysis. -/ | boundary {formula : BoundaryFormula} (atom :
    Atom)
      (member : atom ∈ formula.atoms)
      (notResolved : Geometry.Projective.Hermitian.Formula.Box.findFormOverride
        formOverrides atom.form = none)
      (failure : Geometry.Projective.Hermitian.Box.certificate?
        atom.form bounding current refines sample sampleInside = none)
      (remaining : RemainingBoundary p reference current denominatorMargin
        marginPositive atom) :
      OwnerInspection p reference bounding current denominatorMargin
        marginPositive refines sample sampleInside formOverrides formula

constructive_injectivity OwnerInspection

/-- Traverse one finite formula.  Strictly stable atoms use their ordinary
margin certificates; identically-zero atoms use the parser's equality
convention; the first finite or curve boundary is returned with its complete
bounded analysis. -/
@[expose] def inspectOwnerWith
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix)
    (bounding current : Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (overrides : List
      (Geometry.Projective.Hermitian.Formula.Box.Override bounding current))
    (formOverrides : List
      (Geometry.Projective.Hermitian.Formula.Box.FormOverride current))
    (formula : BoundaryFormula)
    (description : ∀ atom, atom ∈ formula.atoms →
      BoundaryDescription reference atom.form)
    (refines : current.Refines bounding)
    (sample : Canonical) (sampleInside : current.Contains sample) :
    OwnerInspection p reference bounding current denominatorMargin
      marginPositive refines sample sampleInside formOverrides formula := by
  match formula with
  | .truth => exact .stable .truth
  | .falsity => exact .stable .falsity
  | .atom value =>
      have member : value ∈ (BoundaryFormula.atom value).atoms := by
        exact List.Mem.head []
      match found : Geometry.Projective.Hermitian.Formula.Box.findFormOverride
          formOverrides value.form with
      | some formStability =>
          exact .stable (.atom value formStability.toAtom)
      | none =>
          match Geometry.Projective.Hermitian.Formula.Box.findOverride overrides
              value with
          | some stability => exact .stable (.atom value stability)
          | none =>
              match failure : Geometry.Projective.Hermitian.Box.certificate?
                  value.form bounding current refines sample sampleInside with
              | some certificate =>
                  exact .stable (.atom value (.strict certificate))
              | none =>
                  match description value member with
                  | .curve source =>
                      exact .boundary value member found failure
                        (.curve value source
                        (Curve.Chart.analyzeCharts p
                          source current denominatorMargin marginPositive) rfl)
                  | .finite points complete nonnegative =>
                      exact .boundary value member found failure
                        (.finite value points complete nonnegative
                          (Dense.Gaussian.Evaluation.evaluatePoints p
                            points) rfl)
                  | .universal zero =>
                      exact .stable (.atom value (.zero fun point _inside =>
                        zero point))
  | .and left right =>
      let leftDescription : ∀ atom, atom ∈ left.atoms →
          BoundaryDescription reference atom.form := fun atom member =>
        description atom (by
          exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member))
      match inspectOwnerWith p reference bounding current denominatorMargin
          marginPositive overrides formOverrides left leftDescription refines
          sample sampleInside with
      | .boundary atom member notResolved failure remaining =>
          exact .boundary atom (by
            exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)) notResolved failure remaining
      | .stable leftStable =>
          let rightDescription : ∀ atom, atom ∈ right.atoms →
              BoundaryDescription reference atom.form := fun atom member =>
            description atom (by
              exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member))
          match inspectOwnerWith p reference bounding current
              denominatorMargin marginPositive overrides formOverrides right
              rightDescription refines sample
              sampleInside with
          | .boundary atom member notResolved failure remaining =>
              exact .boundary atom (by
                exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)) notResolved failure remaining
          | .stable rightStable =>
              exact .stable (.and leftStable rightStable)
  | .or left right =>
      let leftDescription : ∀ atom, atom ∈ left.atoms →
          BoundaryDescription reference atom.form := fun atom member =>
        description atom (by
          exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member))
      match inspectOwnerWith p reference bounding current denominatorMargin
          marginPositive overrides formOverrides left leftDescription refines
          sample sampleInside with
      | .boundary atom member notResolved failure remaining =>
          exact .boundary atom (by
            exact Purelib.Data.List.Membership.mem_append.mpr (Or.inl member)) notResolved failure remaining
      | .stable leftStable =>
          let rightDescription : ∀ atom, atom ∈ right.atoms →
              BoundaryDescription reference atom.form := fun atom member =>
            description atom (by
              exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member))
          match inspectOwnerWith p reference bounding current
              denominatorMargin marginPositive overrides formOverrides right
              rightDescription refines sample
              sampleInside with
          | .boundary atom member notResolved failure remaining =>
              exact .boundary atom (by
                exact Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)) notResolved failure remaining
          | .stable rightStable =>
              exact .stable (.or leftStable rightStable)

/-- Initial owner inspection with no previously resolved boundaries. -/
@[expose] def inspectOwner
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix)
    (bounding current : Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (formula : BoundaryFormula)
    (description : ∀ atom, atom ∈ formula.atoms →
      BoundaryDescription reference atom.form)
    (refines : current.Refines bounding)
    (sample : Canonical) (sampleInside : current.Contains sample) :
    OwnerInspection p reference bounding current denominatorMargin
      marginPositive refines sample sampleInside [] formula :=
  inspectOwnerWith p reference bounding current denominatorMargin
    marginPositive [] [] formula description refines sample sampleInside

/-- Public entry point using the atom descriptions generated alongside a
parser formula. -/
@[expose] def inspectDescriptions
    (p : CoefficientPolynomial) (reference :
      GaussianMatrix)
    (bounding current : Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (formula : BoundaryFormula)
    (descriptions : Geometry.Projective.Hermitian.Formula.Descriptions
      reference formula)
    (refines : current.Refines bounding)
    (sample : Canonical) (sampleInside : current.Contains sample) :
    OwnerInspection p reference bounding current denominatorMargin
      marginPositive refines sample sampleInside [] formula :=
  inspectOwner p reference bounding current denominatorMargin marginPositive
    formula (fun atom member => descriptions.boundaryFor atom member)
    refines sample sampleInside
end Purelib.RootIsolation.Curve.Boundary

end

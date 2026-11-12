module

import Purelib.Polynomial.Approximation.Gaussian.Residual
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial

public import Purelib.RootIsolation.Multiplicity.Side.CCL.Name
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Admission

/-! # Algebraic admission at the original dependent multiplicity-side indices -/

public section

namespace Purelib.RootIsolation.Multiplicity.Side.CCL

open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open CoherentRoot (CertifiedName)
open Purelib.RootIsolation.Multiplicity.Side.Basic (SideResult)
open Purelib.RootIsolation.Multiplicity.Side.CCL.Basic (SideCCL)
open Purelib.RootIsolation.Multiplicity.Side.Index (SideIndex)

open Purelib.RootIsolation.Multiplicity.Observation.CCL renaming Admission -> ObservationAdmission
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

/-- The original indexed observation admission on a positive side; constant sides have no site indices. -/
@[expose] def Admission {source opposite : CoefficientPolynomial} : (side : SideResult source opposite) →
    (data : SideCCL side) → SideIndex side → Type 1
  | .constant _ _ _, _, index => nomatch index
  | .positive _ family, data, index =>
      ObservationAdmission (family.observationAt index.1) (data index.1) index.2

namespace Admission

/-- Original observation state entries at the same dependent side index.

The positive branch is the exact original observation-cache view. A constant
side has no site indices and therefore needs no cache interpretation.
-/
@[expose] def StateCache {source opposite : CoefficientPolynomial} : (side : SideResult source opposite) →
    (data : SideCCL side) → (index : SideIndex side) → Type
  | .constant _ _ _, _, index => nomatch index
  | .positive _ family, data, index =>
      ObservationAdmission.StateCache (family.observationAt index.1) (data index.1) index.2

/-- Admit the exact original side observation, attachment and site index without rebuilding its isolation. -/
@[expose] def ofSide {source opposite : CoefficientPolynomial} : (side : SideResult source opposite) →
    (data : SideCCL side) → (index : SideIndex side) →
    (cached : Option (StateCache side data index) := none) → Admission side data index
  | .constant _ _ _, _, index, _ => nomatch index
  | .positive _ family, data, index, cached =>
      ObservationAdmission.ofObservation (family.observationAt index.1) (data index.1) index.2 cached

/-- Supplied original state entries preserve the complete same-index side admission. -/
theorem ofSide_cached_eq_default {source opposite : CoefficientPolynomial}
    (side : SideResult source opposite) (data : SideCCL side) (index : SideIndex side)
    (cached : Option (StateCache side data index)) :
    ofSide side data index cached = ofSide side data index none := by
  cases side with
  | constant => exact nomatch index
  | positive _ family =>
      exact ObservationAdmission.ofObservation_cached_eq_default
        (family.observationAt index.1) (data index.1) index.2 cached

/-- An absent state cache retains the complete original side-admission operation. -/
theorem ofSide_none {source opposite : CoefficientPolynomial}
    (side : SideResult source opposite) (data : SideCCL side) (index : SideIndex side) :
    ofSide side data index none = ofSide side data index := rfl

/-- Read the retained original observation's coherent channel at its original dependent side index. -/
@[expose] def channel {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index) : CoherentNamed := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.channel admission

/-- The admitted channel agrees with the same original productive side-site name. -/
def equivalent {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index) :
    Equivalence.NamedEquivalent (Name.sideArithmeticName side data index) (channel admission).name := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.equivalent admission

/-- Lift the original side's retained admission through an ordered source-cofactor identity. -/
def sourceEquation {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index)
    (target multiplier : CoefficientPolynomial)
    (identity : ∀ point, target.eval point = multiplier.eval point * source.eval point) :
    Equivalence.NamedEquivalent (Horner.polynomialEval target (channel admission)).name
      (CoherentNamed.Coherence.exact 0).name := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.sourceEquation admission target multiplier identity

/-- Read the same original side observation's quantitative numerical polynomial residual certificate. -/
def numericalResidual {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index) :
    Σ polynomial : CoefficientPolynomial, PolynomialResidual polynomial (channel admission) := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.numericalResidual admission

/-- Decide exact zero or a prepared presentation using the same retained original side-site admission. -/
def decide {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index) :
    Division.Prepared.Decision (channel admission) := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.decide admission

/-- Project the actual original higher-site root through this same dependent side admission.

The retained observation and bounded index remain unchanged. A constant side
has no site index; an exact observation keeps its separate scalar evidence.
-/
@[expose] def view? {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index) :
    Option (CertifiedName.View (channel admission)) := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.view? admission

/-- Read exact scalar provenance from the same retained original side-site admission. -/
@[expose] def scalar? {source opposite : CoefficientPolynomial} {side : SideResult source opposite}
    {data : SideCCL side} {index : SideIndex side} (admission : Admission side data index) :
    Option (Provenance.Rational.Basic.RationalSidecar (channel admission)) := by
  cases side with
  | constant => exact nomatch index
  | positive _ _ => exact ObservationAdmission.scalar? admission

end Admission

end Purelib.RootIsolation.Multiplicity.Side.CCL

end

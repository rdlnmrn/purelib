module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Boundary
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Phase.Resolution
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Winding on the complete rational unit circle

The raw reading is the original primary-chart doubled Cauchy index minus the
reciprocal-chart index. The original finite phase-resolution engine computes
both integer corrections. Exact agreement at both joins cancels their endpoint
phases and proves divisibility by four, independently of root isolation.
-/

namespace Purelib.Polynomial.Winding.Circle

open Purelib.Data
open Purelib.RationalFunctions.Curve
open Canonical.Circle (circle reciprocalCircle)
open Canonical.Circle.Boundary (Substitutions Clearance parameters)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Rational.CauchyIndex
open Dense.Gaussian
open Rat.Fraction (Rational)

/-- The oriented whole-circle raw reading of the two actual cleared chart pairs. -/
@[expose] public def raw {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial) : Int :=
  Basic.Sturm.cauchyIndex2 paths.primary.real paths.primary.imaginary (-1) 1 -
    Basic.Sturm.cauchyIndex2 paths.reciprocal.real paths.reciprocal.imaginary (-1) 1

/-- Exact polynomial transport preserves the same retained independent raw reading. -/
public theorem raw_transport {source target : CoefficientPolynomial} (equal : source = target)
    (paths : Substitutions source) :
    raw (show Substitutions target from equal ▸ paths) = raw paths := by
  cases equal
  rfl

/-- The endpoint phases of the retained chart pairs agree at both circle joins. -/
public theorem endpoint_phase_eq {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial)
    (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
    Phase.Basic.endpointQuarterPhase paths.primary.real paths.primary.imaginary parameter =
      Phase.Basic.endpointQuarterPhase paths.reciprocal.real paths.reciprocal.imaginary parameter := by
  unfold Phase.Basic.endpointQuarterPhase
  rw [paths.endpoint_real_eq parameter endpoint, paths.endpoint_imaginary_eq parameter endpoint]

set_option genInjectivity false in
/-- A retained independent winding computation on a cleared whole-circle boundary.

Both phase formulas are produced by the original sufficient finite resolution
procedure. The ordinary integer is their difference, and its raw equality is
proved by exact endpoint cancellation rather than by a root count. -/
public structure Reading {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial)
    (clearance : Clearance paths) where
  /-- The actual primary-chart phase formula. -/ primary :
    Phase.Basic.PhaseFormula paths.primary.real paths.primary.imaginary (-1) 1
  /-- The primary formula is the original automatic phase construction. -/ primary_eq : primary =
    Phase.Resolution.phaseFormulaOfClearance clearance.primary (by decide)
  /-- The actual reciprocal-chart phase formula in ascending parameter order. -/ reciprocal :
    Phase.Basic.PhaseFormula paths.reciprocal.real paths.reciprocal.imaginary (-1) 1
  /-- The reciprocal formula is the original automatic phase construction. -/ reciprocal_eq : reciprocal =
    Phase.Resolution.phaseFormulaOfClearance clearance.reciprocal (by decide)
  /-- The retained integer winding in the positive circle orientation. -/ winding : Int
  /-- The winding is exactly the difference of the retained phase corrections. -/ winding_eq :
    winding = primary.turns - reciprocal.turns
  /-- The oriented raw index is exactly four times this winding. -/ raw_eq : raw paths = 4 * winding

constructive_injectivity Reading

namespace Reading

/-- Resolve both original chart-event computations and retain their normalized circle winding.

Every subdivision bound is computed internally by the existing phase engine
from the supplied whole-boundary clearance; no root data or search fuel enters. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial)
    (clearance : Clearance paths) : Reading paths clearance :=
  let primary := Phase.Resolution.phaseFormulaOfClearance clearance.primary (by decide)
  let reciprocal := Phase.Resolution.phaseFormulaOfClearance clearance.reciprocal (by decide)
  { primary, primary_eq := rfl, reciprocal, reciprocal_eq := rfl
    winding := primary.turns - reciprocal.turns, winding_eq := rfl
    raw_eq := by
      unfold raw
      exact primary.closedDifference reciprocal
        (endpoint_phase_eq paths (-1) (Or.inl rfl)) (endpoint_phase_eq paths 1 (Or.inr rfl)) }

end Reading
end Purelib.Polynomial.Winding.Circle

module

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners
import Purelib.Examples.Curves.Legendre.Prepared.RealMinusOne
import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Data.Rat.Fraction.Cast

namespace TestPurelib.Curves.Hyperelliptic.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Examples.Curves.Legendre.Prepared
open Purelib.Riemann.Periods
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)

/-- The exact nonzero affine coordinate used by both degree shapes. -/
private def affine : Canonical := 2

/-- The same inverse coordinate, represented by its exact rational components. -/
private def inverse : Canonical := ⟨Cast.fromInt 1 / Cast.fromInt 2, 0⟩

/-- The genus-one standard differential has exponent zero. -/
private def differential : Differential 1 := ⟨0⟩

/-- The inverse coordinate is obtained from the original affine coordinate. -/
private theorem affine_inverse : affine⁻¹ = inverse := by decide +kernel

/-- Both original winding sheets are retained at the odd-degree curve's nonzero affine radicand. -/
private def oddOwner (sheet : Fin 2) : Owner (RealMinusOne.curve.polynomial.eval affine) :=
  Owner.independent (by change (⟨6, 0⟩ : Canonical) ≠ 0; decide +kernel) sheet

/-- Both original winding sheets are retained at the even-degree curve's nonzero affine radicand. -/
private def evenOwner (sheet : Fin 2) : Owner (PeriodCurves.quarticCurve.polynomial.eval affine) :=
  Owner.independent (by change (⟨15, 0⟩ : Canonical) ≠ 0; decide +kernel) sheet

/-- The odd-degree reciprocal root is scaled from its original affine occurrence. -/
private def oddRoot (sheet : Fin 2) :=
  ReciprocalRootNames.ofOwner RealMinusOne.curve affine (by decide +kernel) (oddOwner sheet)

/-- The even-degree reciprocal root is scaled from its original affine occurrence. -/
private def evenRoot (sheet : Fin 2) :=
  ReciprocalRootNames.ofOwner PeriodCurves.quarticCurve affine (by decide +kernel) (evenOwner sheet)

/-- The odd-degree coefficient retains the original inverse-coordinate denominator guard. -/
private def oddCoefficient (sheet : Fin 2) :=
  ReciprocalRootNames.ScaledRoot.Coefficients.build (oddRoot sheet) differential (by decide +kernel)

/-- The even-degree coefficient retains the original inverse-coordinate denominator guard. -/
private def evenCoefficient (sheet : Fin 2) :=
  ReciprocalRootNames.ScaledRoot.Coefficients.build (evenRoot sheet) differential (by decide +kernel)

/-- The odd-degree pullback check is derived from the actual constructor for either original sheet. -/
private theorem odd_checked (sheet : Fin 2) :
    (oddCoefficient sheet).pullback.Equal (oddCoefficient sheet).scaling.target.source :=
  (oddCoefficient sheet).equal

/-- The even-degree pullback check is derived from the actual constructor for either original sheet. -/
private theorem even_checked (sheet : Fin 2) :
    (evenCoefficient sheet).pullback.Equal (evenCoefficient sheet).scaling.target.source :=
  (evenCoefficient sheet).equal

/-- Odd-degree attachment transports the same cached pair to the actual winding owner. -/
private def oddOwned (sheet : Fin 2) :=
  ReciprocalRootOwners.Coefficient.build (oddCoefficient sheet) (ReciprocalRootOwners.attach (oddRoot sheet))

/-- Even-degree attachment transports the same cached pair to the actual winding owner. -/
private def evenOwned (sheet : Fin 2) :=
  ReciprocalRootOwners.Coefficient.build (evenCoefficient sheet) (ReciprocalRootOwners.attach (evenRoot sheet))

/-- The actual odd-degree construction derives the Jacobian law on either original sheet. -/
private def odd_transport (sheet : Fin 2) :=
  ReciprocalRootOwners.coefficient_transport differential affine (by decide +kernel) (oddOwned sheet)

/-- The actual even-degree construction derives the Jacobian law on either original sheet. -/
private def even_transport (sheet : Fin 2) :=
  ReciprocalRootOwners.coefficient_transport differential affine (by decide +kernel) (evenOwned sheet)

/-- The odd-degree guarded pullback reads the exact coefficient minus eight thirds for either original sheet. -/
private theorem odd_coefficient_readback (sheet : Fin 2) :
    (oddCoefficient sheet).denotation.value.im = (⟨Cast.fromInt (-8) / Cast.fromInt 3, 0⟩ : Canonical) := by
  have readback := congrArg (fun value => value.im) (oddCoefficient sheet).denotation.value_eq
  have evaluated : ((oddCoefficient sheet).pullback.evaluate affine⁻¹).im =
      (⟨Cast.fromInt (-8) / Cast.fromInt 3, 0⟩ : Canonical) := by
    rewrite [(oddCoefficient sheet).pullback_eq, affine_inverse]
    decide +kernel
  exact readback.trans evaluated

/-- The even-degree guarded pullback reads the exact coefficient minus sixteen fifteenths for either original sheet. -/
private theorem even_coefficient_readback (sheet : Fin 2) :
    (evenCoefficient sheet).denotation.value.im = (⟨Cast.fromInt (-16) / Cast.fromInt 15, 0⟩ : Canonical) := by
  have readback := congrArg (fun value => value.im) (evenCoefficient sheet).denotation.value_eq
  have evaluated : ((evenCoefficient sheet).pullback.evaluate affine⁻¹).im =
      (⟨Cast.fromInt (-16) / Cast.fromInt 15, 0⟩ : Canonical) := by
    rewrite [(evenCoefficient sheet).pullback_eq, affine_inverse]
    decide +kernel
  exact readback.trans evaluated

/-- Odd-degree reversal retains the zero affine constant term and the ramified chart origin. -/
private theorem odd_origin :
    RealMinusOne.curve.polynomial.eval 0 = 0 ∧
    HyperellipticReciprocal.originOrder RealMinusOne.curve = 1 ∧
    (HyperellipticReciprocal.polynomial RealMinusOne.curve).eval 0 = 0 := by decide +kernel

/-- The even-degree reciprocal radicand is regular at the chart origin. -/
private theorem even_origin :
    HyperellipticReciprocal.originOrder PeriodCurves.quarticCurve = 0 ∧
    (HyperellipticReciprocal.polynomial PeriodCurves.quarticCurve).eval 0 = 1 := by decide +kernel

/-- At the even-degree origin the reduced expression is admitted while the original affine pullback guard fails. -/
private theorem even_origin_domain :
    (HyperellipticReciprocal.coefficientExpression
      (HyperellipticReciprocal.polynomial PeriodCurves.quarticCurve) differential).Defined 0 ∧
    ¬ (HyperellipticReciprocal.pullbackExpression
      (HyperellipticReciprocal.polynomial PeriodCurves.quarticCurve) differential).Defined 0 := by decide +kernel

/-- A deliberately inexact affine root candidate retains its nonzero residual under reciprocal transport. -/
private theorem odd_inexact_residual :
    HyperellipticReciprocal.rootCoordinate 1 inverse 1 ^ 2 -
      (HyperellipticReciprocal.polynomial RealMinusOne.curve).eval inverse =
      inverse ^ 4 * (1 ^ 2 - RealMinusOne.curve.polynomial.eval inverse⁻¹) :=
  HyperellipticReciprocal.residual_identity RealMinusOne.curve inverse 1 (by decide +kernel)

/-- The deliberately inexact odd-degree candidate is not silently treated as an exact root. -/
private theorem odd_inexact_nonzero :
    HyperellipticReciprocal.rootCoordinate 1 inverse 1 ^ 2 -
      (HyperellipticReciprocal.polynomial RealMinusOne.curve).eval inverse ≠ 0 := by decide +kernel

end TestPurelib.Curves.Hyperelliptic.Reciprocal

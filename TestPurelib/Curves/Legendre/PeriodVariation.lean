module

import Purelib.Curves.Legendre.Periods.Jets.Variation
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Evaluation

/-! # Residual-aware finite Legendre parameter variation

The target sheet reading is deliberately inexact. Both original value rows
use that same displayed reading, and the residual budget pays its nonzero
curve-equation error while preserving the symbolic first derivative rows.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation

open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Polynomial

/-- The displayed parameter increment used by both differential rows. -/
private def increment : Gaussian.Basic.Canonical := ⟨1 / 8, 0⟩

/-- The actual inexact target sheet reading shared by both rows. -/
private def last : Gaussian.Basic.Canonical := ⟨3 / 4, 0⟩

/-- Construct the selected original row with its paid target-sheet square residual. -/
private def certificate (coordinate : Fin 2) : Quadratic.Basic.Certificate increment :=
  Variation.valueCertificate coordinate ⟨3 / 2, 0⟩ increment 2 1 last 0 144
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The deliberately inexact target reading has the paid nonzero square residual. -/
theorem target_residual : Norm.Basic.normSq
    (last * last - Polynomials.curveValue (⟨3 / 2, 0⟩ + increment) 2) = 9 / 256 := by
  change Norm.Basic.normSq
    ((⟨3 / 4, 0⟩ : Gaussian.Basic.Canonical) * ⟨3 / 4, 0⟩ -
      Polynomials.curveValue (⟨3 / 2, 0⟩ + ⟨1 / 8, 0⟩) 2) = 9 / 256
  decide +kernel

/-- The original unweighted first derivative row reads one at the retained initial sheet. -/
theorem first_slope : (certificate 0).slope = 1 := by
  unfold certificate
  rewrite [Variation.valueCertificate_slope]
  rewrite [Variation.firstReading_specification (⟨3 / 2, 0⟩ : Gaussian.Basic.Canonical)]
  rewrite [Specification.firstDerivativeSpecification_zero]
  dsimp only [OddPowerDifferential.ofCoefficients]
  rewrite [Polynomials.basePolynomial_eval]
  change (⟨1 / 2, 0⟩ : Gaussian.Basic.Canonical) * (2 * (2 - 1)) * (1 : Gaussian.Basic.Canonical)⁻¹ ^ 3 = 1
  decide +kernel

/-- The weighted derivative row retains the original spatial coordinate factor two. -/
theorem second_slope : (certificate 1).slope = 2 := by
  unfold certificate
  rewrite [Variation.valueCertificate_slope]
  rewrite [Variation.firstReading_specification (⟨3 / 2, 0⟩ : Gaussian.Basic.Canonical)]
  rewrite [Specification.firstDerivativeSpecification_one]
  dsimp only [OddPowerDifferential.ofCoefficients]
  rewrite [Polynomials.weightedBasePolynomial_eval]
  change (⟨1 / 2, 0⟩ : Gaussian.Basic.Canonical) * (2 * (2 * (2 - 1))) * (1 : Gaussian.Basic.Canonical)⁻¹ ^ 3 = 2
  decide +kernel

/-- The output retains the reciprocal of the actual inexact last sheet reading. -/
theorem first_output : (certificate 0).output = ⟨4 / 3, 0⟩ := by
  unfold certificate
  rewrite [Variation.valueCertificate_output]
  rewrite [Variation.valueReading_specification (⟨3 / 2, 0⟩ : Gaussian.Basic.Canonical)]
  rewrite [Specification.valueSpecification_zero]
  dsimp only [OddPowerDifferential.ofCoefficients]
  rewrite [Dense.Gaussian.Evaluation.constantOnePolynomial_eval]
  change (1 : Gaussian.Basic.Canonical) * 1 * (⟨3 / 4, 0⟩ : Gaussian.Basic.Canonical)⁻¹ = ⟨4 / 3, 0⟩
  decide +kernel

/-- Both rows' actual first-order residuals satisfy their constructed finite quadratic bounds. -/
theorem rows_remainder_le (coordinate : Fin 2) :
    Gaussian.Basic.Canonical.normSq
      ((certificate coordinate).output - (certificate coordinate).base -
        increment * (certificate coordinate).slope) ≤
      (certificate coordinate).factor * Gaussian.Basic.Canonical.normSq increment ^ 2 := by
  rewrite [(certificate coordinate).expansion]
  exact (certificate coordinate).remainder_le

/-- Construct the original first derivative row with the same paid finite sheet readings. -/
private def derivativeCertificate (coordinate : Fin 2) : Quadratic.Basic.Certificate increment :=
  Variation.firstCertificate coordinate ⟨3 / 2, 0⟩ increment 2 1 last 0 144
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The unweighted first derivative variation has the original second derivative coefficient three. -/
theorem first_second_slope : (derivativeCertificate 0).slope = 3 := by
  unfold derivativeCertificate
  rewrite [Variation.firstCertificate_slope]
  rewrite [Variation.secondReading_specification (⟨3 / 2, 0⟩ : Gaussian.Basic.Canonical)]
  rewrite [Specification.secondDerivativeSpecification_zero]
  dsimp only [OddPowerDifferential.ofCoefficients]
  rewrite [Polynomials.squaredBasePolynomial_eval]
  change (⟨3 / 4, 0⟩ : Gaussian.Basic.Canonical) * (2 * (2 - 1)) ^ 2 *
    (1 : Gaussian.Basic.Canonical)⁻¹ ^ 5 = 3
  decide +kernel

/-- The constructed variation of the weighted first derivative preserves the original spatial factor two. -/
theorem weighted_second_slope : (derivativeCertificate 1).slope = 6 := by
  unfold derivativeCertificate
  rewrite [Variation.firstCertificate_slope]
  rewrite [Variation.secondReading_specification (⟨3 / 2, 0⟩ : Gaussian.Basic.Canonical)]
  rewrite [Specification.secondDerivativeSpecification_one]
  dsimp only [OddPowerDifferential.ofCoefficients]
  rewrite [Polynomials.weightedSquaredBasePolynomial_eval]
  change (⟨3 / 4, 0⟩ : Gaussian.Basic.Canonical) * (2 * (2 * (2 - 1)) ^ 2) *
    (1 : Gaussian.Basic.Canonical)⁻¹ ^ 5 = 6
  decide +kernel

/-- Cubic composition retains the original first derivative row on the actual inexact target reading. -/
theorem first_derivative_output : (derivativeCertificate 0).output = ⟨64 / 27, 0⟩ := by
  unfold derivativeCertificate
  rewrite [Variation.firstCertificate_output]
  rewrite [Variation.firstReading_specification (⟨3 / 2, 0⟩ : Gaussian.Basic.Canonical)]
  rewrite [Specification.firstDerivativeSpecification_zero]
  dsimp only [OddPowerDifferential.ofCoefficients]
  rewrite [Polynomials.basePolynomial_eval]
  change (⟨1 / 2, 0⟩ : Gaussian.Basic.Canonical) * (2 * (2 - 1)) *
    (⟨3 / 4, 0⟩ : Gaussian.Basic.Canonical)⁻¹ ^ 3 = ⟨64 / 27, 0⟩
  decide +kernel

/-- Both first derivative rows satisfy their internally constructed finite quadratic remainder bounds. -/
theorem derivative_rows_remainder_le (coordinate : Fin 2) :
    Gaussian.Basic.Canonical.normSq
      ((derivativeCertificate coordinate).output - (derivativeCertificate coordinate).base -
        increment * (derivativeCertificate coordinate).slope) ≤
      (derivativeCertificate coordinate).factor * Gaussian.Basic.Canonical.normSq increment ^ 2 := by
  rewrite [(derivativeCertificate coordinate).expansion]
  exact (derivativeCertificate coordinate).remainder_le

end TestPurelib.Curves.Legendre.PeriodVariation

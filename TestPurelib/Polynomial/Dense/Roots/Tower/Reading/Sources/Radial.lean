module

import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sources.Radial
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast

/-!
# One original linear source with a paid nonzero radial correction

The fixed request is prepared before either point. Its original leading
coefficient is two, so the actual inverse norm is one quarter. A distinct
nearby candidate pays the retained source schedule and the same radial cap,
while the exact-index radial view preserves that cap without reconstruction.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Tower.Reading.Sources.Radial

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Request Sources)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

/-- The original nonmonic linear source has root one half. -/
private def source : DensePolynomial Canonical := ⟨[2, -1]⟩

/-- The same original companion constructor retains the complete one-stage tower. -/
private def tower : Tower Canonical inferInstance inferInstance source :=
  Tower.prepare source (by decide +kernel) (1 / 2) (by decide +kernel)

/-- The same original parameter chain fixes unit candidate quadrance before observations. -/
private def parameters : Parameters tower Norm.weight 1 1 :=
  Parameters.prepare tower Norm.weight 1 1 (by decide) (by decide)

/-- The final error target has its original direct rational representation. -/
private def target : Rational := Cast.fromInt 1024

/-- The same original budget is computed before observing a candidate. -/
private def budget : Request parameters target := Request.prepare parameters target (by decide +kernel)

/-- The same original nonunit Gaussian coefficient supplies every retained leading invariant. -/
private theorem leading : Tower.Leading tower id 2 :=
  Tower.Leading.ofSource tower id 2 (by decide +kernel) (by decide +kernel) rfl rfl (fun _ _ => rfl)

/-- The original source schedule and radial cap share one inverse, inverse norm and root total. -/
private def fixed : Sources.Radial budget.budget leading 1 (1 / 4) :=
  Sources.Radial.prepare budget.budget leading 1 (1 / 4) (by decide) (by decide)

/-- The nonmonic source gives the expected original cache and sufficient radial cap. -/
private theorem fixed_values : fixed.coefficientInverse = 1 / 2 ∧ fixed.inverseNorm = 1 / 4 ∧
    fixed.rootBound = 1 / 2 ∧ fixed.radial.coefficient = 3 / 4 ∧
      fixed.radial.cap = 1 / Cast.fromInt 224 := by decide +kernel

/-- Source scheduling keeps the same actual cached inverse and norm. -/
private theorem source_caches : fixed.sources.coefficientInverse = fixed.coefficientInverse ∧
    fixed.sources.inverseNorm = fixed.inverseNorm := ⟨fixed.sources_inverse_eq, fixed.sources_norm_eq⟩

/-- The radial cap is the active original source demand and its scheduled initial tolerance. -/
private theorem source_cap_active : fixed.sources.targets = [fixed.radial.cap] ∧
    fixed.sources.schedule.val.initial = fixed.radial.cap := by decide +kernel

/-- The same source schedule retains its positive initial tolerance before either point is selected. -/
private theorem initial_positive : 0 < fixed.sources.schedule.val.initial := fixed.initial_positive

/-- The exact original-index radial view preserves the stored cap. -/
private theorem original_cap : fixed.originalRadial.cap = fixed.radial.cap := fixed.originalRadial_cap

/-- The same retained original caches restore the complete request without repeating any numerical producer. -/
private theorem restore_request :
    Sources.Radial.ofRequests budget.budget leading 1 (1 / 4) fixed.separationPositive fixed.widthPositive
        fixed.coefficientInverse fixed.coefficientInverse_eq fixed.inverseNorm fixed.inverseNorm_eq
        fixed.rootBound fixed.rootBound_eq fixed.radial fixed.radial_eq fixed.sources fixed.sources_eq =
      Sources.Radial.prepare budget.budget leading 1 (1 / 4) fixed.separationPositive fixed.widthPositive :=
  Sources.Radial.ofRequests_eq_prepare budget.budget leading 1 (1 / 4) fixed.separationPositive fixed.widthPositive
    fixed.coefficientInverse fixed.coefficientInverse_eq fixed.inverseNorm fixed.inverseNorm_eq
    fixed.rootBound fixed.rootBound_eq fixed.radial fixed.radial_eq fixed.sources fixed.sources_eq

/-- A rational candidate differs from the original source's exact root. -/
private def candidate : Canonical := ⟨31 / Cast.fromInt 64, 0⟩

/-- The exact linear root is used only as a later endpoint in this scalar correction check. -/
private def readRoot : Canonical := ⟨1 / 2, 0⟩

/-- The later source residual is measured at that same candidate. -/
private def residual : Rational := Norm.Basic.normSq (source.eval candidate)

/-- The same source payment certifies a nonzero displacement through its actual retained inverse norm. -/
private theorem actual_correction : 0 < residual ∧ candidate ≠ readRoot ∧
    Norm.Basic.normSq (candidate - readRoot) = residual * fixed.sources.inverseNorm := by decide +kernel

/-- The later candidate pays the same already prepared original source schedule. -/
private theorem source_paid : residual ≤ fixed.sources.schedule.val.initial := by decide +kernel

/-- The same exact-index radial request transfers the original inside collar through the nonzero correction. -/
private theorem corrected_inside : Norm.Basic.normSq readRoot ≤ fixed.originalRadial.ceiling := by
  have capPaid : residual ≤ fixed.radial.cap := by decide +kernel
  exact fixed.originalRadial.inside candidate readRoot (residual := residual)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    actual_correction.right.right.le (capPaid.trans_eq fixed.originalRadial_cap.symm)

/-- The original radial transfer certifies strict interior quadrance for the changed endpoint. -/
private theorem corrected_strict : Norm.Basic.normSq readRoot < 1 :=
  corrected_inside.trans_lt fixed.originalRadial.ceiling_lt_one

end TestPurelib.Polynomial.Dense.Roots.Tower.Reading.Sources.Radial

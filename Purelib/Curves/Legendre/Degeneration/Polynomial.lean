module

public import Purelib.Curves.Legendre.Degeneration
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Named evaluation of the original centered Legendre cubic

The original high-to-low Horner channel is compared with the centered
quadratic and its remaining affine factor at the same named base. Two
bindings keep the base and parameter as original channel owners. Only closed
Gaussian coefficients enter the finite coefficient normalization.
-/

namespace Purelib.Curves.Legendre.Degeneration

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Field
open Purelib.Polynomial.Quadratic
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence

/-- The original midpoint uses the exact Gaussian half as a scalar factor. -/
private theorem center_mul_half (site : Fin 2) (parameter : Canonical) :
    (criticalValue site + parameter) * (1 / 2 : Canonical) = center site parameter := by
  unfold center Split.center
  rewrite [ExplicitField.div_eq_mul_inv]
  exact congrArg (fun value : Canonical => (criticalValue site + parameter) * value)
    (show (1 / 2 : Canonical) = (2 : Canonical)⁻¹ from by decide +kernel)

/-- The original signed half-gap uses the same exact half without changing either root label. -/
private theorem halfGap_mul_half (site : Fin 2) (parameter : Canonical) :
    (parameter + -(criticalValue site)) * (1 / 2 : Canonical) = halfGap site parameter := by
  unfold halfGap Split.halfGap
  rewrite [ExplicitField.div_eq_mul_inv]
  have scalar : parameter + -(criticalValue site) = parameter - criticalValue site := by ring1
  exact (congrArg (fun value : Canonical => value * (1 / 2 : Canonical)) scalar).trans
    (congrArg (fun value : Canonical => (parameter - criticalValue site) * value)
      (show (1 / 2 : Canonical) = (2 : Canonical)⁻¹ from by decide +kernel))

/-- The actual negative Horner coefficient arithmetic retains its terminating coefficient comparison. -/
private def negativeCoefficient (parameter : Canonical) :
    NamedEquivalent (((Coherence.exact (1 : Canonical)).add (Coherence.exact parameter)).neg).name
      (Coherence.exact (-(1 + parameter))).name :=
  Equivalent.of_constant_samples _ _ (-(1 + parameter)) (fun _ => rfl) (fun _ => rfl)

/-- Original exact midpoint arithmetic compares with the original midpoint coefficient. -/
private def centerCoefficient (site : Fin 2) (parameter : Canonical) :
    NamedEquivalent
      ((((Coherence.exact (criticalValue site)).add (Coherence.exact parameter)).mul
        (Coherence.exact (1 / 2 : Canonical))).name)
      (Coherence.exact (center site parameter)).name :=
  Equivalent.of_constant_samples _ _ (center site parameter)
    (fun _ => by
      change (criticalValue site + parameter) * (1 / 2 : Canonical) = center site parameter
      exact center_mul_half site parameter)
    (fun _ => rfl)

/-- The same exact half-gap product compares with the original smoothing coefficient. -/
private def smoothingCoefficient (site : Fin 2) (parameter : Canonical) :
    NamedEquivalent
      (((((Coherence.exact parameter).add (Coherence.exact (criticalValue site)).neg).mul
        (Coherence.exact (1 / 2 : Canonical))).mul
        (((Coherence.exact parameter).add (Coherence.exact (criticalValue site)).neg).mul
          (Coherence.exact (1 / 2 : Canonical)))).name)
      (Coherence.exact (smoothing site parameter)).name :=
  Equivalent.of_constant_samples _ _ (smoothing site parameter)
    (fun _ => by
      change ((parameter + -(criticalValue site)) * (1 / 2 : Canonical)) *
        ((parameter + -(criticalValue site)) * (1 / 2 : Canonical)) = smoothing site parameter
      have same := congrArg (fun value : Canonical => value * value) (halfGap_mul_half site parameter)
      exact same.trans (show halfGap site parameter * halfGap site parameter = smoothing site parameter by
        unfold smoothing
        ring1))
    (fun _ => rfl)

public section

/-- The original Legendre Horner output agrees with its centered factors at the same named base.

The supplied output and whole factory retain the original Horner evaluation.
Normalization constructs finite arithmetic comparisons without replacing the
base, parameter, or output channel. Both labelled collisions are checked using
closed coefficient forms; no coefficient or root agreement is assumed.
-/
def polynomialEval_centered (site : Fin 2) (parameter : Canonical) (input : CoherentNamed)
    (evaluated : { value : CoherentNamed // value = Horner.polynomialEval (Paths.polynomial parameter) input }) :
    NamedEquivalent evaluated.val.name
      (((((input.add (Coherence.exact (center site parameter)).neg).mul
        (input.add (Coherence.exact (center site parameter)).neg)).add
        (Coherence.exact (smoothing site parameter)).neg).mul
        (input.add (Coherence.exact (-(remainingValue site))))).name) := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases input (fun _ => Coherence.exact parameter)
  let x := Normalized.atom bindings 0
  let parameterName := Normalized.atom bindings 1
  let zero := Normalized.constant bindings 0
  let one := Normalized.constant bindings 1
  let half := Normalized.constant bindings (1 / 2 : Canonical)
  let critical := Normalized.constant bindings (criticalValue site)
  let negative := ((one.add parameterName).neg).precompose (negativeCoefficient parameter).symm
  let midpoint := ((critical.add parameterName).mul half).precompose (centerCoefficient site parameter).symm
  let gap := (parameterName.sub critical).mul half
  let smooth := (gap.mul gap).precompose (smoothingCoefficient site parameter).symm
  let initial := (zero.mul x).add one
  let quadratic := (initial.mul x).add negative
  let linear := (quadratic.mul x).add parameterName
  let left := (linear.mul x).add zero
  let translated := x.sub midpoint
  let right := ((translated.mul translated).sub smooth).mul
    (x.add (Normalized.constant bindings (-(remainingValue site))))
  have forms : left.form.terms = right.form.terms := by
    dsimp only [left, right, translated, linear, quadratic, initial, negative, midpoint, smooth, gap,
      zero, one, half, critical, x, parameterName]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.sub_form, Normalized.neg_form,
      Normalized.precompose_form, Normalized.constant_form, Normalized.atom_form, -eq_self, -iff_self]
    rcases Fin.Two.finTwo_cases site with zeroSite | oneSite
    · subst site
      decide +kernel
    · subst site
      decide +kernel
  let original : Normalized bindings (Horner.polynomialEval (Paths.polynomial parameter) input) := left
  have originalForm : original.form = left.form := rfl
  have transportedForm := Normalized.transport_form original evaluated.property.symm
  have retainedTerms := congrArg (fun form => form.terms) (transportedForm.trans originalForm)
  exact (original.transport evaluated.property.symm).compare right (retainedTerms.trans forms)

end

end Purelib.Curves.Legendre.Degeneration

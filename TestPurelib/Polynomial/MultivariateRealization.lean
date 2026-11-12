module

import Purelib.Polynomial.Multivariate.Gaussian.Realization
import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Rational
import Purelib.Approximation.Gaussian.Provenance.Power

/-!
# Original composite inputs interpreted through their admitted coordinates

An arbitrary original channel carrying coordinates `1+r` is a polynomial
variable, although it need not itself satisfy a pure-power equation. Its
cached cubic polynomial has coordinates `7+5*r` at the same original admitted
generator and parameter. Coefficient readback uses the retained exact view.
-/

namespace TestPurelib.Polynomial.MultivariateRealization

open Purelib.Polynomial.Multivariate
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- The original admitted parameter-minus-two realization at a supplied generator equation. -/
private def realized (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) : Realization Rational :=
  Realization.rational 2 generator identity (Square.inspect 2) (by decide +kernel)

/-- The cached cubic form of the original first polynomial variable. -/
private def cubic : Sparse Canonical 1 := Sparse.pow (Sparse.atom 0) 3

/-- The exact coefficient inspection attached to the original cached cubic term list. -/
private def coefficients := Cast.inspectRealList (Terms.coefficientEntries cubic.terms)

/-- Every actual cubic coefficient lies on the exact real axis. -/
private theorem coefficients_complete : coefficients.Complete := by decide +kernel

/-- Retain an original cubic interpretation and its reflexive cached normalization. -/
private def normalized (channel : CoherentNamed) :
    Gaussian.Normalized (fun _ : Fin 1 => channel) (cubic.denote (fun _ => channel)) :=
  Gaussian.Normalized.ofForm (fun _ => channel) cubic (NamedEquivalent.refl _)

/-- Exact coefficient readback uses the same original finite inspection and admitted coefficient map. -/
private def mapped (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) :
    Terms.Coefficients (realized generator identity) cubic.terms :=
  Terms.coefficientsOfRealView (realized generator identity) (fun _ => rfl) coefficients coefficients_complete

/-- The cubic coordinate calculation in the original parameter-minus-two pair ring. -/
private theorem cubic_coordinates :
    (1 : Pair Rational (-2)) * ((⟨1, 1⟩ : Pair Rational (-2)) ^ 3 * 1) + 0 = ⟨7, 5⟩ := by
  decide +kernel

example (generator channel : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (input : Realization.Sidecar (realized generator identity) channel)
    (same : input.value = (⟨1, 1⟩ : Pair Rational (-2))) :
    ((normalized channel).realize (realized generator identity) (mapped generator identity) (fun _ => some input)
      (Terms.supported_all _ (fun _ => rfl) _)).value =
      (⟨7, 5⟩ : Pair Rational (-2)) := by
  rewrite [Gaussian.Normalized.realize_value]
  change (1 : Pair Rational (realized generator identity).parameter) * (input.value ^ 3 * 1) + 0 = _
  rewrite [same]
  exact cubic_coordinates

example (generator channel : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (input : Realization.Sidecar (realized generator identity) channel) :
    ((normalized channel).realize (realized generator identity) (mapped generator identity) (fun _ => some input)
      (Terms.supported_all _ (fun _ => rfl) _)).source =
      cubic.denote (fun _ => channel) :=
  ((normalized channel).realize (realized generator identity) (mapped generator identity) (fun _ => some input)
      (Terms.supported_all _ (fun _ => rfl) _)).source_eq

/-- The original cubic ignores the second retained variable while keeping its original arity. -/
private def supportedCubic : Sparse Canonical 2 := Sparse.pow (Sparse.atom 0) 3

/-- Retain both original variable channels, including the unrelated unused source. -/
private def twoChannels (channel unused : CoherentNamed) : Fin 2 → CoherentNamed :=
  Fin.cases channel (fun _ => unused)

/-- Exact original coordinate evidence is present only for the first retained variable. -/
private def optionalEvidence (generator channel unused : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (input : Realization.Sidecar (realized generator identity) channel) :
    (index : Fin 2) → Option (Realization.Sidecar (realized generator identity) (twoChannels channel unused index)) :=
  Fin.cases (some input) (fun _ => none)

/-- The actual cubic's nonzero exponents need only its first original variable certificate. -/
private theorem optional_supported (generator channel unused : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (input : Realization.Sidecar (realized generator identity) channel) :
    Terms.Supported (fun index => (optionalEvidence generator channel unused identity input index).isSome = true)
      supportedCubic.terms := by
  change ((3 = 0 ∨ (true = true)) ∧ (0 = 0 ∨ (false = true)) ∧ True) ∧ True
  exact ⟨⟨Or.inr rfl, Or.inl rfl, True.intro⟩, True.intro⟩

/-- The retained coefficient view covers the same original two-variable cubic. -/
private def supportedCoefficients := Cast.inspectRealList (Terms.coefficientEntries supportedCubic.terms)

/-- Every coefficient in the actual retained two-variable cubic is real. -/
private theorem supportedCoefficients_complete : supportedCoefficients.Complete := by decide +kernel

example (generator channel unused : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (input : Realization.Sidecar (realized generator identity) channel)
    (same : input.value = (⟨1, 1⟩ : Pair Rational (-2))) :
    let environment := twoChannels channel unused
    let normalized : Gaussian.Normalized environment (supportedCubic.denote environment) :=
      Gaussian.Normalized.ofForm environment supportedCubic (NamedEquivalent.refl _)
    let mapped := Terms.coefficientsOfRealView (realized generator identity) (fun _ => rfl)
      supportedCoefficients supportedCoefficients_complete
    (normalized.realize (realized generator identity) mapped (optionalEvidence generator channel unused identity input)
      (optional_supported generator channel unused identity input)).value = (⟨7, 5⟩ : Pair Rational (-2)) := by
  dsimp only
  rewrite [Gaussian.Normalized.realize_value]
  change (1 : Pair Rational (realized generator identity).parameter) * (input.value ^ 3 * (0 ^ 0 * 1)) + 0 = _
  rewrite [same, pow_zero, one_mul (1 : Pair Rational (realized generator identity).parameter)]
  exact cubic_coordinates

example : ¬ (Monomial.cons 0 (Monomial.cons 1 Monomial.nil)).Supported
    (fun index : Fin 2 => index.val = 0) := by
  intro supported
  cases supported.2.1 with
  | inl zero => cases zero
  | inr available => cases available

end TestPurelib.Polynomial.MultivariateRealization

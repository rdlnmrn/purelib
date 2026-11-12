module

public import Purelib.Algebra.Quadratic.Pair.Gaussian
public import Purelib.Approximation.Gaussian.Division.Prepared.Sum
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Factor
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Rational readings from a retained split power equation

The degree-two equation factors at the same original generator into two
linear factors. Their nonzero sum computes a finite choice of an apart
factor. Its actual preparation cancels the operationally zero product, so
the other factor selects an exact rational reading of the original generator.
The selected sum observation, both original factor channels and its preparation
remain in the returned certificate.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Power

open Purelib.Algebra.Quadratic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Coherent
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

/-- A zero affine pair with generator coefficient minus one identifies the original generator's exact scalar reading. -/
private def generator_of_zero_pair (generator : CoherentNamed) (candidate parameter : Canonical)
    (zero : Zero.ZeroIdentity
      (Pair.Gaussian.denote (fun value : Canonical => value) generator (⟨candidate, -1⟩ : Pair Canonical parameter))) :
    NamedEquivalent generator.name (Coherence.exact candidate).name := by
  let factor := Pair.Gaussian.denote (fun value : Canonical => value) generator
    (⟨candidate, -1⟩ : Pair Canonical parameter)
  let basis := Pair.Gaussian.denote (fun value : Canonical => value) generator
    (Pair.generator : Pair Canonical parameter)
  have basisEq := Pair.Gaussian.denote_generator (parameter := parameter)
    (fun value : Canonical => value) rfl rfl generator
  have coordinates : (⟨candidate, -1⟩ : Pair Canonical parameter) + Pair.generator = Pair.scalar candidate := by
    apply Pair.ext
    · change candidate + 0 = candidate
      exact add_zero _
    · change (-1 : Canonical) + 1 = 0
      ring1
  have affine := Pair.Gaussian.denote_add (fun value : Canonical => value) (fun _ _ => rfl)
    generator (⟨candidate, -1⟩ : Pair Canonical parameter) Pair.generator
  rewrite [coordinates] at affine
  exact NamedEquivalent.trans (NamedEquivalent.symm (Add.coherentAdd_zero_left generator))
    (NamedEquivalent.trans
      (Sum.Congruence.coherentAdd_respects (Coherence.exact 0) factor generator basis
        (NamedEquivalent.symm zero) (NamedEquivalent.symm basisEq))
      (NamedEquivalent.trans affine
        (Pair.Gaussian.denote_scalar (parameter := parameter) (fun value : Canonical => value) rfl
          generator candidate)))

/-- An original signed rational reading with its complete factor-selection observation. -/
@[expose] def SignedReading (generator : CoherentNamed) (candidate : Canonical) : Type 1 :=
  Sigma fun _selection : Prepared.Sum.Selection
    (Pair.Gaussian.denote (fun value : Canonical => value) generator
      (⟨candidate, 1⟩ : Pair Canonical (-(candidate * candidate))))
    (Pair.Gaussian.denote (fun value : Canonical => value) generator
      (⟨candidate, -1⟩ : Pair Canonical (-(candidate * candidate))))
    (2 * candidate) =>
    { reading : RationalSidecar generator // reading.value = candidate ∨ reading.value = -candidate }

/-- Select an exact signed reading from the original generator's retained split degree-two equation. -/
@[noinline, nospecialize] def PowerIdentity.rationalSquare {generator : CoherentNamed} (candidate : Canonical)
    (nonzero : candidate ≠ 0) (identity : PowerIdentity generator 2 (candidate * candidate)) :
    SignedReading generator candidate := by
  let parameter := -(candidate * candidate)
  let plusPair : Pair Canonical parameter := ⟨candidate, 1⟩
  let minusPair : Pair Canonical parameter := ⟨candidate, -1⟩
  let plus := Pair.Gaussian.denote (fun value : Canonical => value) generator plusPair
  let minus := Pair.Gaussian.denote (fun value : Canonical => value) generator minusPair
  have sumCoordinates : plusPair + minusPair = Pair.scalar (2 * candidate) := by
    apply Pair.ext
    · change candidate + candidate = 2 * candidate
      ring1
    · change (1 : Canonical) + -1 = 0
      ring1
  have sum := Pair.Gaussian.denote_add (fun value : Canonical => value) (fun _ _ => rfl)
    generator plusPair minusPair
  rewrite [sumCoordinates] at sum
  have sumIdentity := NamedEquivalent.trans sum
    (Pair.Gaussian.denote_scalar (parameter := parameter) (fun value : Canonical => value) rfl
      generator (2 * candidate))
  have pointNonzero : (2 : Canonical) * candidate ≠ 0 :=
    Field.mul_ne_zero_direct (by decide +kernel) nonzero
  let selection := Prepared.Sum.select plus minus (2 * candidate) pointNonzero sumIdentity
  have productCoordinates : plusPair * minusPair = 0 := by
    apply Pair.ext
    · change candidate * candidate - (-(candidate * candidate)) * 1 * (-1) = 0
      ring1
    · change candidate * (-1) + 1 * candidate = 0
      ring1
  have retained : PowerIdentity generator 2 (-parameter) := by
    have same : -parameter = candidate * candidate := neg_neg _
    rewrite [same]
    exact identity
  have product := Pair.Gaussian.denote_mul (fun value : Canonical => value) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) generator retained plusPair minusPair
  rewrite [productCoordinates] at product
  have productZero := NamedEquivalent.trans product
    (Pair.Gaussian.denote_zero (parameter := parameter) (fun value : Canonical => value) rfl generator)
  refine ⟨selection, ?_⟩
  match selection.prepared with
  | .inl prepared =>
      let minusZero := prepared.zero_other_factor minus productZero
      let reading : RationalSidecar generator :=
        ⟨candidate, generator_of_zero_pair generator candidate parameter minusZero⟩
      exact ⟨reading, Or.inl rfl⟩
  | .inr prepared =>
      let plusZero := prepared.zero_other_factor plus
        (NamedEquivalent.trans (Product.Laws.coherentMul_comm minus plus) productZero)
      have negativeZero := NamedEquivalent.trans
        (NamedEquivalent.symm (Pair.Gaussian.denote_neg (fun value : Canonical => value) rfl
          (fun _ _ => rfl) generator plusPair))
        (NamedEquivalent.trans (Additive.coherentNeg_respects plus (Coherence.exact 0) plusZero)
          (NamedEquivalent.symm Additive.zero_equivalent_neg_zero))
      let reading : RationalSidecar generator :=
        ⟨-candidate, generator_of_zero_pair generator (-candidate) parameter negativeZero⟩
      exact ⟨reading, Or.inr rfl⟩

end Purelib.Approximation.Gaussian.Provenance.Power

end

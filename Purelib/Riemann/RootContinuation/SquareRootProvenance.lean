module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision
public import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Riemann.Branches.SquareRootSheets

import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic

@[expose] public section

/-!
# Exact decisions from square-root provenance

The defining equation is operational: finite rational readings are not
assumed to solve the polynomial exactly. Its finite comparison modulus
instead produces sufficiently accurate square residuals. The audited
square-root residual bound then supplies nonzero separation, while a zero
radicand gives an operational identity to zero.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootProvenance

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Approximation.Gaussian in
/-- The original executable Gaussian approximation carrier. -/
abbrev Approximation := Sequence.ApproximationData
/-- Equivalence of the original Gaussian approximation sequences. -/
abbrev Equivalent := Purelib.Approximation.Gaussian.Equivalence.Equivalent

section
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
/-- The original coherent channel squares to the exact supplied Gaussian parameter. -/
def SquareIdentity (channel : Name.Coherent.CoherentNamed) (parameter : Basic.Canonical) :=
  Equivalence.NamedEquivalent (Name.Coherent.CoherentNamed.mul channel channel).name
    (Name.Coherent.CoherentNamed.Coherence.exact parameter).name

/-- Transport the retained named square identity to the original sampled product approximation. -/
def sampled_square {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (square : SquareIdentity channel parameter) :
    Equivalent (Sequence.Arithmetic.Product.sampledProductApproximation channel.name channel.name)
      (Name.Sampling.approximation
        (Name.Coherent.CoherentNamed.Coherence.exact parameter).name) :=
  Equivalence.Equivalent.trans
    (Equivalence.Equivalent.symm
      (Equivalence.Equivalent.toNamed_sampling _))
    (Equivalence.NamedEquivalent.trans
      (Equivalence.NamedEquivalent.symm
        (Name.Coherent.Arithmetic.Product.Bridge.coherentMul_toNamed channel channel)) square)

end

open Purelib.Data.Rat in
/-- A positive target exceeds a rational value whose square is strictly smaller. -/
private theorem lt_of_square_lt {value target : Fraction.Rational} (positive : 0 < target)
    (small : value ^ 2 < target ^ 2) : value < target :=
  ⟨Fraction.Order.Arithmetic.le_of_sq_le_sq_direct positive.le small.le,
    fun reverse => (not_lt_of_ge
      (Fraction.Order.Arithmetic.pow_le_pow_direct positive.le reverse 2)) small⟩

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A channel whose retained square identity has zero parameter is equivalent to zero.

The comparison requests squared tolerances from the original sampled product, retaining the returned indices and
translating the squared-norm bound constructively. -/
def zero_of_square {channel : Name.Coherent.CoherentNamed} (square : SquareIdentity channel 0) :
    Equivalence.Zero.ZeroIdentity channel where
  compare := by
    intro leftStart rightStart target positive
    let comparison := (sampled_square square).compare leftStart rightStart (target ^ 2)
      (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have close := comparison.close leftOrder rightOrder
          rw [Norm.Basic.normSq_eq_canonical] at close
          change normSq ((Name.Sampling.approximation channel.name).sample leftLater *
            (Name.Sampling.approximation channel.name).sample leftLater - 0) <
              target ^ 2 at close
          rw [Basic.sub_zero, Basic.Canonical.normSq_mul] at close
          rw [Norm.Basic.normSq_eq_canonical]
          change normSq ((Name.Sampling.approximation channel.name).sample leftLater - 0) <
            target
          rw [Basic.sub_zero]
          exact lt_of_square_lt positive (by simpa only [pow_two] using close) }

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- Prepare an original square-root channel for division when its parameter is nonzero.

A sampled residual request provides a persistent apartness witness at the retained source state; the prepared
denominator remains explicitly equivalent to the original channel. -/
def prepared_of_square {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (square : SquareIdentity channel parameter) (nonzero : parameter ≠ 0) : Approximation.Gaussian.Division.Prepared
        channel :=
  let source := Name.Sampling.approximation channel.name
  let sampled := Name.Coherent.CoherentNamed.ofApproximation source
  let comparison := (sampled_square square).compare 0 0
    (SquareRootSheets.residualTarget parameter)
    (SquareRootSheets.residualTarget_positive nonzero)
  let state : Approximation.Gaussian.Name.Coherent.Refinement.State sampled :=
    { source := comparison.leftIndex
      nextIndex := 0
      persists := by
        intro value possible
        rcases possible with ⟨later, _order, equal⟩
        exact ⟨later, Nat.zero_le _, equal⟩ }
  let evidence : Process.Apart.Possible.PossibleApart
      (Process.Based.based sampled.name.process state.source) :=
    { lowerSq := SquareRootSheets.sampleNormLower parameter
      positive := SquareRootSheets.sampleLower_positive nonzero
      lower := by
        intro laterState value possible
        have atBase := laterState.persists possible
        rcases atBase with ⟨later, order, equal⟩
        rw [equal]
        have residual := comparison.close order (Nat.le_refl comparison.rightIndex)
        rw [Norm.Basic.normSq_eq_canonical] at residual
        change normSq (source.sample later * source.sample later - parameter) <
          SquareRootSheets.residualTarget parameter at residual
        rw [Norm.Basic.normSq_eq_canonical]
        exact SquareRootSheets.normSq_lower_of_square_residual residual.le }
  let prepared := Approximation.Gaussian.Division.Prepared.ofEvidence state evidence
  { denominator := prepared.denominator
    apart := prepared.apart
    equivalent := Equivalence.NamedEquivalent.trans
      (Equivalence.Equivalent.symm
        (Equivalence.Equivalent.toNamed_sampling source)) prepared.equivalent }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- The positive residual tolerance for a parameter, with exact fallback one at zero. -/
def residualRequest (parameter : Basic.Canonical) : Fraction.Rational :=
  if parameter = 0 then 1 else SquareRootSheets.residualTarget parameter

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- The original parameter's residual request is strictly positive. -/
theorem residualRequest_positive (parameter : Basic.Canonical) : 0 < residualRequest parameter := by
  unfold residualRequest
  split
  · decide
  · exact SquareRootSheets.residualTarget_positive ‹parameter ≠ 0›

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- The positive sampled-norm separation threshold, with exact fallback one at zero. -/
def separationGap (parameter : Basic.Canonical) : Fraction.Rational :=
  if parameter = 0 then 1 else SquareRootSheets.sampleNormLower parameter

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- The original parameter's separation gap is strictly positive. -/
theorem separationGap_positive (parameter : Basic.Canonical) : 0 < separationGap parameter := by
  unfold separationGap
  split
  · decide
  · exact SquareRootSheets.sampleLower_positive ‹parameter ≠ 0›

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- An authenticated original channel sample with a strict square-residual bound.

The retained index and exact value equality identify the executable sample used to satisfy the parameter's residual
request. -/
structure Observation (channel : Name.Coherent.CoherentNamed) (parameter : Basic.Canonical) where
  /-- The retained sample index of the original channel. -/ index : Nat
  /-- The actual Gaussian sample used by the residual test. -/ value : Basic.Canonical
  /-- Exact equality with the original channel sample at the retained index. -/ value_eq : value =
    (Name.Sampling.approximation channel.name).sample index
  /-- The authenticated sample meets the original parameter's strict square-residual tolerance. -/ residual : normSq
    (value * value - parameter) < residualRequest parameter

constructive_injectivity Observation

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- Acquire one authenticated original sample meeting the retained square-residual request. -/
def observe {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (square : SquareIdentity channel parameter) : Observation channel parameter :=
  let comparison := (sampled_square square).compare 0 0 (residualRequest parameter)
    (residualRequest_positive parameter)
  { index := comparison.leftIndex
    value := (Name.Sampling.approximation channel.name).sample comparison.leftIndex
    value_eq := rfl
    residual := by
      have scalar := comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      change normSq ((Name.Sampling.approximation channel.name).sample comparison.leftIndex *
        (Name.Sampling.approximation channel.name).sample comparison.leftIndex - parameter) <
        residualRequest parameter at scalar
      exact scalar }

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- A sufficiently small authenticated root sample certifies that the original parameter is zero. -/
theorem Observation.parameter_zero_of_small {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (observation : Observation channel parameter)
    (small : normSq observation.value < separationGap parameter) : parameter = 0 := by
  by_cases zero : parameter = 0
  · exact zero
  · have residual := observation.residual
    rw [residualRequest, if_neg zero] at residual
    rw [separationGap, if_neg zero] at small
    exact False.elim ((not_lt_of_ge
      (SquareRootSheets.normSq_lower_of_square_residual residual.le)) small)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An authenticated sample for zero parameter lies below its retained separation gap. -/
theorem Observation.small_of_parameter_zero {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (observation : Observation channel parameter) (zero : parameter = 0) :
    normSq observation.value < separationGap parameter := by
  subst parameter
  have residual := observation.residual
  rw [residualRequest, if_pos rfl, Basic.sub_zero,
    Basic.Canonical.normSq_mul] at residual
  rw [separationGap, if_pos rfl]
  apply lt_of_square_lt (by decide)
  rw [show (1 : Fraction.Rational) ^ 2 = 1 by decide, pow_two]
  exact residual

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- Construct zero-channel evidence from the original authenticated small sample and square identity. -/
def Observation.zero_of_small {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (observation : Observation channel parameter) (square : SquareIdentity channel parameter)
    (small : normSq observation.value < separationGap parameter) : Equivalence.Zero.ZeroIdentity channel :=
  zero_of_square (by simpa only [observation.parameter_zero_of_small small] using square)

section
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
/-- Decide zero exclusion or executable division preparation from the original square identity.

The exact parameter test selects a zero certificate or a prepared denominator with retained equivalence and apartness
evidence. -/
def decide {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (square : SquareIdentity channel parameter) : Approximation.Gaussian.Division.Prepared.Decision channel :=
  if zero : parameter = 0 then
    .excluded (zero_of_square (by simpa only [zero] using square))
  else .prepared (prepared_of_square square zero)

/-- A nonzero original parameter selects its exact prepared-denominator branch. -/
theorem decide_prepared {channel : Name.Coherent.CoherentNamed} {parameter : Basic.Canonical}
    (square : SquareIdentity channel parameter) (nonzero : parameter ≠ 0) :
    decide square = .prepared (prepared_of_square square nonzero) := by
  unfold decide
  exact dif_neg nonzero

end

open Purelib.Approximation.Gaussian in
/-- Zero parameter selects the original zero-channel exclusion certificate. -/
theorem decide_excluded {channel : Name.Coherent.CoherentNamed} (square : SquareIdentity channel 0) :
    decide square = .excluded (zero_of_square square) := by
  unfold decide
  exact dif_pos rfl

namespace SquareIdentity

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

/-- The retained coordinate square law identifies every even finite power with the corresponding radicand power.

The supplied operational square comparison is composed with the original
finite multiplication witnesses at each successor exponent. -/
def even_power {coordinate : Coherent.CoherentNamed} {point : Gaussian}
    (square : SquareIdentity coordinate point) (exponent : Nat) :
    Equivalence.NamedEquivalent (Power.namedPower coordinate (2 * exponent)).name (exact (point ^
      exponent)).name := by
  induction exponent with
  | zero => exact NamedEquivalent.refl _
  | succ exponent previous =>
      change Equivalence.NamedEquivalent (CoherentNamed.mul (CoherentNamed.mul (Power.namedPower coordinate (2
        * exponent)) coordinate) coordinate).name
        (exact (point ^ (exponent + 1))).name
      have result := (Laws.coherentMul_assoc (Power.namedPower coordinate (2 * exponent)) coordinate coordinate).trans
        ((Congruence.coherentMul_respects (Power.namedPower coordinate (2 * exponent)) (exact (point ^ exponent))
          (CoherentNamed.mul coordinate coordinate) (exact point) previous square).trans
          (Exact.Arithmetic.exact_mul (point ^ exponent) point))
      simpa only [pow_succ, CoherentNamed.mul] using result

end SquareIdentity

end Purelib.Riemann.RootContinuation.SquareRootProvenance

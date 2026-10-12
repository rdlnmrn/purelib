module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Sign.Typed
public import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.CauchyIndex.Endpoint
import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Neutral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.Int
import Purelib.Algebra.NatCast

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral (NeutralChainCertificates)

/-!
# Formal Cauchy events from neutral signed chains

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral

open Purelib
open Purelib.Polynomial
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- If the recursively emitted tail is neutral, the complete Cauchy index is exactly the change of the first two
signed-chain jumps.

The exact tail begins with the numerator and the negated denominator
division remainder. Its equal endpoint variations cancel from the retained
full chain, leaving the first jump difference. -/
public theorem cauchyIndex2_eq_firstJumps_of_neutralTail
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (RNonzero : R.isZero = false)
    (tail : NeutralChainCertificates interval
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S
        R).remainder)))) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.lower interval.upper =
      (Data.Rat.Sign.Jump.signJump (S.eval interval.lower) (R.eval interval.lower) : Int) -
        Data.Rat.Sign.Jump.signJump (S.eval interval.upper) (R.eval interval.upper) := by
  unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
  rw [Dense.Rational.SignedRemainder.Variation.endpointVariation2_signedRemainderChain_step S R RNonzero,
    Dense.Rational.SignedRemainder.Variation.endpointVariation2_signedRemainderChain_step S R RNonzero,
    tail.endpointVariation_eq]
  rewrite [Purelib.Algebra.NatCast.add, Purelib.Algebra.NatCast.add]
  ring1

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns

open Purelib
open Purelib.Polynomial
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- A neutral full chain with a fixed denominator sign is the zero-event branch.

The denominator sign is taken from its original lower-endpoint value and
transported to the upper endpoint by the strict-sign certificate. The exact
neutral full chain certifies a zero event with formal numerator sign zero. -/
@[expose] public def ofNeutral
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (denominator : Dense.Rational.Sign.Interval.Basic.Certificate S interval)
    (chain : NeutralChainCertificates interval
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain S R)) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns R S interval := by
  let denominatorSign := FiniteSign.ofCoordinate (S.eval interval.lower)
  have denominatorNonzero : denominatorSign ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr
      (denominator.eval_ne_zero ⟨le_rfl, interval.valid⟩)
  have denominatorStable : denominatorSign =
      FiniteSign.ofCoordinate (S.eval interval.upper) := by
    apply FiniteSign.value_injective
    change FiniteSign.value (FiniteSign.ofCoordinate (S.eval interval.lower)) =
      FiniteSign.value (FiniteSign.ofCoordinate (S.eval interval.upper))
    rewrite [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]
    exact Data.Rat.Sign.Basic.sign_eq_of_mul_pos denominator.endpoint_stable
  refine
    { numerator := .zero
      denominator := denominatorSign
      nonzero := Or.inr denominatorNonzero
      numeratorLowerStable := Or.inl rfl
      denominatorLowerStable := Or.inr rfl
      numeratorUpperStable := Or.inl rfl
      denominatorUpperStable := Or.inr denominatorStable
      index := ?_ }
  rw [chain.cauchyIndex2_eq_zero]
  unfold FiniteSign.eventIndex2
  repeat first
    | rewrite [FiniteSign.leftEndpointIndex2]
    | rewrite [if_neg denominatorNonzero]
  exact Eq.refl _

/-- A fixed nonzero numerator and neutral recursive tail represent the sole possibly nonzero first-chain event; no root
parameter is introduced.

The numerator sign is taken from its original lower-endpoint value. Its
strict-sign certificate and the retained neutral remainder tail identify the
event with the first jump difference, with formal denominator sign zero. -/
@[expose] public def ofResolvedNumerator
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (numerator : Dense.Rational.Sign.Interval.Basic.Certificate R interval)
    (tail : NeutralChainCertificates interval
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S
        R).remainder)))) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns R S interval := by
  let numeratorSign := FiniteSign.ofCoordinate (R.eval interval.lower)
  have numeratorNonzero : numeratorSign ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr
      (numerator.eval_ne_zero ⟨le_rfl, interval.valid⟩)
  have numeratorStable : numeratorSign =
      FiniteSign.ofCoordinate (R.eval interval.upper) := by
    apply FiniteSign.value_injective
    change FiniteSign.value (FiniteSign.ofCoordinate (R.eval interval.lower)) =
      FiniteSign.value (FiniteSign.ofCoordinate (R.eval interval.upper))
    rewrite [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]
    exact Data.Rat.Sign.Basic.sign_eq_of_mul_pos numerator.endpoint_stable
  refine
    { numerator := numeratorSign
      denominator := .zero
      nonzero := Or.inl numeratorNonzero
      numeratorLowerStable := Or.inr rfl
      denominatorLowerStable := Or.inl rfl
      numeratorUpperStable := Or.inr numeratorStable
      denominatorUpperStable := Or.inl rfl
      index := ?_ }
  rw [Dense.Rational.CauchyIndex.Events.Signs.Neutral.cauchyIndex2_eq_firstJumps_of_neutralTail
    numerator.polynomial_nonzero tail,
    ← FiniteSign.jump_ofCoordinate,
    ← FiniteSign.jump_ofCoordinate, ← numeratorStable]
  exact (FiniteSign.eventIndex2_of_stableNumerator
    numeratorSign
    (FiniteSign.ofCoordinate (S.eval interval.lower))
    (FiniteSign.ofCoordinate (S.eval interval.upper))
    numeratorNonzero).symm

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns

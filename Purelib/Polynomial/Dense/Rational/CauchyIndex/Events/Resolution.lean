module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Prepare
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Resolved
import Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Resolution.Bounds
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Resolution
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- If the denominator already has a fixed sign, resolution bounds for the
complete signed chain force the first branch of the Cauchy-event scanner to
succeed.

The original denominator classifier returned its retained strict-sign
certificate. The resolution bounds construct the exact full-chain
certificate consumed by the same first scanner branch. -/
public theorem cauchyEventSigns?_isSome_of_denominator_resolutionBounds
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds} {tail : List
      Dense.Rational.Basic.CoordinatePolynomial}
    (chainEq : SignedRemainder.Basic.Sturm.signedRemainderChain S R = S :: tail)
    (bounds : SignedRemainder.Signs.Resolution.Bounds.NeutralChainResolutionBounds interval S tail)
    (denominator : Sign.Interval.Resolved.ResolvedSign S interval) :
    (CauchyIndex.Events.Prepare.cauchyEventSigns? R S interval).isSome = true := by
  have chain := SignedRemainder.Signs.Neutral.Resolution.neutralChainCertificates?_succeeds_of_resolutionBounds
    interval S tail bounds denominator
  have chainSome :
      (SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
        (SignedRemainder.Basic.Sturm.signedRemainderChain S R)).isSome = true := by
    rw [chainEq, chain.2]
    rfl
  cases chainFound : SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
      (SignedRemainder.Basic.Sturm.signedRemainderChain S R) with
  | none =>
      rw [chainFound] at chainSome
      cases chainSome
  | some chainCertificate =>
      unfold CauchyIndex.Events.Prepare.cauchyEventSigns?
      rw [denominator.found, chainFound]
      rfl

/-- On a nonzero numerator, one adjacent Bézout-pair bound and the finite
chain bounds decide both branches of the executable Cauchy-event scanner.

The original nonzero numerator fixes the signed remainder chain indices.
A resolved denominator selects the first branch; otherwise the same pair
resolution forces the numerator and supplies its retained neutral tail. -/
public theorem cauchyEventSigns?_isSome_of_resolutionBounds
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (RNonzero : R.isZero = false)
    (bounds : SignedRemainder.Signs.Resolution.Bounds.NeutralChainResolutionBounds interval S
      (SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S R).remainder)))) :
    (CauchyIndex.Events.Prepare.cauchyEventSigns? R S interval).isSome = true := by
  have fullChainEq := SignedRemainder.Basic.signedRemainderChain_step_of_second_nonzero
    S R RNonzero
  cases denominatorFound : Sign.Interval.Prepare.certificate? S interval with
  | some denominatorCertificate =>
      let denominator : Sign.Interval.Resolved.ResolvedSign S interval :=
        ⟨denominatorCertificate, denominatorFound⟩
      exact cauchyEventSigns?_isSome_of_denominator_resolutionBounds
        fullChainEq bounds denominator
  | none =>
      have tailEq := SignedRemainder.Basic.signedRemainderChain_eq_head_cons_tail
        R (-((Dense.Basic.DensePolynomial.divMod S R).remainder))
      rw [tailEq] at bounds
      have numeratorSome : (Sign.Interval.Prepare.certificate? R interval).isSome = true :=
        bounds.secondCertificate?_isSome_of_first_none denominatorFound
      cases numeratorFound : Sign.Interval.Prepare.certificate? R interval with
      | none =>
          rw [numeratorFound] at numeratorSome
          cases numeratorSome
      | some numeratorCertificate =>
          let numerator : Sign.Interval.Resolved.ResolvedSign R interval :=
            ⟨numeratorCertificate, numeratorFound⟩
          have tailChain :=
            SignedRemainder.Signs.Neutral.Resolution.neutralChainCertificates?_succeeds_of_resolutionBounds
              interval R (SignedRemainder.Basic.Sturm.signedRemainderChain
                R (-((Dense.Basic.DensePolynomial.divMod S R).remainder))).tail
                bounds.dropHead numerator
          have tailSome :
              (SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
                (SignedRemainder.Basic.Sturm.signedRemainderChain R
                  (-((Dense.Basic.DensePolynomial.divMod S R).remainder)))).isSome = true := by
            rw [tailEq, tailChain.2]
            rfl
          cases tailFound : SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval
              (SignedRemainder.Basic.Sturm.signedRemainderChain R (-((Dense.Basic.DensePolynomial.divMod S
                R).remainder))) with
          | none =>
              rw [tailFound] at tailSome
              cases tailSome
          | some tailCertificate =>
              unfold CauchyIndex.Events.Prepare.cauchyEventSigns?
              rw [denominatorFound, numeratorFound, tailFound]
              rfl

/-- The shrinking squared radius and explicit initial Bézout identity are a
complete finite success condition for one genuine Cauchy-event scan.

The original clearance and squared-radius test construct all finite
resolution bounds on the same refinement. The zero numerator case resolves
the denominator, while the other case follows the retained signed chain. -/
public theorem cauchyEventSigns?_isSome_of_refined_radiusSq
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate S R root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance) :
    (CauchyIndex.Events.Prepare.cauchyEventSigns? R S interval).isSome = true := by
  have bounds := SignedRemainder.Signs.Resolution.Bounds.signedChainResolutionBoundsOfRadiusSq root interval refines
    S R clearance radius
  by_cases RZero : R.isZero = true
  · have pairRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
        Sign.Pair.Resolution.pairResolutionRadiusSq clearance := by
      have bound := radius
      rw [SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_eq] at bound
      rw [RZero] at bound
      exact bound
    have pairResolution := Sign.Pair.Resolution.pairResolution_of_refined_radiusSq
      clearance refines pairRadius
    have denominator := Sign.Pair.Resolution.resolvedSign_of_terminal_pairResolution RZero
      (clearance.restrict refines) pairResolution
    have chainEq : SignedRemainder.Basic.Sturm.signedRemainderChain S R = S :: [] := by
      rw [SignedRemainder.Basic.Sturm.signedRemainderChain, SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
      rw [RZero]
      rfl
    have tailEq : (SignedRemainder.Basic.Sturm.signedRemainderChain S R).tail = [] := by
      rw [chainEq]
      rfl
    rw [tailEq] at bounds
    exact cauchyEventSigns?_isSome_of_denominator_resolutionBounds
      chainEq bounds denominator
  · have RNonzero : R.isZero = false := by
      cases value : R.isZero with
      | false => rfl
      | true => exact (RZero value).elim
    rw [SignedRemainder.Basic.signedRemainderChain_tail_eq_of_second_nonzero S R RNonzero] at bounds
    exact cauchyEventSigns?_isSome_of_resolutionBounds RNonzero bounds

/-- Convenience specialization of the finite-clearance theorem to a
displayed polynomial Bézout identity.

The original explicit polynomial Bézout identity constructs the retained
interval clearance. Its same coefficient-count radius and refinement
then certify success of the original event classifier. -/
public theorem cauchyEventSigns?_isSome_of_coprime_refined_radiusSq
    {R S : Dense.Rational.Basic.CoordinatePolynomial} (coprime : Bezout.Basic.CoprimeCertificate S R)
    {root interval : Data.Rat.Interval.Bounds}
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R
        (Clearance.Pair.Bezout.certificateOfCoprime coprime root)) :
    (CauchyIndex.Events.Prepare.cauchyEventSigns? R S interval).isSome = true :=
  cauchyEventSigns?_isSome_of_refined_radiusSq
    (Clearance.Pair.Bezout.certificateOfCoprime coprime root) refines radius

/-! ## One-sided endpoint cells -/

/-- Total projection of the proof-bearing event returned by the finite
scanner once its coefficient-computed radius bound has been met.

The original option-valued scanner is evaluated on the supplied pair and
interval. Its proved success permits total extraction of exactly its
selected proof-bearing event, without rebuilding any certificate. -/
@[expose] public def cauchyEventSignsOfRefinedRadiusSq
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate S R root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance) :
    CauchyIndex.Events.Signs.CauchyEventSigns R S interval :=
  (CauchyIndex.Events.Prepare.cauchyEventSigns? R S interval).get
    (cauchyEventSigns?_isSome_of_refined_radiusSq clearance refines radius)

/-- The same coefficient-computed resolution, retaining the actual
strict-sign certificate selected by the finite scanner.

The certificate-retaining scanner and its sign projection follow the
same original finite branches. Success of the projected signs therefore
excludes the none branch of that same resolution scanner. -/
public theorem cauchyEventResolution?_isSome_of_refined_radiusSq
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate S R root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance) :
    (CauchyIndex.Events.Prepare.cauchyEventResolution? R S interval).isSome = true := by
  have signsSome := cauchyEventSigns?_isSome_of_refined_radiusSq
    clearance refines radius
  cases found : CauchyIndex.Events.Prepare.cauchyEventResolution? R S interval with
  | none =>
      rw [← CauchyIndex.Events.Prepare.cauchyEventResolution?_map_signs R S interval,
        found] at signsSome
      cases signsSome
  | some certificate => rfl

/-- Extract the event resolution returned by the scanner under the finite squared-radius bound.

The original scanner is evaluated on the supplied polynomial pair and
interval. Its finite radius success certificate permits extraction of the
exact retained resolution and its selected strict-sign witnesses. -/
@[expose] public def cauchyEventResolutionOfRefinedRadiusSq
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate S R root)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq S R clearance) :
    Basic.CauchyEventResolution R S interval :=
  (CauchyIndex.Events.Prepare.cauchyEventResolution? R S interval).get
    (cauchyEventResolution?_isSome_of_refined_radiusSq
      clearance refines radius)

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution

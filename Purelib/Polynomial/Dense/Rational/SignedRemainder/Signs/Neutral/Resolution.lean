module
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Resolved
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Prepare
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Resolution.Bounds
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Prepare
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Resolution
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Dominance
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Resolution

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- Local resolution bounds make every branch of the recursive neutral-chain
scanner succeed.

The original head certificate and resolution bounds select each stable
or cancelling branch of the same finite scanner. Recursion retains the
successful tail certificate and its exact classifier equality. -/
@[expose] public def neutralChainCertificate?_succeeds_of_resolutionBounds
    (interval : Data.Rat.Interval.Bounds) :
    (head : Dense.Rational.Basic.CoordinatePolynomial) → (tail : List Dense.Rational.Basic.CoordinatePolynomial) →
      Dense.Rational.SignedRemainder.Signs.Resolution.Bounds.NeutralChainResolutionBounds interval head tail →
      (headResolved : Dense.Rational.Sign.Interval.Resolved.ResolvedSign head interval) →
      { certificate : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificate interval head tail //
        Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate? interval head tail = some
          certificate }
  | head, [], .single, headResolved => by
      refine ⟨.single headResolved.certificate, ?_⟩
      rw [Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate?, headResolved.found]
  | head, [q], .pair last, headResolved => by
      refine ⟨.stable headResolved.certificate
        (.single last.certificate), ?_⟩
      rw [Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate?, headResolved.found, last.found]
  | head, q :: r :: suffix,
      .step nextEq leftClearance rightClearance leftResolution
        rightResolution dominance rest,
      headResolved => by
      subst r
      by_cases qMargin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
          Interval.Radius.sampleRadiusSq interval interval.lower < q.eval interval.lower ^ 2
      · let qCertificate : Dense.Rational.Sign.Interval.Basic.Certificate q interval :=
          { sample := interval.lower
            sampleInside := ⟨le_rfl, interval.valid⟩
            margin := qMargin }
        have qFound : Dense.Rational.Sign.Interval.Prepare.certificate? q interval = some qCertificate := by
          unfold Dense.Rational.Sign.Interval.Prepare.certificate?
          exact dif_pos qMargin
        let qResolved : Dense.Rational.Sign.Interval.Resolved.ResolvedSign q interval :=
          ⟨qCertificate, qFound⟩
        have recursive :=
          neutralChainCertificate?_succeeds_of_resolutionBounds
          interval q (-((Purelib.Polynomial.Dense.Basic.DensePolynomial.divMod head q).remainder) :: suffix) rest
            qResolved
        refine ⟨.stable headResolved.certificate recursive.1, ?_⟩
        rw [Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate?, headResolved.found,
          qFound]
        dsimp only
        rw (config := { occs := .pos [1] }) [recursive.2]
      · have qNone : Dense.Rational.Sign.Interval.Prepare.certificate? q interval = none := by
          unfold Dense.Rational.Sign.Interval.Prepare.certificate?
          exact dif_neg qMargin
        have stepSome :=
          Dense.Rational.SignedRemainder.Signs.Step.Resolution.signedStepCellCertificate?_isSome_of_resolution
          headResolved.found qNone rightClearance rightResolution dominance
        cases stepFound : Dense.Rational.SignedRemainder.Signs.Step.Prepare.signedStepCellCertificate? head q interval
          with
        | none =>
            rw [stepFound] at stepSome
            cases stepSome
        | some stepCertificate =>
          have nextSome :
              (Dense.Rational.Sign.Interval.Prepare.certificate?
                (-((Purelib.Polynomial.Dense.Basic.DensePolynomial.divMod head q).remainder)) interval).isSome =
                true :=
            Dense.Rational.Sign.Pair.Resolution.certificate?_isSome_of_pairResolution_of_first_none
              rightClearance rightResolution qNone
          cases nextFound :
              Dense.Rational.Sign.Interval.Prepare.certificate?
                (-((Purelib.Polynomial.Dense.Basic.DensePolynomial.divMod head q).remainder)) interval with
          | none =>
              rw [nextFound] at nextSome
              cases nextSome
          | some nextCertificate =>
            let nextResolved :
                Dense.Rational.Sign.Interval.Resolved.ResolvedSign
                  (-((Purelib.Polynomial.Dense.Basic.DensePolynomial.divMod head q).remainder)) interval :=
              ⟨nextCertificate, nextFound⟩
            have recursive :=
              neutralChainCertificate?_succeeds_of_resolutionBounds
              interval (-((Purelib.Polynomial.Dense.Basic.DensePolynomial.divMod head q).remainder)) suffix
                rest.dropHead
                nextResolved
            refine ⟨.event rfl stepCertificate recursive.1, ?_⟩
            rw [Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificate?, headResolved.found,
              qNone]
            dsimp only
            rw [dif_pos rfl, stepFound]
            dsimp only
            rw (config := { occs := .pos [1] }) [recursive.2]
termination_by _ tail _ _ => tail.length
decreasing_by
  · simp only [List.length_cons]
    exact Nat.lt_succ_self _
  · simp only [List.length_cons]
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)

/-- Package the recursively constructed certificate for a displayed nonempty
chain in the exact option type returned by the executable scanner.

The retained recursive certificate is wrapped by the original nonempty
chain constructor. Its displayed equality certifies that the same scanner
returns that exact proof-bearing result. -/
@[expose] public def neutralChainCertificates?_succeeds_of_resolutionBounds
    (interval : Data.Rat.Interval.Bounds) (head : Dense.Rational.Basic.CoordinatePolynomial) (tail : List
      Dense.Rational.Basic.CoordinatePolynomial)
    (bounds : Dense.Rational.SignedRemainder.Signs.Resolution.Bounds.NeutralChainResolutionBounds interval head tail)
    (headResolved : Dense.Rational.Sign.Interval.Resolved.ResolvedSign head interval) :
    { certificates : Dense.Rational.SignedRemainder.Signs.Neutral.NeutralChainCertificates interval (head :: tail) //
      Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates? interval (head :: tail) = some
        certificates } := by
  have recursive := neutralChainCertificate?_succeeds_of_resolutionBounds
    interval head tail bounds headResolved
  refine ⟨.cons recursive.1, ?_⟩
  rw [Dense.Rational.SignedRemainder.Signs.Neutral.Prepare.neutralChainCertificates?]
  exact congrArg
    (fun found : Option (NeutralChainCertificate interval head tail) =>
      match found with
      | none => none
      | some certificate => some
          (NeutralChainCertificates.cons certificate))
    recursive.2

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral.Resolution

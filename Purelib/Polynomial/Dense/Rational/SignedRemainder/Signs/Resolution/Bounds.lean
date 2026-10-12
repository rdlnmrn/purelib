module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Resolved
import Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Dominance
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Operations
import Purelib.Polynomial.Clearance.Pair.SignedRemainder
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Resolution.Bounds

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

@[expose] public section

set_option genInjectivity false in
/-- Finite local bounds following the exact shape of a signed remainder chain.

The original interval and polynomial indices determine every constructor.
A terminal pair retains its resolved sign; a step retains its recurrence,
adjacent clearances, strict resolutions, dominance and actual tail bounds. -/
inductive NeutralChainResolutionBounds (interval : Data.Rat.Interval.Bounds) :
    (head : Dense.Rational.Basic.CoordinatePolynomial) → (tail : List Dense.Rational.Basic.CoordinatePolynomial) → Type
  /-- A chain with no tail needs no further resolution data. -/
  | single {p : Dense.Rational.Basic.CoordinatePolynomial} :
    NeutralChainResolutionBounds interval p []
  /-- A terminal pair retains a resolved sign for its last polynomial. -/ | pair {p q :
    Dense.Rational.Basic.CoordinatePolynomial}
      (last : Dense.Rational.Sign.Interval.Resolved.ResolvedSign q interval) :
      NeutralChainResolutionBounds interval p [q]
  /-- A signed remainder step retains its exact recurrence, adjacent clearances, sign resolutions, dominance bound and
    recursively resolved tail. -/ | step {p q r : Dense.Rational.Basic.CoordinatePolynomial} {suffix : List
    Dense.Rational.Basic.CoordinatePolynomial}
      (nextEq : r = -((Dense.Basic.DensePolynomial.divMod p q).remainder))
      (leftClearance : Clearance.Pair.Basic.Certificate p q interval)
      (rightClearance : Clearance.Pair.Basic.Certificate q r interval)
      (leftResolution : Dense.Rational.Sign.Pair.Resolution.PairResolution leftClearance)
      (rightResolution : Dense.Rational.Sign.Pair.Resolution.PairResolution rightClearance)
      (dominance : Dense.Rational.SignedRemainder.Signs.Dominance.DominanceResolution q
        (Dense.Basic.DensePolynomial.divMod p q).quotient
        r rightClearance)
      (rest : NeutralChainResolutionBounds interval q (r :: suffix)) :
      NeutralChainResolutionBounds interval p (q :: r :: suffix)

constructive_injectivity NeutralChainResolutionBounds

end

/-- Fold the ambient squared radius through the actual finite signed chain,
producing every proof-relevant local field consumed by the scanner.

The retained coefficient-count radius bounds the same signed-remainder
chain. Its zero tests select the terminal constructors; otherwise the
original recurrence and restricted clearances accompany the recursive tail. -/
@[expose] public def signedChainResolutionBoundsOfRadiusSq
    (root interval : Data.Rat.Interval.Bounds) (refines : interval.Refines root)
    (p q : Dense.Rational.Basic.CoordinatePolynomial) (clearance : Clearance.Pair.Basic.Certificate p q root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq p q clearance) :
    NeutralChainResolutionBounds interval p
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q).tail := by
  by_cases qZero : q.isZero = true
  · rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
    rw [qZero]
    exact .single
  · have qNonzero : q.isZero = false := by
      cases value : q.isZero with
      | false => rfl
      | true => exact (qZero value).elim
    let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
    by_cases nextZero : next.isZero = true
    · have terminalRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
          Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep := by
        have bound := radius
        rw [Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_eq] at bound
        rw [qNonzero] at bound
        change Interval.Radius.sampleRadiusSq interval interval.lower <
          (if next.isZero then
            Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
          else min (Dense.Rational.SignedRemainder.Signs.Radius.signedStepResolutionRadiusSq clearance)
            (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq q next clearance.signedStep))
              at bound
        rw [nextZero]
          at bound
        exact bound
      have terminalResolution := Dense.Rational.Sign.Pair.Resolution.pairResolution_of_refined_radiusSq
        clearance.signedStep refines terminalRadius
      have terminalResolved := Dense.Rational.Sign.Pair.Resolution.resolvedSign_of_terminal_pairResolution
        nextZero (clearance.signedStep.restrict refines) terminalResolution
      have rawNextZero : (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).isZero = true := by
        exact nextZero
      rw [Dense.Rational.SignedRemainder.Basic.signedRemainderChain_tail_eq_of_second_nonzero p q qNonzero]
      rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
      rw [rawNextZero]
      exact .pair terminalResolved
    · have nextNonzero : next.isZero = false := by
        cases value : next.isZero with
        | false => rfl
        | true => exact (nextZero value).elim
      have decomposed : Interval.Radius.sampleRadiusSq interval interval.lower <
          min (Dense.Rational.SignedRemainder.Signs.Radius.signedStepResolutionRadiusSq clearance)
            (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq q next clearance.signedStep) :=
              by
        have bound := radius
        rw [Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_eq] at bound
        rw [qNonzero] at bound
        change Interval.Radius.sampleRadiusSq interval interval.lower <
          (if next.isZero then
            Dense.Rational.Sign.Pair.Resolution.pairResolutionRadiusSq clearance.signedStep
          else min (Dense.Rational.SignedRemainder.Signs.Radius.signedStepResolutionRadiusSq clearance)
            (Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq q next clearance.signedStep))
              at bound
        rw [nextNonzero]
          at bound
        exact bound
      have localRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
          Dense.Rational.SignedRemainder.Signs.Radius.signedStepResolutionRadiusSq clearance :=
        decomposed.trans_le (Fraction.Order.Basic.min_le_left _ _)
      have restRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
          Dense.Rational.SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq q next clearance.signedStep :=
        decomposed.trans_le (Fraction.Order.Basic.min_le_right _ _)
      have localResolutions := Dense.Rational.SignedRemainder.Signs.Radius.signedStepResolutions_of_refined_radiusSq
        clearance refines localRadius
      have rest :=
        Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Resolution.Bounds.signedChainResolutionBoundsOfRadiusSq
        root interval refines
        q next clearance.signedStep restRadius
      let nextNext := -((Dense.Basic.DensePolynomial.divMod q next).remainder)
      let suffix := (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain next nextNext).tail
      have nextChainEq : Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain next nextNext = next :: suffix
        :=
        Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_head_cons_tail next nextNext
      rw [Dense.Rational.SignedRemainder.Basic.signedRemainderChain_tail_eq_of_second_nonzero
        q next nextNonzero, nextChainEq] at rest
      rw [Dense.Rational.SignedRemainder.Basic.signedRemainderChain_tail_eq_of_second_nonzero p q qNonzero,
        Dense.Rational.SignedRemainder.Basic.signedRemainderChain_step_of_second_nonzero q next nextNonzero,
        nextChainEq]
      exact .step rfl (clearance.restrict refines)
        (clearance.signedStep.restrict refines) localResolutions.1
        localResolutions.2.1 localResolutions.2.2 rest
termination_by q.degreeCount
decreasing_by
  have qNonzero : q.isZero = false := by
    cases value : q.isZero with
    | false => rfl
    | true => exact (qZero value).elim
  rw [Dense.Basic.DensePolynomial.degreeCount_neg]
  exact Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero

/-- Remove the first polynomial while retaining the existing resolution data for the tail.

A terminal pair leaves the empty-tail constructor. A signed step returns
its already stored tail bounds with the original interval and indices. -/
@[expose] public def NeutralChainResolutionBounds.dropHead {interval : Data.Rat.Interval.Bounds} {p q :
  Dense.Rational.Basic.CoordinatePolynomial}
    {tail : List Dense.Rational.Basic.CoordinatePolynomial}
    (bounds : NeutralChainResolutionBounds interval p (q :: tail)) :
    NeutralChainResolutionBounds interval q tail :=
  match bounds with
  | .pair _ => .single
  | .step _ _ _ _ _ _ rest => rest

/-- The second polynomial has a successful sign certificate whenever the first sign-certificate search fails and the
chain carries resolution bounds.

A terminal pair stores the successful second certificate directly.
A signed step retains the adjacent-pair inequality that forces the second
sample margin when the first classifier is unresolved. -/
public theorem NeutralChainResolutionBounds.secondCertificate?_isSome_of_first_none
    {interval : Data.Rat.Interval.Bounds} {p q : Dense.Rational.Basic.CoordinatePolynomial} {tail : List
      Dense.Rational.Basic.CoordinatePolynomial}
    (bounds : NeutralChainResolutionBounds interval p (q :: tail))
    (firstNone : Dense.Rational.Sign.Interval.Prepare.certificate? p interval = none) :
    (Dense.Rational.Sign.Interval.Prepare.certificate? q interval).isSome = true := by
  cases bounds with
  | pair last => rw [last.found]; rfl
  | step nextEq leftClearance rightClearance leftResolution
      rightResolution dominance rest =>
      exact Dense.Rational.Sign.Pair.Resolution.certificate?_isSome_of_pairResolution_of_first_none
        leftClearance leftResolution firstNone

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Resolution.Bounds

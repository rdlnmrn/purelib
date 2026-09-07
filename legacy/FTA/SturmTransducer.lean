import FTA.SafeCandidates
import FTA.RationalPolynomialBounds
import FTA.Sturm
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Rat.Floor

/-!
# Finite one-dimensional Sturm transducers

This module packages the executable ingredients of Definition 3.3.  A single
dense guard polynomial is the product of every nonzero member of the signed
derivative chain.  The bounded central-third search therefore chooses a
rational cut avoiding every chain event at once.  Count-one refinement then
selects the unique child labelled one, with its count-splitting fact supplied
by the finite Sturm event decomposition.

No completed real zero is a field of any structure below: observations are
only rational intervals, exact endpoint evaluations, finite signed-variation
counts, and refinement proofs.
-/

namespace FTA.SturmTransducer

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.DenseDerivative
open FTA.DenseSquarefree
open FTA.SafeCandidates
open FTA.RationalPolynomialBounds
open FTA.Sturm

abbrev RatPolynomial := DensePolynomial ℚ

/-- Dense product of a finite polynomial list. -/
def polynomialProduct : List RatPolynomial → RatPolynomial
  | [] => constant 1
  | p :: ps => p * polynomialProduct ps

@[simp] theorem polynomialProduct_eval (ps : List RatPolynomial) (x : ℚ) :
    (polynomialProduct ps).eval x = (ps.map fun p => p.eval x).prod := by
  induction ps with
  | nil => simp [polynomialProduct]
  | cons p ps ih => simp [polynomialProduct, ih]

theorem polynomialProduct_toPolynomial_ne_zero {ps : List RatPolynomial}
    (hps : ps.Forall (fun p => p.isZero = false)) :
    (polynomialProduct ps).toPolynomial ≠ 0 := by
  induction ps with
  | nil => simp [polynomialProduct]
  | cons p ps ih =>
      simp only [List.forall_cons] at hps
      rw [polynomialProduct, toPolynomial_mul]
      exact mul_ne_zero (toPolynomial_ne_zero_of_isZero_false hps.1) (ih hps.2)

theorem polynomialProduct_isZero_false {ps : List RatPolynomial}
    (hps : ps.Forall (fun p => p.isZero = false)) :
    (polynomialProduct ps).isZero = false := by
  have hspec := polynomialProduct_toPolynomial_ne_zero hps
  cases hzero : (polynomialProduct ps).isZero with
  | false => rfl
  | true =>
      exact (hspec ((toPolynomial_eq_zero_iff_isZero _).mpr hzero)).elim

theorem eval_ne_zero_of_mem_of_polynomialProduct_ne_zero
    {ps : List RatPolynomial} {p : RatPolynomial} {x : ℚ}
    (hp : p ∈ ps) (hproduct : (polynomialProduct ps).eval x ≠ 0) :
    p.eval x ≠ 0 := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      have hq : q.eval x ≠ 0 := by
        intro hzero
        apply hproduct
        simp [polynomialProduct, hzero]
      have hqs : (polynomialProduct qs).eval x ≠ 0 := by
        intro hzero
        apply hproduct
        simp [polynomialProduct, hzero]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq
      · exact ih hp hqs

/-- Signed derivative chain whose endpoint variation computes the doubled
Sturm count. -/
def derivativeChain (p : RatPolynomial) : List RatPolynomial :=
  p :: cauchyChain (derivative p) p

/-- One polynomial vanishing exactly when at least one derivative-chain
member vanishes. -/
def chainGuard (p : RatPolynomial) : RatPolynomial :=
  polynomialProduct (derivativeChain p)

theorem derivativeChain_all_nonzero {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    (derivativeChain p).Forall (fun q => q.isZero = false) := by
  simp only [derivativeChain, List.forall_cons, hp, true_and, cauchyChain,
    reducedDenominator, reducedNumerator]
  apply signedRemainderChain_all_nonzero
  · exact FTA.DenseGCD.symmetricRightFactor_isZero_false hp
  · exact FTA.DenseGCD.symmetricLeftFactor_isZero_false
      (derivative_isZero_false hp hdegree)

theorem chainGuard_isZero_false {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    (chainGuard p).isZero = false :=
  polynomialProduct_isZero_false (derivativeChain_all_nonzero hp hdegree)

theorem chainGuard_toPolynomial_ne_zero {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) :
    (chainGuard p).toPolynomial ≠ 0 :=
  toPolynomial_ne_zero_of_isZero_false (chainGuard_isZero_false hp hdegree)

/-- The finite data fixed for a squarefree one-dimensional run. -/
structure SquarefreeInput (p : RatPolynomial) where
  nonzero : p.isZero = false
  nonconstant : p.natDegree ≠ 0
  squarefree : SquarefreeCertificate p

/-- Every represented nonzero nonconstant rational polynomial therefore
supplies an executable squarefree input for its gcd-reduced first member. -/
def squarefreePartInput (p : RatPolynomial) (hp : p.isZero = false)
    (hdegree : p.natDegree ≠ 0) : SquarefreeInput (squarefreePart p) where
  nonzero := squarefreePart_isZero_false hp
  nonconstant := squarefreePart_natDegree_ne_zero hp hdegree
  squarefree := squarefreePartCertificate hp hdegree

/-- Bounded search for the first central-third point avoiding every member of
the derivative chain. -/
def safeCut? (p : RatPolynomial) (a b : ℚ) : Option ℚ :=
  centralSearch (chainGuard p) a b (chainGuard p).natDegree

/-- Total executable cut, with a midpoint default that is unreachable under
the proved nonzero/nonconstant hypotheses. -/
def safeCut (p : RatPolynomial) (a b : ℚ) : ℚ :=
  (safeCut? p a b).getD ((a + b) / 2)

theorem safeCut_search_succeeds {p : RatPolynomial} (input : SquarefreeInput p)
    {a b : ℚ} (hab : a < b) : ∃ c, safeCut? p a b = some c := by
  apply centralSearch_succeeds (chainGuard p) (chainGuard p).natDegree hab
    (chainGuard_toPolynomial_ne_zero input.nonzero input.nonconstant)
  rw [natDegree_toPolynomial (chainGuard_isZero_false input.nonzero input.nonconstant)]

theorem safeCut_spec {p : RatPolynomial} (input : SquarefreeInput p)
    {a b : ℚ} (hab : a < b) :
    (chainGuard p).eval (safeCut p a b) ≠ 0 ∧
      centralLeft a b < safeCut p a b ∧ safeCut p a b < centralRight a b := by
  rcases safeCut_search_succeeds input hab with ⟨c, hc⟩
  rcases centralSearch_some_spec hab hc with ⟨-, hguard, hleft, hright⟩
  have hcut : safeCut p a b = c := by simp [safeCut, hc]
  rw [hcut]
  exact ⟨hguard, hleft, hright⟩

theorem safeCut_avoids_chain {p : RatPolynomial} (input : SquarefreeInput p)
    {a b : ℚ} (hab : a < b) {q : RatPolynomial}
    (hq : q ∈ derivativeChain p) : q.eval (safeCut p a b) ≠ 0 := by
  apply eval_ne_zero_of_mem_of_polynomialProduct_ne_zero hq
  exact (safeCut_spec input hab).1

theorem safeCut_polynomial_ne_zero {p : RatPolynomial} (input : SquarefreeInput p)
    {a b : ℚ} (hab : a < b) : p.eval (safeCut p a b) ≠ 0 := by
  apply safeCut_avoids_chain input hab
  simp [derivativeChain]

/-- Closed rational interval record. -/
structure RationalInterval where
  lower : ℚ
  upper : ℚ
deriving DecidableEq, Repr

namespace RationalInterval

def Proper (I : RationalInterval) : Prop := I.lower < I.upper

def width (I : RationalInterval) : ℚ := I.upper - I.lower

def Refines (J I : RationalInterval) : Prop :=
  I.lower ≤ J.lower ∧ J.upper ≤ I.upper

def left (I : RationalInterval) (c : ℚ) : RationalInterval := ⟨I.lower, c⟩

def right (I : RationalInterval) (c : ℚ) : RationalInterval := ⟨c, I.upper⟩

theorem width_pos {I : RationalInterval} (hI : I.Proper) : 0 < I.width := by
  exact sub_pos.mpr hI

theorem refines_refl (I : RationalInterval) : I.Refines I := ⟨le_rfl, le_rfl⟩

theorem refines_trans {I J K : RationalInterval}
    (hKJ : K.Refines J) (hJI : J.Refines I) : K.Refines I :=
  ⟨hJI.1.trans hKJ.1, hKJ.2.trans hJI.2⟩

theorem midpointRadius_eq_half_width {I : RationalInterval} (proper : I.Proper) :
    intervalRadius I.lower I.upper (midpoint I.lower I.upper) = I.width / 2 := by
  simpa [width] using intervalRadius_midpoint proper.le

theorem intervalMagnitude_le_of_refines {I root : RationalInterval}
    (hrefines : I.Refines root) (proper : I.Proper) :
    intervalMagnitude I.lower I.upper ≤
      intervalMagnitude root.lower root.upper :=
  intervalMagnitude_mono_of_nested hrefines.1 proper.le hrefines.2

end RationalInterval

/-- Proof-relevant finite list of whole-cell strict-sign certificates. -/
inductive ChainSignCertificates (a b : ℚ) : List RatPolynomial → Type
  | nil : ChainSignCertificates a b []
  | cons {p : RatPolynomial} {chain : List RatPolynomial}
      (head : IntervalSignCertificate p a b)
      (tail : ChainSignCertificates a b chain) :
      ChainSignCertificates a b (p :: chain)

/-- Executably classify every member of a finite polynomial list at the
common rational midpoint. -/
def chainSignCertificates? (a b : ℚ) (hab : a < b) :
    (chain : List RatPolynomial) → Option (ChainSignCertificates a b chain)
  | [] => some .nil
  | p :: chain =>
      match midpointSignCertificate? p a b hab with
      | none => none
      | some head =>
          match chainSignCertificates? a b hab chain with
          | none => none
          | some tail => some (.cons head tail)

namespace ChainSignCertificates

theorem endpoint_signs {a b : ℚ} {chain : List RatPolynomial}
    (certificates : ChainSignCertificates a b chain) :
    List.Forall₂ (fun x y => ratSign x = ratSign y)
      (chain.map fun p => p.eval a) (chain.map fun p => p.eval b) := by
  induction certificates with
  | nil => exact .nil
  | cons head tail ih =>
      apply List.Forall₂.cons
      · apply ratSign_eq_of_mul_pos
        exact head.eval_mul_pos_between le_rfl
          (head.lowerLe.trans head.leUpper)
          (head.lowerLe.trans head.leUpper) le_rfl
      · exact ih

theorem endpointVariation_eq {a b : ℚ} {chain : List RatPolynomial}
    (certificates : ChainSignCertificates a b chain) :
    endpointVariation2 chain a = endpointVariation2 chain b := by
  apply variation2_congr_of_forall₂_sign
  exact certificates.endpoint_signs

/-- Whole-cell strict-sign certificates for an arbitrary complete Cauchy
chain force its doubled index to vanish. -/
theorem cauchyIndex2_eq_zero {R S : RatPolynomial} {a b : ℚ}
    (certificates : ChainSignCertificates a b (cauchyChain R S)) :
    cauchyIndex2 R S a b = 0 := by
  by_cases hzero : R.isZero || S.isZero
  · simp [cauchyIndex2, hzero]
  · rw [cauchyIndex2, if_neg hzero, certificates.endpointVariation_eq]
    norm_num

theorem sturmRootCount2_eq_zero {p : RatPolynomial} {a b : ℚ}
    (certificates : ChainSignCertificates a b (cauchyChain (derivative p) p)) :
    sturmRootCount2 p a b = 0 := by
  rw [sturmRootCount2]
  by_cases hzero : (derivative p).isZero || p.isZero
  · simp [cauchyIndex2, hzero]
  · rw [cauchyIndex2, if_neg hzero, certificates.endpointVariation_eq]
    norm_num

end ChainSignCertificates

/-- A finite local signed-remainder event cell.  Both outer members have
coefficient-certified fixed signs, and the quotient-times-middle term is
strictly dominated at the rational midpoint. -/
structure SignedStepCellCertificate (p q : RatPolynomial)
    (interval : RationalInterval) where
  proper : interval.Proper
  leftStable : IntervalSignCertificate p interval.lower interval.upper
  rightStable : IntervalSignCertificate
    (-((divMod p q).remainder)) interval.lower interval.upper
  midpointDominance :
    |q.eval (midpoint interval.lower interval.upper) *
        (divMod p q).quotient.eval (midpoint interval.lower interval.upper)| <
      |(-((divMod p q).remainder)).eval
        (midpoint interval.lower interval.upper)|

/-- Executable local signed-step classifier.  It checks two midpoint sign
margins and the exact recurrence domination inequality. -/
def signedStepCellCertificate? (p q : RatPolynomial)
    (interval : RationalInterval) (proper : interval.Proper) :
    Option (SignedStepCellCertificate p q interval) :=
  let sample := midpoint interval.lower interval.upper
  let B := intervalMagnitude interval.lower interval.upper
  let radius := intervalRadius interval.lower interval.upper sample
  let next := -((divMod p q).remainder)
  if hleft : denseEvalLipschitzBound p B * radius < |p.eval sample| then
    if hright : denseEvalLipschitzBound next B * radius < |next.eval sample| then
      if hdominance : |q.eval sample * (divMod p q).quotient.eval sample| <
          |next.eval sample| then
        some
          { proper := proper
            leftStable :=
              { sample := sample
                lowerLe := (lower_lt_midpoint proper).le
                leUpper := (midpoint_lt_upper proper).le
                margin := hleft }
            rightStable :=
              { sample := sample
                lowerLe := (lower_lt_midpoint proper).le
                leUpper := (midpoint_lt_upper proper).le
                margin := hright }
            midpointDominance := hdominance }
      else none
    else none
  else none

/-- Construct an interior signed-step certificate when the middle member
crosses the cell.  The two transported Bézout radii stabilize both outer
members, while a finite quotient bound makes the recurrence term smaller
than the right outer margin. -/
def signedStepCellCertificateOfMiddleCrossing {p q : RatPolynomial}
    (coprime : CoprimeCertificate p q) (interval : RationalInterval)
    (proper : interval.Proper)
    (crossing : q.eval interval.lower * q.eval interval.upper < 0)
    (leftBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.swap interval.lower interval.upper)
    (rightBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.signedStep interval.lower interval.upper)
    (dominanceSmall :
      denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) *
          denseEvalAbsBound (divMod p q).quotient
            (intervalMagnitude interval.lower interval.upper) <
        coprimeExclusionMargin coprime.signedStep
          (intervalMagnitude interval.lower interval.upper)) :
    SignedStepCellCertificate p q interval := by
  let sample := midpoint interval.lower interval.upper
  let B := intervalMagnitude interval.lower interval.upper
  let radius := intervalRadius interval.lower interval.upper sample
  let next := -((divMod p q).remainder)
  have hB : 0 ≤ B := (intervalMagnitude_pos _ _).le
  have hsampleB : |sample| ≤ B :=
    abs_le_intervalMagnitude (lower_lt_midpoint proper).le
      (midpoint_lt_upper proper).le
  have hleft : denseEvalLipschitzBound p B * radius < |p.eval sample| :=
    secondMidpointMarginOfFirstEndpointCrossing coprime.swap proper
      (by simpa [B, radius, sample] using leftBezoutSmall) crossing
  have hright : denseEvalLipschitzBound next B * radius < |next.eval sample| :=
    secondMidpointMarginOfFirstEndpointCrossing coprime.signedStep proper
      (by simpa [B, radius, sample, next] using rightBezoutSmall) crossing
  have hnextMargin : coprimeExclusionMargin coprime.signedStep B ≤
      |next.eval sample| :=
    coprimeExclusionMargin_le_abs_second_midpoint_of_first_crossing
      coprime.signedStep proper
      (by simpa [B, radius, sample, next] using rightBezoutSmall) crossing
  have hqBound : |q.eval sample| ≤ denseEvalLipschitzBound q B * radius :=
    abs_dense_eval_sample_le_lipschitz_radius_of_endpoint_crossing q proper
      (lower_lt_midpoint proper).le (midpoint_lt_upper proper).le crossing
  have hquotientBound : |(divMod p q).quotient.eval sample| ≤
      denseEvalAbsBound (divMod p q).quotient B :=
    abs_dense_eval_le_denseEvalAbsBound (divMod p q).quotient hB hsampleB
  have hslopeNonneg : 0 ≤ denseEvalLipschitzBound q B :=
    (denseHornerBounds_nonneg q hB).2
  have hradiusNonneg : 0 ≤ radius := by
    dsimp [radius, intervalRadius]
    positivity
  have hquotientNonneg : 0 ≤ denseEvalAbsBound (divMod p q).quotient B :=
    (denseHornerBounds_nonneg (divMod p q).quotient hB).1
  have hdominance : |q.eval sample * (divMod p q).quotient.eval sample| <
      |next.eval sample| := by
    rw [abs_mul]
    calc
      |q.eval sample| * |(divMod p q).quotient.eval sample| ≤
          (denseEvalLipschitzBound q B * radius) *
            denseEvalAbsBound (divMod p q).quotient B :=
        mul_le_mul hqBound hquotientBound (abs_nonneg _)
          (mul_nonneg hslopeNonneg hradiusNonneg)
      _ < coprimeExclusionMargin coprime.signedStep B := by
        simpa [B, radius, sample] using dominanceSmall
      _ ≤ |next.eval sample| := hnextMargin
  exact
    { proper
      leftStable :=
        { sample
          lowerLe := (lower_lt_midpoint proper).le
          leUpper := (midpoint_lt_upper proper).le
          margin := hleft }
      rightStable :=
        { sample
          lowerLe := (lower_lt_midpoint proper).le
          leUpper := (midpoint_lt_upper proper).le
          margin := hright }
      midpointDominance := hdominance }

/-- The executable signed-step classifier succeeds under the displayed
interior-event resolution inequalities. -/
theorem signedStepCellCertificate?_isSome_of_middle_crossing
    {p q : RatPolynomial} (coprime : CoprimeCertificate p q)
    (interval : RationalInterval) (proper : interval.Proper)
    (crossing : q.eval interval.lower * q.eval interval.upper < 0)
    (leftBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.swap interval.lower interval.upper)
    (rightBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.signedStep interval.lower interval.upper)
    (dominanceSmall :
      denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) *
          denseEvalAbsBound (divMod p q).quotient
            (intervalMagnitude interval.lower interval.upper) <
        coprimeExclusionMargin coprime.signedStep
          (intervalMagnitude interval.lower interval.upper)) :
    (signedStepCellCertificate? p q interval proper).isSome = true := by
  let certificate := signedStepCellCertificateOfMiddleCrossing coprime interval
    proper crossing leftBezoutSmall rightBezoutSmall dominanceSmall
  have hleft :
      denseEvalLipschitzBound p
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |p.eval (midpoint interval.lower interval.upper)| := by
    exact secondMidpointMarginOfFirstEndpointCrossing coprime.swap proper
      leftBezoutSmall crossing
  have hright :
      denseEvalLipschitzBound (-((divMod p q).remainder))
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |(-((divMod p q).remainder)).eval
          (midpoint interval.lower interval.upper)| := by
    exact secondMidpointMarginOfFirstEndpointCrossing coprime.signedStep proper
      rightBezoutSmall crossing
  have hdominance := certificate.midpointDominance
  have hright' :
      denseEvalLipschitzBound (-((divMod p q).remainder))
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |(divMod p q).remainder.eval
          (midpoint interval.lower interval.upper)| := by
    simpa using hright
  have hdominance' :
      |q.eval (midpoint interval.lower interval.upper)| *
          |(divMod p q).quotient.eval
            (midpoint interval.lower interval.upper)| <
        |(divMod p q).remainder.eval
          (midpoint interval.lower interval.upper)| := by
    simpa [abs_mul] using hdominance
  simp [signedStepCellCertificate?, hleft, hright', hdominance']

/-- Construct the same signed-step certificate directly from failure of the
middle member's midpoint sign test.  This covers both sign crossings and
even-multiplicity tangencies. -/
def signedStepCellCertificateOfMiddleUnresolved {p q : RatPolynomial}
    (coprime : CoprimeCertificate p q) (interval : RationalInterval)
    (proper : interval.Proper)
    (middleUnresolved :
      ¬(denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |q.eval (midpoint interval.lower interval.upper)|))
    (leftBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.swap interval.lower interval.upper)
    (rightBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.signedStep interval.lower interval.upper)
    (dominanceSmall :
      denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) *
          denseEvalAbsBound (divMod p q).quotient
            (intervalMagnitude interval.lower interval.upper) <
        coprimeExclusionMargin coprime.signedStep
          (intervalMagnitude interval.lower interval.upper)) :
    SignedStepCellCertificate p q interval := by
  let sample := midpoint interval.lower interval.upper
  let B := intervalMagnitude interval.lower interval.upper
  let radius := intervalRadius interval.lower interval.upper sample
  let next := -((divMod p q).remainder)
  have hB : 0 ≤ B := (intervalMagnitude_pos _ _).le
  have hsampleB : |sample| ≤ B :=
    abs_le_intervalMagnitude (lower_lt_midpoint proper).le
      (midpoint_lt_upper proper).le
  have hleft : denseEvalLipschitzBound p B * radius < |p.eval sample| :=
    secondMidpointMarginOfFirstUnresolved coprime.swap proper
      (by simpa [B, radius, sample] using leftBezoutSmall)
      (by simpa [B, radius, sample] using middleUnresolved)
  have hright : denseEvalLipschitzBound next B * radius < |next.eval sample| :=
    secondMidpointMarginOfFirstUnresolved coprime.signedStep proper
      (by simpa [B, radius, sample, next] using rightBezoutSmall)
      (by simpa [B, radius, sample, next] using middleUnresolved)
  have hnextMargin : coprimeExclusionMargin coprime.signedStep B ≤
      |next.eval sample| :=
    coprimeExclusionMargin_le_abs_second_midpoint_of_first_unresolved
      coprime.signedStep proper
      (by simpa [B, radius, sample, next] using rightBezoutSmall)
      (by simpa [B, radius, sample, next] using middleUnresolved)
  have hqBound : |q.eval sample| ≤ denseEvalLipschitzBound q B * radius := by
    exact le_of_not_gt (by simpa [B, radius, sample] using middleUnresolved)
  have hquotientBound : |(divMod p q).quotient.eval sample| ≤
      denseEvalAbsBound (divMod p q).quotient B :=
    abs_dense_eval_le_denseEvalAbsBound (divMod p q).quotient hB hsampleB
  have hslopeNonneg : 0 ≤ denseEvalLipschitzBound q B :=
    (denseHornerBounds_nonneg q hB).2
  have hradiusNonneg : 0 ≤ radius := by
    dsimp [radius, intervalRadius]
    positivity
  have hdominance : |q.eval sample * (divMod p q).quotient.eval sample| <
      |next.eval sample| := by
    rw [abs_mul]
    calc
      |q.eval sample| * |(divMod p q).quotient.eval sample| ≤
          (denseEvalLipschitzBound q B * radius) *
            denseEvalAbsBound (divMod p q).quotient B :=
        mul_le_mul hqBound hquotientBound (abs_nonneg _)
          (mul_nonneg hslopeNonneg hradiusNonneg)
      _ < coprimeExclusionMargin coprime.signedStep B := by
        simpa [B, radius, sample] using dominanceSmall
      _ ≤ |next.eval sample| := hnextMargin
  exact
    { proper
      leftStable :=
        { sample
          lowerLe := (lower_lt_midpoint proper).le
          leUpper := (midpoint_lt_upper proper).le
          margin := hleft }
      rightStable :=
        { sample
          lowerLe := (lower_lt_midpoint proper).le
          leUpper := (midpoint_lt_upper proper).le
          margin := hright }
      midpointDominance := hdominance }

/-- The executable signed-step branch succeeds whenever the immediately
preceding midpoint sign branch fails below the explicit local radii. -/
theorem signedStepCellCertificate?_isSome_of_middle_unresolved
    {p q : RatPolynomial} (coprime : CoprimeCertificate p q)
    (interval : RationalInterval) (proper : interval.Proper)
    (middleUnresolved :
      ¬(denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |q.eval (midpoint interval.lower interval.upper)|))
    (leftBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.swap interval.lower interval.upper)
    (rightBezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.signedStep interval.lower interval.upper)
    (dominanceSmall :
      denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) *
          denseEvalAbsBound (divMod p q).quotient
            (intervalMagnitude interval.lower interval.upper) <
        coprimeExclusionMargin coprime.signedStep
          (intervalMagnitude interval.lower interval.upper)) :
    (signedStepCellCertificate? p q interval proper).isSome = true := by
  let certificate := signedStepCellCertificateOfMiddleUnresolved coprime interval
    proper middleUnresolved leftBezoutSmall rightBezoutSmall dominanceSmall
  have hleft :
      denseEvalLipschitzBound p
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |p.eval (midpoint interval.lower interval.upper)| :=
    secondMidpointMarginOfFirstUnresolved coprime.swap proper
      leftBezoutSmall middleUnresolved
  have hright :
      denseEvalLipschitzBound (-((divMod p q).remainder))
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |(-((divMod p q).remainder)).eval
          (midpoint interval.lower interval.upper)| :=
    secondMidpointMarginOfFirstUnresolved coprime.signedStep proper
      rightBezoutSmall middleUnresolved
  have hdominance := certificate.midpointDominance
  have hright' :
      denseEvalLipschitzBound (-((divMod p q).remainder))
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
        |(divMod p q).remainder.eval
          (midpoint interval.lower interval.upper)| := by
    simpa using hright
  have hdominance' :
      |q.eval (midpoint interval.lower interval.upper)| *
          |(divMod p q).quotient.eval
            (midpoint interval.lower interval.upper)| <
        |(divMod p q).remainder.eval
          (midpoint interval.lower interval.upper)| := by
    simpa [abs_mul] using hdominance
  simp [signedStepCellCertificate?, hleft, hright', hdominance']

namespace SignedStepCellCertificate

theorem outer_midpoint_mul_neg {p q : RatPolynomial}
    {interval : RationalInterval}
    (certificate : SignedStepCellCertificate p q interval) :
    p.eval (midpoint interval.lower interval.upper) *
        (-((divMod p q).remainder)).eval
          (midpoint interval.lower interval.upper) < 0 := by
  let sample := midpoint interval.lower interval.upper
  let next := -((divMod p q).remainder)
  have hstep := signedStep_eval_identity p q sample
  have hclose : |(-next.eval sample) - p.eval sample| < |-next.eval sample| := by
    calc
      |(-next.eval sample) - p.eval sample| =
          |-(q.eval sample * (divMod p q).quotient.eval sample)| := by
        rw [hstep]
        congr 1
        dsimp [next]
        ring
      _ = |q.eval sample * (divMod p q).quotient.eval sample| := abs_neg _
      _ < |next.eval sample| := by
        simpa [sample, next] using certificate.midpointDominance
      _ = |-next.eval sample| := (abs_neg _).symm
  have hsame := mul_pos_of_abs_sub_lt_abs_left hclose
  change p.eval sample * next.eval sample < 0
  calc
    p.eval sample * next.eval sample = -((-next.eval sample) * p.eval sample) := by
      ring
    _ < 0 := neg_neg_of_pos hsame

theorem outer_mul_neg {p q : RatPolynomial} {interval : RationalInterval}
    (certificate : SignedStepCellCertificate p q interval) {t : ℚ}
    (hlower : interval.lower ≤ t) (hupper : t ≤ interval.upper) :
    p.eval t * (-((divMod p q).remainder)).eval t < 0 := by
  let sample := midpoint interval.lower interval.upper
  have hsampleLower : interval.lower ≤ sample :=
    (lower_lt_midpoint certificate.proper).le
  have hsampleUpper : sample ≤ interval.upper :=
    (midpoint_lt_upper certificate.proper).le
  have hleft := certificate.leftStable.eval_mul_pos_between
    hsampleLower hsampleUpper hlower hupper
  have hright := certificate.rightStable.eval_mul_pos_between
    hsampleLower hsampleUpper hlower hupper
  exact mul_neg_of_same_sign_transfers hleft hright
    certificate.outer_midpoint_mul_neg

/-- Local signed-remainder cancellation without an exact zero: throughout a
certified cell, the two adjacent doubled jumps always sum to two. -/
theorem local_jump_sum {p q : RatPolynomial} {interval : RationalInterval}
    (certificate : SignedStepCellCertificate p q interval) {t : ℚ}
    (hlower : interval.lower ≤ t) (hupper : t ≤ interval.upper) :
    signJump (p.eval t) (q.eval t) +
        signJump (q.eval t) ((-((divMod p q).remainder)).eval t) = 2 :=
  signJump_add_signJump_of_outer_mul_neg
    (certificate.outer_mul_neg hlower hupper)

/-- Consequently this interior chain position contributes the same amount at
both endpoints and cancels from the interval variation difference. -/
theorem endpoint_cancellation {p q : RatPolynomial}
    {interval : RationalInterval}
    (certificate : SignedStepCellCertificate p q interval) :
    signJump (p.eval interval.lower) (q.eval interval.lower) +
        signJump (q.eval interval.lower)
          ((-((divMod p q).remainder)).eval interval.lower) =
      signJump (p.eval interval.upper) (q.eval interval.upper) +
        signJump (q.eval interval.upper)
          ((-((divMod p q).remainder)).eval interval.upper) := by
  rw [certificate.local_jump_sum le_rfl certificate.proper.le,
    certificate.local_jump_sum certificate.proper.le le_rfl]

theorem of_classifier_endpoint_cancellation {p q : RatPolynomial}
    {interval : RationalInterval} {proper : interval.Proper}
    {certificate : SignedStepCellCertificate p q interval}
    (_hclassified : signedStepCellCertificate? p q interval proper =
      some certificate) :
    signJump (p.eval interval.lower) (q.eval interval.lower) +
        signJump (q.eval interval.lower)
          ((-((divMod p q).remainder)).eval interval.lower) =
      signJump (p.eval interval.upper) (q.eval interval.upper) +
        signJump (q.eval interval.upper)
          ((-((divMod p q).remainder)).eval interval.upper) :=
  certificate.endpoint_cancellation

end SignedStepCellCertificate

/-! ## Recursive neutral signed-chain certificates -/

/-- Exact strict inequality tested by the executable midpoint sign branch. -/
def MidpointResolved (interval : RationalInterval) (p : RatPolynomial) : Prop :=
  denseEvalLipschitzBound p
        (intervalMagnitude interval.lower interval.upper) *
      intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
    |p.eval (midpoint interval.lower interval.upper)|

instance midpointResolvedDecidable (interval : RationalInterval)
    (p : RatPolynomial) : Decidable (MidpointResolved interval p) := by
  unfold MidpointResolved
  infer_instance

def midpointResolvedCertificate (interval : RationalInterval)
    (proper : interval.Proper) (p : RatPolynomial)
    (resolved : MidpointResolved interval p) :
    IntervalSignCertificate p interval.lower interval.upper where
  sample := midpoint interval.lower interval.upper
  lowerLe := (lower_lt_midpoint proper).le
  leUpper := (midpoint_lt_upper proper).le
  margin := resolved

theorem midpointSignCertificate?_eq_some_of_resolved
    (interval : RationalInterval) (proper : interval.Proper)
    (p : RatPolynomial) (resolved : MidpointResolved interval p) :
    midpointSignCertificate? p interval.lower interval.upper proper =
      some (midpointResolvedCertificate interval proper p resolved) := by
  change denseEvalLipschitzBound p
        (intervalMagnitude interval.lower interval.upper) *
      intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
    |p.eval (midpoint interval.lower interval.upper)| at resolved
  simp [midpointSignCertificate?, midpointResolvedCertificate, resolved]

/-- A coefficient-resolved midpoint gives equal strict endpoint signs. -/
theorem eval_lower_mul_eval_upper_pos_of_midpointResolved
    (interval : RationalInterval) (proper : interval.Proper)
    (p : RatPolynomial) (resolved : MidpointResolved interval p) :
    0 < p.eval interval.lower * p.eval interval.upper := by
  let certificate := midpointResolvedCertificate interval proper p resolved
  exact certificate.eval_mul_pos_between le_rfl
    (certificate.lowerLe.trans certificate.leUpper)
    (certificate.lowerLe.trans certificate.leUpper) le_rfl

/-- A nonempty signed chain whose first member has a fixed sign and whose
interior crossing events cancel in disjoint signed triples.  The `event`
constructor consumes two jumps and then continues from the stable right
outer member, so simultaneous events at nonadjacent chain positions are
handled without an invalid pairwise-separation assumption. -/
inductive NeutralChainCertificate (interval : RationalInterval) :
    (head : RatPolynomial) → (tail : List RatPolynomial) → Type
  | single {p : RatPolynomial}
      (headStable : IntervalSignCertificate p interval.lower interval.upper) :
      NeutralChainCertificate interval p []
  | stable {p q : RatPolynomial} {tail : List RatPolynomial}
      (headStable : IntervalSignCertificate p interval.lower interval.upper)
      (rest : NeutralChainCertificate interval q tail) :
      NeutralChainCertificate interval p (q :: tail)
  | event {p q r : RatPolynomial} {tail : List RatPolynomial}
      (nextEq : r = -((divMod p q).remainder))
      (step : SignedStepCellCertificate p q interval)
      (rest : NeutralChainCertificate interval r tail) :
      NeutralChainCertificate interval p (q :: r :: tail)

namespace NeutralChainCertificate

def headStable {interval : RationalInterval} {p : RatPolynomial}
    {tail : List RatPolynomial}
    (certificate : NeutralChainCertificate interval p tail) :
    IntervalSignCertificate p interval.lower interval.upper :=
  match certificate with
  | .single headCertificate => headCertificate
  | .stable headCertificate .. => headCertificate
  | .event _ step .. => step.leftStable

theorem headEndpointSign_eq {interval : RationalInterval} {p : RatPolynomial}
    {tail : List RatPolynomial}
    (certificate : NeutralChainCertificate interval p tail) :
    ratSign (p.eval interval.lower) = ratSign (p.eval interval.upper) := by
  apply ratSign_eq_of_mul_pos
  exact certificate.headStable.eval_mul_pos_between le_rfl
    (certificate.headStable.lowerLe.trans certificate.headStable.leUpper)
    (certificate.headStable.lowerLe.trans certificate.headStable.leUpper) le_rfl

/-- Every finite family of locally certified interior signed events has zero
net endpoint-variation change, including coincident nonadjacent events. -/
theorem endpointVariation_eq {interval : RationalInterval} {p : RatPolynomial}
    {tail : List RatPolynomial}
    (certificate : NeutralChainCertificate interval p tail) :
    endpointVariation2 (p :: tail) interval.lower =
      endpointVariation2 (p :: tail) interval.upper := by
  induction certificate with
  | single headStable => simp [endpointVariation2]
  | @stable p q tail headStable rest ih =>
      have hp : ratSign (p.eval interval.lower) =
          ratSign (p.eval interval.upper) := by
        apply ratSign_eq_of_mul_pos
        exact headStable.eval_mul_pos_between le_rfl
          (headStable.lowerLe.trans headStable.leUpper)
          (headStable.lowerLe.trans headStable.leUpper) le_rfl
      have hq := rest.headEndpointSign_eq
      change signJump (p.eval interval.lower) (q.eval interval.lower) +
          endpointVariation2 (q :: tail) interval.lower =
        signJump (p.eval interval.upper) (q.eval interval.upper) +
          endpointVariation2 (q :: tail) interval.upper
      rw [signJump_congr hp hq, ih]
  | @event p q r tail nextEq step rest ih =>
      subst r
      have hlocal := step.endpoint_cancellation
      change
        signJump (p.eval interval.lower) (q.eval interval.lower) +
            (signJump (q.eval interval.lower)
                ((-((divMod p q).remainder)).eval interval.lower) +
              endpointVariation2
                ((-((divMod p q).remainder)) :: tail) interval.lower) =
          signJump (p.eval interval.upper) (q.eval interval.upper) +
            (signJump (q.eval interval.upper)
                ((-((divMod p q).remainder)).eval interval.upper) +
              endpointVariation2
                ((-((divMod p q).remainder)) :: tail) interval.upper)
      omega

end NeutralChainCertificate

/-- Executable recursive scan for an arbitrary number of neutral interior
events.  A stable head advances one position; a changing middle member is
certified by a signed triple and advances two positions. -/
def neutralChainCertificate? (interval : RationalInterval)
    (proper : interval.Proper) (head : RatPolynomial) :
    (tail : List RatPolynomial) →
      Option (NeutralChainCertificate interval head tail)
  | [] =>
      match midpointSignCertificate? head interval.lower interval.upper proper with
      | some headStable => some (.single headStable)
      | none => none
  | q :: tail =>
      match midpointSignCertificate? head interval.lower interval.upper proper with
      | none => none
      | some headStable =>
          match tail with
          | [] =>
              match midpointSignCertificate? q interval.lower interval.upper proper with
              | some qStable => some (.stable headStable (.single qStable))
              | none => none
          | r :: suffix =>
              match midpointSignCertificate? q interval.lower interval.upper proper with
              | some _qStable =>
                  match neutralChainCertificate? interval proper q (r :: suffix) with
                  | some rest => some (.stable headStable rest)
                  | none => none
              | none =>
                  if hnext : r = -((divMod head q).remainder) then
                    match signedStepCellCertificate? head q interval proper with
                    | some step =>
                        match neutralChainCertificate? interval proper r suffix with
                        | some rest => some (.event hnext step rest)
                        | none => none
                    | none => none
                  else none

/-- Empty-or-nonempty wrapper for recursive neutral certificates. -/
inductive NeutralChainCertificates (interval : RationalInterval) :
    List RatPolynomial → Type
  | nil : NeutralChainCertificates interval []
  | cons {head : RatPolynomial} {tail : List RatPolynomial}
      (certificate : NeutralChainCertificate interval head tail) :
      NeutralChainCertificates interval (head :: tail)

def neutralChainCertificates? (interval : RationalInterval)
    (proper : interval.Proper) :
    (chain : List RatPolynomial) → Option (NeutralChainCertificates interval chain)
  | [] => some .nil
  | head :: tail =>
      match neutralChainCertificate? interval proper head tail with
      | some certificate => some (.cons certificate)
      | none => none

namespace NeutralChainCertificates

theorem endpointVariation_eq {interval : RationalInterval}
    {chain : List RatPolynomial}
    (certificates : NeutralChainCertificates interval chain) :
    endpointVariation2 chain interval.lower =
      endpointVariation2 chain interval.upper := by
  cases certificates with
  | nil => rfl
  | cons certificate => exact certificate.endpointVariation_eq

/-- A neutral certificate for an arbitrary complete Cauchy chain proves that
its doubled Cauchy index is zero. -/
theorem cauchyIndex2_eq_zero {R S : RatPolynomial}
    {interval : RationalInterval}
    (certificates : NeutralChainCertificates interval (cauchyChain R S)) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  by_cases hzero : R.isZero || S.isZero
  · simp [cauchyIndex2, hzero]
  · rw [cauchyIndex2, if_neg hzero, certificates.endpointVariation_eq]
    norm_num

theorem sturmRootCount2_eq_zero {p : RatPolynomial}
    {interval : RationalInterval}
    (certificates : NeutralChainCertificates interval
      (cauchyChain (derivative p) p)) :
    sturmRootCount2 p interval.lower interval.upper = 0 := by
  rw [sturmRootCount2]
  by_cases hzero : (derivative p).isZero || p.isZero
  · simp [cauchyIndex2, hzero]
  · rw [cauchyIndex2, if_neg hzero, certificates.endpointVariation_eq]
    norm_num

end NeutralChainCertificates

/-! ## Proof-relevant local resolution bounds -/

/-- Width form of one signed-step ambient radius. -/
def ambientSignedStepWidthResolution {p q : RatPolynomial}
    (coprime : CoprimeCertificate p q) (root : RationalInterval) : ℚ :=
  2 * ambientSignedStepRadius coprime
    (intervalMagnitude root.lower root.upper)

theorem ambientSignedStepWidthResolution_pos {p q : RatPolynomial}
    (coprime : CoprimeCertificate p q) (root : RationalInterval) :
    0 < ambientSignedStepWidthResolution coprime root := by
  exact mul_pos (by norm_num) (ambientSignedStepRadius_pos coprime
    (intervalMagnitude_pos root.lower root.upper).le)

/-- Every proper refinement below the ambient width supplies exactly the
three local fields required by `NeutralChainResolutionBounds.step`. -/
theorem signedStep_inequalities_of_refined_width {p q : RatPolynomial}
    (coprime : CoprimeCertificate p q) (root interval : RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < ambientSignedStepWidthResolution coprime root) :
    intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.swap interval.lower interval.upper ∧
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius coprime.signedStep interval.lower interval.upper ∧
      denseEvalLipschitzBound q
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) *
          denseEvalAbsBound (divMod p q).quotient
            (intervalMagnitude interval.lower interval.upper) <
        coprimeExclusionMargin coprime.signedStep
          (intervalMagnitude interval.lower interval.upper) := by
  let rootB := intervalMagnitude root.lower root.upper
  have hmagnitude : intervalMagnitude interval.lower interval.upper ≤ rootB :=
    interval.intervalMagnitude_le_of_refines hrefines proper
  have hradiusNonneg : 0 ≤ intervalRadius interval.lower interval.upper
      (midpoint interval.lower interval.upper) := by
    dsimp [intervalRadius]
    positivity
  have hhalf : interval.width / 2 < ambientSignedStepRadius coprime rootB := by
    dsimp [ambientSignedStepWidthResolution] at hwidth
    linarith
  have hradius : intervalRadius interval.lower interval.upper
      (midpoint interval.lower interval.upper) <
        ambientSignedStepRadius coprime rootB := by
    rw [interval.midpointRadius_eq_half_width proper]
    exact hhalf
  exact signedStep_inequalities_of_ambient_radius coprime hmagnitude
    hradiusNonneg hradius

theorem second_natDegree_eq_zero_of_remainder_zero {p q : RatPolynomial}
    (coprime : CoprimeCertificate p q) (hq : q.isZero = false)
    (hremainder : (divMod p q).remainder.isZero = true) :
    q.natDegree = 0 := by
  have hremPoly := (toPolynomial_eq_zero_iff_isZero
    (divMod p q).remainder).2 hremainder
  have hdvd : q.toPolynomial ∣ p.toPolynomial := by
    refine ⟨(divMod p q).quotient.toPolynomial, ?_⟩
    rw [divMod_toPolynomial_equation p q, hremPoly, add_zero]
  have hunit := coprime.isCoprime.symm.isUnit_of_dvd hdvd
  have hdegree := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rwa [natDegree_toPolynomial hq] at hdegree

/-- Positive ambient radius for a complete signed Euclidean chain.  Each
nonterminal step takes the minimum of its local radius and the recursively
computed tail radius; the terminal nonzero constant uses its direct sign
radius. -/
def signedChainAmbientRadius (p q : RatPolynomial)
    (coprime : CoprimeCertificate p q) (B : ℚ) : ℚ :=
  if _hq : q.isZero then 1
  else if _hremainder : (divMod p q).remainder.isZero then
    ambientConstantSignRadius q B
  else
    min (ambientSignedStepRadius coprime B)
      (signedChainAmbientRadius q (-((divMod p q).remainder))
        coprime.signedStep B)
termination_by q.degreeCount
decreasing_by
  have hqFalse : q.isZero = false := by simpa using _hq
  have hrFalse : (divMod p q).remainder.isZero = false := by
    simpa using _hremainder
  rcases divMod_remainder_small p q hqFalse with hzero | hdegree
  · exact (_hremainder hzero).elim
  · have hrCount := natDegree_add_one_eq_degreeCount hrFalse
    have hqCount := natDegree_add_one_eq_degreeCount hqFalse
    rw [degreeCount_neg]
    omega

theorem signedChainAmbientRadius_pos (p q : RatPolynomial)
    (coprime : CoprimeCertificate p q) {B : ℚ} (hB : 0 ≤ B) :
    0 < signedChainAmbientRadius p q coprime B := by
  rw [signedChainAmbientRadius]
  split
  · norm_num
  · rename_i hq
    have hqFalse : q.isZero = false := by simpa using hq
    split
    · rename_i hremainder
      exact ambientConstantSignRadius_pos hqFalse
        (second_natDegree_eq_zero_of_remainder_zero coprime hqFalse
          (by simpa using hremainder))
    · apply lt_min
      · exact ambientSignedStepRadius_pos coprime hB
      · exact signedChainAmbientRadius_pos q (-((divMod p q).remainder))
          coprime.signedStep hB
termination_by q.degreeCount
decreasing_by
  rename_i hq hremainder
  have hqFalse : q.isZero = false := by simpa using hq
  have hrFalse : (divMod p q).remainder.isZero = false := by
    simpa using hremainder
  rcases divMod_remainder_small p q hqFalse with hzero | hdegree
  · exact (hremainder hzero).elim
  · have hrCount := natDegree_add_one_eq_degreeCount hrFalse
    have hqCount := natDegree_add_one_eq_degreeCount hqFalse
    rw [degreeCount_neg]
    omega

/-- Finite local inequalities sufficient for every branch of the neutral
chain scanner.  The list shape records the signed Euclidean recurrence, and
the tail field carries the remaining finite bounds. -/
inductive NeutralChainResolutionBounds (interval : RationalInterval) :
    (head : RatPolynomial) → (tail : List RatPolynomial) → Type
  | single {p : RatPolynomial} : NeutralChainResolutionBounds interval p []
  | pair {p q : RatPolynomial}
      (lastResolved : MidpointResolved interval q) :
      NeutralChainResolutionBounds interval p [q]
  | step {p q r : RatPolynomial} {suffix : List RatPolynomial}
      (nextEq : r = -((divMod p q).remainder))
      (coprime : CoprimeCertificate p q)
      (leftBezoutSmall :
        intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
          coprimeCellRadius coprime.swap interval.lower interval.upper)
      (rightBezoutSmall :
        intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) <
          coprimeCellRadius coprime.signedStep interval.lower interval.upper)
      (dominanceSmall :
        denseEvalLipschitzBound q
              (intervalMagnitude interval.lower interval.upper) *
            intervalRadius interval.lower interval.upper
              (midpoint interval.lower interval.upper) *
            denseEvalAbsBound (divMod p q).quotient
              (intervalMagnitude interval.lower interval.upper) <
          coprimeExclusionMargin coprime.signedStep
            (intervalMagnitude interval.lower interval.upper))
      (rest : NeutralChainResolutionBounds interval q (r :: suffix)) :
      NeutralChainResolutionBounds interval p (q :: r :: suffix)

namespace NeutralChainResolutionBounds

def dropHead {interval : RationalInterval} {p q : RatPolynomial}
    {tail : List RatPolynomial}
    (bounds : NeutralChainResolutionBounds interval p (q :: tail)) :
    NeutralChainResolutionBounds interval q tail :=
  match bounds with
  | .pair _ => .single
  | .step _ _ _ _ _ rest => rest

/-- If the first member of a bounded nontrivial chain is not resolved, the
second member is.  In a nonterminal Euclidean step this is the contrapositive
of the transported Bézout selector; in the terminal pair it is stored
directly. -/
theorem secondResolvedOfFirstUnresolved {interval : RationalInterval}
    {p q : RatPolynomial} {tail : List RatPolynomial}
    (proper : interval.Proper)
    (bounds : NeutralChainResolutionBounds interval p (q :: tail))
    (hfirst : ¬MidpointResolved interval p) : MidpointResolved interval q := by
  cases bounds with
  | pair qResolved => exact qResolved
  | step nextEq coprime leftSmall rightSmall dominanceSmall rest =>
      by_contra hq
      apply hfirst
      exact secondMidpointMarginOfFirstUnresolved coprime.swap proper leftSmall
        (by simpa [MidpointResolved] using hq)

end NeutralChainResolutionBounds

theorem signedRemainderChain_tail_eq_of_second_nonzero
    (p q : RatPolynomial) (hq : q.isZero = false) :
    (signedRemainderChain p q).tail =
      q :: (signedRemainderChain q (-((divMod p q).remainder))).tail := by
  rw [signedRemainderChain, signedRemainderChainWF]
  simp only [hq, Bool.false_eq_true, dite_false]
  split
  · rename_i hremainder
    have hnextZero : (-((divMod p q).remainder)).isZero = true := by
      simpa using hremainder
    rw [signedRemainderChain, signedRemainderChainWF]
    simp [hnextZero]
  · change signedRemainderChain q (-((divMod p q).remainder)) =
      q :: (signedRemainderChain q (-((divMod p q).remainder))).tail
    rcases signedRemainderChain_eq_cons q (-((divMod p q).remainder)) with
      ⟨tail, htail⟩
    rw [htail]
    rfl

/-- Fold the positive ambient radius through the actual signed Euclidean
chain, producing every proof-relevant local field consumed by the scanner. -/
def signedChainResolutionBoundsOfAmbient
    (root interval : RationalInterval) (hrefines : interval.Refines root)
    (proper : interval.Proper) (p q : RatPolynomial)
    (coprime : CoprimeCertificate p q)
    (hradius : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
      signedChainAmbientRadius p q coprime
        (intervalMagnitude root.lower root.upper)) :
    NeutralChainResolutionBounds interval p (signedRemainderChain p q).tail := by
  let rootB := intervalMagnitude root.lower root.upper
  have hmagnitude : intervalMagnitude interval.lower interval.upper ≤ rootB :=
    interval.intervalMagnitude_le_of_refines hrefines proper
  have hradiusNonneg : 0 ≤ intervalRadius interval.lower interval.upper
      (midpoint interval.lower interval.upper) := by
    dsimp [intervalRadius]
    positivity
  by_cases hq : q.isZero = true
  · rw [signedRemainderChain, signedRemainderChainWF]
    simp [hq]
    exact .single
  · have hqFalse : q.isZero = false := by
      cases hvalue : q.isZero <;> simp_all
    by_cases hremainder : (divMod p q).remainder.isZero = true
    · have hdegree := second_natDegree_eq_zero_of_remainder_zero coprime hqFalse
        hremainder
      have qResolved : MidpointResolved interval q := by
        apply constant_midpoint_resolved_of_ambient_radius hqFalse hdegree
          hmagnitude hradiusNonneg
        have h := hradius
        rw [signedChainAmbientRadius] at h
        simpa only [hq, hremainder, Bool.false_eq_true, dite_false, dite_true,
          rootB] using h
      rw [signedRemainderChain, signedRemainderChainWF]
      simp [hq, hremainder]
      exact NeutralChainResolutionBounds.pair qResolved
    · have hrFalse : (divMod p q).remainder.isZero = false := by
        cases hvalue : (divMod p q).remainder.isZero <;> simp_all
      let next := -((divMod p q).remainder)
      have hnextFalse : next.isZero = false := by simpa [next] using hrFalse
      have hdecomposedRadius : intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
          min (ambientSignedStepRadius coprime rootB)
            (signedChainAmbientRadius q next coprime.signedStep rootB) := by
        have h := hradius
        rw [signedChainAmbientRadius] at h
        simpa only [hq, hremainder, Bool.false_eq_true, dite_false, rootB,
          next] using h
      have hlocalRadius : intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
          ambientSignedStepRadius coprime rootB :=
        hdecomposedRadius.trans_le (min_le_left _ _)
      have htailRadius : intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
          signedChainAmbientRadius q next coprime.signedStep rootB :=
        hdecomposedRadius.trans_le (min_le_right _ _)
      have hlocal := signedStep_inequalities_of_ambient_radius coprime
        hmagnitude hradiusNonneg hlocalRadius
      have rest := signedChainResolutionBoundsOfAmbient root interval hrefines
        proper q next coprime.signedStep htailRadius
      rw [signedRemainderChain_tail_eq_of_second_nonzero q next hnextFalse] at rest
      rw [signedRemainderChain_tail_eq_of_second_nonzero p q hqFalse]
      rw [signedRemainderChain_tail_eq_of_second_nonzero q next hnextFalse]
      exact .step (r := next) rfl coprime hlocal.1 hlocal.2.1 hlocal.2.2 rest
termination_by q.degreeCount
decreasing_by
  have hcount : next.degreeCount < q.degreeCount := by
    rcases divMod_remainder_small p q hqFalse with hzero | hdegree
    · exact (hremainder hzero).elim
    · have hrCount := natDegree_add_one_eq_degreeCount hrFalse
      have hqCount := natDegree_add_one_eq_degreeCount hqFalse
      dsimp [next]
      rw [degreeCount_neg]
      omega
  exact hcount

/-- Local branch bounds lift through the complete finite scanner.  Recursive
calls consume one or two actual chain members. -/
def neutralChainCertificate?_succeeds_of_resolutionBounds
    (interval : RationalInterval) (proper : interval.Proper) :
    (head : RatPolynomial) → (tail : List RatPolynomial) →
      NeutralChainResolutionBounds interval head tail →
      MidpointResolved interval head →
      { certificate : NeutralChainCertificate interval head tail //
        neutralChainCertificate? interval proper head tail = some certificate }
  | head, [], .single, headResolved => by
      refine ⟨.single (midpointResolvedCertificate interval proper head
        headResolved), ?_⟩
      rw [neutralChainCertificate?,
        midpointSignCertificate?_eq_some_of_resolved interval proper head
          headResolved]
  | head, [q], .pair qResolved, headResolved => by
      refine ⟨.stable (midpointResolvedCertificate interval proper head
        headResolved) (.single (midpointResolvedCertificate interval proper q
          qResolved)), ?_⟩
      rw [neutralChainCertificate?,
        midpointSignCertificate?_eq_some_of_resolved interval proper head
          headResolved,
        midpointSignCertificate?_eq_some_of_resolved interval proper q qResolved]
  | head, q :: r :: suffix,
      .step nextEq coprime leftSmall rightSmall dominanceSmall rest,
      headResolved => by
      have hhead := midpointSignCertificate?_eq_some_of_resolved
        interval proper head headResolved
      by_cases qResolved : MidpointResolved interval q
      · have hq := midpointSignCertificate?_eq_some_of_resolved
          interval proper q qResolved
        have restResult := neutralChainCertificate?_succeeds_of_resolutionBounds
          interval proper q (r :: suffix) rest qResolved
        refine ⟨.stable (midpointResolvedCertificate interval proper head
          headResolved) restResult.1, ?_⟩
        simp only [neutralChainCertificate?, hhead, hq, restResult.2]
      · have hqNone : midpointSignCertificate? q interval.lower interval.upper
            proper = none := by
          simp [midpointSignCertificate?, MidpointResolved] at qResolved ⊢
          exact qResolved
        have hstepSome :=
          signedStepCellCertificate?_isSome_of_middle_unresolved coprime interval
            proper (by simpa [MidpointResolved] using qResolved)
            leftSmall rightSmall dominanceSmall
        cases hstep : signedStepCellCertificate? head q interval proper with
        | none => simp [hstep] at hstepSome
        | some stepCertificate =>
            have hnextResolved : MidpointResolved interval
                (-((divMod head q).remainder)) := by
              exact secondMidpointMarginOfFirstUnresolved coprime.signedStep proper
                rightSmall (by simpa [MidpointResolved] using qResolved)
            have hrResolved : MidpointResolved interval r := by
              simpa [nextEq] using hnextResolved
            have rBounds := rest.dropHead
            have restResult :=
              neutralChainCertificate?_succeeds_of_resolutionBounds interval proper
                r suffix rBounds hrResolved
            refine ⟨.event nextEq stepCertificate restResult.1, ?_⟩
            simp only [neutralChainCertificate?, hhead, hqNone]
            simp [nextEq, hstep, restResult.2]
termination_by _ tail _ _ => tail.length

/-- Package the recursive scanner result for an actual signed Euclidean
chain once its proof-relevant local bounds and resolved head are available. -/
def neutralSignedRemainderChainCertificates?_succeeds_of_resolutionBounds
    (interval : RationalInterval) (proper : interval.Proper)
    (p q : RatPolynomial)
    (bounds : NeutralChainResolutionBounds interval p
      (signedRemainderChain p q).tail)
    (headResolved : MidpointResolved interval p) :
    { certificates : NeutralChainCertificates interval
        (signedRemainderChain p q) //
      neutralChainCertificates? interval proper (signedRemainderChain p q) =
        some certificates } := by
  let tail := (signedRemainderChain p q).tail
  have hchain : signedRemainderChain p q = p :: tail := by
    rcases signedRemainderChain_eq_cons p q with ⟨actualTail, hactual⟩
    have htail : actualTail = tail := by
      dsimp only [tail]
      simpa using (congrArg List.tail hactual).symm
    simpa [htail] using hactual
  rw [hchain] at bounds
  have result := neutralChainCertificate?_succeeds_of_resolutionBounds interval
    proper p tail bounds headResolved
  rw [hchain]
  refine ⟨.cons result.1, ?_⟩
  simp only [neutralChainCertificates?, result.2]

/-- The ambient fold supplies the local bounds for the packaged signed-chain
scanner; only resolution of the first member remains an external branch
choice. -/
def neutralSignedRemainderChainCertificates?_succeeds_of_ambient
    (root interval : RationalInterval) (hrefines : interval.Refines root)
    (proper : interval.Proper) (p q : RatPolynomial)
    (coprime : CoprimeCertificate p q)
    (hradius : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
      signedChainAmbientRadius p q coprime
        (intervalMagnitude root.lower root.upper))
    (headResolved : MidpointResolved interval p) :
    { certificates : NeutralChainCertificates interval
        (signedRemainderChain p q) //
      neutralChainCertificates? interval proper (signedRemainderChain p q) =
        some certificates } := by
  apply neutralSignedRemainderChainCertificates?_succeeds_of_resolutionBounds
    interval proper p q
  · exact signedChainResolutionBoundsOfAmbient root interval hrefines proper
      p q coprime hradius
  · exact headResolved

/-- Executable Bézout certificate for the gcd-reduced denominator/numerator
pair underlying an arbitrary nondegenerate Cauchy index. -/
def reducedCauchyPairCertificate (R S : RatPolynomial)
    (hR : R.isZero = false) (hS : S.isZero = false) :
    CoprimeCertificate (reducedDenominator R S) (reducedNumerator R S) :=
  certificateOfIsCoprime (reducedDenominator R S)
    (reducedNumerator R S) (reducedDenominator_isZero_false hS)
    (reducedPair_isCoprime hR hS)

/-- Positive coefficient-computed width resolving every local branch of an
arbitrary gcd-reduced Cauchy chain. -/
def cauchyChainAmbientWidthResolution (R S : RatPolynomial)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (root : RationalInterval) : ℚ :=
  2 * signedChainAmbientRadius
    (reducedDenominator R S) (reducedNumerator R S)
    (reducedCauchyPairCertificate R S hR hS)
    (intervalMagnitude root.lower root.upper)

theorem cauchyChainAmbientWidthResolution_pos (R S : RatPolynomial)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (root : RationalInterval) :
    0 < cauchyChainAmbientWidthResolution R S hR hS root := by
  exact mul_pos (by norm_num)
    (signedChainAmbientRadius_pos
      (reducedDenominator R S) (reducedNumerator R S)
      (reducedCauchyPairCertificate R S hR hS)
      (intervalMagnitude_pos root.lower root.upper).le)

/-- Below the computed Cauchy-chain width, a resolved first chain member
makes the genuine recursive neutral scanner return its exact certificate. -/
def neutralCauchyChainCertificates?_succeeds_of_refined_width
    (R S : RatPolynomial) (hR : R.isZero = false) (hS : S.isZero = false)
    (root interval : RationalInterval) (hrefines : interval.Refines root)
    (proper : interval.Proper)
    (hwidth : interval.width <
      cauchyChainAmbientWidthResolution R S hR hS root)
    (headResolved : MidpointResolved interval (reducedDenominator R S)) :
    { certificates : NeutralChainCertificates interval (cauchyChain R S) //
      neutralChainCertificates? interval proper (cauchyChain R S) =
        some certificates } := by
  have hradius : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
      signedChainAmbientRadius
        (reducedDenominator R S) (reducedNumerator R S)
        (reducedCauchyPairCertificate R S hR hS)
        (intervalMagnitude root.lower root.upper) := by
    rw [interval.midpointRadius_eq_half_width proper]
    dsimp only [cauchyChainAmbientWidthResolution] at hwidth
    linarith
  simpa only [cauchyChain] using
    neutralSignedRemainderChainCertificates?_succeeds_of_ambient
      root interval hrefines proper (reducedDenominator R S)
      (reducedNumerator R S) (reducedCauchyPairCertificate R S hR hS)
      hradius headResolved

/-- One interior event embedded in a complete finite signed chain.  Every
member outside the changing middle position has a whole-cell sign
certificate. -/
structure InteriorChainEventCertificate (interval : RationalInterval)
    (chainPrefix : List RatPolynomial) (p q : RatPolynomial)
    (suffix : List RatPolynomial) where
  prefixStable : ChainSignCertificates interval.lower interval.upper chainPrefix
  step : SignedStepCellCertificate p q interval
  suffixStable : ChainSignCertificates interval.lower interval.upper suffix

namespace InteriorChainEventCertificate

theorem endpointVariation_eq {interval : RationalInterval}
    {chainPrefix : List RatPolynomial} {p q : RatPolynomial}
    {suffix : List RatPolynomial}
    (certificate : InteriorChainEventCertificate interval chainPrefix p q suffix) :
    endpointVariation2
        (chainPrefix ++ p :: q :: (-((divMod p q).remainder)) :: suffix)
        interval.lower =
    endpointVariation2
        (chainPrefix ++ p :: q :: (-((divMod p q).remainder)) :: suffix)
        interval.upper := by
  simp only [endpointVariation2, List.map_append, List.map_cons]
  apply variation2_eq_of_middle_change
  · exact certificate.prefixStable.endpoint_signs
  · exact certificate.suffixStable.endpoint_signs
  · apply ratSign_eq_of_mul_pos
    exact certificate.step.leftStable.eval_mul_pos_between le_rfl
      certificate.step.proper.le certificate.step.proper.le le_rfl
  · apply ratSign_eq_of_mul_pos
    exact certificate.step.rightStable.eval_mul_pos_between le_rfl
      certificate.step.proper.le certificate.step.proper.le le_rfl
  · exact certificate.step.endpoint_cancellation

/-- An interior-event decomposition of a complete Cauchy chain has zero
index on the cell. -/
theorem cauchyIndex2_eq_zero {R S : RatPolynomial}
    {interval : RationalInterval} {chainPrefix : List RatPolynomial}
    {p q : RatPolynomial} {suffix : List RatPolynomial}
    (certificate : InteriorChainEventCertificate interval chainPrefix p q suffix)
    (hchain : cauchyChain R S =
      chainPrefix ++ p :: q :: (-((divMod p q).remainder)) :: suffix) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  by_cases hzero : R.isZero || S.isZero
  · simp [cauchyIndex2, hzero]
  · rw [cauchyIndex2, if_neg hzero, hchain, certificate.endpointVariation_eq]
    norm_num

end InteriorChainEventCertificate

/-- Proof-relevant result of finding one certified interior event inside an
arbitrary finite signed-chain list. -/
structure InteriorChainSearchResult (interval : RationalInterval)
    (chain : List RatPolynomial) where
  chainPrefix : List RatPolynomial
  leftMember : RatPolynomial
  middleMember : RatPolynomial
  suffix : List RatPolynomial
  decomposition : chain = chainPrefix ++ leftMember :: middleMember ::
    (-((divMod leftMember middleMember).remainder)) :: suffix
  event : InteriorChainEventCertificate interval chainPrefix leftMember
    middleMember suffix

/-- Structural finite scan for one interior event.  At each signed triple it
first tries the local cancellation classifier; otherwise a fixed-sign head is
moved into the certified prefix and the scan continues on the tail. -/
def interiorChainEventCertificate? (interval : RationalInterval)
    (proper : interval.Proper) :
    (chain : List RatPolynomial) → Option (InteriorChainSearchResult interval chain)
  | p :: q :: r :: suffix =>
      if hnext : r = -((divMod p q).remainder) then
        match signedStepCellCertificate? p q interval proper with
        | some step =>
            match chainSignCertificates? interval.lower interval.upper proper suffix with
            | some suffixStable =>
                some
                  { chainPrefix := []
                    leftMember := p
                    middleMember := q
                    suffix := suffix
                    decomposition := by simp [hnext]
                    event :=
                      { prefixStable := .nil
                        step := step
                        suffixStable := suffixStable } }
            | none => none
        | none =>
            match midpointSignCertificate? p interval.lower interval.upper proper with
            | none => none
            | some head =>
                match interiorChainEventCertificate? interval proper (q :: r :: suffix) with
                | none => none
                | some result =>
                    some
                      { chainPrefix := p :: result.chainPrefix
                        leftMember := result.leftMember
                        middleMember := result.middleMember
                        suffix := result.suffix
                        decomposition := by
                          have hcons := congrArg
                            (fun chain : List RatPolynomial => p :: chain)
                            result.decomposition
                          simpa only [List.cons_append] using hcons
                        event :=
                          { prefixStable := .cons head result.event.prefixStable
                            step := result.event.step
                            suffixStable := result.event.suffixStable } }
      else none
  | _ => none

theorem InteriorChainSearchResult.cauchyIndex2_eq_zero
    {R S : RatPolynomial} {interval : RationalInterval}
    {chain : List RatPolynomial}
    (result : InteriorChainSearchResult interval chain)
    (hchain : cauchyChain R S = chain) :
    cauchyIndex2 R S interval.lower interval.upper = 0 :=
  result.event.cauchyIndex2_eq_zero (hchain.trans result.decomposition)

/-- Executable interior-event classifier specialized to the complete
squarefree derivative Cauchy chain. -/
def interiorSturmEventCertificate? (p : RatPolynomial)
    (interval : RationalInterval) (proper : interval.Proper) :
    Option (InteriorChainSearchResult interval (cauchyChain (derivative p) p)) :=
  interiorChainEventCertificate? interval proper (cauchyChain (derivative p) p)

theorem InteriorChainSearchResult.sturmRootCount2_eq_zero
    {p : RatPolynomial} {interval : RationalInterval}
    (result : InteriorChainSearchResult interval (cauchyChain (derivative p) p)) :
    sturmRootCount2 p interval.lower interval.upper = 0 := by
  exact result.cauchyIndex2_eq_zero rfl

/-- Native regression for the whole-chain interior classifier at the
derivative event `0` of `T² - 1`. -/
theorem interiorSturmEventCertificate_quadratic_example :
    (interiorSturmEventCertificate? ⟨[1, 0, -1]⟩
      ⟨-1 / 4, 1 / 4⟩
      (by norm_num [RationalInterval.Proper])).isSome = true := by
  native_decide

/-- Native regression for the local classifier at the interior derivative
event of `T² - 1`: the signed step `(T²-1, 2T)` is certified on
`[-1/4,1/4]`. -/
theorem signedStepCellCertificate_quadratic_example :
    (signedStepCellCertificate? ⟨[1, 0, -1]⟩ ⟨[2, 0]⟩
      ⟨-1 / 4, 1 / 4⟩ (by norm_num [RationalInterval.Proper])).isSome = true := by
  native_decide

/-- Finite first-member event certificate.  The derivative keeps a strict
sign on the cell, while the polynomial is opposite to that sign at the lower
endpoint and aligned with it at the upper endpoint. -/
structure FirstMemberCellCertificate (p : RatPolynomial)
    (interval : RationalInterval) where
  proper : interval.Proper
  derivativeStable : IntervalSignCertificate (derivative p)
    interval.lower interval.upper
  lowerOpposite : p.eval interval.lower *
    (derivative p).eval (midpoint interval.lower interval.upper) < 0
  upperAligned : 0 < p.eval interval.upper *
    (derivative p).eval (midpoint interval.lower interval.upper)

/-- Executable orientation classifier for a first-member event cell. -/
def firstMemberCellCertificate? (p : RatPolynomial)
    (interval : RationalInterval) (proper : interval.Proper) :
    Option (FirstMemberCellCertificate p interval) :=
  let sample := midpoint interval.lower interval.upper
  let B := intervalMagnitude interval.lower interval.upper
  let radius := intervalRadius interval.lower interval.upper sample
  let derivativeP := derivative p
  if hstable : denseEvalLipschitzBound derivativeP B * radius <
      |derivativeP.eval sample| then
    if hlower : p.eval interval.lower * derivativeP.eval sample < 0 then
      if hupper : 0 < p.eval interval.upper * derivativeP.eval sample then
        some
          { proper := proper
            derivativeStable :=
              { sample := sample
                lowerLe := (lower_lt_midpoint proper).le
                leUpper := (midpoint_lt_upper proper).le
                margin := hstable }
            lowerOpposite := hlower
            upperAligned := hupper }
      else none
    else none
  else none

/-- Construct the first-event certificate from the two explicit local
resolution inequalities: the squarefree Bézout radius stabilizes the
derivative, and the executable Taylor bound fixes the crossing orientation. -/
def firstMemberCellCertificateOfSmallCrossing {p : RatPolynomial}
    (input : SquarefreeInput p) (interval : RationalInterval)
    (proper : interval.Proper)
    (crossing : p.eval interval.lower * p.eval interval.upper < 0)
    (bezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius input.squarefree interval.lower interval.upper)
    (taylorSmall :
      2 * denseTaylorHornerRemainderBound p
          (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) ^ 2 <
        |(derivative p).eval (midpoint interval.lower interval.upper)| *
          interval.width) :
    FirstMemberCellCertificate p interval := by
  let sample := midpoint interval.lower interval.upper
  have hstable :
      denseEvalLipschitzBound (derivative p)
          (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper sample <
        |(derivative p).eval sample| :=
    secondMidpointMarginOfFirstEndpointCrossing input.squarefree proper
      (by simpa [sample] using bezoutSmall) crossing
  have hdifference :
      0 < (p.eval interval.upper - p.eval interval.lower) *
        (derivative p).eval sample :=
    endpointDifference_mul_derivative_pos_of_taylor_margin p proper
      (lower_lt_midpoint proper).le (midpoint_lt_upper proper).le
      (by simpa [sample, RationalInterval.width] using taylorSmall)
  have horientation := endpoint_orientation_of_crossing_and_difference
    crossing hdifference
  exact
    { proper
      derivativeStable :=
        { sample
          lowerLe := (lower_lt_midpoint proper).le
          leUpper := (midpoint_lt_upper proper).le
          margin := hstable }
      lowerOpposite := horientation.1
      upperAligned := horientation.2 }

/-- The Boolean orientation classifier succeeds whenever the displayed
Bézout and Taylor resolution inequalities hold. -/
theorem firstMemberCellCertificate?_isSome_of_small_crossing
    {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper)
    (crossing : p.eval interval.lower * p.eval interval.upper < 0)
    (bezoutSmall :
      intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius input.squarefree interval.lower interval.upper)
    (taylorSmall :
      2 * denseTaylorHornerRemainderBound p
          (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) ^ 2 <
        |(derivative p).eval (midpoint interval.lower interval.upper)| *
          interval.width) :
    (firstMemberCellCertificate? p interval proper).isSome = true := by
  let sample := midpoint interval.lower interval.upper
  have hstable :
      denseEvalLipschitzBound (derivative p)
          (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper sample <
        |(derivative p).eval sample| :=
    secondMidpointMarginOfFirstEndpointCrossing input.squarefree proper
      (by simpa [sample] using bezoutSmall) crossing
  have hdifference :
      0 < (p.eval interval.upper - p.eval interval.lower) *
        (derivative p).eval sample :=
    endpointDifference_mul_derivative_pos_of_taylor_margin p proper
      (lower_lt_midpoint proper).le (midpoint_lt_upper proper).le
      (by simpa [sample, RationalInterval.width] using taylorSmall)
  have horientation := endpoint_orientation_of_crossing_and_difference
    crossing hdifference
  simp [firstMemberCellCertificate?, sample, hstable,
    horientation.1, horientation.2]

/-- Uniform width below which a first-member endpoint crossing has both its
Bézout derivative margin and its executable Taylor orientation margin on
every refinement of `root`. -/
def ambientFirstMemberWidthResolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) : ℚ :=
  let B := intervalMagnitude root.lower root.upper
  let remainderMajorant := max 1 (denseTaylorHornerRemainderBound p B)
  min (2 * ambientCoprimeCellRadius input.squarefree B)
    (2 * coprimeExclusionMargin input.squarefree B / remainderMajorant)

theorem ambientFirstMemberWidthResolution_pos {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) :
    0 < ambientFirstMemberWidthResolution input root := by
  let B := intervalMagnitude root.lower root.upper
  let remainderMajorant := max 1 (denseTaylorHornerRemainderBound p B)
  have hB : 0 ≤ B := (intervalMagnitude_pos root.lower root.upper).le
  have hmajorant : 0 < remainderMajorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply lt_min
  · exact mul_pos (by norm_num) (ambientCoprimeCellRadius_pos input.squarefree hB)
  · exact div_pos
      (mul_pos (by norm_num) (coprimeExclusionMargin_pos input.squarefree hB))
      hmajorant

/-- The uniform width resolves precisely the two inequalities consumed by
the executable first-member classifier whenever the endpoints cross. -/
theorem firstMember_inequalities_of_refined_width {p : RatPolynomial}
    (input : SquarefreeInput p) (root interval : RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (crossing : p.eval interval.lower * p.eval interval.upper < 0)
    (hwidth : interval.width < ambientFirstMemberWidthResolution input root) :
    intervalRadius interval.lower interval.upper
          (midpoint interval.lower interval.upper) <
        coprimeCellRadius input.squarefree interval.lower interval.upper ∧
      2 * denseTaylorHornerRemainderBound p
            (intervalMagnitude interval.lower interval.upper) *
          intervalRadius interval.lower interval.upper
            (midpoint interval.lower interval.upper) ^ 2 <
        |(derivative p).eval (midpoint interval.lower interval.upper)| *
          interval.width := by
  let rootB := intervalMagnitude root.lower root.upper
  let subB := intervalMagnitude interval.lower interval.upper
  let remainderMajorant := max 1 (denseTaylorHornerRemainderBound p rootB)
  let exclusion := coprimeExclusionMargin input.squarefree rootB
  have hmagnitude : subB ≤ rootB :=
    interval.intervalMagnitude_le_of_refines hrefines proper
  have hsubB : 0 ≤ subB := (intervalMagnitude_pos _ _).le
  have hrootB : 0 ≤ rootB := hsubB.trans hmagnitude
  have hwidthBezout : interval.width <
      2 * ambientCoprimeCellRadius input.squarefree rootB :=
    hwidth.trans_le (by
      dsimp only [ambientFirstMemberWidthResolution, rootB]
      exact min_le_left _ _)
  have hhalfBezout : interval.width / 2 <
      ambientCoprimeCellRadius input.squarefree rootB := by
    linarith
  have hbezout : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
      coprimeCellRadius input.squarefree interval.lower interval.upper := by
    rw [interval.midpointRadius_eq_half_width proper]
    exact hhalfBezout.trans_le
      (ambientCoprimeCellRadius_le_cellRadius input.squarefree hmagnitude)
  refine ⟨hbezout, ?_⟩
  have hwidthTaylor : interval.width < 2 * exclusion / remainderMajorant :=
    hwidth.trans_le (by
      dsimp only [ambientFirstMemberWidthResolution, rootB, exclusion,
        remainderMajorant]
      exact min_le_right _ _)
  have hmajorantPos : 0 < remainderMajorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hscaled : remainderMajorant * interval.width < 2 * exclusion := by
    have h := (lt_div_iff₀ hmajorantPos).mp hwidthTaylor
    simpa [mul_comm] using h
  have hremainderSub : denseTaylorHornerRemainderBound p subB ≤
      denseTaylorHornerRemainderBound p rootB :=
    denseTaylorHornerRemainderBound_mono p hsubB hmagnitude
  have hremainderMajorant : denseTaylorHornerRemainderBound p subB ≤
      remainderMajorant :=
    hremainderSub.trans (le_max_right _ _)
  have hremainderNonneg : 0 ≤ denseTaylorHornerRemainderBound p subB :=
    (denseTaylorHornerBounds_nonneg p hsubB).2.2
  have hexclusionSub : exclusion ≤
      coprimeExclusionMargin input.squarefree subB :=
    coprimeExclusionMargin_anti input.squarefree hsubB hmagnitude
  have hexclusionDerivative : exclusion ≤
      |(derivative p).eval (midpoint interval.lower interval.upper)| :=
    hexclusionSub.trans
      (coprimeExclusionMargin_le_abs_second_midpoint_of_first_crossing
        input.squarefree proper hbezout crossing)
  have hwidthPos : 0 < interval.width := RationalInterval.width_pos proper
  rw [interval.midpointRadius_eq_half_width proper]
  change 2 * denseTaylorHornerRemainderBound p subB *
      (interval.width / 2) ^ 2 <
    |(derivative p).eval (midpoint interval.lower interval.upper)| *
      interval.width
  nlinarith

namespace FirstMemberCellCertificate

theorem lower_derivative_mul_neg {p : RatPolynomial}
    {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    p.eval interval.lower * (derivative p).eval interval.lower < 0 := by
  let sample := midpoint interval.lower interval.upper
  have hsampleLower : interval.lower ≤ sample :=
    (lower_lt_midpoint certificate.proper).le
  have hsampleUpper : sample ≤ interval.upper :=
    (midpoint_lt_upper certificate.proper).le
  have hderivative := certificate.derivativeStable.eval_mul_pos_between
    hsampleLower hsampleUpper le_rfl certificate.proper.le
  have hpLower : p.eval interval.lower ≠ 0 := by
    intro hzero
    have hopposite := certificate.lowerOpposite
    rw [hzero, zero_mul] at hopposite
    linarith
  have hpSquare : 0 < p.eval interval.lower * p.eval interval.lower :=
    mul_self_pos.mpr hpLower
  have hopposite :
      (derivative p).eval sample * p.eval interval.lower < 0 := by
    simpa [sample, mul_comm] using certificate.lowerOpposite
  have htransfer := mul_neg_of_same_sign_transfers
    hderivative hpSquare hopposite
  simpa [mul_comm] using htransfer

theorem upper_derivative_mul_pos {p : RatPolynomial}
    {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    0 < p.eval interval.upper * (derivative p).eval interval.upper := by
  let sample := midpoint interval.lower interval.upper
  have hsampleLower : interval.lower ≤ sample :=
    (lower_lt_midpoint certificate.proper).le
  have hsampleUpper : sample ≤ interval.upper :=
    (midpoint_lt_upper certificate.proper).le
  have hderivative := certificate.derivativeStable.eval_mul_pos_between
    hsampleLower hsampleUpper certificate.proper.le le_rfl
  have haligned : 0 < (derivative p).eval sample * p.eval interval.upper := by
    simpa [sample, mul_comm] using certificate.upperAligned
  have htransfer := mul_pos_of_mul_pos_left haligned hderivative
  simpa [mul_comm] using htransfer

theorem lower_jump {p : RatPolynomial} {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    signJump (p.eval interval.lower) ((derivative p).eval interval.lower) = 2 :=
  signJump_eq_two_of_mul_neg certificate.lower_derivative_mul_neg

theorem upper_jump {p : RatPolynomial} {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    signJump (p.eval interval.upper) ((derivative p).eval interval.upper) = 0 :=
  signJump_eq_zero_of_mul_pos certificate.upper_derivative_mul_pos

/-- A certified first-member cell contributes one ordinary event, represented
as two units in the doubled variation convention. -/
theorem jump_difference {p : RatPolynomial} {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    (signJump (p.eval interval.lower) ((derivative p).eval interval.lower) : ℤ) -
      signJump (p.eval interval.upper) ((derivative p).eval interval.upper) = 2 := by
  rw [certificate.lower_jump, certificate.upper_jump]
  norm_num

theorem reduced_lower_jump {p : RatPolynomial} {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    signJump
        ((reducedDenominator (derivative p) p).eval interval.lower)
        ((reducedNumerator (derivative p) p).eval interval.lower) = 2 := by
  have hraw : (derivative p).eval interval.lower * p.eval interval.lower < 0 := by
    simpa [mul_comm] using certificate.lower_derivative_mul_neg
  have hreduced := FTA.DenseGCD.symmetricFactors_eval_mul_neg_of_input_mul_neg
    (derivative p) p interval.lower hraw
  apply signJump_eq_two_of_mul_neg
  simpa [reducedDenominator, reducedNumerator, mul_comm] using hreduced

theorem reduced_upper_jump {p : RatPolynomial} {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    signJump
        ((reducedDenominator (derivative p) p).eval interval.upper)
        ((reducedNumerator (derivative p) p).eval interval.upper) = 0 := by
  have hraw : 0 < (derivative p).eval interval.upper * p.eval interval.upper := by
    simpa [mul_comm] using certificate.upper_derivative_mul_pos
  have hreduced := FTA.DenseGCD.symmetricFactors_eval_mul_pos_of_input_mul_pos
    (derivative p) p interval.upper hraw
  apply signJump_eq_zero_of_mul_pos
  simpa [reducedDenominator, reducedNumerator, mul_comm] using hreduced

/-- The orientation certificate computes exactly the first-pair term on the
right side of Cauchy--Sturm inversion, including executable gcd reduction. -/
theorem pairVariationDifference2_eq_two {p : RatPolynomial}
    {interval : RationalInterval}
    (certificate : FirstMemberCellCertificate p interval) :
    pairVariationDifference2 (derivative p) p
      interval.lower interval.upper = 2 := by
  rw [pairVariationDifference2, pairEndpointVariation2,
    pairEndpointVariation2, certificate.reduced_lower_jump,
    certificate.reduced_upper_jump]
  norm_num

end FirstMemberCellCertificate

/-- Native regression for the oriented first event of `T² - 1` around `1`. -/
theorem firstMemberCellCertificate_quadratic_example :
    (firstMemberCellCertificate? ⟨[1, 0, -1]⟩
      ⟨3 / 4, 5 / 4⟩ (by norm_num [RationalInterval.Proper])).isSome = true := by
  native_decide

/-- Signed-chain tail remaining after the first reduced denominator/numerator
jump has been split off. -/
def derivativeRestChain (p : RatPolynomial) : List RatPolynomial :=
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  signedRemainderChain numerator (-((divMod denominator numerator).remainder))

/-- Executable Bézout certificate for the gcd-reduced derivative pair used
by the actual Cauchy chain. -/
def derivativeReducedPairCertificate {p : RatPolynomial}
    (input : SquarefreeInput p) :
    CoprimeCertificate (reducedDenominator (derivative p) p)
      (reducedNumerator (derivative p) p) :=
  certificateOfIsCoprime _ _
    (reducedDenominator_isZero_false input.nonzero)
    (reducedPair_isCoprime
      (derivative_isZero_false input.nonzero input.nonconstant) input.nonzero)

/-- If the reduced first member is unresolved, the ambient full-chain bounds
force the reduced derivative member to be resolved and therefore run the
entire residual scanner. -/
def derivativeRestChainCertificates?_succeeds_of_resolutionBounds
    {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper)
    (bounds : NeutralChainResolutionBounds interval
      (reducedDenominator (derivative p) p)
      (signedRemainderChain (reducedDenominator (derivative p) p)
        (reducedNumerator (derivative p) p)).tail)
    (hfirst : ¬MidpointResolved interval
      (reducedDenominator (derivative p) p)) :
    { certificates : NeutralChainCertificates interval (derivativeRestChain p) //
      neutralChainCertificates? interval proper (derivativeRestChain p) =
        some certificates } := by
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  let next := -((divMod denominator numerator).remainder)
  have hnumerator : numerator.isZero = false :=
    reducedNumerator_isZero_false
      (derivative_isZero_false input.nonzero input.nonconstant)
  change NeutralChainResolutionBounds interval denominator
    (signedRemainderChain denominator numerator).tail at bounds
  change ¬MidpointResolved interval denominator at hfirst
  rw [signedRemainderChain_tail_eq_of_second_nonzero denominator numerator
    hnumerator] at bounds
  have numeratorResolved : MidpointResolved interval numerator :=
    bounds.secondResolvedOfFirstUnresolved proper hfirst
  have restBounds := bounds.dropHead
  have result :=
    neutralSignedRemainderChainCertificates?_succeeds_of_resolutionBounds
      interval proper numerator next restBounds numeratorResolved
  simpa only [derivativeRestChain, denominator, numerator, next] using result

/-- When the original polynomial has the same strict endpoint sign and the
reduced derivative member is midpoint-resolved, both entries of the reduced
first pair preserve their endpoint signs, so its doubled jump is unchanged. -/
theorem reducedPairEndpointVariation_eq_of_same_first_sign
    {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper)
    (firstSame : 0 < p.eval interval.lower * p.eval interval.upper)
    (numeratorResolved : MidpointResolved interval
      (reducedNumerator (derivative p) p)) :
    pairEndpointVariation2 (derivative p) p interval.lower =
      pairEndpointVariation2 (derivative p) p interval.upper := by
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  have hcoprime : IsCoprime (derivative p).toPolynomial p.toPolynomial :=
    by simpa [toPolynomial_derivative] using
      input.squarefree.isCoprimeDerivative.symm
  have denominatorSame : 0 < denominator.eval interval.lower *
      denominator.eval interval.upper := by
    exact FTA.DenseGCD.symmetricRightFactor_endpoint_mul_pos_of_isCoprime
      (p := derivative p) (q := p) (a := interval.lower) (b := interval.upper)
      input.nonzero hcoprime firstSame
  have numeratorSame : 0 < numerator.eval interval.lower *
      numerator.eval interval.upper := by
    exact (midpointResolvedCertificate interval proper numerator
      numeratorResolved).eval_mul_pos_between le_rfl proper.le proper.le le_rfl
  change signJump (denominator.eval interval.lower) (numerator.eval interval.lower) =
    signJump (denominator.eval interval.upper) (numerator.eval interval.upper)
  apply signJump_congr
  · exact ratSign_eq_of_mul_pos denominatorSame
  · exact ratSign_eq_of_mul_pos numeratorSame

/-- Whole-chain certificate for one oriented first-member event.  Every
polynomial in the residual signed chain has a fixed strict sign on the cell. -/
structure FirstChainEventCertificate {p : RatPolynomial}
    (_input : SquarefreeInput p) (interval : RationalInterval) where
  first : FirstMemberCellCertificate p interval
  restStable : NeutralChainCertificates interval
    (derivativeRestChain p)

/-- Executable whole-chain first-event classifier. -/
def firstChainEventCertificate? {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper) :
    Option (FirstChainEventCertificate input interval) :=
  match firstMemberCellCertificate? p interval proper with
  | none => none
  | some first =>
      match neutralChainCertificates? interval proper (derivativeRestChain p) with
      | none => none
      | some restStable => some { first, restStable }

namespace FirstChainEventCertificate

/-- A successful whole-chain first-event certificate proves the actual
doubled Sturm count is two. -/
theorem count_eq_two {p : RatPolynomial} {input : SquarefreeInput p}
    {interval : RationalInterval}
    (certificate : FirstChainEventCertificate input interval) :
    sturmRootCount2 p interval.lower interval.upper = 2 := by
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  have hderivative : (derivative p).isZero = false :=
    derivative_isZero_false input.nonzero input.nonconstant
  have hnumerator : numerator.isZero = false := by
    exact reducedNumerator_isZero_false hderivative
  have hcondition : ¬((derivative p).isZero || p.isZero) := by
    simp [hderivative, input.nonzero]
  have hlower := endpointVariation2_signedRemainderChain_step
    (p := denominator) (q := numerator) hnumerator interval.lower
  have hupper := endpointVariation2_signedRemainderChain_step
    (p := denominator) (q := numerator) hnumerator interval.upper
  have hrest := certificate.restStable.endpointVariation_eq
  rw [sturmRootCount2, cauchyIndex2, if_neg hcondition, cauchyChain]
  change (endpointVariation2 (signedRemainderChain denominator numerator)
      interval.lower : ℤ) -
    endpointVariation2 (signedRemainderChain denominator numerator)
      interval.upper = 2
  rw [hlower, hupper]
  change ((signJump (denominator.eval interval.lower)
      (numerator.eval interval.lower) +
        endpointVariation2 (derivativeRestChain p) interval.lower : ℕ) : ℤ) -
    (signJump (denominator.eval interval.upper)
      (numerator.eval interval.upper) +
        endpointVariation2 (derivativeRestChain p) interval.upper : ℕ) = 2
  rw [certificate.first.reduced_lower_jump,
    certificate.first.reduced_upper_jump, hrest]
  norm_num

end FirstChainEventCertificate

/-- Zero-event alternative at the first chain position: the reduced first
jump agrees at both endpoints and the entire residual chain keeps its signs. -/
structure FirstPairNoEventCertificate {p : RatPolynomial}
    (_input : SquarefreeInput p) (interval : RationalInterval) where
  pairUnchanged : pairEndpointVariation2 (derivative p) p interval.lower =
    pairEndpointVariation2 (derivative p) p interval.upper
  restStable : NeutralChainCertificates interval
    (derivativeRestChain p)

def firstPairNoEventCertificate? {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper) :
    Option (FirstPairNoEventCertificate input interval) :=
  if hpair : pairEndpointVariation2 (derivative p) p interval.lower =
      pairEndpointVariation2 (derivative p) p interval.upper then
    match neutralChainCertificates? interval proper (derivativeRestChain p) with
    | some restStable => some { pairUnchanged := hpair, restStable }
    | none => none
  else none

namespace FirstPairNoEventCertificate

theorem count_eq_zero {p : RatPolynomial} {input : SquarefreeInput p}
    {interval : RationalInterval}
    (certificate : FirstPairNoEventCertificate input interval) :
    sturmRootCount2 p interval.lower interval.upper = 0 := by
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  have hderivative : (derivative p).isZero = false :=
    derivative_isZero_false input.nonzero input.nonconstant
  have hnumerator : numerator.isZero = false :=
    reducedNumerator_isZero_false hderivative
  have hcondition : ¬((derivative p).isZero || p.isZero) := by
    simp [hderivative, input.nonzero]
  have hlower := endpointVariation2_signedRemainderChain_step
    (p := denominator) (q := numerator) hnumerator interval.lower
  have hupper := endpointVariation2_signedRemainderChain_step
    (p := denominator) (q := numerator) hnumerator interval.upper
  have hrest := certificate.restStable.endpointVariation_eq
  have hpair : signJump (denominator.eval interval.lower)
        (numerator.eval interval.lower) =
      signJump (denominator.eval interval.upper)
        (numerator.eval interval.upper) := by
    simpa [pairEndpointVariation2, denominator, numerator] using
      certificate.pairUnchanged
  rw [sturmRootCount2, cauchyIndex2, if_neg hcondition, cauchyChain]
  change (endpointVariation2 (signedRemainderChain denominator numerator)
      interval.lower : ℤ) -
    endpointVariation2 (signedRemainderChain denominator numerator)
      interval.upper = 0
  rw [hlower, hupper]
  change ((signJump (denominator.eval interval.lower)
      (numerator.eval interval.lower) +
        endpointVariation2 (derivativeRestChain p) interval.lower : ℕ) : ℤ) -
    (signJump (denominator.eval interval.upper)
      (numerator.eval interval.upper) +
        endpointVariation2 (derivativeRestChain p) interval.upper : ℕ) = 0
  rw [hpair, hrest]
  norm_num

end FirstPairNoEventCertificate

theorem firstChainEventCertificate?_some_count_eq_two
    {p : RatPolynomial} {input : SquarefreeInput p}
    {interval : RationalInterval} {proper : interval.Proper}
    {certificate : FirstChainEventCertificate input interval}
    (_hclassified : firstChainEventCertificate? input interval proper =
      some certificate) :
    sturmRootCount2 p interval.lower interval.upper = 2 :=
  certificate.count_eq_two

private def quadraticPolynomial : RatPolynomial := ⟨[1, 0, -1]⟩

private def quadraticSquarefreeInput : SquarefreeInput quadraticPolynomial where
  nonzero := by native_decide
  nonconstant := by native_decide
  squarefree :=
    { left := ⟨[-1]⟩
      right := ⟨[1 / 2, 0]⟩
      polynomialIdentity := by
        rw [show derivative quadraticPolynomial = ⟨[2, 0]⟩ by native_decide]
        simp [quadraticPolynomial, toPolynomial_eq_foldl_horner]
        have hhalf : Polynomial.C ((2 : ℚ)⁻¹) * Polynomial.C 2 = 1 := by
          rw [← map_mul]
          norm_num
        rw [show Polynomial.C ((2 : ℚ)⁻¹) * Polynomial.X *
            (Polynomial.C 2 * Polynomial.X) =
          (Polynomial.C ((2 : ℚ)⁻¹) * Polynomial.C 2) *
            (Polynomial.X * Polynomial.X) by ac_rfl]
        rw [hhalf, one_mul, neg_add_cancel_right] }

private def simultaneousCubicPolynomial : RatPolynomial := ⟨[1, 0, 2, 0]⟩

/-- `T³ + 2T` is squarefree, but its first member and a nonadjacent signed
remainder both vanish at zero. -/
private def simultaneousCubicSquarefreeInput :
    SquarefreeInput simultaneousCubicPolynomial where
  nonzero := by native_decide
  nonconstant := by native_decide
  squarefree :=
    { left := ⟨[-9 / 8, 0]⟩
      right := ⟨[3 / 8, 0, 1 / 2]⟩
      polynomialIdentity := by
        rw [show derivative simultaneousCubicPolynomial = ⟨[3, 0, 2]⟩ by
          native_decide]
        simp [simultaneousCubicPolynomial, toPolynomial_eq_foldl_horner]
        have hx2 :
            Polynomial.C (-9 / 8 : ℚ) * Polynomial.C 2 +
                Polynomial.C 2 * Polynomial.C (3 / 8 : ℚ) +
              Polynomial.C (1 / 2 : ℚ) * Polynomial.C 3 = 0 := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add]
          norm_num
        have hx4 : Polynomial.C (-9 / 8 : ℚ) +
            Polynomial.C (3 / 8 : ℚ) * Polynomial.C 3 = 0 := by
          rw [← map_mul, ← map_add]
          norm_num
        have hconstant : Polynomial.C 2 * Polynomial.C (1 / 2 : ℚ) = 1 := by
          rw [← map_mul]
          norm_num
        calc
          _ = (Polynomial.C (-9 / 8 : ℚ) * Polynomial.C 2 +
                  Polynomial.C 2 * Polynomial.C (3 / 8 : ℚ) +
                    Polynomial.C (1 / 2 : ℚ) * Polynomial.C 3) *
                Polynomial.X ^ 2 +
              (Polynomial.C (-9 / 8 : ℚ) +
                Polynomial.C (3 / 8 : ℚ) * Polynomial.C 3) *
                  Polynomial.X ^ 4 +
                Polynomial.C 2 * Polynomial.C (1 / 2 : ℚ) := by ring_nf
          _ = 1 := by rw [hx2, hx4, hconstant]; simp }

private def tangencyLeftPolynomial : RatPolynomial := ⟨[1, 0, -1]⟩

private def tangencyMiddlePolynomial : RatPolynomial := ⟨[1, 0, 0]⟩

private def tangencyCoprimeCertificate :
    CoprimeCertificate tangencyLeftPolynomial tangencyMiddlePolynomial where
  left := ⟨[-1]⟩
  right := ⟨[1]⟩
  polynomialIdentity := by
    simp [tangencyLeftPolynomial, tangencyMiddlePolynomial,
      toPolynomial_eq_foldl_horner]

/-- Native regression that the explicit Bézout and Taylor inequalities, not
merely the classifier's final Boolean, recognize the positive quadratic
event. -/
theorem firstMemberResolution_quadratic_example :
    (firstMemberCellCertificate? quadraticPolynomial ⟨15 / 16, 17 / 16⟩
      (by norm_num [RationalInterval.Proper])).isSome = true := by
  apply firstMemberCellCertificate?_isSome_of_small_crossing
    quadraticSquarefreeInput
  · native_decide
  · native_decide
  · native_decide

/-- Native regression that transported Bézout margins and quotient dominance
recognize the quadratic's interior derivative event. -/
theorem signedStepResolution_quadratic_example :
    (signedStepCellCertificate? quadraticPolynomial
      (derivative quadraticPolynomial) ⟨-1 / 16, 1 / 16⟩
      (by norm_num [RationalInterval.Proper])).isSome = true := by
  apply signedStepCellCertificate?_isSome_of_middle_crossing
    quadraticSquarefreeInput.squarefree
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Regression for an even-multiplicity middle event: `T²` has positive
endpoint values but an unresolved zero midpoint, and the signed-step branch
still certifies cancellation. -/
theorem signedStepResolution_tangency_example :
    (signedStepCellCertificate? tangencyLeftPolynomial tangencyMiddlePolynomial
      ⟨-1 / 16, 1 / 16⟩
      (by norm_num [RationalInterval.Proper])).isSome = true := by
  apply signedStepCellCertificate?_isSome_of_middle_unresolved
    tangencyCoprimeCertificate
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- The proof-relevant bounds lift through the recursive neutral scanner on
the same tangency chain. -/
theorem neutralChainResolution_tangency_example :
    (neutralChainCertificate? ⟨-1 / 16, 1 / 16⟩
      (by norm_num [RationalInterval.Proper]) tangencyLeftPolynomial
      [tangencyMiddlePolynomial, ⟨[1]⟩]).isSome = true := by
  let interval : RationalInterval := ⟨-1 / 16, 1 / 16⟩
  have proper : interval.Proper := by norm_num [interval, RationalInterval.Proper]
  let bounds : NeutralChainResolutionBounds interval tangencyLeftPolynomial
      [tangencyMiddlePolynomial, ⟨[1]⟩] :=
    .step (by native_decide) tangencyCoprimeCertificate
      (by native_decide) (by native_decide) (by native_decide)
      (.pair (by native_decide))
  have headResolved : MidpointResolved interval tangencyLeftPolynomial := by
    native_decide
  let result := neutralChainCertificate?_succeeds_of_resolutionBounds interval
    proper tangencyLeftPolynomial [tangencyMiddlePolynomial, ⟨[1]⟩]
    bounds headResolved
  change (neutralChainCertificate? interval proper tangencyLeftPolynomial
    [tangencyMiddlePolynomial, ⟨[1]⟩]).isSome = true
  rw [result.2]
  rfl

/-- Regression for the case excluded by the former one-event-only model:
the first cubic member and a nonadjacent residual member cross simultaneously,
yet the recursive neutral-chain certificate accepts the whole first event. -/
theorem firstChainEventCertificate_simultaneous_cubic_example :
    (firstChainEventCertificate? simultaneousCubicSquarefreeInput
      ⟨-1 / 64, 1 / 64⟩
      (by norm_num [RationalInterval.Proper])).isSome = true := by
  native_decide

/-- Native regression for the complete first-event classifier, including the
residual signed-chain sign scan. -/
theorem firstChainEventCertificate_quadratic_example :
    (firstChainEventCertificate? quadraticSquarefreeInput
      ⟨3 / 4, 5 / 4⟩
      (by norm_num [RationalInterval.Proper])).isSome = true := by
  native_decide

/-- One finite observation labelled by a doubled Sturm count of two. -/
structure CountOneInterval (p : RatPolynomial) where
  interval : RationalInterval
  proper : interval.Proper
  countOne : sturmRootCount2 p interval.lower interval.upper = 2
  lowerClear : p.eval interval.lower ≠ 0
  upperClear : p.eval interval.upper ≠ 0

/-- Nonnegativity part of Theorem 3.2(d), isolated as the exact theorem needed
by the refinement machine. -/
def SturmNonnegativeLaw {p : RatPolynomial} (_input : SquarefreeInput p) : Prop :=
  ∀ {a b : ℚ}, a < b → p.eval a ≠ 0 → p.eval b ≠ 0 →
    0 ≤ sturmRootCount2 p a b

/-- Classification of one terminal cell in the finite sign-event
decomposition from Theorem 3.2(d). -/
inductive EventKind where
  | interior
  | firstMember
deriving DecidableEq, Repr

def EventKind.contribution2 : EventKind → ℤ
  | .interior => 0
  | .firstMember => 2

def EventKind.firstMemberCount : EventKind → ℕ
  | .interior => 0
  | .firstMember => 1

@[simp] theorem EventKind.contribution2_eq_two_mul (kind : EventKind) :
    kind.contribution2 = 2 * kind.firstMemberCount := by
  cases kind <;> rfl

/-- A finite recursive partition certificate.  A leaf carries the exact local
signed-remainder cancellation result; a split carries the rational cut and
two finite child certificates. -/
inductive EventPartition (p : RatPolynomial) : RationalInterval → Type
  | leaf {interval : RationalInterval}
      (proper : interval.Proper)
      (lowerClear : p.eval interval.lower ≠ 0)
      (upperClear : p.eval interval.upper ≠ 0)
      (kind : EventKind)
      (countCertificate :
        sturmRootCount2 p interval.lower interval.upper = kind.contribution2) :
      EventPartition p interval
  | split {interval : RationalInterval} (cut : ℚ)
      (lowerLt : interval.lower < cut) (ltUpper : cut < interval.upper)
      (cutClear : p.eval cut ≠ 0)
      (left : EventPartition p (interval.left cut))
      (right : EventPartition p (interval.right cut)) :
      EventPartition p interval

namespace EventPartition

/-- Number of terminal first-member event cells in a finite partition. -/
def firstMemberCount {p : RatPolynomial} {interval : RationalInterval} :
    EventPartition p interval → ℕ
  | .leaf _ _ _ kind _ => kind.firstMemberCount
  | .split _ _ _ _ left right => left.firstMemberCount + right.firstMemberCount

/-- Iterated subdivision and local cancellation make the parent Sturm count
exactly twice the number of first-member leaves. -/
theorem count_eq_two_mul_firstMemberCount
    {p : RatPolynomial} {interval : RationalInterval}
    (partition : EventPartition p interval) :
    sturmRootCount2 p interval.lower interval.upper =
      2 * (partition.firstMemberCount : ℤ) := by
  induction partition with
  | leaf proper lowerClear upperClear kind countCertificate =>
      rw [countCertificate, EventKind.contribution2_eq_two_mul]
      rfl
  | @split partitionInterval cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      have hadd := sturmRootCount2_add
        p partitionInterval.lower cut partitionInterval.upper
      have leftIH' : sturmRootCount2 p partitionInterval.lower cut =
          2 * (left.firstMemberCount : ℤ) := by
        simpa only [RationalInterval.left] using leftIH
      have rightIH' : sturmRootCount2 p cut partitionInterval.upper =
          2 * (right.firstMemberCount : ℤ) := by
        simpa only [RationalInterval.right] using rightIH
      change sturmRootCount2 p partitionInterval.lower partitionInterval.upper =
        2 * ((left.firstMemberCount + right.firstMemberCount : ℕ) : ℤ)
      calc
        sturmRootCount2 p partitionInterval.lower partitionInterval.upper =
            sturmRootCount2 p partitionInterval.lower cut +
              sturmRootCount2 p cut partitionInterval.upper := hadd.symm
        _ = 2 * (left.firstMemberCount : ℤ) +
            2 * (right.firstMemberCount : ℤ) := by rw [leftIH', rightIH']
        _ = 2 * ((left.firstMemberCount + right.firstMemberCount : ℕ) : ℤ) := by
          rw [Nat.cast_add, mul_add]

theorem count_nonnegative {p : RatPolynomial} {interval : RationalInterval}
    (partition : EventPartition p interval) :
    0 ≤ sturmRootCount2 p interval.lower interval.upper := by
  rw [partition.count_eq_two_mul_firstMemberCount]
  positivity

end EventPartition

/-- Decidable local contribution classifier.  It accepts an oriented first
event together with any number of neutral residual events, or a completely
neutral chain.  The older one-event scanner remains as a conservative
fallback. -/
def classifiedEventLeaf? {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval)
    (proper : interval.Proper) (lowerClear : p.eval interval.lower ≠ 0)
    (upperClear : p.eval interval.upper ≠ 0) :
    Option (EventPartition p interval) :=
  match firstChainEventCertificate? input interval proper with
  | some first =>
      some (.leaf proper lowerClear upperClear .firstMember (by
        simpa [EventKind.contribution2] using first.count_eq_two))
  | none =>
      match firstPairNoEventCertificate? input interval proper with
      | some noEvent =>
          some (.leaf proper lowerClear upperClear .interior (by
            simpa [EventKind.contribution2] using noEvent.count_eq_zero))
      | none =>
          match neutralChainCertificates? interval proper
              (cauchyChain (derivative p) p) with
          | some stable =>
              some (.leaf proper lowerClear upperClear .interior (by
                simpa [EventKind.contribution2] using
                  stable.sturmRootCount2_eq_zero))
          | none =>
              match interiorSturmEventCertificate? p interval proper with
              | some interior =>
                  some (.leaf proper lowerClear upperClear .interior (by
                    simpa [EventKind.contribution2] using
                      interior.sturmRootCount2_eq_zero))
              | none => none

/-- Every successful local classifier result is genuinely a single leaf,
not an internally split event partition. -/
theorem classifiedEventLeaf?_some_isLeaf
    {p : RatPolynomial} {interval : RationalInterval}
    {proper : interval.Proper} {lowerClear : p.eval interval.lower ≠ 0}
    {upperClear : p.eval interval.upper ≠ 0}
    {partition : EventPartition p interval} {input : SquarefreeInput p}
    (success : classifiedEventLeaf? input interval proper lowerClear upperClear =
      some partition) :
    ∃ kind : EventKind,
      ∃ countCertificate :
        sturmRootCount2 p interval.lower interval.upper = kind.contribution2,
        partition = .leaf proper lowerClear upperClear kind countCertificate := by
  simp only [classifiedEventLeaf?] at success
  split at success
  · rename_i first firstFound
    simp only [Option.some.injEq] at success
    subst partition
    refine ⟨.firstMember, ?_, rfl⟩
    simpa [EventKind.contribution2] using first.count_eq_two
  · split at success
    · rename_i noEvent noEventFound
      simp only [Option.some.injEq] at success
      subst partition
      refine ⟨.interior, ?_, rfl⟩
      simpa [EventKind.contribution2] using noEvent.count_eq_zero
    · split at success
      · rename_i stable stableFound
        simp only [Option.some.injEq] at success
        subst partition
        refine ⟨.interior, ?_, rfl⟩
        simpa [EventKind.contribution2] using
          stable.sturmRootCount2_eq_zero
      · split at success
        · rename_i interior interiorFound
          simp only [Option.some.injEq] at success
          subst partition
          refine ⟨.interior, ?_, rfl⟩
          simpa [EventKind.contribution2] using
            interior.sturmRootCount2_eq_zero
        · simp at success

theorem classifiedEventLeaf?_some_count
    {p : RatPolynomial} {interval : RationalInterval}
    {proper : interval.Proper} {lowerClear : p.eval interval.lower ≠ 0}
    {upperClear : p.eval interval.upper ≠ 0}
    {partition : EventPartition p interval}
    {input : SquarefreeInput p}
    (h : classifiedEventLeaf? input interval proper lowerClear upperClear =
      some partition) :
    sturmRootCount2 p interval.lower interval.upper = 0 ∨
      sturmRootCount2 p interval.lower interval.upper = 2 := by
  simp only [classifiedEventLeaf?] at h
  split at h
  · right
    rename_i first hfirst
    exact first.count_eq_two
  · split at h
    · left
      rename_i noEvent hnoEvent
      exact noEvent.count_eq_zero
    · split at h
      · left
        rename_i stable hstable
        exact stable.sturmRootCount2_eq_zero
      · split at h
        · left
          rename_i interior hinterior
          exact interior.sturmRootCount2_eq_zero
        · contradiction

/-- Native regressions for both genuine local leaf kinds of `T² - 1`. -/
theorem classifiedEventLeaf_first_quadratic_example :
    (classifiedEventLeaf? quadraticSquarefreeInput ⟨3 / 4, 5 / 4⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide)).isSome = true := by
  native_decide

theorem classifiedEventLeaf_interior_quadratic_example :
    (classifiedEventLeaf? quadraticSquarefreeInput ⟨-1 / 4, 1 / 4⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide)).isSome = true := by
  native_decide

/-- One root-ambient width resolving both the oriented first-member test and
every local test in the complete gcd-reduced signed derivative chain. -/
def ambientEventClassifierWidthResolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) : ℚ :=
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  let coprime := derivativeReducedPairCertificate input
  let B := intervalMagnitude root.lower root.upper
  min (ambientFirstMemberWidthResolution input root)
    (2 * signedChainAmbientRadius denominator numerator coprime B)

theorem ambientEventClassifierWidthResolution_pos {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) :
    0 < ambientEventClassifierWidthResolution input root := by
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  let coprime := derivativeReducedPairCertificate input
  let B := intervalMagnitude root.lower root.upper
  apply lt_min
  · exact ambientFirstMemberWidthResolution_pos input root
  · exact mul_pos (by norm_num)
      (signedChainAmbientRadius_pos denominator numerator coprime
        (intervalMagnitude_pos root.lower root.upper).le)

/-- Every proper clear refinement below the computed ambient width is
accepted by the genuine finite event classifier.  The proof follows the
classifier's actual executable branches and returns its exact output. -/
def classifiedEventLeaf?_succeeds_of_refined_width
    {p : RatPolynomial} (input : SquarefreeInput p)
    (root interval : RationalInterval) (hrefines : interval.Refines root)
    (proper : interval.Proper)
    (lowerClear : p.eval interval.lower ≠ 0)
    (upperClear : p.eval interval.upper ≠ 0)
    (hwidth : interval.width < ambientEventClassifierWidthResolution input root) :
    { partition : EventPartition p interval //
      classifiedEventLeaf? input interval proper lowerClear upperClear =
        some partition } := by
  let denominator := reducedDenominator (derivative p) p
  let numerator := reducedNumerator (derivative p) p
  let coprime := derivativeReducedPairCertificate input
  let B := intervalMagnitude root.lower root.upper
  have hfirstWidth : interval.width <
      ambientFirstMemberWidthResolution input root :=
    hwidth.trans_le (by
      dsimp only [ambientEventClassifierWidthResolution]
      exact min_le_left _ _)
  have hchainWidth : interval.width <
      2 * signedChainAmbientRadius denominator numerator coprime B :=
    hwidth.trans_le (by
      dsimp only [ambientEventClassifierWidthResolution, denominator, numerator,
        coprime, B]
      exact min_le_right _ _)
  have hradius : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
      signedChainAmbientRadius denominator numerator coprime B := by
    rw [interval.midpointRadius_eq_half_width proper]
    linarith
  have bounds : NeutralChainResolutionBounds interval denominator
      (signedRemainderChain denominator numerator).tail :=
    signedChainResolutionBoundsOfAmbient root interval hrefines proper
      denominator numerator coprime hradius
  by_cases denominatorResolved : MidpointResolved interval denominator
  · have stableResultRaw :=
      neutralSignedRemainderChainCertificates?_succeeds_of_resolutionBounds
        interval proper denominator numerator bounds denominatorResolved
    have stableResult :
        { certificates : NeutralChainCertificates interval
            (cauchyChain (derivative p) p) //
          neutralChainCertificates? interval proper
              (cauchyChain (derivative p) p) = some certificates } := by
      simpa only [cauchyChain, denominator, numerator] using stableResultRaw
    cases hfirst : firstChainEventCertificate? input interval proper with
    | some first =>
        refine ⟨.leaf proper lowerClear upperClear .firstMember ?_, ?_⟩
        · simpa [EventKind.contribution2] using first.count_eq_two
        · simp [classifiedEventLeaf?, hfirst]
    | none =>
        cases hpair : firstPairNoEventCertificate? input interval proper with
        | some noEvent =>
            refine ⟨.leaf proper lowerClear upperClear .interior ?_, ?_⟩
            · simpa [EventKind.contribution2] using noEvent.count_eq_zero
            · simp [classifiedEventLeaf?, hfirst, hpair]
        | none =>
            refine ⟨.leaf proper lowerClear upperClear .interior ?_, ?_⟩
            · simpa [EventKind.contribution2] using
                stableResult.1.sturmRootCount2_eq_zero
            · simp [classifiedEventLeaf?, hfirst, hpair, stableResult.2]
  · have hnumerator : numerator.isZero = false :=
      reducedNumerator_isZero_false
        (derivative_isZero_false input.nonzero input.nonconstant)
    have boundsFromSecond := bounds
    rw [signedRemainderChain_tail_eq_of_second_nonzero denominator numerator
      hnumerator] at boundsFromSecond
    have numeratorResolved : MidpointResolved interval numerator :=
      boundsFromSecond.secondResolvedOfFirstUnresolved proper denominatorResolved
    have restResult :=
      derivativeRestChainCertificates?_succeeds_of_resolutionBounds input
        interval proper bounds denominatorResolved
    by_cases crossing : p.eval interval.lower * p.eval interval.upper < 0
    · have firstInequalities := firstMember_inequalities_of_refined_width input
        root interval hrefines proper crossing hfirstWidth
      have firstSome := firstMemberCellCertificate?_isSome_of_small_crossing
        input interval proper crossing firstInequalities.1 firstInequalities.2
      cases hfirst : firstMemberCellCertificate? p interval proper with
      | none => simp [hfirst] at firstSome
      | some first =>
          let firstChain : FirstChainEventCertificate input interval :=
            { first := first, restStable := restResult.1 }
          have hfirstChain : firstChainEventCertificate? input interval proper =
              some firstChain := by
            simp [firstChainEventCertificate?, hfirst, restResult.2, firstChain]
          refine ⟨.leaf proper lowerClear upperClear .firstMember ?_, ?_⟩
          · simpa [EventKind.contribution2] using firstChain.count_eq_two
          · simp [classifiedEventLeaf?, hfirstChain]
    · have productNonzero :
          p.eval interval.lower * p.eval interval.upper ≠ 0 :=
        mul_ne_zero lowerClear upperClear
      have firstSame : 0 < p.eval interval.lower * p.eval interval.upper :=
        lt_of_le_of_ne (le_of_not_gt crossing) (Ne.symm productNonzero)
      have pairUnchanged := reducedPairEndpointVariation_eq_of_same_first_sign
        input interval proper firstSame (by
          simpa only [numerator] using numeratorResolved)
      let noEvent : FirstPairNoEventCertificate input interval :=
        { pairUnchanged := pairUnchanged, restStable := restResult.1 }
      have hnoEvent : firstPairNoEventCertificate? input interval proper =
          some noEvent := by
        simp [firstPairNoEventCertificate?, pairUnchanged, restResult.2, noEvent]
      cases hfirstChain : firstChainEventCertificate? input interval proper with
      | some first =>
          refine ⟨.leaf proper lowerClear upperClear .firstMember ?_, ?_⟩
          · simpa [EventKind.contribution2] using first.count_eq_two
          · simp [classifiedEventLeaf?, hfirstChain]
      | none =>
          refine ⟨.leaf proper lowerClear upperClear .interior ?_, ?_⟩
          · simpa [EventKind.contribution2] using noEvent.count_eq_zero
          · simp [classifiedEventLeaf?, hfirstChain, hnoEvent]

/-- Local-completeness datum: every clear proper subinterval of the root whose
width is below `threshold` is accepted by the genuine finite sign-event
classifier. -/
structure EventClassifierResolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) where
  threshold : ℚ
  positive : 0 < threshold
  classify : ∀ (interval : RationalInterval), interval.Refines root →
    (proper : interval.Proper) →
    (lowerClear : p.eval interval.lower ≠ 0) →
    (upperClear : p.eval interval.upper ≠ 0) →
    interval.width < threshold →
      { partition : EventPartition p interval //
        classifiedEventLeaf? input interval proper lowerClear upperClear =
          some partition }

/-- Uniform constructive provider for root-dependent local resolution data. -/
structure EventClassifierResolutionProgram {p : RatPolynomial}
    (input : SquarefreeInput p) where
  resolve : ∀ (a b : ℚ), a < b →
    EventClassifierResolution input ⟨a, b⟩

/-- The explicit Bézout--Taylor--Euclidean width is the local classifier
resolution required by the finite partition builder. -/
def computedEventClassifierResolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) :
    EventClassifierResolution input root where
  threshold := ambientEventClassifierWidthResolution input root
  positive := ambientEventClassifierWidthResolution_pos input root
  classify := by
    intro interval hrefines proper lowerClear upperClear hwidth
    exact classifiedEventLeaf?_succeeds_of_refined_width input root interval
      hrefines proper lowerClear upperClear hwidth

/-- Uniform executable resolution program for every rational root interval. -/
def computedEventClassifierResolutionProgram {p : RatPolynomial}
    (input : SquarefreeInput p) : EventClassifierResolutionProgram input where
  resolve := fun a b _hab =>
    computedEventClassifierResolution input ⟨a, b⟩

/-- Regression through the computed uniform resolution, rather than a direct
Boolean check, for the positive root of `T² - 1`. -/
theorem computedEventClassifierResolution_quadratic_first_example :
    (classifiedEventLeaf? quadraticSquarefreeInput
      ⟨1048575 / 1048576, 1048577 / 1048576⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide)).isSome = true := by
  let root : RationalInterval := ⟨-2, 2⟩
  let interval : RationalInterval :=
    ⟨1048575 / 1048576, 1048577 / 1048576⟩
  have hrefines : interval.Refines root := by
    norm_num [interval, root, RationalInterval.Refines]
  have proper : interval.Proper := by
    norm_num [interval, RationalInterval.Proper]
  have lowerClear : quadraticPolynomial.eval interval.lower ≠ 0 := by
    native_decide
  have upperClear : quadraticPolynomial.eval interval.upper ≠ 0 := by
    native_decide
  have hwidth : interval.width <
      (computedEventClassifierResolution quadraticSquarefreeInput root).threshold := by
    native_decide
  let result := (computedEventClassifierResolution quadraticSquarefreeInput root).classify
    interval hrefines proper lowerClear upperClear hwidth
  change (classifiedEventLeaf? quadraticSquarefreeInput interval proper
    lowerClear upperClear).isSome = true
  rw [result.2]
  rfl

/-- The same computed resolution recognizes the neutral derivative event at
zero, exercising the full-chain branch. -/
theorem computedEventClassifierResolution_quadratic_interior_example :
    (classifiedEventLeaf? quadraticSquarefreeInput
      ⟨-1 / 1048576, 1 / 1048576⟩
      (by norm_num [RationalInterval.Proper])
      (by native_decide) (by native_decide)).isSome = true := by
  let root : RationalInterval := ⟨-2, 2⟩
  let interval : RationalInterval := ⟨-1 / 1048576, 1 / 1048576⟩
  have hrefines : interval.Refines root := by
    norm_num [interval, root, RationalInterval.Refines]
  have proper : interval.Proper := by
    norm_num [interval, RationalInterval.Proper]
  have lowerClear : quadraticPolynomial.eval interval.lower ≠ 0 := by
    native_decide
  have upperClear : quadraticPolynomial.eval interval.upper ≠ 0 := by
    native_decide
  have hwidth : interval.width <
      (computedEventClassifierResolution quadraticSquarefreeInput root).threshold := by
    native_decide
  let result := (computedEventClassifierResolution quadraticSquarefreeInput root).classify
    interval hrefines proper lowerClear upperClear hwidth
  change (classifiedEventLeaf? quadraticSquarefreeInput interval proper
    lowerClear upperClear).isSome = true
  rw [result.2]
  rfl

/-- One executable simultaneous-guard cut for an arbitrary proper interval. -/
structure GuardedIntervalCut {p : RatPolynomial} (interval : RationalInterval) where
  point : ℚ
  lowerLt : interval.lower < point
  ltUpper : point < interval.upper
  centralLeftLt : centralLeft interval.lower interval.upper < point
  ltCentralRight : point < centralRight interval.lower interval.upper
  clear : p.eval point ≠ 0

def guardedIntervalCut {p : RatPolynomial} (input : SquarefreeInput p)
    (interval : RationalInterval) (proper : interval.Proper) :
    GuardedIntervalCut (p := p) interval := by
  let c := safeCut p interval.lower interval.upper
  have hspec := safeCut_spec input proper
  have hproper := proper
  change interval.lower < interval.upper at hproper
  refine
    { point := c
      lowerLt := ?_
      ltUpper := ?_
      centralLeftLt := hspec.2.1
      ltCentralRight := hspec.2.2
      clear := ?_ }
  · have hleft := hspec.2.1
    dsimp only [c, centralLeft] at hleft ⊢
    linarith
  · have hright := hspec.2.2
    dsimp only [c, centralRight] at hright ⊢
    linarith
  · dsimp only [c]
    exact safeCut_polynomial_ne_zero input proper

theorem guardedIntervalCut_left_width_lt {p : RatPolynomial}
    (input : SquarefreeInput p) (interval : RationalInterval)
    (proper : interval.Proper) :
    (interval.left (guardedIntervalCut input interval proper).point).width <
      (2 / 3 : ℚ) * interval.width := by
  have hcentral := (guardedIntervalCut input interval proper).ltCentralRight
  dsimp [RationalInterval.left, RationalInterval.width, centralRight] at hcentral ⊢
  linarith

theorem guardedIntervalCut_right_width_lt {p : RatPolynomial}
    (input : SquarefreeInput p) (interval : RationalInterval)
    (proper : interval.Proper) :
    (interval.right (guardedIntervalCut input interval proper).point).width <
      (2 / 3 : ℚ) * interval.width := by
  have hcentral := (guardedIntervalCut input interval proper).centralLeftLt
  dsimp [RationalInterval.right, RationalInterval.width, centralLeft] at hcentral ⊢
  linarith

theorem guardedIntervalCut_left_refines {p : RatPolynomial}
    (input : SquarefreeInput p) (interval : RationalInterval)
    (proper : interval.Proper) :
    (interval.left (guardedIntervalCut input interval proper).point).Refines interval :=
  ⟨le_rfl, (guardedIntervalCut input interval proper).ltUpper.le⟩

theorem guardedIntervalCut_right_refines {p : RatPolynomial}
    (input : SquarefreeInput p) (interval : RationalInterval)
    (proper : interval.Proper) :
    (interval.right (guardedIntervalCut input interval proper).point).Refines interval :=
  ⟨(guardedIntervalCut input interval proper).lowerLt.le, le_rfl⟩

/-- Fuel-recursive central-third event decomposition.  Failure is explicit;
the separation-depth theorem must prove that a displayed fuel makes every
terminal classifier succeed. -/
def buildEventPartition? {p : RatPolynomial} (input : SquarefreeInput p) :
    (fuel : ℕ) → (interval : RationalInterval) → interval.Proper →
      p.eval interval.lower ≠ 0 → p.eval interval.upper ≠ 0 →
        Option (EventPartition p interval)
  | 0, interval, proper, lowerClear, upperClear =>
      classifiedEventLeaf? input interval proper lowerClear upperClear
  | fuel + 1, interval, proper, lowerClear, upperClear =>
      match classifiedEventLeaf? input interval proper lowerClear upperClear with
      | some partition => some partition
      | none =>
          let cut := guardedIntervalCut input interval proper
          match buildEventPartition? input fuel (interval.left cut.point)
              cut.lowerLt lowerClear cut.clear with
          | none => none
          | some left =>
              match buildEventPartition? input fuel (interval.right cut.point)
                  cut.ltUpper cut.clear upperClear with
              | none => none
              | some right => some (.split cut.point cut.lowerLt cut.ltUpper
                  cut.clear left right)

/-- A displayed classifier resolution and a displayed geometric depth make
the fuel-recursive partition builder constructively successful. -/
def buildEventPartition?_succeeds_of_resolution
    {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) (resolution : EventClassifierResolution input root)
    (fuel : ℕ) (interval : RationalInterval) (hrefines : interval.Refines root)
    (proper : interval.Proper) (lowerClear : p.eval interval.lower ≠ 0)
    (upperClear : p.eval interval.upper ≠ 0)
    (hsufficient : (2 / 3 : ℚ) ^ fuel * interval.width < resolution.threshold) :
    { partition : EventPartition p interval //
      buildEventPartition? input fuel interval proper lowerClear upperClear =
        some partition } := by
  induction fuel generalizing interval with
  | zero =>
      apply resolution.classify interval hrefines proper lowerClear upperClear
      simpa using hsufficient
  | succ fuel ih =>
      cases hclassified : classifiedEventLeaf? input interval proper
          lowerClear upperClear with
      | some partition =>
          exact ⟨partition, by simp [buildEventPartition?, hclassified]⟩
      | none =>
          let cut := guardedIntervalCut input interval proper
          let leftInterval := interval.left cut.point
          let rightInterval := interval.right cut.point
          have hfactor : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
          have hleftWidth : leftInterval.width <
              (2 / 3 : ℚ) * interval.width := by
            simpa [cut, leftInterval] using
              guardedIntervalCut_left_width_lt input interval proper
          have hrightWidth : rightInterval.width <
              (2 / 3 : ℚ) * interval.width := by
            simpa [cut, rightInterval] using
              guardedIntervalCut_right_width_lt input interval proper
          have hleftSufficient : (2 / 3 : ℚ) ^ fuel * leftInterval.width <
              resolution.threshold := by
            calc
              (2 / 3 : ℚ) ^ fuel * leftInterval.width <
                  (2 / 3 : ℚ) ^ fuel *
                    ((2 / 3 : ℚ) * interval.width) :=
                mul_lt_mul_of_pos_left hleftWidth hfactor
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
                rw [pow_succ]
                ring
              _ < resolution.threshold := by simpa [Nat.succ_eq_add_one] using hsufficient
          have hrightSufficient : (2 / 3 : ℚ) ^ fuel * rightInterval.width <
              resolution.threshold := by
            calc
              (2 / 3 : ℚ) ^ fuel * rightInterval.width <
                  (2 / 3 : ℚ) ^ fuel *
                    ((2 / 3 : ℚ) * interval.width) :=
                mul_lt_mul_of_pos_left hrightWidth hfactor
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
                rw [pow_succ]
                ring
              _ < resolution.threshold := by simpa [Nat.succ_eq_add_one] using hsufficient
          have hleftRefines : leftInterval.Refines root :=
            RationalInterval.refines_trans
              (by simpa [cut, leftInterval] using
                guardedIntervalCut_left_refines input interval proper)
              hrefines
          have hrightRefines : rightInterval.Refines root :=
            RationalInterval.refines_trans
              (by simpa [cut, rightInterval] using
                guardedIntervalCut_right_refines input interval proper)
              hrefines
          have leftResult := ih leftInterval hleftRefines cut.lowerLt
            lowerClear cut.clear hleftSufficient
          have rightResult := ih rightInterval hrightRefines cut.ltUpper
            cut.clear upperClear hrightSufficient
          refine ⟨.split cut.point cut.lowerLt cut.ltUpper cut.clear
            leftResult.1 rightResult.1, ?_⟩
          simp [buildEventPartition?, hclassified, cut, leftInterval, rightInterval,
            leftResult.2, rightResult.2]

theorem buildEventPartition?_some_nonnegative
    {p : RatPolynomial} (input : SquarefreeInput p) (fuel : ℕ)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear : p.eval interval.lower ≠ 0)
    (upperClear : p.eval interval.upper ≠ 0)
    {partition : EventPartition p interval}
    (_hbuild : buildEventPartition? input fuel interval proper lowerClear upperClear =
      some partition) :
    0 ≤ sturmRootCount2 p interval.lower interval.upper :=
  partition.count_nonnegative

/-- Constructive output interface for Theorem 3.2(d): every clear rational
interval is answered by finite partition data, not merely by an existential
proposition. -/
structure EventPartitionProgram {p : RatPolynomial} (_input : SquarefreeInput p) where
  run : ∀ (a b : ℚ), a < b → p.eval a ≠ 0 → p.eval b ≠ 0 →
    EventPartition p ⟨a, b⟩

/-- Standalone proof transcript for a successful fuel-recursive build.  The
equality records that the executable builder actually returns the displayed
partition at the displayed depth. -/
structure SuccessfulEventPartitionBuild {p : RatPolynomial}
    (input : SquarefreeInput p) where
  depth : ℚ → ℚ → ℕ
  partition : ∀ (a b : ℚ), (proper : a < b) →
    (lowerClear : p.eval a ≠ 0) → (upperClear : p.eval b ≠ 0) →
      EventPartition p ⟨a, b⟩
  succeeds : ∀ (a b : ℚ), (proper : a < b) →
    (lowerClear : p.eval a ≠ 0) → (upperClear : p.eval b ≠ 0) →
      buildEventPartition? input (depth a b) ⟨a, b⟩ proper lowerClear upperClear =
        some (partition a b proper lowerClear upperClear)

/-- A certified successful run supplies the event-partition program consumed
by all later refinement operations. -/
def SuccessfulEventPartitionBuild.toProgram {p : RatPolynomial}
    {input : SquarefreeInput p} (build : SuccessfulEventPartitionBuild input) :
    EventPartitionProgram input where
  run := build.partition

theorem EventPartitionProgram.nonnegativeLaw {p : RatPolynomial}
    {input : SquarefreeInput p} (program : EventPartitionProgram input) :
    SturmNonnegativeLaw input := by
  intro a b hab ha hb
  exact (program.run a b hab ha hb).count_nonnegative

def cutFor {p : RatPolynomial} (_input : SquarefreeInput p)
    (parent : CountOneInterval p) : ℚ :=
  safeCut p parent.interval.lower parent.interval.upper

/-- The event-decomposition fact consumed by one count-one refinement.  The
universal Sturm isolation theorem will provide this dichotomy once its
separation-depth hypotheses are in place. -/
def LeftSplitDichotomy {p : RatPolynomial} (input : SquarefreeInput p)
    (parent : CountOneInterval p) : Prop :=
  sturmRootCount2 p parent.interval.lower (cutFor input parent) = 0 ∨
    sturmRootCount2 p parent.interval.lower (cutFor input parent) = 2

/-- Additivity, endpoint parity, and nonnegativity force a count-one parent to
put count one on exactly one side of every safe cut. -/
theorem leftSplitDichotomy_of_nonnegative {p : RatPolynomial}
    (input : SquarefreeInput p) (nonnegative : SturmNonnegativeLaw input)
    (parent : CountOneInterval p) : LeftSplitDichotomy input parent := by
  let c := cutFor input parent
  have hsafe := safeCut_spec input parent.proper
  have hleftCentral := hsafe.2.1
  have hrightCentral := hsafe.2.2
  have hproper := parent.proper
  change parent.interval.lower < parent.interval.upper at hproper
  have hlower : parent.interval.lower < c := by
    dsimp only [c, cutFor, centralLeft] at hleftCentral ⊢
    linarith
  have hupper : c < parent.interval.upper := by
    dsimp only [c, cutFor, centralRight] at hrightCentral ⊢
    linarith
  have hcut : p.eval c ≠ 0 := by
    dsimp only [c, cutFor]
    exact safeCut_polynomial_ne_zero input parent.proper
  have hleftNonneg :
      0 ≤ sturmRootCount2 p parent.interval.lower c :=
    nonnegative hlower parent.lowerClear hcut
  have hrightNonneg :
      0 ≤ sturmRootCount2 p c parent.interval.upper :=
    nonnegative hupper hcut parent.upperClear
  have hsum := sturmRootCount2_add
    p parent.interval.lower c parent.interval.upper
  rw [parent.countOne] at hsum
  have heven := sturmRootCount2_even input.nonzero input.nonconstant
    parent.lowerClear hcut
  rcases heven with ⟨k, hk⟩
  change sturmRootCount2 p parent.interval.lower c = 0 ∨
    sturmRootCount2 p parent.interval.lower c = 2
  omega

/-- Certified output of one transducer step. -/
structure RefinementResult {p : RatPolynomial} (parent : CountOneInterval p) where
  child : CountOneInterval p
  refines : child.interval.Refines parent.interval
  widthContract : child.interval.width < (2 / 3 : ℚ) * parent.interval.width

/-- Deterministically retain the count-one child of a safe central-third cut. -/
def refineCountOne {p : RatPolynomial} (input : SquarefreeInput p)
    (parent : CountOneInterval p) (hsplit : LeftSplitDichotomy input parent) :
    RefinementResult parent := by
  let c := cutFor input parent
  have hsafe := safeCut_spec input parent.proper
  have hguard : (chainGuard p).eval c ≠ 0 := hsafe.1
  have hcentralLeft : centralLeft parent.interval.lower parent.interval.upper < c := hsafe.2.1
  have hcentralRight : c < centralRight parent.interval.lower parent.interval.upper := hsafe.2.2
  have hproper := parent.proper
  change parent.interval.lower < parent.interval.upper at hproper
  have hlower : parent.interval.lower < c := by
    dsimp [centralLeft] at hcentralLeft
    linarith
  have hupper : c < parent.interval.upper := by
    dsimp [centralRight] at hcentralRight
    linarith
  have hcut : p.eval c ≠ 0 := by
    apply eval_ne_zero_of_mem_of_polynomialProduct_ne_zero
      (by simp [derivativeChain]) hguard
  have hsum := sturmRootCount2_add p parent.interval.lower c parent.interval.upper
  rw [parent.countOne] at hsum
  by_cases hleft : sturmRootCount2 p parent.interval.lower c = 2
  · refine
      { child :=
          { interval := parent.interval.left c
            proper := hlower
            countOne := hleft
            lowerClear := parent.lowerClear
            upperClear := hcut }
        refines := ?_
        widthContract := ?_ }
    · exact ⟨le_rfl, hupper.le⟩
    · dsimp [RationalInterval.left, RationalInterval.width, centralRight] at hcentralRight ⊢
      linarith
  · have hleftZero : sturmRootCount2 p parent.interval.lower c = 0 :=
      hsplit.resolve_right hleft
    have hright : sturmRootCount2 p c parent.interval.upper = 2 := by omega
    refine
      { child :=
          { interval := parent.interval.right c
            proper := hupper
            countOne := hright
            lowerClear := hcut
            upperClear := parent.upperClear }
        refines := ?_
        widthContract := ?_ }
    · exact ⟨hlower.le, le_rfl⟩
    · dsimp [RationalInterval.right, RationalInterval.width, centralLeft] at hcentralLeft ⊢
      linarith

/-- Global finite-event dichotomy needed by the repeated count-one machine. -/
def SplitLaw {p : RatPolynomial} (input : SquarefreeInput p) : Prop :=
  ∀ parent : CountOneInterval p, LeftSplitDichotomy input parent

theorem splitLaw_of_nonnegative {p : RatPolynomial}
    (input : SquarefreeInput p) (nonnegative : SturmNonnegativeLaw input) :
    SplitLaw input := by
  intro parent
  exact leftSplitDichotomy_of_nonnegative input nonnegative parent

theorem EventPartitionProgram.splitLaw {p : RatPolynomial}
    {input : SquarefreeInput p} (program : EventPartitionProgram input) :
    SplitLaw input :=
  splitLaw_of_nonnegative input program.nonnegativeLaw

def refineStep {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p) :
    CountOneInterval p :=
  (refineCountOne input parent (program.splitLaw parent)).child

theorem refineStep_refines {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p) :
    (refineStep input program parent).interval.Refines parent.interval :=
  (refineCountOne input parent (program.splitLaw parent)).refines

theorem refineStep_width_lt {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p) :
    (refineStep input program parent).interval.width <
      (2 / 3 : ℚ) * parent.interval.width :=
  (refineCountOne input parent (program.splitLaw parent)).widthContract

/-- Execute exactly `depth` finite safe-cut refinements. -/
def refineN {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) : ℕ → CountOneInterval p → CountOneInterval p
  | 0, parent => parent
  | depth + 1, parent => refineN input program depth (refineStep input program parent)

theorem refineN_refines {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (depth : ℕ) (parent : CountOneInterval p) :
    (refineN input program depth parent).interval.Refines parent.interval := by
  induction depth generalizing parent with
  | zero => exact RationalInterval.refines_refl parent.interval
  | succ depth ih =>
      exact RationalInterval.refines_trans (ih (refineStep input program parent))
        (refineStep_refines input program parent)

/-- After `depth` calls, width is bounded by the displayed finite geometric
factor. -/
theorem refineN_width_le {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (depth : ℕ) (parent : CountOneInterval p) :
    (refineN input program depth parent).interval.width ≤
      (2 / 3 : ℚ) ^ depth * parent.interval.width := by
  induction depth generalizing parent with
  | zero => simp [refineN]
  | succ depth ih =>
      have hrecursive := ih (refineStep input program parent)
      have hstep := refineStep_width_lt input program parent
      have hpow : 0 ≤ (2 / 3 : ℚ) ^ depth := by positivity
      calc
        (refineN input program (depth + 1) parent).interval.width =
            (refineN input program depth (refineStep input program parent)).interval.width := rfl
        _ ≤ (2 / 3 : ℚ) ^ depth *
            (refineStep input program parent).interval.width := hrecursive
        _ ≤ (2 / 3 : ℚ) ^ depth * ((2 / 3 : ℚ) * parent.interval.width) :=
          mul_le_mul_of_nonneg_left hstep.le hpow
        _ = (2 / 3 : ℚ) ^ (depth + 1) * parent.interval.width := by
          rw [pow_succ]
          ring

/-- Finite natural-number evidence that a requested positive rational width
is reached after a displayed number of transducer calls. -/
structure WidthDepth (parent : RationalInterval) (epsilon : ℚ) where
  depth : ℕ
  epsilonPos : 0 < epsilon
  sufficient : (2 / 3 : ℚ) ^ depth * parent.width ≤ epsilon

/-- Answer a finite width request using only the certified natural depth. -/
def answerWidth {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p) (epsilon : ℚ)
    (request : WidthDepth parent.interval epsilon) : CountOneInterval p :=
  refineN input program request.depth parent

theorem answerWidth_refines {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p) (epsilon : ℚ)
    (request : WidthDepth parent.interval epsilon) :
    (answerWidth input program parent epsilon request).interval.Refines parent.interval :=
  refineN_refines input program request.depth parent

theorem answerWidth_le {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p) (epsilon : ℚ)
    (request : WidthDepth parent.interval epsilon) :
    (answerWidth input program parent epsilon request).interval.width ≤ epsilon :=
  (refineN_width_le input program request.depth parent).trans request.sufficient

/-- Explicit natural depth obtained from rational ceiling arithmetic.  The
linear bound is deliberately conservative and avoids logarithms. -/
def geometricDepth (width epsilon : ℚ) : ℕ :=
  ⌈2 * width / epsilon⌉₊

theorem geometricDepth_sufficient {width epsilon : ℚ}
    (_hwidth : 0 ≤ width) (hepsilon : 0 < epsilon) :
    (2 / 3 : ℚ) ^ geometricDepth width epsilon * width ≤ epsilon := by
  let depth := geometricDepth width epsilon
  have hceil : 2 * width / epsilon ≤ (depth : ℚ) := by
    exact Nat.le_ceil (2 * width / epsilon)
  have hratio : width / epsilon ≤ (depth : ℚ) / 2 := by
    rw [show 2 * width / epsilon = 2 * (width / epsilon) by ring] at hceil
    linarith
  have hbernoulli :
      1 + (depth : ℚ) * ((3 / 2 : ℚ) - 1) ≤ (3 / 2 : ℚ) ^ depth :=
    one_add_mul_sub_le_pow (a := (3 / 2 : ℚ)) (by norm_num) depth
  have hdepth : (depth : ℚ) / 2 ≤ (3 / 2 : ℚ) ^ depth := by
    norm_num at hbernoulli ⊢
    linarith
  have hratioPow : width / epsilon ≤ (3 / 2 : ℚ) ^ depth :=
    hratio.trans hdepth
  have hwidthBound : width ≤ epsilon * (3 / 2 : ℚ) ^ depth := by
    rw [div_le_iff₀ hepsilon] at hratioPow
    nlinarith
  have hcontractNonneg : 0 ≤ (2 / 3 : ℚ) ^ depth := by positivity
  have hinverse : (2 / 3 : ℚ) ^ depth * (3 / 2 : ℚ) ^ depth = 1 := by
    rw [← mul_pow]
    norm_num
  change (2 / 3 : ℚ) ^ depth * width ≤ epsilon
  calc
    (2 / 3 : ℚ) ^ depth * width ≤
        (2 / 3 : ℚ) ^ depth * (epsilon * (3 / 2 : ℚ) ^ depth) :=
      mul_le_mul_of_nonneg_left hwidthBound hcontractNonneg
    _ = epsilon := by rw [show (2 / 3 : ℚ) ^ depth *
      (epsilon * (3 / 2 : ℚ) ^ depth) = epsilon *
        ((2 / 3 : ℚ) ^ depth * (3 / 2 : ℚ) ^ depth) by ring, hinverse, mul_one]

/-- Explicit central-third depth chosen strictly below a local classifier's
resolution width. -/
def eventResolutionDepth {p : RatPolynomial} {input : SquarefreeInput p}
    {root : RationalInterval} (resolution : EventClassifierResolution input root) : ℕ :=
  geometricDepth root.width (resolution.threshold / 2)

theorem eventResolutionDepth_sufficient {p : RatPolynomial}
    {input : SquarefreeInput p} {root : RationalInterval}
    (proper : root.Proper) (resolution : EventClassifierResolution input root) :
    (2 / 3 : ℚ) ^ eventResolutionDepth resolution * root.width <
      resolution.threshold := by
  have hhalf : 0 < resolution.threshold / 2 := by
    linarith [resolution.positive]
  have hgeometric := geometricDepth_sufficient
    (RationalInterval.width_pos proper).le hhalf
  calc
    (2 / 3 : ℚ) ^ eventResolutionDepth resolution * root.width ≤
        resolution.threshold / 2 := by
      simpa [eventResolutionDepth] using hgeometric
    _ < resolution.threshold := by linarith [resolution.positive]

/-- A uniform root-dependent resolution and the explicit geometric scan
remove the local event-classifier parameter from the one-dimensional
transducer. -/
def EventClassifierResolutionProgram.toEventPartitionProgram
    {p : RatPolynomial} {input : SquarefreeInput p}
    (resolutions : EventClassifierResolutionProgram input) :
    EventPartitionProgram input where
  run := by
    intro a b hab lowerClear upperClear
    let root : RationalInterval := ⟨a, b⟩
    let resolution := resolutions.resolve a b hab
    let depth := eventResolutionDepth resolution
    have hsufficient : (2 / 3 : ℚ) ^ depth * root.width <
        resolution.threshold := by
      simpa [root, resolution, depth] using
        eventResolutionDepth_sufficient (root := root) hab resolution
    let result := buildEventPartition?_succeeds_of_resolution input root resolution
      depth root (RationalInterval.refines_refl root) hab lowerClear upperClear
      hsufficient
    exact result.1

/-- Canonical finite event-partition program computed from a squarefree input;
no caller-supplied resolution or termination oracle remains. -/
def computedEventPartitionProgram {p : RatPolynomial}
    (input : SquarefreeInput p) : EventPartitionProgram input :=
  (computedEventClassifierResolutionProgram input).toEventPartitionProgram

/-- Construct the finite depth certificate directly from a positive rational
accuracy request. -/
def widthDepthOf {p : RatPolynomial} (parent : CountOneInterval p)
    (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    WidthDepth parent.interval epsilon where
  depth := geometricDepth parent.interval.width epsilon
  epsilonPos := hepsilon
  sufficient := geometricDepth_sufficient
    (RationalInterval.width_pos parent.proper).le hepsilon

/-- The transducer call exposed to a client: a positive rational request is
converted to an explicit natural iteration bound and answered by a finite
count-one interval. -/
def runToWidth {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p)
    (epsilon : ℚ) (hepsilon : 0 < epsilon) : CountOneInterval p :=
  answerWidth input program parent epsilon (widthDepthOf parent epsilon hepsilon)

theorem runToWidth_refines {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p)
    (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    (runToWidth input program parent epsilon hepsilon).interval.Refines parent.interval :=
  answerWidth_refines input program parent epsilon (widthDepthOf parent epsilon hepsilon)

theorem runToWidth_le {p : RatPolynomial} (input : SquarefreeInput p)
    (program : EventPartitionProgram input) (parent : CountOneInterval p)
    (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    (runToWidth input program parent epsilon hepsilon).interval.width ≤ epsilon :=
  answerWidth_le input program parent epsilon (widthDepthOf parent epsilon hepsilon)

/-- Native check of the full simultaneous-guard search for `T` on `[-1,1]`.
The first of the three displayed safe candidates is `-1/6`. -/
theorem safeCut_linear_example :
    safeCut ⟨[1, 0]⟩ (-1) 1 = (-1 / 6 : ℚ) := by
  native_decide

end FTA.SturmTransducer

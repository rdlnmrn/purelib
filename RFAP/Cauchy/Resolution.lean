import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.ProductCells

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

namespace RFAP.CauchyResolution

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev CoprimeCertificate := RFAP.PathClearance.CoprimeCertificate
abbrev ClearanceCertificate := RFAP.PathClearance.Certificate
abbrev SignCertificate := RFAP.IntervalSign.Certificate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathClearance
open RFAP.IntervalSign
open RFAP.Sturm
open RFAP.CauchyCells

/-- A successful executable sign classification retained with its witness. -/
structure ResolvedSign (p : Polynomial) (interval : Interval) where
  certificate : SignCertificate p interval
  found : certificate? p interval = some certificate

/-- A small-cell inequality forcing one member of an adjacent clear pair to
be sign-resolved whenever the other is not. -/
def PairResolution {p q : Polynomial}
    (clearance : ClearanceCertificate p q interval) : Prop :=
  (denseEvalSqLipschitzBound p interval +
      denseEvalSqLipschitzBound q interval) *
      sampleRadiusSq interval interval.lower <
    clearance.bound

instance {p q : Polynomial} {interval : Interval}
    (clearance : ClearanceCertificate p q interval) :
    Decidable (PairResolution clearance) := by
  unfold PairResolution
  infer_instance

private theorem sampleRadiusSq_nonneg (interval : Interval) :
    0 ≤ sampleRadiusSq interval interval.lower :=
  (RFAP.ConstructiveFraction.sq_nonneg_direct
      (interval.lower - interval.lower)).trans (le_max_left _ _)

/-- Positive ambient squared radius making one adjacent-pair resolution
inequality hold on every displayed refinement. -/
def pairResolutionRadiusSq {p q : Polynomial}
    {root : Interval} (clearance : ClearanceCertificate p q root) : Coordinate :=
  clearance.bound /
    (denseEvalSqLipschitzBound p root +
      denseEvalSqLipschitzBound q root + 1)

theorem pairResolutionRadiusSq_pos {p q : Polynomial}
    {root : Interval} (clearance : ClearanceCertificate p q root) :
    0 < pairResolutionRadiusSq clearance := by
  apply RFAP.ConstructiveFraction.div_pos_direct
  · exact clearance.positive
  · have coefficientNonnegative : 0 ≤
        denseEvalSqLipschitzBound p root +
          denseEvalSqLipschitzBound q root :=
      add_nonneg (denseHornerSqBounds_nonneg p root).2
        (denseHornerSqBounds_nonneg q root).2
    calc
      0 < 1 := by decide
      _ ≤ denseEvalSqLipschitzBound p root +
          denseEvalSqLipschitzBound q root + 1 := by
        exact add_le_add coefficientNonnegative (le_refl 1)

theorem pairResolution_of_refined_radiusSq
    {p q : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate p q root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      pairResolutionRadiusSq clearance) :
    PairResolution (clearance.restrict refines) := by
  let localCoefficient := denseEvalSqLipschitzBound p interval +
    denseEvalSqLipschitzBound q interval
  let rootCoefficient := denseEvalSqLipschitzBound p root +
    denseEvalSqLipschitzBound q root
  let localRadius := sampleRadiusSq interval interval.lower
  have localCoefficientNonnegative : 0 ≤ localCoefficient :=
    add_nonneg (denseHornerSqBounds_nonneg p interval).2
      (denseHornerSqBounds_nonneg q interval).2
  have rootCoefficientNonnegative : 0 ≤ rootCoefficient :=
    add_nonneg (denseHornerSqBounds_nonneg p root).2
      (denseHornerSqBounds_nonneg q root).2
  have localRadiusNonnegative : 0 ≤ localRadius := sampleRadiusSq_nonneg interval
  have coefficientLe : localCoefficient ≤ rootCoefficient :=
    add_le_add (denseEvalSqLipschitzBound_le_of_refines p refines)
      (denseEvalSqLipschitzBound_le_of_refines q refines)
  have denominatorPositive : 0 < rootCoefficient + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ rootCoefficient + 1 := by
        exact add_le_add rootCoefficientNonnegative (le_refl 1)
  have scaledRadius : (rootCoefficient + 1) * localRadius <
      clearance.bound := by
    calc
      (rootCoefficient + 1) * localRadius <
          (rootCoefficient + 1) * pairResolutionRadiusSq clearance :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          denominatorPositive radius
      _ = clearance.bound := by
        dsimp only [pairResolutionRadiusSq]
        rw [RFAP.ConstructiveFraction.mul_comm]
        apply RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        simpa only [rootCoefficient] using denominatorPositive.ne'
  change localCoefficient * localRadius < clearance.bound
  calc
    localCoefficient * localRadius ≤ rootCoefficient * localRadius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientLe localRadiusNonnegative
    _ ≤ (rootCoefficient + 1) * localRadius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) localRadiusNonnegative
    _ < clearance.bound := scaledRadius

private theorem second_margin_of_first_unresolved
    {p q : Polynomial} {interval : Interval}
    (clearance : ClearanceCertificate p q interval)
    (resolution : PairResolution clearance)
    (firstUnresolved : ¬(
      denseEvalSqLipschitzBound p interval *
          sampleRadiusSq interval interval.lower <
        p.eval interval.lower ^ 2)) :
    denseEvalSqLipschitzBound q interval *
        sampleRadiusSq interval interval.lower <
      q.eval interval.lower ^ 2 := by
  let radius := sampleRadiusSq interval interval.lower
  let pMargin := denseEvalSqLipschitzBound p interval * radius
  let qMargin := denseEvalSqLipschitzBound q interval * radius
  have firstBound : p.eval interval.lower ^ 2 ≤ pMargin :=
    not_lt.mp firstUnresolved
  have lower := clearance.lower
    interval.lower ⟨le_rfl, interval.valid⟩
  have marginBelowValues : pMargin + qMargin <
      p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 := by
    calc
      pMargin + qMargin =
          (denseEvalSqLipschitzBound p interval +
            denseEvalSqLipschitzBound q interval) * radius := by
        dsimp only [pMargin, qMargin]
        ring1
      _ < clearance.bound := resolution
      _ ≤ p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 := lower
  have shifted : p.eval interval.lower ^ 2 + qMargin <
      p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 := by
    calc
      p.eval interval.lower ^ 2 + qMargin ≤ pMargin + qMargin :=
        add_le_add firstBound (le_refl qMargin)
      _ < p.eval interval.lower ^ 2 + q.eval interval.lower ^ 2 :=
        marginBelowValues
  exact (add_lt_add_iff_left (p.eval interval.lower ^ 2)).mp shifted

theorem certificate?_isSome_of_pairResolution_of_first_none
    {p q : Polynomial} {interval : Interval}
    (clearance : ClearanceCertificate p q interval)
    (resolution : PairResolution clearance)
    (firstNone : certificate? p interval = none) :
    (certificate? q interval).isSome = true := by
  have firstUnresolved : ¬(
      denseEvalSqLipschitzBound p interval *
          sampleRadiusSq interval interval.lower <
        p.eval interval.lower ^ 2) := by
    intro margin
    have firstSome := (certificate?_isSome_iff p interval).2 margin
    rw [firstNone] at firstSome
    contradiction
  exact (certificate?_isSome_iff q interval).2
    (second_margin_of_first_unresolved clearance resolution firstUnresolved)

/-- Quantitative dominance of the next signed remainder over an unresolved
middle member after multiplying by the displayed quotient. -/
def DominanceResolution
    (q quotient next : Polynomial) {interval : Interval}
    (rightClearance : ClearanceCertificate q next interval) : Prop :=
  denseEvalSqLipschitzBound q interval *
      sampleRadiusSq interval interval.lower *
      (RFAP.PathClearance.evalSqBound quotient interval + 1) <
    rightClearance.bound

instance (q quotient next : Polynomial) {interval : Interval}
    (rightClearance : ClearanceCertificate q next interval) :
    Decidable (DominanceResolution q quotient next rightClearance) := by
  unfold DominanceResolution
  infer_instance

/-- Positive ambient squared radius forcing the signed-remainder dominance
test on every displayed refinement. -/
def dominanceResolutionRadiusSq
    (q quotient next : Polynomial) {root : Interval}
    (rightClearance : ClearanceCertificate q next root) : Coordinate :=
  rightClearance.bound /
    (denseEvalSqLipschitzBound q root *
      (RFAP.PathClearance.evalSqBound quotient root + 1) + 1)

theorem dominanceResolutionRadiusSq_pos
    (q quotient next : Polynomial) {root : Interval}
    (rightClearance : ClearanceCertificate q next root) :
    0 < dominanceResolutionRadiusSq q quotient next rightClearance := by
  apply RFAP.ConstructiveFraction.div_pos_direct
  · exact rightClearance.positive
  · have coefficientNonnegative : 0 ≤
        denseEvalSqLipschitzBound q root *
          (RFAP.PathClearance.evalSqBound quotient root + 1) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (denseHornerSqBounds_nonneg q root).2
        (add_nonneg
          (RFAP.PathClearance.evalSqBound_nonneg quotient root)
          (by decide))
    calc
      0 < 1 := by decide
      _ ≤ denseEvalSqLipschitzBound q root *
          (RFAP.PathClearance.evalSqBound quotient root + 1) + 1 := by
        exact add_le_add coefficientNonnegative (le_refl 1)

theorem dominanceResolution_of_refined_radiusSq
    {q quotient next : Polynomial}
    {root interval : Interval}
    (rightClearance : ClearanceCertificate q next root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      dominanceResolutionRadiusSq q quotient next rightClearance) :
    DominanceResolution q quotient next (rightClearance.restrict refines) := by
  let localCoefficient := denseEvalSqLipschitzBound q interval *
    (RFAP.PathClearance.evalSqBound quotient interval + 1)
  let rootCoefficient := denseEvalSqLipschitzBound q root *
    (RFAP.PathClearance.evalSqBound quotient root + 1)
  let localRadius := sampleRadiusSq interval interval.lower
  have localRadiusNonnegative : 0 ≤ localRadius := sampleRadiusSq_nonneg interval
  have localFactorNonnegative : 0 ≤
      RFAP.PathClearance.evalSqBound quotient interval + 1 :=
    add_nonneg
      (RFAP.PathClearance.evalSqBound_nonneg quotient interval)
      (by decide)
  have rootLipschitzNonnegative :
      0 ≤ denseEvalSqLipschitzBound q root :=
    (denseHornerSqBounds_nonneg q root).2
  have coefficientLe : localCoefficient ≤ rootCoefficient :=
    RFAP.ConstructiveFraction.mul_le_mul_direct
      (denseEvalSqLipschitzBound_le_of_refines q refines)
      (add_le_add
        (RFAP.PathClearance.evalSqBound_le_of_refines
          quotient refines)
        (le_refl 1))
      localFactorNonnegative rootLipschitzNonnegative
  have rootCoefficientNonnegative : 0 ≤ rootCoefficient :=
    RFAP.ConstructiveFraction.mul_nonneg_direct rootLipschitzNonnegative
      (add_nonneg
        (RFAP.PathClearance.evalSqBound_nonneg quotient root)
        (by decide))
  have denominatorPositive : 0 < rootCoefficient + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ rootCoefficient + 1 := by
        exact add_le_add rootCoefficientNonnegative (le_refl 1)
  have scaledRadius : (rootCoefficient + 1) * localRadius <
      rightClearance.bound := by
    calc
      (rootCoefficient + 1) * localRadius <
          (rootCoefficient + 1) *
            dominanceResolutionRadiusSq q quotient next rightClearance :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          denominatorPositive radius
      _ = rightClearance.bound := by
        dsimp only [dominanceResolutionRadiusSq]
        rw [RFAP.ConstructiveFraction.mul_comm]
        apply RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        simpa only [rootCoefficient] using denominatorPositive.ne'
  change denseEvalSqLipschitzBound q interval * localRadius *
      (RFAP.PathClearance.evalSqBound quotient interval + 1) <
    rightClearance.bound
  calc
    denseEvalSqLipschitzBound q interval * localRadius *
        (RFAP.PathClearance.evalSqBound quotient interval + 1) =
        localCoefficient * localRadius := by
      dsimp only [localCoefficient, localRadius]
      ring1
    _ ≤ rootCoefficient * localRadius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientLe localRadiusNonnegative
    _ ≤ (rootCoefficient + 1) * localRadius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) localRadiusNonnegative
    _ < rightClearance.bound := scaledRadius

/-- One positive local squared radius covers the two adjacent clearance tests
and the quotient-dominance test at a signed Euclidean step. -/
def signedStepResolutionRadiusSq {p q : Polynomial}
    {root : Interval} (clearance : ClearanceCertificate p q root) : Coordinate :=
  let next := -((divMod p q).remainder)
  min (pairResolutionRadiusSq clearance)
    (min (pairResolutionRadiusSq clearance.signedStep)
      (dominanceResolutionRadiusSq q (divMod p q).quotient next
        clearance.signedStep))

theorem signedStepResolutionRadiusSq_pos {p q : Polynomial}
    {root : Interval} (clearance : ClearanceCertificate p q root) :
    0 < signedStepResolutionRadiusSq clearance := by
  apply lt_min
  · exact pairResolutionRadiusSq_pos clearance
  · apply lt_min
    · exact pairResolutionRadiusSq_pos clearance.signedStep
    · exact dominanceResolutionRadiusSq_pos q (divMod p q).quotient
        (-((divMod p q).remainder)) clearance.signedStep

theorem signedStepResolutions_of_refined_radiusSq
    {p q : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate p q root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      signedStepResolutionRadiusSq clearance) :
    PairResolution (clearance.restrict refines) ∧
      PairResolution (clearance.signedStep.restrict refines) ∧
      DominanceResolution q (divMod p q).quotient
        (-((divMod p q).remainder))
        (clearance.signedStep.restrict refines) := by
  refine ⟨pairResolution_of_refined_radiusSq clearance refines
      (radius.trans_le (min_le_left _ _)), ?_⟩
  refine ⟨pairResolution_of_refined_radiusSq clearance.signedStep refines
      (radius.trans_le ((min_le_right _ _).trans (min_le_left _ _))), ?_⟩
  exact dominanceResolution_of_refined_radiusSq clearance.signedStep refines
    (radius.trans_le ((min_le_right _ _).trans (min_le_right _ _)))

/-- The terminal member of a signed chain is sign-resolved by the same
adjacent-pair inequality when its displayed successor is the zero
polynomial. -/
def resolvedSign_of_terminal_pairResolution
    {q next : Polynomial} {interval : Interval}
    (nextZero : next.isZero = true)
    (clearance : ClearanceCertificate q next interval)
    (resolution : PairResolution clearance) :
    ResolvedSign q interval := by
  let radius := sampleRadiusSq interval interval.lower
  have radiusNonnegative : 0 ≤ radius := sampleRadiusSq_nonneg interval
  have nextEvalZero := eval_eq_zero_of_isZero nextZero interval.lower
  have qMargin : denseEvalSqLipschitzBound q interval * radius <
      q.eval interval.lower ^ 2 := by
    calc
      denseEvalSqLipschitzBound q interval * radius ≤
          (denseEvalSqLipschitzBound q interval +
            denseEvalSqLipschitzBound next interval) * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (le_add_of_nonneg_right
            (denseHornerSqBounds_nonneg next interval).2)
          radiusNonnegative
      _ < clearance.bound := resolution
      _ ≤ q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 :=
        clearance.lower interval.lower ⟨le_rfl, interval.valid⟩
      _ = q.eval interval.lower ^ 2 := by rw [nextEvalZero]; ring1
  have qMargin' : denseEvalSqLipschitzBound q interval *
      sampleRadiusSq interval interval.lower < q.eval interval.lower ^ 2 := by
    simpa only [radius] using qMargin
  let certificate : SignCertificate q interval :=
    { sample := interval.lower
      sampleInside := ⟨le_rfl, interval.valid⟩
      margin := qMargin' }
  have found : certificate? q interval = some certificate := by
    unfold certificate?
    split
    · rfl
    · rename_i marginFailure
      exact (marginFailure qMargin').elim
  exact ⟨certificate, found⟩

/-- Fuel-bounded radius fold over a finite signed Euclidean chain.  Zero fuel
returns the current adjacent-pair radius; once the fuel covers the second
polynomial's coefficient count, this fallback can only be reached at a zero
second polynomial. -/
def signedChainResolutionRadiusSqFuel : Nat →
    (p q : Polynomial) → {root : Interval} →
      ClearanceCertificate p q root → Coordinate
  | 0, _, _, _, clearance => pairResolutionRadiusSq clearance
  | fuel + 1, p, q, _, clearance =>
      if q.isZero then pairResolutionRadiusSq clearance
      else
        let next := -((divMod p q).remainder)
        if next.isZero then
          pairResolutionRadiusSq clearance.signedStep
        else
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSqFuel fuel q next
              clearance.signedStep)

@[simp] theorem signedChainResolutionRadiusSqFuel_zero
    (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root) :
    signedChainResolutionRadiusSqFuel 0 p q clearance =
      pairResolutionRadiusSq clearance := rfl

theorem signedChainResolutionRadiusSqFuel_succ
    (fuel : Nat) (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root) :
    signedChainResolutionRadiusSqFuel (fuel + 1) p q clearance =
      if q.isZero then pairResolutionRadiusSq clearance
      else
        let next := -((divMod p q).remainder)
        if next.isZero then
          pairResolutionRadiusSq clearance.signedStep
        else
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSqFuel fuel q next
              clearance.signedStep) := rfl

/-- Once the fuel covers the represented degree, one further step leaves the
radius fold unchanged. -/
theorem signedChainResolutionRadiusSqFuel_succ_of_degreeCount_le :
    ∀ (fuel : Nat) (p q : Polynomial) {root : Interval}
      (clearance : ClearanceCertificate p q root),
      q.degreeCount ≤ fuel →
        signedChainResolutionRadiusSqFuel (fuel + 1) p q clearance =
          signedChainResolutionRadiusSqFuel fuel p q clearance := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q root clearance enough
      have degreeZero : q.degreeCount = 0 :=
        Nat.eq_zero_of_le_zero enough
      have qZero := isZero_true_of_degreeCount_eq_zero degreeZero
      change (if q.isZero then pairResolutionRadiusSq clearance
          else
            let next := -((divMod p q).remainder)
            if next.isZero then
              pairResolutionRadiusSq clearance.signedStep
            else
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel 0 q next
                  clearance.signedStep)) =
        pairResolutionRadiusSq clearance
      rw [qZero]
      simp only [↓reduceIte]
  | succ fuel inductionHypothesis =>
      intro p q root clearance enough
      change (if q.isZero then pairResolutionRadiusSq clearance
          else
            let next := -((divMod p q).remainder)
            if next.isZero then
              pairResolutionRadiusSq clearance.signedStep
            else
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel (fuel + 1) q next
                  clearance.signedStep)) =
        if q.isZero then pairResolutionRadiusSq clearance
          else
            let next := -((divMod p q).remainder)
            if next.isZero then
              pairResolutionRadiusSq clearance.signedStep
            else
              min (signedStepResolutionRadiusSq clearance)
                (signedChainResolutionRadiusSqFuel fuel q next
                  clearance.signedStep)
      cases qZero : q.isZero
      · simp only [Bool.false_eq_true, ↓reduceIte]
        let next := -((divMod p q).remainder)
        cases nextZero : next.isZero
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply congrArg (fun tail =>
            min (signedStepResolutionRadiusSq clearance) tail)
          apply inductionHypothesis q next clearance.signedStep
          have remainderDegree :=
            divMod_remainder_degreeCount_lt p q qZero
          change (-((divMod p q).remainder)).degreeCount ≤ fuel
          rw [degreeCount_neg]
          exact Nat.lt_succ_iff.mp
            (remainderDegree.trans_le enough)
        · simp only [↓reduceIte]
      · simp only [↓reduceIte]

theorem signedChainResolutionRadiusSqFuel_add_of_degreeCount_le
    (extra fuel : Nat) (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root)
    (enough : q.degreeCount ≤ fuel) :
    signedChainResolutionRadiusSqFuel (fuel + extra) p q clearance =
      signedChainResolutionRadiusSqFuel fuel p q clearance := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      calc
        signedChainResolutionRadiusSqFuel
              (fuel + extra + 1) p q clearance =
            signedChainResolutionRadiusSqFuel
              (fuel + extra) p q clearance :=
          signedChainResolutionRadiusSqFuel_succ_of_degreeCount_le
            (fuel + extra) p q clearance
              (enough.trans (Nat.le_add_right fuel extra))
        _ = signedChainResolutionRadiusSqFuel fuel p q clearance :=
          inductionHypothesis

theorem signedChainResolutionRadiusSqFuel_stable
    (fuel : Nat) (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root)
    (enough : q.degreeCount ≤ fuel) :
    signedChainResolutionRadiusSqFuel fuel p q clearance =
      signedChainResolutionRadiusSqFuel q.degreeCount p q clearance := by
  have fuelEquation : q.degreeCount + (fuel - q.degreeCount) = fuel :=
    Nat.add_sub_of_le enough
  rw [← fuelEquation]
  exact signedChainResolutionRadiusSqFuel_add_of_degreeCount_le
    (fuel - q.degreeCount) q.degreeCount p q clearance le_rfl

/-- Positive ambient squared radius for a complete finite signed Euclidean
chain, evaluated with the second polynomial's coefficient count as its exact
finite recursion budget. -/
def signedChainResolutionRadiusSq
    (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root) : Coordinate :=
  signedChainResolutionRadiusSqFuel q.degreeCount p q clearance

/-- One executable unfolding of the canonically fuelled radius fold. -/
theorem signedChainResolutionRadiusSq_eq
    (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root) :
    signedChainResolutionRadiusSq p q clearance =
      if q.isZero then pairResolutionRadiusSq clearance
      else
        let next := -((divMod p q).remainder)
        if next.isZero then
          pairResolutionRadiusSq clearance.signedStep
        else
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSq q next
              clearance.signedStep) := by
  change signedChainResolutionRadiusSqFuel q.degreeCount p q clearance =
    if q.isZero then pairResolutionRadiusSq clearance
    else
      let next := -((divMod p q).remainder)
      if next.isZero then
        pairResolutionRadiusSq clearance.signedStep
      else
        min (signedStepResolutionRadiusSq clearance)
          (signedChainResolutionRadiusSqFuel
            (-((divMod p q).remainder)).degreeCount q
              (-((divMod p q).remainder)) clearance.signedStep)
  cases qZero : q.isZero
  · have degreePositive := degreeCount_pos_of_isZero_false qZero
    obtain ⟨qDegree, degreeEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero degreePositive.ne'
    rw [degreeEq, signedChainResolutionRadiusSqFuel_succ, qZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    let next := -((divMod p q).remainder)
    cases nextZero : next.isZero
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply congrArg (fun tail =>
        min (signedStepResolutionRadiusSq clearance) tail)
      apply signedChainResolutionRadiusSqFuel_stable qDegree q next
        clearance.signedStep
      have remainderDegree := divMod_remainder_degreeCount_lt p q qZero
      change (-((divMod p q).remainder)).degreeCount ≤ qDegree
      rw [degreeCount_neg]
      exact Nat.lt_succ_iff.mp (by
        simpa only [degreeEq] using remainderDegree)
    · simp only [↓reduceIte]
  · have degreeZero := degreeCount_eq_zero_of_isZero qZero
    rw [degreeZero, signedChainResolutionRadiusSqFuel_zero]
    simp only [↓reduceIte]

theorem signedChainResolutionRadiusSq_pos
    (p q : Polynomial) {root : Interval}
    (clearance : ClearanceCertificate p q root) :
    0 < signedChainResolutionRadiusSq p q clearance := by
  rw [signedChainResolutionRadiusSq_eq]
  split
  · exact pairResolutionRadiusSq_pos clearance
  · dsimp only
    split
    · exact pairResolutionRadiusSq_pos clearance.signedStep
    · apply lt_min
      · exact signedStepResolutionRadiusSq_pos clearance
      · exact signedChainResolutionRadiusSq_pos q
          (-((divMod p q).remainder)) clearance.signedStep
termination_by q.degreeCount
decreasing_by
  rename_i qZero _
  have qNonzero : q.isZero = false := by simpa using qZero
  rw [degreeCount_neg]
  exact divMod_remainder_degreeCount_lt p q qNonzero

theorem lt_of_sq_lt_sq_of_nonneg {a b : Coordinate}
    (bNonnegative : 0 ≤ b)
    (squares : a ^ 2 < b ^ 2) : a < b := by
  rcases lt_trichotomy a b with less | rfl | greater
  · exact less
  · exact (lt_irrefl _ squares).elim
  · by_cases bZero : b = 0
    · subst b
      exact ((not_lt_of_ge
        (RFAP.ConstructiveFraction.sq_nonneg_direct a)) squares).elim
    · have bPositive : 0 < b := lt_of_le_of_ne bNonnegative (Ne.symm bZero)
      have aPositive : 0 < a := bPositive.trans greater
      have first : b * b < a * b :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          greater bPositive
      have second : a * b < a * a :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          aPositive greater
      have reverse : b ^ 2 < a ^ 2 := by
        simpa only [pow_two] using first.trans second
      exact (lt_asymm squares reverse).elim

theorem coefficient_mul_lt_of_radius_lt_div_add_one
    {coefficient radius bound : Coordinate}
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusNonnegative : 0 ≤ radius)
    (small : radius < bound / (coefficient + 1)) :
    coefficient * radius < bound := by
  have denominatorPositive : 0 < coefficient + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ coefficient + 1 :=
        add_le_add coefficientNonnegative (le_refl 1)
  calc
    coefficient * radius ≤ (coefficient + 1) * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) radiusNonnegative
    _ < (coefficient + 1) * (bound / (coefficient + 1)) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        denominatorPositive small
    _ = bound := by
      rw [RFAP.ConstructiveFraction.mul_comm]
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        bound (coefficient + 1) denominatorPositive.ne'

theorem cross_sq_le_product_sums
    (a b da db : Coordinate) :
    (a * db - b * da) ^ 2 ≤
      (a ^ 2 + b ^ 2) * (da ^ 2 + db ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (a * da + b * db) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (da ^ 2 + db ^ 2) -
        (a * db - b * da) ^ 2 := by ring1

theorem abs_sq_direct (x : Coordinate) : |x| ^ 2 = x ^ 2 := by
  rcases lt_trichotomy x 0 with negative | rfl | positive
  · rw [abs_of_neg negative]
    ring1
  · rfl
  · rw [abs_of_pos positive]

theorem lt_of_two_mul_lt_two_mul_direct {a b : Coordinate}
    (scaled : 2 * a < 2 * b) : a < b := by
  rcases lt_trichotomy a b with less | rfl | greater
  · exact less
  · exact (lt_irrefl _ scaled).elim
  · have reverse : 2 * b < 2 * a :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide) greater
    exact (lt_asymm scaled reverse).elim

/-- A positive ambient squared radius forcing the two endpoint vectors of a
clear polynomial pair to make a narrow complex turn. -/
def narrowTurnResolutionRadiusSq
    {A B : Polynomial} {root : Interval}
    (clearance : ClearanceCertificate A B root) : Coordinate :=
  let differenceCoefficient :=
    denseEvalSqLipschitzBound A root + denseEvalSqLipschitzBound B root
  let normBound :=
    RFAP.PathClearance.evalSqBound A root +
      RFAP.PathClearance.evalSqBound B root
  min (clearance.bound / (differenceCoefficient + 1))
    (clearance.bound ^ 2 /
      (36 * normBound * differenceCoefficient + 1))

theorem narrowTurnResolutionRadiusSq_pos
    {A B : Polynomial} {root : Interval}
    (clearance : ClearanceCertificate A B root) :
    0 < narrowTurnResolutionRadiusSq clearance := by
  let differenceCoefficient :=
    denseEvalSqLipschitzBound A root + denseEvalSqLipschitzBound B root
  let normBound :=
    RFAP.PathClearance.evalSqBound A root +
      RFAP.PathClearance.evalSqBound B root
  have differenceNonnegative : 0 ≤ differenceCoefficient :=
    add_nonneg (denseHornerSqBounds_nonneg A root).2
      (denseHornerSqBounds_nonneg B root).2
  have normNonnegative : 0 ≤ normBound :=
    add_nonneg
      (RFAP.PathClearance.evalSqBound_nonneg A root)
      (RFAP.PathClearance.evalSqBound_nonneg B root)
  have thirtySixNonnegative : 0 ≤ (36 : Coordinate) :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 36) (by decide)).le
  have onePositive : 0 < (1 : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 1) (by decide)
  have crossCoefficientNonnegative :
      0 ≤ 36 * normBound * differenceCoefficient :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        thirtySixNonnegative normNonnegative)
      differenceNonnegative
  unfold narrowTurnResolutionRadiusSq
  apply lt_min
  · apply RFAP.ConstructiveFraction.div_pos_direct clearance.positive
    calc
      0 < 1 := onePositive
      _ ≤ differenceCoefficient + 1 :=
        by
          simpa only [zero_add] using
            RFAP.ConstructiveFraction.add_le_add_right_direct
              differenceNonnegative (1 : Coordinate)
  · apply RFAP.ConstructiveFraction.div_pos_direct
    · simpa only [pow_two] using
        RFAP.ConstructiveFraction.mul_pos_direct
          clearance.positive clearance.positive
    · calc
        0 < 1 := onePositive
        _ ≤ 36 * normBound * differenceCoefficient + 1 :=
          by
            simpa only [zero_add] using
              RFAP.ConstructiveFraction.add_le_add_right_direct
                crossCoefficientNonnegative (1 : Coordinate)

/-- Below the computed squared radius, the two endpoint coordinate vectors
make the square-root-free narrow turn consumed by the finite sign table. -/
theorem narrowComplexTurn_of_refined_radiusSq
    {A B : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate A B root)
    (refines : interval.Refines root)
    (radiusSmall : sampleRadiusSq interval interval.lower <
      narrowTurnResolutionRadiusSq clearance) :
    RFAP.CauchyProductCells.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper) := by
  let radius := sampleRadiusSq interval interval.lower
  let differenceCoefficient :=
    denseEvalSqLipschitzBound A root + denseEvalSqLipschitzBound B root
  let normBound :=
    RFAP.PathClearance.evalSqBound A root +
      RFAP.PathClearance.evalSqBound B root
  let a := A.eval interval.lower
  let b := B.eval interval.lower
  let c := A.eval interval.upper
  let d := B.eval interval.upper
  let da := c - a
  let db := d - b
  let differenceSq := da ^ 2 + db ^ 2
  let cross := a * d - b * c
  let dot := a * c + b * d
  have radiusNonnegative : 0 ≤ radius := sampleRadiusSq_nonneg interval
  have differenceCoefficientNonnegative : 0 ≤ differenceCoefficient :=
    add_nonneg (denseHornerSqBounds_nonneg A root).2
      (denseHornerSqBounds_nonneg B root).2
  have normBoundNonnegative : 0 ≤ normBound :=
    add_nonneg
      (RFAP.PathClearance.evalSqBound_nonneg A root)
      (RFAP.PathClearance.evalSqBound_nonneg B root)
  have upperInside : root.Contains interval.upper :=
    ⟨refines.1.trans interval.valid, refines.2⟩
  have lowerInside : root.Contains interval.lower :=
    ⟨refines.1, interval.valid.trans refines.2⟩
  have endpointDistance :
      (interval.upper - interval.lower) ^ 2 ≤ radius :=
    sub_sq_le_sampleRadiusSq interval ⟨interval.valid, le_rfl⟩
  have daBound : da ^ 2 ≤
      denseEvalSqLipschitzBound A root * radius := by
    have localBound := eval_sub_sq_le A interval
      (x := interval.upper) (y := interval.lower)
      ⟨interval.valid, le_rfl⟩ ⟨le_rfl, interval.valid⟩
    have ambientProduct := RFAP.ConstructiveFraction.mul_le_mul_direct
      (denseEvalSqLipschitzBound_le_of_refines A refines)
      endpointDistance
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (interval.upper - interval.lower))
      (denseHornerSqBounds_nonneg A root).2
    exact localBound.trans (by
      simpa only [da, c, a] using ambientProduct)
  have dbBound : db ^ 2 ≤
      denseEvalSqLipschitzBound B root * radius := by
    have localBound := eval_sub_sq_le B interval
      (x := interval.upper) (y := interval.lower)
      ⟨interval.valid, le_rfl⟩ ⟨le_rfl, interval.valid⟩
    have ambientProduct := RFAP.ConstructiveFraction.mul_le_mul_direct
      (denseEvalSqLipschitzBound_le_of_refines B refines)
      endpointDistance
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (interval.upper - interval.lower))
      (denseHornerSqBounds_nonneg B root).2
    exact localBound.trans (by
      simpa only [db, d, b] using ambientProduct)
  have differenceBound : differenceSq ≤ differenceCoefficient * radius := by
    dsimp only [differenceSq, differenceCoefficient]
    calc
      da ^ 2 + db ^ 2 ≤
          denseEvalSqLipschitzBound A root * radius +
            denseEvalSqLipschitzBound B root * radius :=
        add_le_add daBound dbBound
      _ = (denseEvalSqLipschitzBound A root +
          denseEvalSqLipschitzBound B root) * radius := by ring1
  have firstRadius : radius < clearance.bound /
      (differenceCoefficient + 1) :=
    radiusSmall.trans_le (min_le_left _ _)
  have differenceBelowClearance : differenceSq < clearance.bound :=
    differenceBound.trans_lt
      (coefficient_mul_lt_of_radius_lt_div_add_one
        differenceCoefficientNonnegative radiusNonnegative firstRadius)
  have lowerClearance : clearance.bound ≤ a ^ 2 + b ^ 2 := by
    simpa only [a, b] using clearance.lower interval.lower lowerInside
  have upperClearance : clearance.bound ≤ c ^ 2 + d ^ 2 := by
    simpa only [c, d] using clearance.lower interval.upper upperInside
  have lowerNormBound : a ^ 2 + b ^ 2 ≤ normBound := by
    dsimp only [normBound, a, b]
    exact add_le_add
      (RFAP.PathClearance.eval_sq_le_evalSqBound A root lowerInside)
      (RFAP.PathClearance.eval_sq_le_evalSqBound B root lowerInside)
  have differenceNonnegative : 0 ≤ differenceSq :=
    add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct da)
      (RFAP.ConstructiveFraction.sq_nonneg_direct db)
  have crossBound : cross ^ 2 ≤
      normBound * (differenceCoefficient * radius) := by
    have cauchy : cross ^ 2 ≤
        (a ^ 2 + b ^ 2) * differenceSq := by
      have base := cross_sq_le_product_sums a b da db
      have crossIdentity : cross = a * db - b * da := by
        dsimp only [cross, da, db, a, b, c, d]
        ring1
      rw [crossIdentity]
      exact base
    exact cauchy.trans
      (RFAP.ConstructiveFraction.mul_le_mul_direct lowerNormBound
        differenceBound differenceNonnegative normBoundNonnegative)
  have thirtySixNonnegative : 0 ≤ (36 : Coordinate) :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 36) (by decide)).le
  have crossCoefficientNonnegative :
      0 ≤ 36 * normBound * differenceCoefficient :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct thirtySixNonnegative
        normBoundNonnegative)
      differenceCoefficientNonnegative
  have secondRadius : radius < clearance.bound ^ 2 /
      (36 * normBound * differenceCoefficient + 1) :=
    radiusSmall.trans_le (min_le_right _ _)
  have scaledCrossBelow : 36 * cross ^ 2 < clearance.bound ^ 2 := by
    calc
      36 * cross ^ 2 ≤
          36 * (normBound * (differenceCoefficient * radius)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          crossBound thirtySixNonnegative
      _ = (36 * normBound * differenceCoefficient) * radius := by ring1
      _ < clearance.bound ^ 2 :=
        coefficient_mul_lt_of_radius_lt_div_add_one
          crossCoefficientNonnegative radiusNonnegative secondRadius
  have sixAbsCrossBelow : 6 * |cross| < clearance.bound := by
    apply lt_of_sq_lt_sq_of_nonneg clearance.positive.le
    calc
      (6 * |cross|) ^ 2 = 36 * cross ^ 2 := by
        rw [mul_pow, abs_sq_direct]
        ring1
      _ < clearance.bound ^ 2 := scaledCrossBelow
  have sumLess : differenceSq + clearance.bound <
      (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) := by
    have first := RFAP.ConstructiveFraction.add_lt_add_right_direct
      (differenceBelowClearance.trans_le lowerClearance) clearance.bound
    exact first.trans_le
      (add_le_add (le_refl (a ^ 2 + b ^ 2)) upperClearance)
  have clearanceBelowTwiceDot : clearance.bound < 2 * dot := by
    have positiveDifference := RFAP.ConstructiveFraction.sub_pos_direct sumLess
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      positiveDifference clearance.bound
    calc
      clearance.bound = 0 + clearance.bound := by ring1
      _ < ((a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) -
            (differenceSq + clearance.bound)) + clearance.bound := shifted
      _ = 2 * dot := by
        dsimp only [differenceSq, da, db, dot]
        ring1
  have scaledNarrow : 2 * (3 * |cross|) < 2 * dot := by
    calc
      2 * (3 * |cross|) = 6 * |cross| := by ring1
      _ < clearance.bound := sixAbsCrossBelow
      _ < 2 * dot := clearanceBelowTwiceDot
  have narrow : 3 * |cross| < dot :=
    lt_of_two_mul_lt_two_mul_direct scaledNarrow
  simpa only [RFAP.CauchyProductCells.NarrowComplexTurn,
    cross, dot, a, b, c, d] using narrow

theorem sub_mul_neg_of_sq_lt_sq_of_right_neg {a b : Coordinate}
    (bNegative : b < 0) (squares : a ^ 2 < b ^ 2) :
    (a - b) * b < 0 := by
  have bLessA : b < a := by
    rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · rcases lt_trichotomy b a with less | equal | reverse
      · exact less
      · subst a
        exact (lt_irrefl _ squares).elim
      · have differenceNegative : a - b < 0 := by
          have reverseDifferencePositive :=
            RFAP.ConstructiveFraction.sub_pos_direct reverse
          calc
            a - b = -(b - a) := by ring1
            _ < 0 := neg_neg_of_pos reverseDifferencePositive
        have sumNegative : a + b < 0 := add_neg aNegative bNegative
        have productPositive : 0 < (a - b) * (a + b) :=
          RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
            differenceNegative sumNegative
        have reverseSquares : b ^ 2 < a ^ 2 := by
          have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
            productPositive (b ^ 2)
          calc
            b ^ 2 = 0 + b ^ 2 := by ring1
            _ < (a - b) * (a + b) + b ^ 2 := shifted
            _ = a ^ 2 := by ring1
        exact (lt_asymm squares reverseSquares).elim
    · exact bNegative
    · exact bNegative.trans aPositive
  have differencePositive := RFAP.ConstructiveFraction.sub_pos_direct bLessA
  exact RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
    differencePositive bNegative

theorem sub_mul_neg_of_sq_lt_sq_of_right_pos {a b : Coordinate}
    (bPositive : 0 < b) (squares : a ^ 2 < b ^ 2) :
    (a - b) * b < 0 := by
  have aLessB : a < b := by
    rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · exact aNegative.trans bPositive
    · exact bPositive
    · exact lt_of_sq_lt_sq_of_nonneg bPositive.le squares
  have reverseDifferencePositive :=
    RFAP.ConstructiveFraction.sub_pos_direct aLessB
  have differenceNegative : a - b < 0 := by
    calc
      a - b = -(b - a) := by ring1
      _ < 0 := neg_neg_of_pos reverseDifferencePositive
  exact RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
    differenceNegative bPositive

/-- If `a` is strictly smaller than `b` in squared magnitude, subtracting
`b` from `a` has the sign opposite to `b`. -/
theorem sub_mul_neg_of_sq_lt_sq {a b : Coordinate}
    (squares : a ^ 2 < b ^ 2) : (a - b) * b < 0 := by
  rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
  · exact sub_mul_neg_of_sq_lt_sq_of_right_neg bNegative squares
  · exact ((not_lt_of_ge
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)) squares).elim
  · exact sub_mul_neg_of_sq_lt_sq_of_right_pos bPositive squares

theorem product_eval_sq_lt_next_eval_sq_of_dominance
    {q quotient next : Polynomial} {interval : Interval}
    (rightClearance : ClearanceCertificate q next interval)
    (dominance : DominanceResolution
      q quotient next rightClearance)
    (qUnresolved : ¬(
      denseEvalSqLipschitzBound q interval *
          sampleRadiusSq interval interval.lower <
        q.eval interval.lower ^ 2)) :
    (q.eval interval.lower * quotient.eval interval.lower) ^ 2 <
      next.eval interval.lower ^ 2 := by
  let radius := sampleRadiusSq interval interval.lower
  let qMargin := denseEvalSqLipschitzBound q interval * radius
  let quotientBound :=
    RFAP.PathClearance.evalSqBound quotient interval
  have qSqBound : q.eval interval.lower ^ 2 ≤ qMargin :=
    not_lt.mp qUnresolved
  have quotientSqBound : quotient.eval interval.lower ^ 2 ≤ quotientBound :=
    eval_sq_le_evalSqBound quotient interval ⟨le_rfl, interval.valid⟩
  have qMarginNonnegative : 0 ≤ qMargin :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (denseHornerSqBounds_nonneg q interval).2
      (sampleRadiusSq_nonneg interval)
  have quotientSqNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct
      (quotient.eval interval.lower)
  have productBound :
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 ≤
        qMargin * quotientBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct qSqBound quotientSqBound
      quotientSqNonnegative qMarginNonnegative
  have lower := rightClearance.lower
    interval.lower ⟨le_rfl, interval.valid⟩
  have sumBelow :
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 +
          q.eval interval.lower ^ 2 <
        q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 := by
    calc
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 +
          q.eval interval.lower ^ 2 ≤
          qMargin * quotientBound + qMargin :=
        add_le_add productBound qSqBound
      _ = qMargin * (quotientBound + 1) := by ring1
      _ < rightClearance.bound := dominance
      _ ≤ q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 :=
        lower
  have shifted : q.eval interval.lower ^ 2 +
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 <
      q.eval interval.lower ^ 2 + next.eval interval.lower ^ 2 := by
    simpa only [add_comm] using sumBelow
  have productLess :
      q.eval interval.lower ^ 2 * quotient.eval interval.lower ^ 2 <
        next.eval interval.lower ^ 2 :=
    (add_lt_add_iff_left (q.eval interval.lower ^ 2)).mp shifted
  simpa only [mul_pow] using productLess

theorem signedStepCellCertificate?_isSome_of_resolution
    {p q : Polynomial} {interval : Interval}
    {head : SignCertificate p interval}
    (headFound : certificate? p interval = some head)
    (qNone : certificate? q interval = none)
    (rightClearance : ClearanceCertificate q
      (-((divMod p q).remainder)) interval)
    (rightResolution : PairResolution rightClearance)
    (dominance : DominanceResolution q (divMod p q).quotient
      (-((divMod p q).remainder)) rightClearance) :
    (signedStepCellCertificate? p q interval).isSome = true := by
  let next := -((divMod p q).remainder)
  have qUnresolved : ¬(
      denseEvalSqLipschitzBound q interval *
          sampleRadiusSq interval interval.lower <
        q.eval interval.lower ^ 2) := by
    intro margin
    have some := (certificate?_isSome_iff q interval).2 margin
    rw [qNone] at some
    contradiction
  have nextMargin : denseEvalSqLipschitzBound next interval *
      sampleRadiusSq interval interval.lower <
      next.eval interval.lower ^ 2 :=
    second_margin_of_first_unresolved rightClearance rightResolution qUnresolved
  have headMargin := certificate?_some_margin headFound
  have productSquares :
      (q.eval interval.lower * (divMod p q).quotient.eval interval.lower) ^ 2 <
        next.eval interval.lower ^ 2 := by
    exact product_eval_sq_lt_next_eval_sq_of_dominance
      rightClearance dominance qUnresolved
  have outerOpposite : p.eval interval.lower * next.eval interval.lower < 0 := by
    have step := signedStep_eval_identity p q interval.lower
    change p.eval interval.lower =
      q.eval interval.lower * (divMod p q).quotient.eval interval.lower -
        next.eval interval.lower at step
    rw [step]
    exact sub_mul_neg_of_sq_lt_sq productSquares
  have nextMargin' :
      denseEvalSqLipschitzBound (-((divMod p q).remainder)) interval *
          sampleRadiusSq interval interval.lower <
        (divMod p q).remainder.eval interval.lower ^ 2 := by
    simpa only [next, eval_neg, neg_sq] using nextMargin
  have remainderProductPositive :
      0 < p.eval interval.lower * (divMod p q).remainder.eval interval.lower := by
    apply neg_lt_zero.mp
    calc
      -(p.eval interval.lower * (divMod p q).remainder.eval interval.lower) =
          p.eval interval.lower * next.eval interval.lower := by
        dsimp only [next]
        rw [eval_neg]
        ring1
      _ < 0 := outerOpposite
  unfold signedStepCellCertificate?
  simp [headMargin, nextMargin', remainderProductPositive]

/-- Finite local bounds following the exact shape of a signed remainder
chain. -/
inductive NeutralChainResolutionBounds (interval : Interval) :
    (head : Polynomial) → (tail : List Polynomial) → Type
  | single {p : Polynomial} : NeutralChainResolutionBounds interval p []
  | pair {p q : Polynomial}
      (last : ResolvedSign q interval) :
      NeutralChainResolutionBounds interval p [q]
  | step {p q r : Polynomial} {suffix : List Polynomial}
      (nextEq : r = -((divMod p q).remainder))
      (leftClearance : ClearanceCertificate p q interval)
      (rightClearance : ClearanceCertificate q r interval)
      (leftResolution : PairResolution leftClearance)
      (rightResolution : PairResolution rightClearance)
      (dominance : DominanceResolution q (divMod p q).quotient
        r rightClearance)
      (rest : NeutralChainResolutionBounds interval q (r :: suffix)) :
      NeutralChainResolutionBounds interval p (q :: r :: suffix)

theorem signedRemainderChain_tail_eq_of_second_nonzero
    (p q : Polynomial) (qNonzero : q.isZero = false) :
    (signedRemainderChain p q).tail =
      signedRemainderChain q (-((divMod p q).remainder)) := by
  rw [signedRemainderChain_step_of_second_nonzero p q qNonzero]
  rfl

theorem signedRemainderChain_eq_head_cons_tail (p q : Polynomial) :
    signedRemainderChain p q =
      p :: (signedRemainderChain p q).tail := by
  rcases signedRemainderChain_eq_cons p q with ⟨tail, chainEq⟩
  rw [chainEq]
  rfl

/-- Fold the ambient squared radius through the actual finite signed chain,
producing every proof-relevant local field consumed by the scanner. -/
def signedChainResolutionBoundsOfRadiusSq
    (root interval : Interval) (refines : interval.Refines root)
    (p q : Polynomial) (clearance : ClearanceCertificate p q root)
    (radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq p q clearance) :
    NeutralChainResolutionBounds interval p
      (signedRemainderChain p q).tail := by
  by_cases qZero : q.isZero = true
  · rw [signedRemainderChain, signedRemainderChainWF_eq]
    simp only [qZero, ↓reduceIte, List.tail_cons]
    exact .single
  · have qNonzero : q.isZero = false := by
      cases value : q.isZero <;> simp_all
    let next := -((divMod p q).remainder)
    by_cases nextZero : next.isZero = true
    · have terminalRadius : sampleRadiusSq interval interval.lower <
          pairResolutionRadiusSq clearance.signedStep := by
        have bound := radius
        rw [signedChainResolutionRadiusSq_eq] at bound
        simpa only [qNonzero, Bool.false_eq_true, if_false, next,
          nextZero, if_true] using bound
      have terminalResolution := pairResolution_of_refined_radiusSq
        clearance.signedStep refines terminalRadius
      have terminalResolved := resolvedSign_of_terminal_pairResolution
        nextZero (clearance.signedStep.restrict refines) terminalResolution
      have rawNextZero : (-((divMod p q).remainder)).isZero = true := by
        simpa only [next] using nextZero
      rw [signedRemainderChain_tail_eq_of_second_nonzero p q qNonzero]
      rw [signedRemainderChain, signedRemainderChainWF_eq]
      simp only [rawNextZero, ↓reduceIte]
      exact .pair terminalResolved
    · have nextNonzero : next.isZero = false := by
        cases value : next.isZero <;> simp_all
      have decomposed : sampleRadiusSq interval interval.lower <
          min (signedStepResolutionRadiusSq clearance)
            (signedChainResolutionRadiusSq q next clearance.signedStep) := by
        have bound := radius
        rw [signedChainResolutionRadiusSq_eq] at bound
        simpa only [qNonzero, Bool.false_eq_true, if_false, next,
          nextNonzero] using bound
      have localRadius : sampleRadiusSq interval interval.lower <
          signedStepResolutionRadiusSq clearance :=
        decomposed.trans_le (min_le_left _ _)
      have restRadius : sampleRadiusSq interval interval.lower <
          signedChainResolutionRadiusSq q next clearance.signedStep :=
        decomposed.trans_le (min_le_right _ _)
      have localResolutions := signedStepResolutions_of_refined_radiusSq
        clearance refines localRadius
      have rest := signedChainResolutionBoundsOfRadiusSq root interval refines
        q next clearance.signedStep restRadius
      let nextNext := -((divMod q next).remainder)
      let suffix := (signedRemainderChain next nextNext).tail
      have nextChainEq : signedRemainderChain next nextNext = next :: suffix :=
        signedRemainderChain_eq_head_cons_tail next nextNext
      rw [signedRemainderChain_tail_eq_of_second_nonzero
        q next nextNonzero, nextChainEq] at rest
      rw [signedRemainderChain_tail_eq_of_second_nonzero p q qNonzero,
        signedRemainderChain_step_of_second_nonzero q next nextNonzero,
        nextChainEq]
      exact .step rfl (clearance.restrict refines)
        (clearance.signedStep.restrict refines) localResolutions.1
        localResolutions.2.1 localResolutions.2.2 rest
termination_by q.degreeCount
decreasing_by
  have qNonzero : q.isZero = false := by
    cases value : q.isZero <;> simp_all
  rw [degreeCount_neg]
  exact divMod_remainder_degreeCount_lt p q qNonzero

namespace NeutralChainResolutionBounds

def dropHead {interval : Interval} {p q : Polynomial}
    {tail : List Polynomial}
    (bounds : NeutralChainResolutionBounds interval p (q :: tail)) :
    NeutralChainResolutionBounds interval q tail :=
  match bounds with
  | .pair _ => .single
  | .step _ _ _ _ _ _ rest => rest

theorem secondCertificate?_isSome_of_first_none
    {interval : Interval} {p q : Polynomial} {tail : List Polynomial}
    (bounds : NeutralChainResolutionBounds interval p (q :: tail))
    (firstNone : certificate? p interval = none) :
    (certificate? q interval).isSome = true := by
  cases bounds with
  | pair last => rw [last.found]; rfl
  | step nextEq leftClearance rightClearance leftResolution
      rightResolution dominance rest =>
      exact certificate?_isSome_of_pairResolution_of_first_none
        leftClearance leftResolution firstNone

end NeutralChainResolutionBounds

/-- Local resolution bounds make every branch of the recursive neutral-chain
scanner succeed. -/
def neutralChainCertificate?_succeeds_of_resolutionBounds
    (interval : Interval) :
    (head : Polynomial) → (tail : List Polynomial) →
      NeutralChainResolutionBounds interval head tail →
      (headResolved : ResolvedSign head interval) →
      { certificate : NeutralChainCertificate interval head tail //
        neutralChainCertificate? interval head tail = some certificate }
  | head, [], .single, headResolved => by
      refine ⟨.single headResolved.certificate, ?_⟩
      simp only [neutralChainCertificate?, headResolved.found]
  | head, [q], .pair last, headResolved => by
      refine ⟨.stable headResolved.certificate
        (.single last.certificate), ?_⟩
      simp only [neutralChainCertificate?, headResolved.found, last.found]
  | head, q :: r :: suffix,
      .step nextEq leftClearance rightClearance leftResolution
        rightResolution dominance rest,
      headResolved => by
      subst r
      by_cases qMargin : denseEvalSqLipschitzBound q interval *
          sampleRadiusSq interval interval.lower < q.eval interval.lower ^ 2
      · let qCertificate : SignCertificate q interval :=
          { sample := interval.lower
            sampleInside := ⟨le_rfl, interval.valid⟩
            margin := qMargin }
        have qFound : certificate? q interval = some qCertificate := by
          simp [certificate?, qMargin, qCertificate]
        let qResolved : ResolvedSign q interval :=
          ⟨qCertificate, qFound⟩
        have recursive := neutralChainCertificate?_succeeds_of_resolutionBounds
          interval q (-((divMod head q).remainder) :: suffix) rest qResolved
        refine ⟨.stable headResolved.certificate recursive.1, ?_⟩
        simp only [neutralChainCertificate?, headResolved.found,
          qFound, recursive.2]
      · have qNone : certificate? q interval = none := by
          simp [certificate?, qMargin]
        have stepSome := signedStepCellCertificate?_isSome_of_resolution
          headResolved.found qNone rightClearance rightResolution dominance
        cases stepFound : signedStepCellCertificate? head q interval with
        | none => simp [stepFound] at stepSome
        | some stepCertificate =>
          have nextSome :
              (certificate? (-((divMod head q).remainder)) interval).isSome =
                true :=
            certificate?_isSome_of_pairResolution_of_first_none
              rightClearance rightResolution qNone
          cases nextFound :
              certificate? (-((divMod head q).remainder)) interval with
          | none => simp [nextFound] at nextSome
          | some nextCertificate =>
            let nextResolved :
                ResolvedSign (-((divMod head q).remainder)) interval :=
              ⟨nextCertificate, nextFound⟩
            have recursive := neutralChainCertificate?_succeeds_of_resolutionBounds
              interval (-((divMod head q).remainder)) suffix rest.dropHead
                nextResolved
            refine ⟨.event rfl stepCertificate recursive.1, ?_⟩
            simp only [neutralChainCertificate?, headResolved.found, qNone]
            simp [stepFound, recursive.2]
termination_by _ tail _ _ => tail.length
decreasing_by
  · simp only [List.length_cons]
    exact Nat.lt_succ_self _
  · simp only [List.length_cons]
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)

/-- Package the recursively constructed certificate for a displayed nonempty
chain in the exact option type returned by the executable scanner. -/
def neutralChainCertificates?_succeeds_of_resolutionBounds
    (interval : Interval) (head : Polynomial) (tail : List Polynomial)
    (bounds : NeutralChainResolutionBounds interval head tail)
    (headResolved : ResolvedSign head interval) :
    { certificates : NeutralChainCertificates interval (head :: tail) //
      neutralChainCertificates? interval (head :: tail) = some certificates } := by
  have recursive := neutralChainCertificate?_succeeds_of_resolutionBounds
    interval head tail bounds headResolved
  refine ⟨.cons recursive.1, ?_⟩
  simp only [neutralChainCertificates?, recursive.2]

/-- If the denominator already has a fixed sign, resolution bounds for the
complete signed chain force the first branch of the Cauchy-event scanner to
succeed. -/
theorem cauchyEventSigns?_isSome_of_denominator_resolutionBounds
    {R S : Polynomial} {interval : Interval} {tail : List Polynomial}
    (chainEq : signedRemainderChain S R = S :: tail)
    (bounds : NeutralChainResolutionBounds interval S tail)
    (denominator : ResolvedSign S interval) :
    (cauchyEventSigns? R S interval).isSome = true := by
  have chain := neutralChainCertificates?_succeeds_of_resolutionBounds
    interval S tail bounds denominator
  have chainSome :
      (neutralChainCertificates? interval
        (signedRemainderChain S R)).isSome = true := by
    rw [chainEq, chain.2]
    rfl
  cases chainFound : neutralChainCertificates? interval
      (signedRemainderChain S R) with
  | none => simp [chainFound] at chainSome
  | some chainCertificate =>
      simp [cauchyEventSigns?, denominator.found, chainFound]

/-- On a nonzero numerator, one adjacent Bézout-pair bound and the finite
chain bounds decide both branches of the executable Cauchy-event scanner. -/
theorem cauchyEventSigns?_isSome_of_resolutionBounds
    {R S : Polynomial} {interval : Interval}
    (RNonzero : R.isZero = false)
    (bounds : NeutralChainResolutionBounds interval S
      (signedRemainderChain R (-((divMod S R).remainder)))) :
    (cauchyEventSigns? R S interval).isSome = true := by
  have fullChainEq := signedRemainderChain_step_of_second_nonzero
    S R RNonzero
  cases denominatorFound : certificate? S interval with
  | some denominatorCertificate =>
      let denominator : ResolvedSign S interval :=
        ⟨denominatorCertificate, denominatorFound⟩
      exact cauchyEventSigns?_isSome_of_denominator_resolutionBounds
        fullChainEq bounds denominator
  | none =>
      have tailEq := signedRemainderChain_eq_head_cons_tail
        R (-((divMod S R).remainder))
      rw [tailEq] at bounds
      have numeratorSome : (certificate? R interval).isSome = true :=
        bounds.secondCertificate?_isSome_of_first_none denominatorFound
      cases numeratorFound : certificate? R interval with
      | none => simp [numeratorFound] at numeratorSome
      | some numeratorCertificate =>
          let numerator : ResolvedSign R interval :=
            ⟨numeratorCertificate, numeratorFound⟩
          have tailChain :=
            neutralChainCertificates?_succeeds_of_resolutionBounds
              interval R (signedRemainderChain
                R (-((divMod S R).remainder))).tail
                bounds.dropHead numerator
          have tailSome :
              (neutralChainCertificates? interval
                (signedRemainderChain R
                  (-((divMod S R).remainder)))).isSome = true := by
            rw [tailEq, tailChain.2]
            rfl
          cases tailFound : neutralChainCertificates? interval
              (signedRemainderChain R (-((divMod S R).remainder))) with
          | none => simp [tailFound] at tailSome
          | some tailCertificate =>
              simp [cauchyEventSigns?, denominatorFound, numeratorFound,
                tailFound]

/-- The shrinking squared radius and explicit initial Bézout identity are a
complete finite success condition for one genuine Cauchy-event scan. -/
theorem cauchyEventSigns?_isSome_of_refined_radiusSq
    {R S : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate S R root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R clearance) :
    (cauchyEventSigns? R S interval).isSome = true := by
  have bounds := signedChainResolutionBoundsOfRadiusSq root interval refines
    S R clearance radius
  by_cases RZero : R.isZero = true
  · have pairRadius : sampleRadiusSq interval interval.lower <
        pairResolutionRadiusSq clearance := by
      have bound := radius
      rw [signedChainResolutionRadiusSq_eq] at bound
      simpa only [RZero, if_true] using bound
    have pairResolution := pairResolution_of_refined_radiusSq
      clearance refines pairRadius
    have denominator := resolvedSign_of_terminal_pairResolution RZero
      (clearance.restrict refines) pairResolution
    have chainEq : signedRemainderChain S R = S :: [] := by
      rw [signedRemainderChain, signedRemainderChainWF_eq]
      simp only [RZero, ↓reduceIte]
    have tailEq : (signedRemainderChain S R).tail = [] := by
      rw [chainEq]
      rfl
    rw [tailEq] at bounds
    exact cauchyEventSigns?_isSome_of_denominator_resolutionBounds
      chainEq bounds denominator
  · have RNonzero : R.isZero = false := by
      cases value : R.isZero <;> simp_all
    rw [signedRemainderChain_tail_eq_of_second_nonzero S R RNonzero] at bounds
    exact cauchyEventSigns?_isSome_of_resolutionBounds RNonzero bounds

/-- Convenience specialization of the finite-clearance theorem to a
displayed polynomial Bézout identity. -/
theorem cauchyEventSigns?_isSome_of_coprime_refined_radiusSq
    {R S : Polynomial} (coprime : CoprimeCertificate S R)
    {root interval : Interval}
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R
        (certificateOfCoprime coprime root)) :
    (cauchyEventSigns? R S interval).isSome = true :=
  cauchyEventSigns?_isSome_of_refined_radiusSq
    (certificateOfCoprime coprime root) refines radius

/-! ## One-sided endpoint cells -/

/-- Total projection of the proof-bearing event returned by the finite
scanner once its coefficient-computed radius bound has been met. -/
def cauchyEventSignsOfRefinedRadiusSq
    {R S : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate S R root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R clearance) :
    CauchyEventSigns R S interval :=
  (cauchyEventSigns? R S interval).get
    (cauchyEventSigns?_isSome_of_refined_radiusSq clearance refines radius)

/-- The same coefficient-computed resolution, retaining the actual
strict-sign certificate selected by the finite scanner. -/
theorem cauchyEventResolution?_isSome_of_refined_radiusSq
    {R S : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate S R root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R clearance) :
    (cauchyEventResolution? R S interval).isSome = true := by
  have signsSome := cauchyEventSigns?_isSome_of_refined_radiusSq
    clearance refines radius
  rw [← cauchyEventResolution?_map_signs R S interval] at signsSome
  simpa using signsSome

def cauchyEventResolutionOfRefinedRadiusSq
    {R S : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate S R root)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R clearance) :
    CauchyEventResolution R S interval :=
  (cauchyEventResolution? R S interval).get
    (cauchyEventResolution?_isSome_of_refined_radiusSq
      clearance refines radius)

private theorem sq_pos_of_ne_zero {x : Coordinate} (nonzero : x ≠ 0) :
    0 < x ^ 2 := by
  have squareNonzero : x ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((RFAP.ConstructiveFraction.sq_eq_zero_direct x).mp zero)
  exact lt_of_le_of_ne (RFAP.ConstructiveFraction.sq_nonneg_direct x)
    (Ne.symm squareNonzero)

/-- Positive squared radius which fixes the sign of one coordinate relative
to a displayed endpoint, unless that endpoint coordinate is exactly zero. -/
def endpointStabilityRadiusSq
    (p : Polynomial) (root : Interval) (endpoint : Coordinate) : Coordinate :=
  if p.eval endpoint = 0 then 1
  else p.eval endpoint ^ 2 /
    (denseEvalSqLipschitzBound p root + 1)

theorem endpointStabilityRadiusSq_pos
    (p : Polynomial) (root : Interval) (endpoint : Coordinate) :
    0 < endpointStabilityRadiusSq p root endpoint := by
  unfold endpointStabilityRadiusSq
  split
  · decide
  · rename_i nonzero
    apply RFAP.ConstructiveFraction.div_pos_direct
    · exact sq_pos_of_ne_zero nonzero
    · calc
        0 < 1 := by decide
        _ ≤ denseEvalSqLipschitzBound p root + 1 :=
          add_le_add (denseHornerSqBounds_nonneg p root).2 (le_refl 1)

private theorem sampleRadiusSq_nonneg_at
    (interval : Interval) (sample : Coordinate) :
    0 ≤ sampleRadiusSq interval sample :=
  (RFAP.ConstructiveFraction.sq_nonneg_direct
      (interval.lower - sample)).trans (le_max_left _ _)

/-- A small refinement produces a strict-sign certificate sampled at either
displayed endpoint.  The endpoint is an explicit finite datum. -/
def endpointSignCertificateOfRadiusSq
    {p : Polynomial} {root interval : Interval} {endpoint : Coordinate}
    (refines : interval.Refines root)
    (atEndpoint : endpoint = interval.lower ∨ endpoint = interval.upper)
    (nonzero : p.eval endpoint ≠ 0)
    (radius : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq p root endpoint) :
    SignCertificate p interval := by
  have endpointInside : interval.Contains endpoint := by
    rcases atEndpoint with rfl | rfl
    · exact ⟨le_rfl, interval.valid⟩
    · exact ⟨interval.valid, le_rfl⟩
  have endpointRadius : sampleRadiusSq interval endpoint =
      sampleRadiusSq interval interval.lower := by
    rcases atEndpoint with rfl | rfl
    · rfl
    · exact sampleRadiusSq_upper_eq_lower interval
  have rootCoefficientNonnegative :
      0 ≤ denseEvalSqLipschitzBound p root :=
    (denseHornerSqBounds_nonneg p root).2
  have localCoefficientLe :
      denseEvalSqLipschitzBound p interval ≤
        denseEvalSqLipschitzBound p root :=
    denseEvalSqLipschitzBound_le_of_refines p refines
  have radiusNonnegative :
      0 ≤ sampleRadiusSq interval endpoint :=
    sampleRadiusSq_nonneg_at interval endpoint
  have radiusBelow : sampleRadiusSq interval endpoint <
      p.eval endpoint ^ 2 /
        (denseEvalSqLipschitzBound p root + 1) := by
    rw [endpointRadius]
    simpa only [endpointStabilityRadiusSq, if_neg nonzero] using radius
  have rootMargin : denseEvalSqLipschitzBound p root *
      sampleRadiusSq interval endpoint < p.eval endpoint ^ 2 :=
    coefficient_mul_lt_of_radius_lt_div_add_one
      rootCoefficientNonnegative radiusNonnegative radiusBelow
  exact
    { sample := endpoint
      sampleInside := endpointInside
      margin :=
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          localCoefficientLe radiusNonnegative).trans_lt rootMargin }

/-- The componentwise stability condition consumed by the one-sided product
table, oriented from `start` toward `stop`. -/
def EndpointStable (p : Polynomial) (start stop : Coordinate) : Prop :=
  p.eval start = 0 ∨ 0 < p.eval start * p.eval stop

theorem endpointStable_of_refined_radiusSq
    {p : Polynomial} {root interval : Interval} {start stop : Coordinate}
    (refines : interval.Refines root)
    (orientation :
      (start = interval.lower ∧ stop = interval.upper) ∨
      (start = interval.upper ∧ stop = interval.lower))
    (radius : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq p root start) :
    EndpointStable p start stop := by
  by_cases zero : p.eval start = 0
  · exact Or.inl zero
  · have atEndpoint : start = interval.lower ∨
        start = interval.upper := orientation.elim
          (fun ordered => Or.inl ordered.1)
          (fun reversed => Or.inr reversed.1)
    let certificate := endpointSignCertificateOfRadiusSq
      refines atEndpoint zero radius
    apply Or.inr
    rcases orientation with ordered | reversed
    · rw [ordered.1, ordered.2]
      exact certificate.endpoint_stable
    · rw [reversed.1, reversed.2]
      rw [RFAP.ConstructiveFraction.mul_comm]
      exact certificate.endpoint_stable

/-- Six componentwise endpoint stabilities for the two factors and their
displayed product coordinates. -/
structure EndpointStabilities
    (A B C D E H : Polynomial) (start stop : Coordinate) : Prop where
  leftReal : EndpointStable A start stop
  leftImag : EndpointStable B start stop
  rightReal : EndpointStable C start stop
  rightImag : EndpointStable D start stop
  productReal : EndpointStable E start stop
  productImag : EndpointStable H start stop

/-- One finite minimum covers all six endpoint-coordinate stability tests. -/
def endpointStabilitiesRadiusSq
    (A B C D E H : Polynomial) (root : Interval)
    (endpoint : Coordinate) : Coordinate :=
  min (endpointStabilityRadiusSq A root endpoint)
    (min (endpointStabilityRadiusSq B root endpoint)
      (min (endpointStabilityRadiusSq C root endpoint)
        (min (endpointStabilityRadiusSq D root endpoint)
          (min (endpointStabilityRadiusSq E root endpoint)
            (endpointStabilityRadiusSq H root endpoint)))))

theorem endpointStabilitiesRadiusSq_pos
    (A B C D E H : Polynomial) (root : Interval)
    (endpoint : Coordinate) :
    0 < endpointStabilitiesRadiusSq A B C D E H root endpoint := by
  unfold endpointStabilitiesRadiusSq
  apply lt_min
  · exact endpointStabilityRadiusSq_pos A root endpoint
  · apply lt_min
    · exact endpointStabilityRadiusSq_pos B root endpoint
    · apply lt_min
      · exact endpointStabilityRadiusSq_pos C root endpoint
      · apply lt_min
        · exact endpointStabilityRadiusSq_pos D root endpoint
        · apply lt_min
          · exact endpointStabilityRadiusSq_pos E root endpoint
          · exact endpointStabilityRadiusSq_pos H root endpoint

theorem endpointStabilities_of_refined_radiusSq
    {A B C D E H : Polynomial} {root interval : Interval}
    {start stop : Coordinate}
    (refines : interval.Refines root)
    (orientation :
      (start = interval.lower ∧ stop = interval.upper) ∨
      (start = interval.upper ∧ stop = interval.lower))
    (radius : sampleRadiusSq interval interval.lower <
      endpointStabilitiesRadiusSq A B C D E H root start) :
    EndpointStabilities A B C D E H start stop := by
  have radiusA : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq A root start :=
    radius.trans_le (min_le_left _ _)
  have radiusB : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq B root start :=
    radius.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have radiusC : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq C root start :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have radiusD : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq D root start :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
  have radiusE : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq E root start :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))))
  have radiusH : sampleRadiusSq interval interval.lower <
      endpointStabilityRadiusSq H root start :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))))
  exact
    { leftReal := endpointStable_of_refined_radiusSq
        refines orientation radiusA
      leftImag := endpointStable_of_refined_radiusSq
        refines orientation radiusB
      rightReal := endpointStable_of_refined_radiusSq
        refines orientation radiusC
      rightImag := endpointStable_of_refined_radiusSq
        refines orientation radiusD
      productReal := endpointStable_of_refined_radiusSq
        refines orientation radiusE
      productImag := endpointStable_of_refined_radiusSq
        refines orientation radiusH }

theorem complexProductPair_ne_zero
    (A B C D E H : Coordinate)
    (left : A ≠ 0 ∨ B ≠ 0) (right : C ≠ 0 ∨ D ≠ 0)
    (realIdentity : E = A * C - B * D)
    (imagIdentity : H = A * D + B * C) :
    E ≠ 0 ∨ H ≠ 0 := by
  let z : RFAP.ConstructiveGaussian.Gaussian := ⟨A, B⟩
  let w : RFAP.ConstructiveGaussian.Gaussian := ⟨C, D⟩
  have zNonzero : z ≠ 0 := by
    intro zero
    have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
    have imagZero := congrArg RFAP.ConstructiveGaussian.Gaussian.im zero
    simp only [z, RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im] at realZero imagZero
    exact left.elim (fun nonzero => nonzero realZero)
      (fun nonzero => nonzero imagZero)
  have wNonzero : w ≠ 0 := by
    intro zero
    have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
    have imagZero := congrArg RFAP.ConstructiveGaussian.Gaussian.im zero
    simp only [w, RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im] at realZero imagZero
    exact right.elim (fun nonzero => nonzero realZero)
      (fun nonzero => nonzero imagZero)
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct zNonzero wNonzero
  by_cases realZero : E = 0
  · apply Or.inr
    intro imagZero
    apply productNonzero
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re]
      dsimp only [z, w]
      rw [← realIdentity]
      exact realZero.trans RFAP.ConstructiveGaussian.Gaussian.zero_re.symm
    · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_im]
      dsimp only [z, w]
      rw [← imagIdentity, imagZero]
      exact RFAP.ConstructiveGaussian.Gaussian.zero_im.symm
  · exact Or.inl realZero

/-- One positive squared radius covers the three event scanners and the six
component stabilities needed at a possibly axis-aligned outer endpoint. -/
def endpointProductResolutionRadiusSq
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (endpoint : Coordinate) : Coordinate :=
  let product := left.complexProduct right realIdentity imagIdentity
  min (signedChainResolutionRadiusSq B A left.swap)
    (min (signedChainResolutionRadiusSq D C right.swap)
      (min (signedChainResolutionRadiusSq H E product.swap)
        (endpointStabilitiesRadiusSq A B C D E H root endpoint)))

theorem endpointProductResolutionRadiusSq_pos
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (endpoint : Coordinate) :
    0 < endpointProductResolutionRadiusSq left right
      realIdentity imagIdentity endpoint := by
  let product := left.complexProduct right realIdentity imagIdentity
  unfold endpointProductResolutionRadiusSq
  apply lt_min
  · exact signedChainResolutionRadiusSq_pos B A left.swap
  · apply lt_min
    · exact signedChainResolutionRadiusSq_pos D C right.swap
    · apply lt_min
      · exact signedChainResolutionRadiusSq_pos H E product.swap
      · exact endpointStabilitiesRadiusSq_pos A B C D E H root endpoint

/-- The left outer cell may begin on coordinate axes.  Its Gaussian factor
values need only be nonzero as pairs; the inner endpoint is chosen away from
the three denominator coordinates. -/
theorem auxiliaryProductFormula_of_leftEndpoint_refined_radiusSq
    {A B C D E H : Polynomial} {root interval : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      endpointProductResolutionRadiusSq left right
        realIdentity imagIdentity interval.lower)
    (leftStart : A.eval interval.lower ≠ 0 ∨
      B.eval interval.lower ≠ 0)
    (rightStart : C.eval interval.lower ≠ 0 ∨
      D.eval interval.lower ≠ 0)
    (leftImagStop : B.eval interval.upper ≠ 0)
    (rightImagStop : D.eval interval.upper ≠ 0)
    (productImagStop : H.eval interval.upper ≠ 0) :
    RFAP.CauchyProduct.AuxiliaryProductFormula
      A B C D E H interval.lower interval.upper := by
  let product := left.complexProduct right realIdentity imagIdentity
  have leftRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq B A left.swap :=
    radius.trans_le (min_le_left _ _)
  have rightRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq D C right.swap :=
    radius.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have productRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq H E product.swap :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have stabilityRadius : sampleRadiusSq interval interval.lower <
      endpointStabilitiesRadiusSq A B C D E H root interval.lower :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (le_refl _))))
  let leftEvent := cauchyEventSignsOfRefinedRadiusSq
    left.swap refines leftRadius
  let rightEvent := cauchyEventSignsOfRefinedRadiusSq
    right.swap refines rightRadius
  let productEvent := cauchyEventSignsOfRefinedRadiusSq
    product.swap refines productRadius
  have stabilities := endpointStabilities_of_refined_radiusSq refines
    (Or.inl ⟨rfl, rfl⟩) stabilityRadius
  have productStart : E.eval interval.lower ≠ 0 ∨
      H.eval interval.lower ≠ 0 :=
    complexProductPair_ne_zero
      (A.eval interval.lower) (B.eval interval.lower)
      (C.eval interval.lower) (D.eval interval.lower)
      (E.eval interval.lower) (H.eval interval.lower)
      leftStart rightStart (realIdentity interval.lower)
      (imagIdentity interval.lower)
  apply RFAP.CauchyProduct.auxiliaryProductFormula_of_localEndpointData
  exact
    { leftIndex := leftEvent.index_eq_leftEndpointIndex2
        leftStart stabilities.leftReal stabilities.leftImag
      rightIndex := rightEvent.index_eq_leftEndpointIndex2
        rightStart stabilities.rightReal stabilities.rightImag
      productIndex := productEvent.index_eq_leftEndpointIndex2
        productStart stabilities.productReal stabilities.productImag
      factorLeftStart := leftStart
      factorRightStart := rightStart
      leftImagStop := leftImagStop
      rightImagStop := rightImagStop
      productImagStop := productImagStop
      leftRealStable := stabilities.leftReal
      leftImagStable := stabilities.leftImag
      rightRealStable := stabilities.rightReal
      rightImagStable := stabilities.rightImag
      productRealStable := stabilities.productReal
      productImagStable := stabilities.productImag
      productRealStart := realIdentity interval.lower
      productImagStart := imagIdentity interval.lower
      productRealStop := realIdentity interval.upper
      productImagStopEq := imagIdentity interval.upper }

/-- Symmetric right-outer-cell theorem, proved by re-centering the same three
finite event records at the right endpoint and reversing their indices. -/
theorem auxiliaryProductFormula_of_rightEndpoint_refined_radiusSq
    {A B C D E H : Polynomial} {root interval : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      endpointProductResolutionRadiusSq left right
        realIdentity imagIdentity interval.upper)
    (leftStart : A.eval interval.upper ≠ 0 ∨
      B.eval interval.upper ≠ 0)
    (rightStart : C.eval interval.upper ≠ 0 ∨
      D.eval interval.upper ≠ 0)
    (leftImagStop : B.eval interval.lower ≠ 0)
    (rightImagStop : D.eval interval.lower ≠ 0)
    (productImagStop : H.eval interval.lower ≠ 0) :
    RFAP.CauchyProduct.AuxiliaryProductFormula
      A B C D E H interval.lower interval.upper := by
  let product := left.complexProduct right realIdentity imagIdentity
  have leftRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq B A left.swap :=
    radius.trans_le (min_le_left _ _)
  have rightRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq D C right.swap :=
    radius.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have productRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq H E product.swap :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have stabilityRadius : sampleRadiusSq interval interval.lower <
      endpointStabilitiesRadiusSq A B C D E H root interval.upper :=
    radius.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (le_refl _))))
  let leftEvent := cauchyEventSignsOfRefinedRadiusSq
    left.swap refines leftRadius
  let rightEvent := cauchyEventSignsOfRefinedRadiusSq
    right.swap refines rightRadius
  let productEvent := cauchyEventSignsOfRefinedRadiusSq
    product.swap refines productRadius
  have stabilities := endpointStabilities_of_refined_radiusSq refines
    (Or.inr ⟨rfl, rfl⟩) stabilityRadius
  have productStart : E.eval interval.upper ≠ 0 ∨
      H.eval interval.upper ≠ 0 :=
    complexProductPair_ne_zero
      (A.eval interval.upper) (B.eval interval.upper)
      (C.eval interval.upper) (D.eval interval.upper)
      (E.eval interval.upper) (H.eval interval.upper)
      leftStart rightStart (realIdentity interval.upper)
      (imagIdentity interval.upper)
  have reversed :
      RFAP.CauchyProduct.AuxiliaryProductFormula
        A B C D E H interval.upper interval.lower := by
    apply RFAP.CauchyProduct.auxiliaryProductFormula_of_localEndpointData
    exact
      { leftIndex := leftEvent.reverseIndex_eq_leftEndpointIndex2
          leftStart stabilities.leftReal stabilities.leftImag
        rightIndex := rightEvent.reverseIndex_eq_leftEndpointIndex2
          rightStart stabilities.rightReal stabilities.rightImag
        productIndex := productEvent.reverseIndex_eq_leftEndpointIndex2
          productStart stabilities.productReal stabilities.productImag
        factorLeftStart := leftStart
        factorRightStart := rightStart
        leftImagStop := leftImagStop
        rightImagStop := rightImagStop
        productImagStop := productImagStop
        leftRealStable := stabilities.leftReal
        leftImagStable := stabilities.leftImag
        rightRealStable := stabilities.rightReal
        rightImagStable := stabilities.rightImag
        productRealStable := stabilities.productReal
        productImagStable := stabilities.productImag
        productRealStart := realIdentity interval.upper
        productImagStart := imagIdentity interval.upper
        productRealStop := realIdentity interval.lower
        productImagStopEq := imagIdentity interval.lower }
  exact reversed.reverse

/-- One positive squared-radius threshold covers all three finite Cauchy
scanners and the two factor-turn checks used by the local product cell. -/
def localProductResolutionRadiusSq
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Coordinate :=
  let product := left.complexProduct right realIdentity imagIdentity
  min (signedChainResolutionRadiusSq B A left.swap)
    (min (signedChainResolutionRadiusSq D C right.swap)
      (min (signedChainResolutionRadiusSq H E product.swap)
        (min (narrowTurnResolutionRadiusSq left)
          (narrowTurnResolutionRadiusSq right))))

theorem localProductResolutionRadiusSq_pos
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < localProductResolutionRadiusSq left right
      realIdentity imagIdentity := by
  let product := left.complexProduct right realIdentity imagIdentity
  unfold localProductResolutionRadiusSq
  apply lt_min
  · exact signedChainResolutionRadiusSq_pos B A left.swap
  · apply lt_min
    · exact signedChainResolutionRadiusSq_pos D C right.swap
    · apply lt_min
      · exact signedChainResolutionRadiusSq_pos H E product.swap
      · apply lt_min
        · exact narrowTurnResolutionRadiusSq_pos left
        · exact narrowTurnResolutionRadiusSq_pos right

/-- Every clear refinement below the combined squared radius makes the
complete executable local product-cell classifier return `true`. -/
theorem localProductCell?_eq_true_of_refined_radiusSq
    {A B C D E H : Polynomial} {root interval : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      localProductResolutionRadiusSq left right realIdentity imagIdentity)
    (AₗNonzero : A.eval interval.lower ≠ 0)
    (BₗNonzero : B.eval interval.lower ≠ 0)
    (CₗNonzero : C.eval interval.lower ≠ 0)
    (DₗNonzero : D.eval interval.lower ≠ 0)
    (EₗNonzero : E.eval interval.lower ≠ 0)
    (HₗNonzero : H.eval interval.lower ≠ 0)
    (AᵣNonzero : A.eval interval.upper ≠ 0)
    (BᵣNonzero : B.eval interval.upper ≠ 0)
    (CᵣNonzero : C.eval interval.upper ≠ 0)
    (DᵣNonzero : D.eval interval.upper ≠ 0)
    (EᵣNonzero : E.eval interval.upper ≠ 0)
    (HᵣNonzero : H.eval interval.upper ≠ 0) :
    RFAP.CauchyProductCells.localProductCell?
      A B C D E H interval = true := by
  let product := left.complexProduct right realIdentity imagIdentity
  have leftRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq B A left.swap :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact min_le_left _ _)
  have rightRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq D C right.swap :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (min_le_right _ _).trans (min_le_left _ _))
  have productRadius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq H E product.swap :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have leftTurnRadius : sampleRadiusSq interval interval.lower <
      narrowTurnResolutionRadiusSq left :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have rightTurnRadius : sampleRadiusSq interval interval.lower <
      narrowTurnResolutionRadiusSq right :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
  have leftFound := cauchyEventSigns?_isSome_of_refined_radiusSq
    left.swap refines leftRadius
  have rightFound := cauchyEventSigns?_isSome_of_refined_radiusSq
    right.swap refines rightRadius
  have productFound := cauchyEventSigns?_isSome_of_refined_radiusSq
    product.swap refines productRadius
  have leftNarrow := narrowComplexTurn_of_refined_radiusSq
    left refines leftTurnRadius
  have rightNarrow := narrowComplexTurn_of_refined_radiusSq
    right refines rightTurnRadius
  have centerFound :=
    RFAP.CauchyProductCells.ProductCenterSigns.search?_isSome_of_narrowTurns
      AₗNonzero BₗNonzero CₗNonzero DₗNonzero EₗNonzero HₗNonzero
      AᵣNonzero BᵣNonzero CᵣNonzero DᵣNonzero EᵣNonzero HᵣNonzero
      (realIdentity interval.lower) (imagIdentity interval.lower)
      (realIdentity interval.upper) (imagIdentity interval.upper)
      leftNarrow rightNarrow
  have eventDataFound :=
    RFAP.CauchyProductCells.localEventData?_isSome
      leftFound rightFound productFound centerFound
      BₗNonzero DₗNonzero HₗNonzero BᵣNonzero DᵣNonzero HᵣNonzero
      (realIdentity interval.lower) (imagIdentity interval.lower)
      (realIdentity interval.upper) (imagIdentity interval.upper)
  exact eventDataFound

/-- The coefficient-finite shrinking-radius construction proves the complete
local doubled Cauchy-product formula on every clear refined cell. -/
theorem auxiliaryProductFormula_of_refined_radiusSq
    {A B C D E H : Polynomial} {root interval : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : sampleRadiusSq interval interval.lower <
      localProductResolutionRadiusSq left right realIdentity imagIdentity)
    (AₗNonzero : A.eval interval.lower ≠ 0)
    (BₗNonzero : B.eval interval.lower ≠ 0)
    (CₗNonzero : C.eval interval.lower ≠ 0)
    (DₗNonzero : D.eval interval.lower ≠ 0)
    (EₗNonzero : E.eval interval.lower ≠ 0)
    (HₗNonzero : H.eval interval.lower ≠ 0)
    (AᵣNonzero : A.eval interval.upper ≠ 0)
    (BᵣNonzero : B.eval interval.upper ≠ 0)
    (CᵣNonzero : C.eval interval.upper ≠ 0)
    (DᵣNonzero : D.eval interval.upper ≠ 0)
    (EᵣNonzero : E.eval interval.upper ≠ 0)
    (HᵣNonzero : H.eval interval.upper ≠ 0) :
    RFAP.CauchyProduct.AuxiliaryProductFormula
      A B C D E H interval.lower interval.upper := by
  apply RFAP.CauchyProductCells.auxiliaryProductFormula_of_localProductCell
    A B C D E H interval
  exact localProductCell?_eq_true_of_refined_radiusSq left right
    realIdentity imagIdentity refines radius
    AₗNonzero BₗNonzero CₗNonzero DₗNonzero EₗNonzero HₗNonzero
    AᵣNonzero BᵣNonzero CᵣNonzero DᵣNonzero EᵣNonzero HᵣNonzero

end RFAP.CauchyResolution

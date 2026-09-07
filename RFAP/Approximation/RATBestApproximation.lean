import RFAP.Approximation.LocalSuccessor
import RFAP.Polynomial.GaussianDenominatorHeight
import RFAP.Polynomial.HeightApproximation

/-!
# Best approximations of finite RAT responses

A root-approximation track is a finite request-and-response object, not an
unnamed completed root.  One response contains a displayed rational sample
strictly inside its new winding-one box, together with a polynomial residual
bound.  This module converts that sample to the Gaussian-denominator format
used by the best-approximation calculation.

The resulting program emits only pairs satisfying the full two-tier best
predicate for the displayed RAT response.  From a supplied best pair it
selects one pair at the next occupied denominator level.  The selector is
empty exactly when the supplied pair already has zero error, so every call
constructively returns either a genuine next best pair or an exact terminal
certificate.

No assertion is made about an unrepresented limiting point of the track.
-/

namespace RFAP.RATBestApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev RawWindingState := RFAP.RawSubdivision.RawWindingState
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev SquarefreeCertificate := RFAP.LocalExtraction.SquarefreeCertificate
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev CommonFraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation

/-! ## Exact finite successor selection -/

/-- Select one representative from the next occupied best denominator level.
The complete finite successor list may contain several tied representatives;
this program deterministically retains its first one. -/
def nextBest? (source : Fraction) (lower : Pair) : Option Pair :=
  match consecutiveSuccessors source lower with
  | [] => none
  | next :: _ => some next

/-- Every pair emitted by `nextBest?` really is at the consecutive best level
above the supplied pair. -/
theorem nextBest?_sound
    {source : Fraction} {lower next : Pair}
    (selected : nextBest? source lower = some next) :
    AreConsecutiveBest source.value lower next := by
  unfold nextBest? at selected
  cases listIdentity : consecutiveSuccessors source lower with
  | nil =>
      rw [listIdentity] at selected
      cases selected
  | cons head remaining =>
      rw [listIdentity] at selected
      have headIdentity : head = next := Option.some.inj selected
      subst next
      apply (mem_consecutiveSuccessors_iff source lower head).mp
      rw [listIdentity]
      exact List.mem_cons_self

/-- Finite descent from the displayed exact pair produces a best pair with
exactly zero error. -/
theorem exists_zeroErrorBest (source : Fraction) :
    ∃ pair : Pair,
      IsBest source.value pair ∧ errorQuadrance source.value pair = 0 := by
  have exactSmall : errorQuadrance source.value (exactPair source) ≤ 1 / 2 := by
    rw [errorQuadrance, exactPair_error,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
    decide
  obtain ⟨pair, best, _, errorLe⟩ :=
    exists_best_below_of_small source.denominatorNonzero le_rfl exactSmall
  have exactZero : errorQuadrance source.value (exactPair source) = 0 := by
    rw [errorQuadrance, exactPair_error,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
  rw [exactZero] at errorLe
  have nonnegative : 0 ≤ errorQuadrance source.value pair := by
    unfold errorQuadrance
    exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  exact ⟨pair, best, le_antisymm errorLe nonnegative⟩

/-- Every nonterminal best pair has a computable next occupied best level.
The proof first constructs a zero-error terminal best pair and then performs
a finite minimum over the displayed best pairs lying strictly above `lower`.
-/
theorem exists_nextBest_of_error_ne_zero
    {source : Fraction} {lower : Pair}
    (lowerBest : IsBest source.value lower)
    (errorNonzero : errorQuadrance source.value lower ≠ 0) :
    ∃ next : Pair,
      nextBest? source lower = some next ∧
        AreConsecutiveBest source.value lower next := by
  obtain ⟨terminal, terminalBest, terminalZero⟩ :=
    exists_zeroErrorBest source
  have lowerBeforeTerminal :
      denominatorQuadrance lower < denominatorQuadrance terminal := by
    apply Nat.lt_of_not_ge
    intro terminalNoHigher
    have lowerErrorLeZero := lowerBest.2.2 terminal terminalBest.1
      terminalNoHigher
    rw [terminalZero] at lowerErrorLeZero
    have lowerErrorNonnegative :
        0 ≤ errorQuadrance source.value lower := by
      unfold errorQuadrance
      exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
    exact errorNonzero (le_antisymm lowerErrorLeZero lowerErrorNonnegative)
  obtain ⟨witness, consecutive, _⟩ :=
    RFAP.LocalSuccessor.exists_consecutiveBest_below
      lowerBest terminalBest lowerBeforeTerminal
  have witnessMember : witness ∈ consecutiveSuccessors source lower :=
    (mem_consecutiveSuccessors_iff source lower witness).mpr consecutive
  cases listIdentity : consecutiveSuccessors source lower with
  | nil =>
      rw [listIdentity] at witnessMember
      exact (List.not_mem_nil witnessMember).elim
  | cons next remaining =>
      refine ⟨next, ?_, ?_⟩
      · simp only [nextBest?, listIdentity]
      · apply (mem_consecutiveSuccessors_iff source lower next).mp
        rw [listIdentity]
        exact List.mem_cons_self

/-- A zero-error best pair has no later best denominator level. -/
theorem nextBest?_eq_none_of_error_eq_zero
    {source : Fraction} {lower : Pair}
    (lowerBest : IsBest source.value lower)
    (errorZero : errorQuadrance source.value lower = 0) :
    nextBest? source lower = none := by
  unfold nextBest?
  cases listIdentity : consecutiveSuccessors source lower with
  | nil => rfl
  | cons next remaining =>
      have nextConsecutive : AreConsecutiveBest source.value lower next := by
        apply (mem_consecutiveSuccessors_iff source lower next).mp
        rw [listIdentity]
        exact List.mem_cons_self
      have impossible := nextConsecutive.2.1.2.1 lower lowerBest.1
        nextConsecutive.2.2.1
      rw [errorZero] at impossible
      exact (not_lt_of_ge
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        impossible).elim

/-- Exact terminal specification of the executable next-best selector. -/
theorem nextBest?_eq_none_iff
    {source : Fraction} {lower : Pair}
    (lowerBest : IsBest source.value lower) :
    nextBest? source lower = none ↔
      errorQuadrance source.value lower = 0 := by
  constructor
  · intro selectedNone
    by_cases errorZero : errorQuadrance source.value lower = 0
    · exact errorZero
    · obtain ⟨next, selected, _⟩ :=
        exists_nextBest_of_error_ne_zero lowerBest errorZero
      rw [selectedNone] at selected
      cases selected
  · exact nextBest?_eq_none_of_error_eq_zero lowerBest

/-- Total finite alternative: a best pair has a certified consecutive
successor, or it is already an exact terminal for the displayed source. -/
theorem nextBest_or_exactTerminal
    {source : Fraction} {lower : Pair}
    (lowerBest : IsBest source.value lower) :
    (∃ next : Pair,
      nextBest? source lower = some next ∧
        AreConsecutiveBest source.value lower next) ∨
      errorQuadrance source.value lower = 0 := by
  by_cases errorZero : errorQuadrance source.value lower = 0
  · exact Or.inr errorZero
  · exact Or.inl (exists_nextBest_of_error_ne_zero lowerBest errorZero)

/-! ## RAT-response interface -/

/-- Convert the common-denominator sample returned by a finite RAT request to
the Gaussian-denominator source consumed by the best-approximation program. -/
def responseSource (sample : CommonFraction) : Fraction :=
  RFAP.GaussianDenominatorHeight.ofCommon sample

theorem responseSource_value (sample : CommonFraction) :
    (responseSource sample).value = sample.value :=
  RFAP.GaussianDenominatorHeight.ofCommon_value sample

/-- Complete finite list of all and only the best approximants to one
displayed rational RAT response. -/
def bestApproximations (sample : CommonFraction) : List Pair :=
  allBest (responseSource sample)

theorem mem_bestApproximations_iff
    (sample : CommonFraction) (pair : Pair) :
    pair ∈ bestApproximations sample ↔ IsBest sample.value pair := by
  rw [bestApproximations, mem_allBest_iff_isBest,
    responseSource_value]

/-- Every displayed RAT response has at least one computed best approximant. -/
theorem bestApproximations_nonempty (sample : CommonFraction) :
    bestApproximations sample ≠ [] := by
  obtain ⟨pair, best, _⟩ := exists_zeroErrorBest (responseSource sample)
  have sampleBest : IsBest sample.value pair := by
    rwa [responseSource_value] at best
  have member := (mem_bestApproximations_iff sample pair).mpr sampleBest
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

/-- Select the next best approximant to one displayed RAT response. -/
def nextBestApproximation?
    (sample : CommonFraction) (lower : Pair) : Option Pair :=
  nextBest? (responseSource sample) lower

/-- The RAT-facing selector emits only genuine consecutive best
approximants. -/
theorem nextBestApproximation?_sound
    {sample : CommonFraction} {lower next : Pair}
    (selected : nextBestApproximation? sample lower = some next) :
    AreConsecutiveBest sample.value lower next := by
  have sound := nextBest?_sound selected
  rwa [responseSource_value] at sound

/-- For a certified best approximant to a RAT response, the executable
selector produces the next occupied best level or certifies exact
termination. -/
theorem nextBestApproximation_or_exactTerminal
    {sample : CommonFraction} {lower : Pair}
    (lowerBest : IsBest sample.value lower) :
    (∃ next : Pair,
      nextBestApproximation? sample lower = some next ∧
        AreConsecutiveBest sample.value lower next) ∨
      errorQuadrance sample.value lower = 0 := by
  have sourceBest : IsBest (responseSource sample).value lower := by
    rwa [responseSource_value]
  have result := nextBest_or_exactTerminal sourceBest
  change (∃ next : Pair,
    nextBestApproximation? sample lower = some next ∧
      AreConsecutiveBest (responseSource sample).value lower next) ∨
    errorQuadrance (responseSource sample).value lower = 0 at result
  rw [responseSource_value] at result
  exact result

/-- The next-best selector for a RAT response is empty exactly at a displayed
zero-error terminal. -/
theorem nextBestApproximation?_eq_none_iff
    {sample : CommonFraction} {lower : Pair}
    (lowerBest : IsBest sample.value lower) :
    nextBestApproximation? sample lower = none ↔
      errorQuadrance sample.value lower = 0 := by
  have sourceBest : IsBest (responseSource sample).value lower := by
    rwa [responseSource_value]
  have result := nextBest?_eq_none_iff sourceBest
  change nextBestApproximation? sample lower = none ↔
    errorQuadrance (responseSource sample).value lower = 0 at result
  rw [responseSource_value] at result
  exact result

/-! ## Exact finite observations -/

/-- Best-approximation arithmetic attached to one exact rational observation,
such as the degree-one branch of the finite FTA or a linear RFAP site. -/
structure PointBestResponse (point : Gaussian) where
  sample : CommonFraction
  sampleValue : sample.value = point
  approximants : List Pair
  approximantsNonempty : approximants ≠ []
  memApproximantsIff : ∀ pair : Pair,
    pair ∈ approximants ↔ IsBest point pair
  next? : Pair → Option Pair
  nextSound : ∀ {lower next : Pair}, next? lower = some next →
    AreConsecutiveBest point lower next
  nextOrTerminal : ∀ {lower : Pair}, IsBest point lower →
    (∃ next : Pair, next? lower = some next ∧
      AreConsecutiveBest point lower next) ∨
      errorQuadrance point lower = 0

/-- Construct the complete all-best and next-best package for an exact
displayed Gaussian-rational point. -/
def respondToPoint (point : Gaussian) : PointBestResponse point := by
  let sample := RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian point
  have sampleValue : sample.value = point :=
    RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian_value point
  exact
    { sample := sample
      sampleValue := sampleValue
      approximants := bestApproximations sample
      approximantsNonempty := bestApproximations_nonempty sample
      memApproximantsIff := fun pair => by
        rw [mem_bestApproximations_iff, sampleValue]
      next? := nextBestApproximation? sample
      nextSound := fun selected => by
        have sound := nextBestApproximation?_sound selected
        rwa [sampleValue] at sound
      nextOrTerminal := fun {lower} best => by
        have sampleBest : IsBest sample.value lower := by
          rwa [sampleValue]
        have result := nextBestApproximation_or_exactTerminal sampleBest
        rw [sampleValue] at result
        exact result }

/-! ## Direct RFAP-I track responses -/

/-- The refined winding-one state returned by one finite call to an RFAP-I
root-approximation track. -/
def trackResponseState
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    WindingOneState p ambient :=
  track.refine current epsilon epsilonPositive

/-- Canonical common-denominator presentation of the rational anchor carried
by one finite RFAP-I track response. -/
def trackResponseSample
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) : CommonFraction :=
  RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian
    (trackResponseState track current epsilon epsilonPositive).box.anchor

theorem trackResponseSample_value
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    (trackResponseSample track current epsilon epsilonPositive).value =
      (trackResponseState track current epsilon epsilonPositive).box.anchor :=
  RFAP.ConstructiveGaussianHeight.Fraction.ofGaussian_value _

/-- The displayed RAT response sample lies in its returned winding-one box. -/
theorem trackResponseSample_inside
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    (trackResponseState track current epsilon epsilonPositive).box.Contains
      (trackResponseSample track current epsilon epsilonPositive).value := by
  rw [trackResponseSample_value]
  exact RFAP.Boxes.Box.contains_anchor _

theorem trackResponseState_refines
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    (trackResponseState track current epsilon epsilonPositive).box.Refines
      current.box :=
  track.nested current epsilon epsilonPositive

theorem trackResponseState_accurate
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    (trackResponseState track current epsilon epsilonPositive).box.diagonalSq ≤
      epsilon ^ 2 :=
  track.accurate current epsilon epsilonPositive

/-- The canonical RAT response sample inherits the RFAP-I anchor residual
bound from the returned nonzero-winding box. -/
theorem trackResponseSample_residual_le
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (trackResponseSample track current epsilon epsilonPositive).value) ≤
      RFAP.LocalExtraction.anchorResidualBound p ambient
        (trackResponseState track current epsilon epsilonPositive).box := by
  rw [trackResponseSample_value]
  let state := trackResponseState track current epsilon epsilonPositive
  exact RFAP.LocalExtraction.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
    p degreePositive state.refinesAmbient state.proper state.raw.rawWinding_ne

/-- Execute the complete all-best table at one direct response of an RFAP-I
root-approximation track. -/
def trackBestApproximations
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) : List Pair :=
  bestApproximations (trackResponseSample track current epsilon epsilonPositive)

theorem mem_trackBestApproximations_iff
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) (pair : Pair) :
    pair ∈ trackBestApproximations track current epsilon epsilonPositive ↔
      IsBest
        (trackResponseState track current epsilon epsilonPositive).box.anchor
        pair := by
  rw [trackBestApproximations, mem_bestApproximations_iff,
    trackResponseSample_value]

theorem trackBestApproximations_nonempty
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    trackBestApproximations track current epsilon epsilonPositive ≠ [] :=
  bestApproximations_nonempty
    (trackResponseSample track current epsilon epsilonPositive)

/-- Select one representative of the next occupied best level at a direct
RFAP-I track response. -/
def trackNextBestApproximation?
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (lower : Pair) : Option Pair :=
  nextBestApproximation?
    (trackResponseSample track current epsilon epsilonPositive) lower

theorem trackNextBestApproximation?_sound
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient} {current : WindingOneState p ambient}
    {epsilon : Coordinate} {epsilonPositive : 0 < epsilon}
    {lower next : Pair}
    (selected : trackNextBestApproximation? track current epsilon
      epsilonPositive lower = some next) :
    AreConsecutiveBest
      (trackResponseState track current epsilon epsilonPositive).box.anchor
      lower next := by
  have sound := nextBestApproximation?_sound selected
  rwa [trackResponseSample_value] at sound

/-- Every best approximant to a direct RFAP-I track response has a computed
consecutive successor or is an exact terminal for that displayed response. -/
theorem trackNextBestApproximation_or_exactTerminal
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient} {current : WindingOneState p ambient}
    {epsilon : Coordinate} {epsilonPositive : 0 < epsilon}
    {lower : Pair}
    (lowerBest : IsBest
      (trackResponseState track current epsilon epsilonPositive).box.anchor
      lower) :
    (∃ next : Pair,
      trackNextBestApproximation? track current epsilon epsilonPositive lower =
          some next ∧
        AreConsecutiveBest
          (trackResponseState track current epsilon epsilonPositive).box.anchor
          lower next) ∨
      errorQuadrance
        (trackResponseState track current epsilon epsilonPositive).box.anchor
        lower = 0 := by
  have sampleBest : IsBest
      (trackResponseSample track current epsilon epsilonPositive).value lower := by
    rwa [trackResponseSample_value]
  have result := nextBestApproximation_or_exactTerminal sampleBest
  change (∃ next : Pair,
    trackNextBestApproximation? track current epsilon epsilonPositive lower =
        some next ∧
      AreConsecutiveBest
        (trackResponseSample track current epsilon epsilonPositive).value
        lower next) ∨
    errorQuadrance
      (trackResponseSample track current epsilon epsilonPositive).value lower = 0
      at result
  rw [trackResponseSample_value] at result
  exact result

/-- One finite response of any RFAP-I root-approximation track, packaged with
its refinement, residual, complete all-best table, and total next-best step. -/
structure TrackBestResponse
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) where
  refined : WindingOneState p ambient
  refinesCurrent : refined.box.Refines current.box
  accurate : refined.box.diagonalSq ≤ epsilon ^ 2
  sample : CommonFraction
  sampleValue : sample.value = refined.box.anchor
  sampleInside : refined.box.Contains sample.value
  residualLe : RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval sample.value) ≤
    RFAP.LocalExtraction.anchorResidualBound p ambient refined.box
  approximants : List Pair
  approximantsNonempty : approximants ≠ []
  memApproximantsIff : ∀ pair : Pair,
    pair ∈ approximants ↔ IsBest sample.value pair
  next? : Pair → Option Pair
  nextSound : ∀ {lower next : Pair}, next? lower = some next →
    AreConsecutiveBest sample.value lower next
  nextOrTerminal : ∀ {lower : Pair}, IsBest sample.value lower →
    (∃ next : Pair, next? lower = some next ∧
      AreConsecutiveBest sample.value lower next) ∨
      errorQuadrance sample.value lower = 0

/-- Construct the complete proof-bearing response package by finite
calculation from an RFAP-I track call. -/
def respondToTrack
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    TrackBestResponse degreePositive track current epsilon epsilonPositive where
  refined := trackResponseState track current epsilon epsilonPositive
  refinesCurrent := trackResponseState_refines track current epsilon
    epsilonPositive
  accurate := trackResponseState_accurate track current epsilon epsilonPositive
  sample := trackResponseSample track current epsilon epsilonPositive
  sampleValue := trackResponseSample_value track current epsilon epsilonPositive
  sampleInside := trackResponseSample_inside track current epsilon epsilonPositive
  residualLe := trackResponseSample_residual_le degreePositive track current
    epsilon epsilonPositive
  approximants := trackBestApproximations track current epsilon epsilonPositive
  approximantsNonempty := trackBestApproximations_nonempty track current epsilon
    epsilonPositive
  memApproximantsIff := fun pair => by
    rw [trackBestApproximations, mem_bestApproximations_iff]
  next? := trackNextBestApproximation? track current epsilon epsilonPositive
  nextSound := fun selected => by
    exact nextBestApproximation?_sound selected
  nextOrTerminal := fun best => by
    exact nextBestApproximation_or_exactTerminal best

/-! ## Polynomial RAT request -/

/-- Execute one polynomial RAT-compatible refinement request and retain its
interior rational response point and residual certificate. -/
def respond
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    RFAP.HeightApproximation.Output degreeAtLeastTwo squarefree elimination
      current epsilon :=
  RFAP.HeightApproximation.approximate degreeAtLeastTwo squarefree elimination
    current epsilonPositive

/-- The finite list computed from a polynomial RAT request contains all and
only the best approximants to that request's certified rational response. -/
theorem mem_bestApproximations_respond_iff
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) (pair : Pair) :
    pair ∈ bestApproximations
        (respond degreeAtLeastTwo squarefree elimination current
          epsilonPositive).fraction ↔
      IsBest
        (respond degreeAtLeastTwo squarefree elimination current
          epsilonPositive).fraction.value pair :=
  mem_bestApproximations_iff _ _

/-- One polynomial RAT request therefore supports a total next-best step:
from any certified best response approximant, compute its genuine next best
level or certify that the response is represented exactly. -/
theorem respond_nextBest_or_exactTerminal
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) (lower : Pair)
    (lowerBest : IsBest
      (respond degreeAtLeastTwo squarefree elimination current
        epsilonPositive).fraction.value lower) :
    (∃ next : Pair,
      nextBestApproximation?
          (respond degreeAtLeastTwo squarefree elimination current
            epsilonPositive).fraction lower = some next ∧
        AreConsecutiveBest
          (respond degreeAtLeastTwo squarefree elimination current
            epsilonPositive).fraction.value lower next) ∨
      errorQuadrance
        (respond degreeAtLeastTwo squarefree elimination current
          epsilonPositive).fraction.value lower = 0 :=
  nextBestApproximation_or_exactTerminal lowerBest

end RFAP.RATBestApproximation

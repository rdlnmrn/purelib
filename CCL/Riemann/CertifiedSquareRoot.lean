import CCL.Riemann.SquareRootContinuation

/-!
# An operational square root from any certified winding track

`SquareRootSheets` starts from the two independently isolated owners of
`Z^2 - w`.  Rouché continuation produces different tracks, in different
finite ambient boxes.  This file proves the same operational square-root
contract for every such track.  Thus a transported owner can be used as an
actual division-safe CCL value without re-isolating, and hence without losing
its sheet identity.
-/

namespace CCL.Riemann.CertifiedSquareRoot

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian

private theorem quarterRadius_index_antitone {scale : Coordinate}
    (scaleNonnegative : 0 <= scale) {earlier later : Nat}
    (order : earlier <= later) :
    CCL.FiniteGeometric.quarterRadius scale later <=
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra <= 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) <= 1 / 4 by decide)
      (show (1 / 4 : Coordinate) <= 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 <= (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 <= scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ <= (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_one_direct _

/-- First index at which an arbitrary square-root track has residual smaller
than the fixed nonzero-radicand threshold. -/
def baseIndex {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.CoherentRoot.residualScale
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      ambient track)
    0 (CCL.Riemann.SquareRootSheets.residualTarget parameter)

/-- The track approximation after dropping the finitely many samples that
may still meet zero. -/
def approximation {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) : Approximation :=
  CCL.Riemann.SquareRootSheets.tail
    (CCL.Riemann.CoherentRoot.approximation track) (baseIndex track)

theorem sample_residual_le {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (index : Nat) :
    normSq
        ((approximation track).sample index *
            (approximation track).sample index - parameter) <=
      CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.CoherentRoot.residualScale
          (CCL.PowerMonodromy.polynomial parameter
            CCL.Riemann.SquareRootSheets.degreeTwo)
          ambient track) index := by
  let selected := max (baseIndex track) index
  have raw := CCL.Riemann.CoherentRoot.sample_residual_le track (by
    rw [CCL.PowerMonodromy.polynomial_degree]
    exact CCL.Riemann.SquareRootSheets.degreeTwo.positive) selected
  rw [CCL.PowerMonodromy.polynomial_eval] at raw
  have selectedBound := quarterRadius_index_antitone
    (CCL.Riemann.CoherentRoot.residualScale_nonneg
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      ambient track)
    (Nat.le_max_right (baseIndex track) index)
  simpa only [approximation, CCL.Riemann.SquareRootSheets.tail_sample,
    selected, CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two] using
      raw.trans selectedBound

theorem sample_residual_lt_target {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (index : Nat) :
    normSq
        ((approximation track).sample index *
            (approximation track).sample index - parameter) <
      CCL.Riemann.SquareRootSheets.residualTarget parameter := by
  let scale := CCL.Riemann.CoherentRoot.residualScale
    (CCL.PowerMonodromy.polynomial parameter
      CCL.Riemann.SquareRootSheets.degreeTwo)
    ambient track
  have baseSmall : CCL.FiniteGeometric.quarterRadius scale
      (baseIndex track) <
      CCL.Riemann.SquareRootSheets.residualTarget parameter := by
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate scale
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        ambient track)
      0 (CCL.Riemann.SquareRootSheets.residualTarget parameter)
      (CCL.Riemann.SquareRootSheets.residualTarget_positive parameterNonzero)
  let selected := max (baseIndex track) index
  have raw := CCL.Riemann.CoherentRoot.sample_residual_le track (by
    rw [CCL.PowerMonodromy.polynomial_degree]
    exact CCL.Riemann.SquareRootSheets.degreeTwo.positive) selected
  rw [CCL.PowerMonodromy.polynomial_eval] at raw
  have selectedSmall : CCL.FiniteGeometric.quarterRadius scale selected <
      CCL.Riemann.SquareRootSheets.residualTarget parameter :=
    (quarterRadius_index_antitone
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        ambient track)
      (Nat.le_max_left (baseIndex track) index)).trans_lt baseSmall
  simpa only [approximation, CCL.Riemann.SquareRootSheets.tail_sample,
    selected, CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two] using
      raw.trans_lt selectedSmall

/-- First explicit approximation index whose quadratic residual allowance is
below an arbitrary positive rational target. -/
def residualIndex {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (target : Coordinate) (_positive : 0 < target) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.CoherentRoot.residualScale
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      ambient track) 0 target

theorem residualIndex_accurate {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (target : Coordinate) (positive : 0 < target) :
    CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.CoherentRoot.residualScale
          (CCL.PowerMonodromy.polynomial parameter
            CCL.Riemann.SquareRootSheets.degreeTwo)
          ambient track)
        (residualIndex track target positive) < target := by
  exact CCL.FiniteGeometric.firstQuarterBelow_accurate _
    (CCL.Riemann.CoherentRoot.residualScale_nonneg
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      ambient track) 0 target positive

theorem sample_norm_lower {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (index : Nat) :
    CCL.Riemann.SquareRootSheets.sampleNormLower parameter <=
      normSq ((approximation track).sample index) :=
  CCL.Riemann.SquareRootSheets.normSq_lower_of_square_residual
    (sample_residual_lt_target parameterNonzero track index).le

/-- Candidate apartness supplied purely by the polynomial residual. -/
def possibleApart {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    CCL.ProgressiveCharts.PossibleApart (approximation track).toProcess where
  lowerSq := CCL.Riemann.SquareRootSheets.sampleNormLower parameter
  positive := CCL.Riemann.SquareRootSheets.sampleLower_positive
    parameterNonzero
  lower := by
    intro state value possible
    change (approximation track).Possible state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact sample_norm_lower parameterNonzero track later

/-- Coherent root carried by the supplied owner track. -/
def rawRoot {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    (approximation track)

/-- Division-ready version of the coherent root. -/
def root {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (rawRoot track) (possibleApart parameterNonzero track)

def rootApart {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    CCL.ProgressiveTransducer.Named.Apart
      (root parameterNonzero track).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (possibleApart parameterNonzero track)

/-- A division-ready root state whose every later finite candidate has the
requested quadratic residual.  The apartness preparation may refine beyond
the selected residual index, but never retreats from it. -/
def residualState {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (target : Coordinate) (positive : 0 < target) :
    (root parameterNonzero track).name.process.State := by
  change CCL.ProgressiveCharts.ApartState
    (approximation track).toProcess (possibleApart parameterNonzero track)
  exact CCL.ProgressiveCharts.prepareApartState
    (possibleApart parameterNonzero track)
    (residualIndex track target positive)

theorem residualState_candidate_residual_lt
    {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (target : Coordinate) (positive : 0 < target) {candidate : Gaussian}
    (possible : (root parameterNonzero track).name.process.Possible
      (residualState parameterNonzero track target positive) candidate) :
    normSq (candidate * candidate - parameter) < target := by
  change (approximation track).Possible
    (residualState parameterNonzero track target positive).source candidate
      at possible
  rcases possible with ⟨later, stateLeLater, rfl⟩
  have indexLeState : residualIndex track target positive <=
      (residualState parameterNonzero track target positive).source := by
    change residualIndex track target positive <=
      (approximation track).refineIndex
        (residualIndex track target positive)
        ((possibleApart parameterNonzero track).lowerSq / 12)
        (possibleApart parameterNonzero track).twelfth_pos
    exact (approximation track).refineIndex_ge _ _ _
  have indexLeLater : residualIndex track target positive <= later :=
    indexLeState.trans stateLeLater
  have residual := sample_residual_le track later
  have radiusLe := quarterRadius_index_antitone
    (CCL.Riemann.CoherentRoot.residualScale_nonneg
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      ambient track) indexLeLater
  exact residual.trans_lt
    (radiusLe.trans_lt (residualIndex_accurate track target positive))

/-- Pointwise square of the tailed track, with a finite geometric modulus. -/
def squareApproximation {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) : Approximation :=
  let source := approximation track
  let scale := 4 * source.centerBound *
    CCL.Riemann.CoherentRoot.scale track
  { sample := fun index => source.sample index * source.sample index
    radiusSq := CCL.FiniteGeometric.quarterRadius scale
    radiusSq_nonneg := CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          source.centerBound_nonneg)
        (CCL.Riemann.CoherentRoot.scale_positive track).le)
    later_close := by
      intro earlier later order
      have movement := source.later_close order
      have sourceRadiusLe : source.radiusSq earlier <=
          CCL.FiniteGeometric.quarterRadius
            (CCL.Riemann.CoherentRoot.scale track) earlier :=
        quarterRadius_index_antitone
          (CCL.Riemann.CoherentRoot.scale_positive track).le
          (Nat.le_max_right (baseIndex track) earlier)
      have firstTerm :
          normSq ((source.sample later - source.sample earlier) *
              source.sample later) <=
            CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.CoherentRoot.scale track) earlier *
              source.centerBound := by
        rw [normSq_mul]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct
          (movement.trans sourceRadiusLe) (source.sample_bounded later)
          (normSq_nonneg _) (CCL.FiniteGeometric.quarterRadius_nonneg
            (CCL.Riemann.CoherentRoot.scale_positive track).le earlier)
      have secondTerm :
          normSq (source.sample earlier *
              (source.sample later - source.sample earlier)) <=
            source.centerBound *
              CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.CoherentRoot.scale track) earlier := by
        rw [normSq_mul]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct
          (source.sample_bounded earlier) (movement.trans sourceRadiusLe)
          (normSq_nonneg _) source.centerBound_nonneg
      have identity :
          source.sample later * source.sample later -
              source.sample earlier * source.sample earlier =
            (source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
      rw [identity]
      calc
        normSq
            ((source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier)) <=
          2 *
            (normSq ((source.sample later - source.sample earlier) *
                source.sample later) +
              normSq (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
          normSq_add_le_two _ _
        _ <= 2 *
            (CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.CoherentRoot.scale track) earlier *
                source.centerBound +
              source.centerBound *
                CCL.FiniteGeometric.quarterRadius
                  (CCL.Riemann.CoherentRoot.scale track) earlier) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        _ = CCL.FiniteGeometric.quarterRadius scale earlier := by
          rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
            CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
          dsimp only [scale]
          ring1
    refineIndex current target _ :=
      CCL.FiniteGeometric.firstQuarterBelow scale current target
    refineIndex_ge current target _ :=
      CCL.FiniteGeometric.firstQuarterBelow_ge scale current target
    refineIndex_accurate :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate scale
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            source.centerBound_nonneg)
          (CCL.Riemann.CoherentRoot.scale_positive track).le)
    centerBound := source.centerBound * source.centerBound
    centerBound_nonneg := RFAP.ConstructiveFraction.mul_nonneg_direct
      source.centerBound_nonneg source.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (source.sample_bounded index) (source.sample_bounded index)
        (normSq_nonneg _) source.centerBound_nonneg }

@[simp] theorem squareApproximation_sample {parameter : Gaussian}
    {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (index : Nat) :
    (squareApproximation track).sample index =
      (approximation track).sample index *
        (approximation track).sample index := by
  simp [squareApproximation]

/-- The sampled square converges operationally to the exact radicand. -/
def squareApproximation_equivalent_parameter {parameter : Gaussian}
    {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    CCL.OperationalEquivalence.Equivalent
      (squareApproximation track)
      (CCL.TranscendentalLaws.constantApproximation parameter) where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let scale := CCL.Riemann.CoherentRoot.residualScale
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo)
      ambient track
    let index := CCL.FiniteGeometric.firstQuarterBelow scale start target
    have radiusSmall : CCL.FiniteGeometric.quarterRadius scale index < target :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate scale
        (CCL.Riemann.CoherentRoot.residualScale_nonneg
          (CCL.PowerMonodromy.polynomial parameter
            CCL.Riemann.SquareRootSheets.degreeTwo)
          ambient track) start target positive
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := (Nat.le_max_left _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge scale start target)
        right_ge := (Nat.le_max_right _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge scale start target)
        close := by
          intro leftLater rightLater leftOrder _rightOrder
          have residualBound := sample_residual_le track leftLater
          have radiusLater := quarterRadius_index_antitone
            (CCL.Riemann.CoherentRoot.residualScale_nonneg
              (CCL.PowerMonodromy.polynomial parameter
                CCL.Riemann.SquareRootSheets.degreeTwo)
              ambient track) leftOrder
          simpa only [squareApproximation_sample,
            CCL.TranscendentalLaws.constantApproximation] using
              residualBound.trans_lt (radiusLater.trans_lt radiusSmall) }

/-- The unprepared arithmetic root squares to the exact parameter. -/
def rawRoot_square {parameter : Gaussian} {ambient : Box}
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (rawRoot track) (rawRoot track)).name
      (CCL.ProgressiveTransducer.Named.exact parameter) := by
  let source := approximation track
  let product := squareApproximation track
  have actualToProduct : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul source.toNamed source.toNamed)
      product.toNamed :=
    CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
      source source product (by intro index; rfl)
  have productToConstant : NamedEquivalent product.toNamed
      (CCL.TranscendentalLaws.constantApproximation parameter).toNamed :=
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (squareApproximation_equivalent_parameter track)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by simpa only [rawRoot,
      CCL.ProgressiveCoherence.CoherentNamed.mul,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation, source, product]
      using actualToProduct)
    (CCL.OperationalEquivalence.NamedEquivalent.trans productToConstant
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.TranscendentalCoherence.exact_toConstantNamed parameter)))

/-- Apartification preserves the exact square equation. -/
def root_square {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (root parameterNonzero track)
        (root parameterNonzero track)).name
      (CCL.ProgressiveTransducer.Named.exact parameter) := by
  let raw := rawRoot track
  let prepared := root parameterNonzero track
  have preparedToRaw : NamedEquivalent prepared.name raw.name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent raw
        (possibleApart parameterNonzero track))
  have products : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul prepared prepared).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul raw raw).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      prepared raw prepared raw preparedToRaw preparedToRaw
  exact CCL.OperationalEquivalence.NamedEquivalent.trans products
    (rawRoot_square track)

/-- Complete operational contract extracted from an arbitrary continued
winding owner. -/
structure Certificate (parameter : Gaussian) where
  value : CoherentNamed
  apart : CCL.ProgressiveTransducer.Named.Apart value.name
  square : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.mul value value).name
    (CCL.ProgressiveTransducer.Named.exact parameter)

def certificate {parameter : Gaussian} {ambient : Box}
    (parameterNonzero : parameter ≠ 0)
    (track : WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    Certificate parameter where
  value := root parameterNonzero track
  apart := rootApart parameterNonzero track
  square := root_square parameterNonzero track

end CCL.Riemann.CertifiedSquareRoot

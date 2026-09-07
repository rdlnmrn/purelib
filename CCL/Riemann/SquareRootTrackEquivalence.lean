import CCL.Riemann.RobustSquareRootPreparation
import CCL.Riemann.UniformSquareRootPreparation

/-!
# Operational equivalence from finite winding-one overlap

The reconditioning bridge is topological data.  This module turns that data
into the analytic statement needed by integration: two shrinking square-root
tracks joined by a strictly nested winding-one box name the same operational
CCL value.  The proof is entirely finite.  If two sufficiently small boxes
were separated inside one winding-one owner, finite winding additivity would
force winding at least two in that owner, contradicting its displayed winding
one certificate.  A rational overlap point then bounds the two displayed
anchors by the sum of their box diagonals.
-/

namespace CCL.Riemann.SquareRootTrackEquivalence

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

open RFAP.ConstructiveGaussian.Gaussian

/-- Re-extract an inner winding-one state in the outer state's own box.  The
finite Newton-band extractor chooses fresh axis-safe boundaries, which is
essential: merely changing the ambient index would not supply clearance on
the full vertical and horizontal lines through the larger outer box. -/
def supportedInside {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (refines : inner.box.Refines outer.box) :
    WindingOneState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outer.box := by
  let input := CCL.Riemann.SquareRootReconditioning.isolationInput
    parameterNonzero
  let raw : RFAP.RawSubdivision.RawWindingState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outer.box :=
    { box := inner.box
      refinesAmbient := refines
      proper := inner.proper
      clearance := inner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← inner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }
  let extracted := RFAP.NewtonBand.extract input.degreeAtLeastTwo
    input.squarefree input.elimination raw (epsilon := (1 : Coordinate))
      (by decide)
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }

theorem supportedInside_refines_inner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (refines : inner.box.Refines outer.box) :
    (supportedInside parameterNonzero outer inner refines).box.Refines
      inner.box := by
  change (RFAP.NewtonBand.extract _ _ _ _ (epsilon := (1 : Coordinate))
    (by decide)).box.Refines inner.box
  exact (RFAP.NewtonBand.extract _ _ _ _ (epsilon := (1 : Coordinate))
    (by decide)).strictCurrent.refines

/-- Every positive-index state is strictly inside the initial state. -/
theorem state_strict_initial_of_pos
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    {index : Nat} (positive : 0 < index) :
    (CCL.Riemann.CoherentRoot.state track index).box.StrictInterior
      track.initial.box := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le positive
  have firstStrict :
      (CCL.Riemann.CoherentRoot.state track 1).box.StrictInterior
        track.initial.box := by
    change
      (track.refine track.initial
        (CCL.BoxedNameProcess.accuracyRadius
          (CCL.Riemann.CoherentRoot.stepTarget track 0))
        (CCL.BoxedNameProcess.accuracyRadius_pos
          (CCL.Riemann.CoherentRoot.stepTarget_positive track 0))).box.StrictInterior
        track.initial.box
    exact track.strict _ _ _
  exact firstStrict.of_refines
    (CCL.Riemann.CoherentRoot.state_refines_of_le track (by omega :
      1 ≤ 1 + extra))

/-- Two states joined through strict nesting in one winding-one owner cannot
be positively separated. -/
theorem states_not_separated_of_initial_strict
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (innerStrict : inner.initial.box.StrictInterior outer.initial.box)
    {outerIndex : Nat} (outerIndexPositive : 0 < outerIndex)
    (innerIndex : Nat) :
    ¬(CCL.Riemann.CoherentRoot.state outer outerIndex).box.Separated
      (CCL.Riemann.CoherentRoot.state inner innerIndex).box := by
  intro separated
  let polynomial :=
    CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter
  let input := CCL.Riemann.SquareRootReconditioning.isolationInput
    parameterNonzero
  let outerState := CCL.Riemann.CoherentRoot.state outer outerIndex
  let innerState := CCL.Riemann.CoherentRoot.state inner innerIndex
  have outerStrict : outerState.box.StrictInterior outer.initial.box :=
    state_strict_initial_of_pos outer outerIndexPositive
  have innerRefinesInitial : innerState.box.Refines inner.initial.box :=
    CCL.Riemann.CoherentRoot.state_refines_of_le inner (Nat.zero_le innerIndex)
  have innerStrictOuter : innerState.box.StrictInterior outer.initial.box :=
    innerStrict.of_refines innerRefinesInitial
  let outerSupported := supportedInside parameterNonzero outer.initial
    outerState outerStrict.refines
  let innerSupported := supportedInside parameterNonzero outer.initial
    innerState innerStrictOuter.refines
  have outerSupportedRefines : outerSupported.box.Refines outerState.box :=
    supportedInside_refines_inner parameterNonzero outer.initial outerState
      outerStrict.refines
  have innerSupportedRefines : innerSupported.box.Refines innerState.box :=
    supportedInside_refines_inner parameterNonzero outer.initial innerState
      innerStrictOuter.refines
  have supportedSeparated : outerSupported.box.Separated innerSupported.box :=
    separated.of_refines outerSupportedRefines innerSupportedRefines
  have outerSupportedStrict :
      outerSupported.box.StrictInterior outer.initial.box :=
    outerStrict.of_refines outerSupportedRefines
  have innerSupportedStrict :
      innerSupported.box.StrictInterior outer.initial.box :=
    innerStrictOuter.of_refines innerSupportedRefines
  let region : RFAP.ExactIsolation.ClearRegion polynomial outer.initial.box :=
    { box := outer.initial.box
      refinesAmbient := RFAP.Boxes.Box.refines_refl _
      proper := outer.initial.proper
      clearance := outer.initial.clearance }
  have atLeastEight := RFAP.Maximality.region_rawWinding_ge_eight_of_separated
    input.degreeAtLeastTwo input.squarefree input.elimination region
      outerSupported innerSupported outerSupportedStrict innerSupportedStrict
        supportedSeparated
  have exactlyFour := outer.initial.rawWindingFour
  dsimp only [region] at atLeastEight
  rw [exactlyFour] at atLeastEight
  omega

private theorem quarterRadius_index_antitone {scale : Coordinate}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius scale later ≤
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) ≤ 1 / 4 by decide)
      (show (1 / 4 : Coordinate) ≤ 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 ≤ scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier := by ring1

private theorem two_quarter_sums (target : Coordinate) :
    2 * (target / 4 + target / 4) = target := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (4 : Coordinate) ≠ 0 by decide)
  calc
    (2 * (target / 4 + target / 4)) * 4 =
        2 * ((target / 4) * 4 + (target / 4) * 4) := by ring1
    _ = 2 * (target + target) := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 4 := by ring1

/-- Strict nesting of the inner initial winding-one box in the outer one is
enough to identify the two finite root approximations operationally. -/
def approximationEquivalent_of_initial_strict
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (innerStrict : inner.initial.box.StrictInterior outer.initial.box) :
    CCL.OperationalEquivalence.Equivalent
      (CCL.Riemann.CertifiedSquareRoot.approximation outer)
      (CCL.Riemann.CertifiedSquareRoot.approximation inner) where
  compare := by
    intro outerStart innerStart target targetPositive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      RFAP.ConstructiveFraction.div_pos_direct targetPositive (by decide)
    let outerApprox := CCL.Riemann.CertifiedSquareRoot.approximation outer
    let innerApprox := CCL.Riemann.CertifiedSquareRoot.approximation inner
    let outerIndex := outerApprox.refineIndex (max outerStart 1)
      smallTarget smallPositive
    let innerIndex := innerApprox.refineIndex innerStart
      smallTarget smallPositive
    exact
      { leftIndex := outerIndex
        rightIndex := innerIndex
        left_ge := (Nat.le_max_left outerStart 1).trans
          (outerApprox.refineIndex_ge (max outerStart 1)
            smallTarget smallPositive)
        right_ge := innerApprox.refineIndex_ge innerStart
          smallTarget smallPositive
        close := by
          intro outerLater innerLater outerOrder innerOrder
          let outerRawIndex := max
            (CCL.Riemann.CertifiedSquareRoot.baseIndex outer) outerLater
          let innerRawIndex := max
            (CCL.Riemann.CertifiedSquareRoot.baseIndex inner) innerLater
          have outerIndexPositive : 0 < outerRawIndex := by
            have oneLeOuterIndex : 1 ≤ outerIndex :=
              (Nat.le_max_right outerStart 1).trans
                (outerApprox.refineIndex_ge (max outerStart 1)
                  smallTarget smallPositive)
            have oneLeLater : 1 ≤ outerLater := oneLeOuterIndex.trans outerOrder
            exact oneLeLater.trans (Nat.le_max_right _ _)
          have notSeparated := states_not_separated_of_initial_strict
            parameterNonzero outer inner innerStrict outerIndexPositive
              innerRawIndex
          let overlap := RFAP.Boxes.Box.overlapPoint
            (CCL.Riemann.CoherentRoot.state outer outerRawIndex).box
            (CCL.Riemann.CoherentRoot.state inner innerRawIndex).box
          have overlapInside :=
            RFAP.Boxes.Box.contains_overlapPoint_of_not_separated notSeparated
          have outerDistance :
              normSq
                ((CCL.Riemann.CoherentRoot.state outer outerRawIndex).box.anchor -
                  overlap) ≤
                (CCL.Riemann.CoherentRoot.state outer
                  outerRawIndex).box.diagonalSq :=
            (CCL.Riemann.CoherentRoot.state outer
              outerRawIndex).box.normSq_sub_le_diagonalSq
                (CCL.Riemann.CoherentRoot.state outer
                  outerRawIndex).box.contains_anchor overlapInside.1
          have innerDistance :
              normSq
                (overlap -
                  (CCL.Riemann.CoherentRoot.state inner
                    innerRawIndex).box.anchor) ≤
                (CCL.Riemann.CoherentRoot.state inner
                  innerRawIndex).box.diagonalSq :=
            (CCL.Riemann.CoherentRoot.state inner
              innerRawIndex).box.normSq_sub_le_diagonalSq overlapInside.2
                (CCL.Riemann.CoherentRoot.state inner
                  innerRawIndex).box.contains_anchor
          have outerRawOrder :
              max (CCL.Riemann.CertifiedSquareRoot.baseIndex outer) outerIndex ≤
                outerRawIndex := by
            exact max_le_max (Nat.le_refl _) outerOrder
          have innerRawOrder :
              max (CCL.Riemann.CertifiedSquareRoot.baseIndex inner) innerIndex ≤
                innerRawIndex := by
            exact max_le_max (Nat.le_refl _) innerOrder
          have outerDiagonalSmall :
              (CCL.Riemann.CoherentRoot.state outer
                outerRawIndex).box.diagonalSq < smallTarget := by
            calc
              (CCL.Riemann.CoherentRoot.state outer
                  outerRawIndex).box.diagonalSq ≤
                  CCL.FiniteGeometric.quarterRadius
                    (CCL.Riemann.CoherentRoot.scale outer) outerRawIndex :=
                CCL.Riemann.CoherentRoot.state_diagonal_le outer outerRawIndex
              _ ≤ CCL.FiniteGeometric.quarterRadius
                    (CCL.Riemann.CoherentRoot.scale outer)
                    (max (CCL.Riemann.CertifiedSquareRoot.baseIndex outer)
                      outerIndex) :=
                quarterRadius_index_antitone
                  (CCL.Riemann.CoherentRoot.scale_positive outer).le
                  outerRawOrder
              _ < smallTarget := by
                exact outerApprox.refineIndex_accurate
                  (max outerStart 1) smallTarget smallPositive
          have innerDiagonalSmall :
              (CCL.Riemann.CoherentRoot.state inner
                innerRawIndex).box.diagonalSq < smallTarget := by
            calc
              (CCL.Riemann.CoherentRoot.state inner
                  innerRawIndex).box.diagonalSq ≤
                  CCL.FiniteGeometric.quarterRadius
                    (CCL.Riemann.CoherentRoot.scale inner) innerRawIndex :=
                CCL.Riemann.CoherentRoot.state_diagonal_le inner innerRawIndex
              _ ≤ CCL.FiniteGeometric.quarterRadius
                    (CCL.Riemann.CoherentRoot.scale inner)
                    (max (CCL.Riemann.CertifiedSquareRoot.baseIndex inner)
                      innerIndex) :=
                quarterRadius_index_antitone
                  (CCL.Riemann.CoherentRoot.scale_positive inner).le
                  innerRawOrder
              _ < smallTarget := by
                exact innerApprox.refineIndex_accurate innerStart smallTarget
                  smallPositive
          change normSq
              ((CCL.Riemann.CoherentRoot.state outer outerRawIndex).box.anchor -
                (CCL.Riemann.CoherentRoot.state inner
                  innerRawIndex).box.anchor) < target
          calc
            normSq
                ((CCL.Riemann.CoherentRoot.state outer
                    outerRawIndex).box.anchor -
                  (CCL.Riemann.CoherentRoot.state inner
                    innerRawIndex).box.anchor) ≤
                2 * (normSq
                    ((CCL.Riemann.CoherentRoot.state outer
                      outerRawIndex).box.anchor - overlap) +
                  normSq (overlap -
                    (CCL.Riemann.CoherentRoot.state inner
                      innerRawIndex).box.anchor)) :=
              normSq_sub_le_via _ _ _
            _ ≤ 2 *
                ((CCL.Riemann.CoherentRoot.state outer
                    outerRawIndex).box.diagonalSq +
                  (CCL.Riemann.CoherentRoot.state inner
                    innerRawIndex).box.diagonalSq) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add outerDistance innerDistance) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  outerDiagonalSmall innerDiagonalSmall)
            _ = target := two_quarter_sums target }

/-- The division-ready coherent roots of strictly nested tracks are the same
operational value. -/
def rootEquivalent_of_initial_strict
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (innerStrict : inner.initial.box.StrictInterior outer.initial.box) :
    NamedEquivalent
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero outer).name
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero inner).name := by
  let outerRaw := CCL.Riemann.CertifiedSquareRoot.rawRoot outer
  let innerRaw := CCL.Riemann.CertifiedSquareRoot.rawRoot inner
  have rawEquivalent : NamedEquivalent outerRaw.name innerRaw.name :=
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (approximationEquivalent_of_initial_strict parameterNonzero outer inner
        innerStrict)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent outerRaw
        (CCL.Riemann.CertifiedSquareRoot.possibleApart parameterNonzero outer)))
    (CCL.OperationalEquivalence.NamedEquivalent.trans rawEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent innerRaw
        (CCL.Riemann.CertifiedSquareRoot.possibleApart parameterNonzero
          inner)))

/-- Forget the division-ready wrappers on two operationally equal square-root
names.  The resulting equivalence compares the original shrinking-track
approximations directly, which makes their displayed samples available for
finite owner-separation arguments. -/
def approximationEquivalent_of_rootEquivalent
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {firstAmbient secondAmbient : Box}
    (first : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      firstAmbient)
    (second : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      secondAmbient)
    (equivalent : NamedEquivalent
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero first).name
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero second).name) :
    CCL.OperationalEquivalence.Equivalent
      (CCL.Riemann.CertifiedSquareRoot.approximation first)
      (CCL.Riemann.CertifiedSquareRoot.approximation second) := by
  let firstApprox := CCL.Riemann.CertifiedSquareRoot.approximation first
  let secondApprox := CCL.Riemann.CertifiedSquareRoot.approximation second
  let firstRaw := CCL.Riemann.CertifiedSquareRoot.rawRoot first
  let secondRaw := CCL.Riemann.CertifiedSquareRoot.rawRoot second
  have firstRawToRoot : NamedEquivalent firstRaw.name
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero first).name :=
    CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent firstRaw
      (CCL.Riemann.CertifiedSquareRoot.possibleApart parameterNonzero first)
  have secondRawToRoot : NamedEquivalent secondRaw.name
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero second).name :=
    CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent secondRaw
      (CCL.Riemann.CertifiedSquareRoot.possibleApart parameterNonzero second)
  have rawEquivalent : NamedEquivalent firstRaw.name secondRaw.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans firstRawToRoot
      (CCL.OperationalEquivalence.NamedEquivalent.trans equivalent
        secondRawToRoot.symm)
  exact CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling firstApprox))
    (CCL.OperationalEquivalence.Equivalent.trans rawEquivalent
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling secondApprox))

/-- Two canonical global square-root owners with operationally equal roots
have the same finite owner index.  Distinct indices have positively separated
rational boxes, while operational equivalence produces displayed samples
closer than the computed squared separation gap. -/
theorem canonicalOwner_index_eq_of_rootEquivalent
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (firstIndex secondIndex : Fin 2)
    (equivalent : NamedEquivalent
      ((CCL.Riemann.SquareRootReconditioning.canonicalOwner parameterNonzero
        firstIndex).certificate parameterNonzero).value.name
      ((CCL.Riemann.SquareRootReconditioning.canonicalOwner parameterNonzero
        secondIndex).certificate parameterNonzero).value.name) :
    firstIndex = secondIndex := by
  by_cases equal : firstIndex = secondIndex
  · exact equal
  · let first := CCL.Riemann.SquareRootReconditioning.canonicalOwner
      parameterNonzero firstIndex
    let second := CCL.Riemann.SquareRootReconditioning.canonicalOwner
      parameterNonzero secondIndex
    have separated : first.track.initial.box.Separated
        second.track.initial.box := by
      let output := (CCL.Riemann.SquareRootReconditioning.isolationInput
        parameterNonzero).isolation
      have firstCast : output.trackIndex firstIndex = firstIndex :=
        Fin.ext (output.trackIndex_val firstIndex)
      have secondCast : output.trackIndex secondIndex = secondIndex :=
        Fin.ext (output.trackIndex_val secondIndex)
      have separatedCast := output.trackAt_pairwiseSeparated firstIndex
        secondIndex equal
      rw [show output.trackAt firstIndex = output.tracks.get
          (output.trackIndex firstIndex) from rfl,
        show output.trackAt secondIndex = output.tracks.get
          (output.trackIndex secondIndex) from rfl,
        firstCast, secondCast] at separatedCast
      exact separatedCast
    let separation := RFAP.Boxes.Box.separationCertificate separated
    let approximationEquivalent := approximationEquivalent_of_rootEquivalent
      parameterNonzero first.track second.track equivalent
    let comparison := approximationEquivalent.compare 0 0 (separation.gap ^ 2)
      (RFAP.ConstructiveFraction.pow_pos_direct separation.positive 2)
    have firstInside : first.track.initial.box.Contains
        ((CCL.Riemann.CertifiedSquareRoot.approximation first.track).sample
          comparison.leftIndex) := by
      change first.track.initial.box.Contains
        (CCL.Riemann.CoherentRoot.state first.track
          (max (CCL.Riemann.CertifiedSquareRoot.baseIndex first.track)
            comparison.leftIndex)).box.anchor
      exact (CCL.Riemann.CoherentRoot.state_refines_of_le first.track
        (Nat.zero_le _)).contains
          (CCL.Riemann.CoherentRoot.state first.track _).box.contains_anchor
    have secondInside : second.track.initial.box.Contains
        ((CCL.Riemann.CertifiedSquareRoot.approximation second.track).sample
          comparison.rightIndex) := by
      change second.track.initial.box.Contains
        (CCL.Riemann.CoherentRoot.state second.track
          (max (CCL.Riemann.CertifiedSquareRoot.baseIndex second.track)
            comparison.rightIndex)).box.anchor
      exact (CCL.Riemann.CoherentRoot.state_refines_of_le second.track
        (Nat.zero_le _)).contains
          (CCL.Riemann.CoherentRoot.state second.track _).box.contains_anchor
    have lower := separation.lower firstInside secondInside
    have close := comparison.close (Nat.le_refl comparison.leftIndex)
      (Nat.le_refl comparison.rightIndex)
    exact ((not_lt_of_ge lower) close).elim

/-- View the finite Rouché transport of one source state as a total shrinking
track for the target square-root polynomial on the unchanged source box. -/
def transportedTrack {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceTrack : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial source) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceTrack.initial.clearance.bound) :
    WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial target)
      sourceTrack.initial.box :=
  (CCL.Riemann.SquareRootContinuation.transportedOwner
      sourceTrack.initial small).track
    (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
    (CCL.PowerMonodromy.squarefree targetNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo)

@[simp] theorem transportedTrack_initial_box {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceTrack : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial source) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceTrack.initial.clearance.bound) :
    (transportedTrack targetNonzero sourceTrack small).initial.box =
      sourceTrack.initial.box := rfl

/-- Finite continuation respects a displayed common source occurrence.  A
common source track strictly inside both input owners is transported to the
same target.  The transported local winding-one owners then identify all
three target tracks by finite winding maximality. -/
def rootEquivalent_continued_of_common_source
    {source target : Gaussian} (targetNonzero : target ≠ 0)
    {firstAmbient secondAmbient commonAmbient : Box}
    (first : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial source)
      firstAmbient)
    (second : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial source)
      secondAmbient)
    (common : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial source)
      commonAmbient)
    (commonStrictFirst : common.initial.box.StrictInterior first.initial.box)
    (commonStrictSecond : common.initial.box.StrictInterior second.initial.box)
    (firstSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      first.initial.clearance.bound)
    (secondSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      second.initial.clearance.bound)
    (commonSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      common.initial.clearance.bound) :
    NamedEquivalent
      (CCL.Riemann.CertifiedSquareRoot.root targetNonzero
        (CCL.Riemann.SquareRootContinuation.continuedTrack targetNonzero
          first.initial firstSmall)).name
      (CCL.Riemann.CertifiedSquareRoot.root targetNonzero
        (CCL.Riemann.SquareRootContinuation.continuedTrack targetNonzero
          second.initial secondSmall)).name := by
  let firstTarget := CCL.Riemann.SquareRootContinuation.continuedTrack
    targetNonzero first.initial firstSmall
  let secondTarget := CCL.Riemann.SquareRootContinuation.continuedTrack
    targetNonzero second.initial secondSmall
  let commonTarget := CCL.Riemann.SquareRootContinuation.continuedTrack
    targetNonzero common.initial commonSmall
  let firstOuter := transportedTrack targetNonzero first firstSmall
  let secondOuter := transportedTrack targetNonzero second secondSmall
  have firstTargetStrict : firstTarget.initial.box.StrictInterior
      firstOuter.initial.box := by
    change firstTarget.initial.box.StrictInterior first.initial.box
    exact CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
      targetNonzero first.initial firstSmall
  have secondTargetStrict : secondTarget.initial.box.StrictInterior
      secondOuter.initial.box := by
    change secondTarget.initial.box.StrictInterior second.initial.box
    exact CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
      targetNonzero second.initial secondSmall
  have commonTargetRefines : commonTarget.initial.box.Refines
      common.initial.box :=
    CCL.Riemann.SquareRootContinuation.continuedTrack_initial_refines_source
      targetNonzero common.initial commonSmall
  have commonTargetStrictFirst : commonTarget.initial.box.StrictInterior
      firstOuter.initial.box := by
    change commonTarget.initial.box.StrictInterior first.initial.box
    exact commonStrictFirst.of_refines commonTargetRefines
  have commonTargetStrictSecond : commonTarget.initial.box.StrictInterior
      secondOuter.initial.box := by
    change commonTarget.initial.box.StrictInterior second.initial.box
    exact commonStrictSecond.of_refines commonTargetRefines
  have firstOuterToFirst := rootEquivalent_of_initial_strict targetNonzero
    firstOuter firstTarget firstTargetStrict
  have firstOuterToCommon := rootEquivalent_of_initial_strict targetNonzero
    firstOuter commonTarget commonTargetStrictFirst
  have secondOuterToSecond := rootEquivalent_of_initial_strict targetNonzero
    secondOuter secondTarget secondTargetStrict
  have secondOuterToCommon := rootEquivalent_of_initial_strict targetNonzero
    secondOuter commonTarget commonTargetStrictSecond
  exact CCL.OperationalEquivalence.NamedEquivalent.trans firstOuterToFirst.symm
    (CCL.OperationalEquivalence.NamedEquivalent.trans firstOuterToCommon
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        secondOuterToCommon.symm secondOuterToSecond))

/-- Owner-level form of continuation congruence.  The common source owner is
executable data, not an existential occurrence: its initial winding-one box
is displayed strictly inside both source owners, and its own clearance checks
the same finite parameter move. -/
def rootEquivalent_advance_of_common_source
    {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second common :
      CCL.Riemann.SquareRootContinuationChain.Owner source)
    (commonStrictFirst :
      common.track.initial.box.StrictInterior first.track.initial.box)
    (commonStrictSecond :
      common.track.initial.box.StrictInterior second.track.initial.box)
    (firstSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      first.track.initial.clearance.bound)
    (secondSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      second.track.initial.clearance.bound)
    (commonSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      common.track.initial.clearance.bound) :
    NamedEquivalent
      ((first.advance targetNonzero firstSmall).certificate
        targetNonzero).value.name
      ((second.advance targetNonzero secondSmall).certificate
        targetNonzero).value.name :=
  rootEquivalent_continued_of_common_source targetNonzero first.track
    second.track common.track commonStrictFirst commonStrictSecond firstSmall
      secondSmall commonSmall

/-- A direct Rouché move and the corresponding two-step move name the same
target occurrence whenever all three finite moves fit.  Both target tracks
are strict descendants of the target local owner transported on the original
source box, so finite winding-one uniqueness proves associativity without a
completed homotopy or path space. -/
def rootEquivalent_continued_compose
    {source middle target : Gaussian}
    (middleNonzero : middle ≠ 0) (targetNonzero : target ≠ 0)
    {sourceAmbient : Box}
    (sourceTrack : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial source)
      sourceAmbient)
    (sourceMiddleSmall : normSq (source - middle) <
      sourceTrack.initial.clearance.bound)
    (sourceTargetSmall : normSq (source - target) <
      sourceTrack.initial.clearance.bound)
    (middleTargetSmall : normSq (middle - target) <
      (CCL.Riemann.SquareRootContinuation.continuedTrack middleNonzero
        sourceTrack.initial sourceMiddleSmall).initial.clearance.bound) :
    NamedEquivalent
      (CCL.Riemann.CertifiedSquareRoot.root targetNonzero
        (CCL.Riemann.SquareRootContinuation.continuedTrack targetNonzero
          sourceTrack.initial sourceTargetSmall)).name
      (CCL.Riemann.CertifiedSquareRoot.root targetNonzero
        (CCL.Riemann.SquareRootContinuation.continuedTrack targetNonzero
          (CCL.Riemann.SquareRootContinuation.continuedTrack middleNonzero
            sourceTrack.initial sourceMiddleSmall).initial
          middleTargetSmall)).name := by
  let middleTrack := CCL.Riemann.SquareRootContinuation.continuedTrack
    middleNonzero sourceTrack.initial sourceMiddleSmall
  let directTrack := CCL.Riemann.SquareRootContinuation.continuedTrack
    targetNonzero sourceTrack.initial sourceTargetSmall
  let stagedTrack := CCL.Riemann.SquareRootContinuation.continuedTrack
    targetNonzero middleTrack.initial middleTargetSmall
  let outer := transportedTrack targetNonzero sourceTrack sourceTargetSmall
  have directStrict : directTrack.initial.box.StrictInterior
      outer.initial.box := by
    change directTrack.initial.box.StrictInterior sourceTrack.initial.box
    exact CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
      targetNonzero sourceTrack.initial sourceTargetSmall
  have middleStrict : middleTrack.initial.box.StrictInterior
      sourceTrack.initial.box :=
    CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
      middleNonzero sourceTrack.initial sourceMiddleSmall
  have stagedRefinesMiddle : stagedTrack.initial.box.Refines
      middleTrack.initial.box :=
    CCL.Riemann.SquareRootContinuation.continuedTrack_initial_refines_source
      targetNonzero middleTrack.initial middleTargetSmall
  have stagedStrict : stagedTrack.initial.box.StrictInterior
      outer.initial.box := by
    change stagedTrack.initial.box.StrictInterior sourceTrack.initial.box
    exact middleStrict.of_refines stagedRefinesMiddle
  have outerToDirect := rootEquivalent_of_initial_strict targetNonzero outer
    directTrack directStrict
  have outerToStaged := rootEquivalent_of_initial_strict targetNonzero outer
    stagedTrack stagedStrict
  exact CCL.OperationalEquivalence.NamedEquivalent.trans outerToDirect.symm
    outerToStaged

/-- Path-controlled preparation preserves the inherited square-root
occurrence.  The witness is the explicit same-sample bridge track whose
initial band is strictly inside both initial owners. -/
def rootEquivalent_robustPrepare
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment
      polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    NamedEquivalent
      (owner.certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name
      ((CCL.Riemann.RobustSquareRootPreparation.prepared
          segment parameter inside owner rootDiameter
          rootDiameterPositive).certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name := by
  let common := CCL.Riemann.RobustSquareRootPreparation.bridgeTrack
    segment parameter inside owner rootDiameter rootDiameterPositive
  let robust := CCL.Riemann.RobustSquareRootPreparation.prepared
    segment parameter inside owner rootDiameter rootDiameterPositive
  have oldToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) owner.track common
    (CCL.Riemann.RobustSquareRootPreparation.bridgeTrack_initial_strict_owner
      segment parameter inside owner rootDiameterPositive)
  have robustToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) robust.track common
    (CCL.Riemann.RobustSquareRootPreparation.bridgeTrack_initial_strict_prepared
      segment parameter inside owner rootDiameterPositive)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans oldToCommon
    (CCL.OperationalEquivalence.NamedEquivalent.symm robustToCommon)

/-- Uniform path-wide preparation preserves the inherited square-root
occurrence.  Both owners contain the explicit same-sample bridge track as a
strict descendant. -/
def rootEquivalent_uniformPrepare
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment
      polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    NamedEquivalent
      (owner.certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name
      ((CCL.Riemann.UniformSquareRootPreparation.prepared
          segment parameter inside owner rootDiameter
          rootDiameterPositive).certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name := by
  let common := CCL.Riemann.UniformSquareRootPreparation.bridgeTrack
    segment parameter inside owner rootDiameter rootDiameterPositive
  let uniform := CCL.Riemann.UniformSquareRootPreparation.prepared
    segment parameter inside owner rootDiameter rootDiameterPositive
  have oldToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) owner.track common
    (CCL.Riemann.UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
      segment parameter inside owner rootDiameterPositive)
  have uniformToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) uniform.track common
    (CCL.Riemann.UniformSquareRootPreparation.bridgeTrack_initial_strict_prepared
      segment parameter inside owner rootDiameterPositive)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans oldToCommon
    (CCL.OperationalEquivalence.NamedEquivalent.symm uniformToCommon)

/-- Quantitative owner preparation preserves the division-ready root.  This
is the analytic justification for shrinking an owner before estimating one
integration cell. -/
def rootEquivalent_prepare {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (target : Coordinate) (positive : 0 < target) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((owner.prepare target positive).certificate parameterNonzero).value.name := by
  exact rootEquivalent_of_initial_strict parameterNonzero owner.track
    (owner.prepare target positive).track
    (by
      change
        (CCL.Riemann.CoherentRoot.state owner.track
          (CCL.Riemann.SquareRootContinuationChain.Owner.preparationIndex
            owner target positive)).box.StrictInterior owner.track.initial.box
      exact state_strict_initial_of_pos owner.track
        (CCL.Riemann.SquareRootContinuationChain.Owner.preparationIndex_positive
          owner target positive))

/-- The explicit-clearance preparation names the same square-root occurrence
as its outer owner.  Its strictly nested Newton square is enough for the
finite winding-one uniqueness argument. -/
def rootEquivalent_quantitativePrepare {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (target : Coordinate) (positive : 0 < target) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((owner.quantitativePrepare parameterNonzero target positive).certificate
        parameterNonzero).value.name := by
  exact rootEquivalent_of_initial_strict parameterNonzero owner.track
    (owner.quantitativePrepare parameterNonzero target positive).track
    (owner.quantitativePrepare_initial_strict parameterNonzero target positive)

/-- A zero-parameter continuation step retains the same operational root.
The freshly extracted winding-one box is strictly inside the source owner,
so the conclusion follows from finite winding-one uniqueness. -/
def rootEquivalent_advance_same {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (small : normSq (parameter - parameter) <
      owner.track.initial.clearance.bound) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((owner.advance parameterNonzero small).certificate
        parameterNonzero).value.name := by
  exact rootEquivalent_of_initial_strict parameterNonzero owner.track
    (owner.advance parameterNonzero small).track
    (CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
      parameterNonzero owner.track.initial small)

/-- Restart a track at one of its explicitly computed descendant states. -/
def restart {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (initial : WindingOneState polynomial ambient) :
    WindingOneTrack polynomial ambient where
  initial := initial
  refine := track.refine
  nested := track.nested
  strict := track.strict
  accurate := track.accurate

/-- A common track whose initial state is inside an old owner and whose one
displayed refinement is inside a fresh owner identifies the old and fresh
division-ready roots.  `SquareRootReconditioning.Bridge` supplies exactly
these five finite pieces of data. -/
def rootEquivalent_of_common_bridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {oldAmbient commonAmbient freshAmbient : Box}
    (old : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      oldAmbient)
    (common : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      commonAmbient)
    (fresh : WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      freshAmbient)
    (commonStrictOld : common.initial.box.StrictInterior old.initial.box)
    (refinementRadius : Coordinate) (refinementPositive : 0 < refinementRadius)
    (refined : WindingOneState
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      commonAmbient)
    (refined_eq : refined = common.refine common.initial refinementRadius
      refinementPositive)
    (refinedStrictFresh : refined.box.StrictInterior fresh.initial.box) :
    NamedEquivalent
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero old).name
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero fresh).name := by
  let commonTail := restart common refined
  have commonTailStrictCommon :
      commonTail.initial.box.StrictInterior common.initial.box := by
    rw [show commonTail.initial = refined from rfl, refined_eq]
    exact common.strict _ _ _
  have oldToCommon := rootEquivalent_of_initial_strict parameterNonzero
    old common commonStrictOld
  have commonToTail := rootEquivalent_of_initial_strict parameterNonzero
    common commonTail commonTailStrictCommon
  have freshToTail := rootEquivalent_of_initial_strict parameterNonzero
    fresh commonTail refinedStrictFresh
  exact CCL.OperationalEquivalence.NamedEquivalent.trans oldToCommon
    (CCL.OperationalEquivalence.NamedEquivalent.trans commonToTail
      (CCL.OperationalEquivalence.NamedEquivalent.symm freshToTail))

/-- Any displayed reconditioning bridge identifies its source owner with the
fresh global owner named by that bridge. -/
def rootEquivalent_of_bridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((CCL.Riemann.SquareRootReconditioning.freshOwner parameterNonzero
        owner).certificate parameterNonzero).value.name := by
  exact rootEquivalent_of_common_bridge parameterNonzero owner.track
    reset.common
    (CCL.Riemann.SquareRootReconditioning.freshOwner parameterNonzero
      owner).track
    reset.commonInitialStrictOwner reset.refinementRadius
    reset.refinementRadiusPositive reset.refined reset.refined_eq
    reset.refinedStrictFresh

/-- Restart the reconditioning bridge at its displayed refinement.  This is a
single executable winding-one track strictly inside both the source owner and
the canonical fresh owner. -/
def commonTailOfBridge {parameter : Gaussian}
    {parameterNonzero : parameter ≠ 0}
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter}
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    WindingOneTrack
      (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
      (RFAP.GlobalWinding.largeSquareBox
        (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)) :=
  restart reset.common reset.refined

/-- Package the common bridge tail with its displayed parameter. -/
def commonOwnerOfBridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter}
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge parameterNonzero
      owner) : CCL.Riemann.SquareRootContinuationChain.Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := RFAP.GlobalWinding.largeSquareBox
    (CCL.Riemann.SquareRootReconditioning.rootPolynomial parameter)
  track := commonTailOfBridge reset

@[simp] theorem commonOwnerOfBridge_track {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter}
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    (commonOwnerOfBridge parameterNonzero reset).track =
      commonTailOfBridge reset := rfl

theorem commonTailOfBridge_initial_strict_owner {parameter : Gaussian}
    {parameterNonzero : parameter ≠ 0}
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter}
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    (commonTailOfBridge reset).initial.box.StrictInterior
      owner.track.initial.box := by
  apply reset.commonInitialStrictOwner.of_refines
  change reset.refined.box.Refines reset.common.initial.box
  rw [reset.refined_eq]
  exact (reset.common.strict _ _ _).refines

theorem commonTailOfBridge_initial_strict_fresh {parameter : Gaussian}
    {parameterNonzero : parameter ≠ 0}
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter}
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    (commonTailOfBridge reset).initial.box.StrictInterior
      (CCL.Riemann.SquareRootReconditioning.freshOwner parameterNonzero
        owner).track.initial.box := by
  exact reset.refinedStrictFresh

/-- Reconditioning is extensional on a square-root occurrence.  Operationally
equal source roots are assigned to the same one of the two finite canonical
owners; equality follows from the positive separation of distinct owners. -/
theorem freshOwner_eq_of_rootEquivalent {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (first second :
      CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (equivalent : NamedEquivalent
      (first.certificate parameterNonzero).value.name
      (second.certificate parameterNonzero).value.name) :
    CCL.Riemann.SquareRootReconditioning.freshOwner parameterNonzero first =
      CCL.Riemann.SquareRootReconditioning.freshOwner parameterNonzero
        second := by
  let firstReset := CCL.Riemann.SquareRootReconditioning.bridge
    parameterNonzero first
  let secondReset := CCL.Riemann.SquareRootReconditioning.bridge
    parameterNonzero second
  have firstToFresh := rootEquivalent_of_bridge parameterNonzero first
    firstReset
  have secondToFresh := rootEquivalent_of_bridge parameterNonzero second
    secondReset
  have freshEquivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
    firstToFresh.symm
      (CCL.OperationalEquivalence.NamedEquivalent.trans equivalent
        secondToFresh)
  let firstIndex : Fin 2 :=
    (CCL.Riemann.SquareRootReconditioning.assignment parameterNonzero
      first).owner.owner
  let secondIndex : Fin 2 :=
    (CCL.Riemann.SquareRootReconditioning.assignment parameterNonzero
      second).owner.owner
  have indexEqual : firstIndex = secondIndex :=
    canonicalOwner_index_eq_of_rootEquivalent parameterNonzero firstIndex
      secondIndex (by
        simpa only [firstIndex, secondIndex,
          CCL.Riemann.SquareRootReconditioning.freshOwner_eq_canonicalOwner]
          using freshEquivalent)
  rw [CCL.Riemann.SquareRootReconditioning.freshOwner_eq_canonicalOwner,
    CCL.Riemann.SquareRootReconditioning.freshOwner_eq_canonicalOwner]
  exact congrArg
    (CCL.Riemann.SquareRootReconditioning.canonicalOwner parameterNonzero)
    indexEqual

/-- Clearance of the canonical source owner used to synchronize two
operational presentations before a congruent move. -/
abbrev freshSourceClearance {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner source) :
    Coordinate :=
  (CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero owner).track
    |>.initial.clearance.bound

/-- Clearance of the explicit common tail joining an owner to its canonical
reconditioning. -/
abbrev bridgeTailClearance {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner source) :
    Coordinate :=
  (commonTailOfBridge
    (CCL.Riemann.SquareRootReconditioning.bridge sourceNonzero owner)).initial
      |>.clearance.bound

/-- Clearance after one strict refinement of the first canonical owner.  This
track is the common source for the two equal canonical presentations. -/
abbrev freshCommonClearance {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner source) :
    Coordinate :=
  ((CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero owner).refineAt
      1).track.initial.clearance.bound

/-- The complete finite rational mesh condition for one congruent square-root
continuation move. -/
structure ContinuationCongruenceSmall {source : Gaussian}
    (sourceNonzero : source ≠ 0)
    (first second : CCL.Riemann.SquareRootContinuationChain.Owner source)
    (target : Gaussian) : Prop where
  firstSmall : normSq (source - target) < first.track.initial.clearance.bound
  secondSmall : normSq (source - target) < second.track.initial.clearance.bound
  firstFresh : normSq (source - target) <
    freshSourceClearance sourceNonzero first
  secondFresh : normSq (source - target) <
    freshSourceClearance sourceNonzero second
  firstBridge : normSq (source - target) <
    bridgeTailClearance sourceNonzero first
  secondBridge : normSq (source - target) <
    bridgeTailClearance sourceNonzero second
  freshCommon : normSq (source - target) <
    freshCommonClearance sourceNonzero first

instance continuationCongruenceSmallDecidable {source : Gaussian}
    (sourceNonzero : source ≠ 0)
    (first second : CCL.Riemann.SquareRootContinuationChain.Owner source)
    (target : Gaussian) :
    Decidable (ContinuationCongruenceSmall sourceNonzero first second target) := by
  by_cases firstSmall : normSq (source - target) <
      first.track.initial.clearance.bound
  · by_cases secondSmall : normSq (source - target) <
        second.track.initial.clearance.bound
    · by_cases firstFresh : normSq (source - target) <
          freshSourceClearance sourceNonzero first
      · by_cases secondFresh : normSq (source - target) <
            freshSourceClearance sourceNonzero second
        · by_cases firstBridge : normSq (source - target) <
              bridgeTailClearance sourceNonzero first
          · by_cases secondBridge : normSq (source - target) <
                bridgeTailClearance sourceNonzero second
            · by_cases freshCommon : normSq (source - target) <
                  freshCommonClearance sourceNonzero first
              · exact isTrue
                  { firstSmall := firstSmall
                    secondSmall := secondSmall
                    firstFresh := firstFresh
                    secondFresh := secondFresh
                    firstBridge := firstBridge
                    secondBridge := secondBridge
                    freshCommon := freshCommon }
              · exact isFalse (fun small => freshCommon small.freshCommon)
            · exact isFalse (fun small => secondBridge small.secondBridge)
          · exact isFalse (fun small => firstBridge small.firstBridge)
        · exact isFalse (fun small => secondFresh small.secondFresh)
      · exact isFalse (fun small => firstFresh small.firstFresh)
    · exact isFalse (fun small => secondSmall small.secondSmall)
  · exact isFalse (fun small => firstSmall small.firstSmall)

/-- Productive target root obtained by one displayed Rouché move.  Naming
this expression keeps dependent continuation proofs small at public theorem
boundaries. -/
def continuedRootName {source target : Gaussian}
    (targetNonzero : target ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner source)
    (small : normSq (source - target) <
      owner.track.initial.clearance.bound) : CCL.ProgressiveTransducer.Named :=
  (CCL.Riemann.CertifiedSquareRoot.root targetNonzero
    (CCL.Riemann.SquareRootContinuation.continuedTrack targetNonzero
      owner.track.initial small)).name

/-- Division-ready root name carried by one owner. -/
def ownerRootName {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner source) :
    CCL.ProgressiveTransducer.Named :=
  (owner.certificate sourceNonzero).value.name

/-- Compare one continued owner with the continuation from the fresh owner
named by a supplied reconditioning bridge. -/
def rootEquivalent_continued_to_bridgeFresh
    {source target : Gaussian} {sourceNonzero : source ≠ 0}
    (targetNonzero : target ≠ 0)
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner source}
    (reset : CCL.Riemann.SquareRootReconditioning.Bridge sourceNonzero owner)
    (ownerSmall : normSq (source - target) <
      owner.track.initial.clearance.bound)
    (freshSmall : normSq (source - target) <
      (CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero
        owner).track.initial.clearance.bound)
    (bridgeSmall : normSq (source - target) <
      (commonTailOfBridge reset).initial.clearance.bound) :
    NamedEquivalent
      (continuedRootName targetNonzero owner ownerSmall)
      (continuedRootName targetNonzero
        (CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero owner)
        freshSmall) := by
  exact rootEquivalent_continued_of_common_source targetNonzero owner.track
    (CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero owner).track
      (commonTailOfBridge reset)
      (commonTailOfBridge_initial_strict_owner reset)
      (commonTailOfBridge_initial_strict_fresh reset)
      ownerSmall freshSmall bridgeSmall

/-- Continuations from two equal owner records agree.  One strict refinement
of the first record is a displayed common source track for the move. -/
def rootEquivalent_continued_of_owner_eq
    {source target : Gaussian}
    (targetNonzero : target ≠ 0)
    (first second : CCL.Riemann.SquareRootContinuationChain.Owner source)
    (equal : first = second)
    (firstSmall : normSq (source - target) <
      first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) <
      second.track.initial.clearance.bound)
    (commonSmall : normSq (source - target) <
      (first.refineAt 1).track.initial.clearance.bound) :
    NamedEquivalent
      (continuedRootName targetNonzero first firstSmall)
      (continuedRootName targetNonzero second secondSmall) := by
  have commonStrictFirst : (first.refineAt 1).track.initial.box.StrictInterior
      first.track.initial.box := by
    change (CCL.Riemann.CoherentRoot.state first.track 1).box.StrictInterior
      first.track.initial.box
    exact state_strict_initial_of_pos first.track (by decide)
  have commonStrictSecond : (first.refineAt 1).track.initial.box.StrictInterior
      second.track.initial.box := by
    rw [← equal]
    exact commonStrictFirst
  exact rootEquivalent_continued_of_common_source targetNonzero
    first.track second.track (first.refineAt 1).track commonStrictFirst
      commonStrictSecond firstSmall secondSmall commonSmall

/-- One-step continuation is congruent for operationally equal source roots
once the finite move is checked against the two source owners, their canonical
reconditionings, and three displayed common tails.  These finite positive
clearances form an executable mesh condition for recursive path comparison. -/
def rootEquivalent_continued_of_rootEquivalent
    {source target : Gaussian} (sourceNonzero : source ≠ 0)
    (targetNonzero : target ≠ 0)
    (first second : CCL.Riemann.SquareRootContinuationChain.Owner source)
    (sourceEquivalent : NamedEquivalent
      (ownerRootName sourceNonzero first)
      (ownerRootName sourceNonzero second))
    (small : ContinuationCongruenceSmall sourceNonzero first second target) :
    NamedEquivalent
      (continuedRootName targetNonzero first small.firstSmall)
      (continuedRootName targetNonzero second small.secondSmall) := by
  have firstToFresh := rootEquivalent_continued_to_bridgeFresh targetNonzero
    (CCL.Riemann.SquareRootReconditioning.bridge sourceNonzero first)
      small.firstSmall small.firstFresh small.firstBridge
  have freshEqual := freshOwner_eq_of_rootEquivalent sourceNonzero first second
    sourceEquivalent
  have freshToFresh := rootEquivalent_continued_of_owner_eq targetNonzero
    (CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero first)
    (CCL.Riemann.SquareRootReconditioning.freshOwner sourceNonzero second)
      freshEqual small.firstFresh small.secondFresh small.freshCommon
  have secondToFresh := rootEquivalent_continued_to_bridgeFresh targetNonzero
    (CCL.Riemann.SquareRootReconditioning.bridge sourceNonzero second)
      small.secondSmall small.secondFresh small.secondBridge
  exact CCL.OperationalEquivalence.NamedEquivalent.trans firstToFresh
    (CCL.OperationalEquivalence.NamedEquivalent.trans freshToFresh
      secondToFresh.symm)

end CCL.Riemann.SquareRootTrackEquivalence

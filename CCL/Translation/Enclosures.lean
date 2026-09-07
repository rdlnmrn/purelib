import CCL.Translation.Finite
import CCL.Arithmetic.BoxedNames
import CCL.Progressive.Approximation

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace CCL.FiniteTranslation

abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev Box := RFAP.Boxes.Box
abbrev Certificate := CCL.BoxedNames.Certificate
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Process := CCL.ProgressiveEnclosures.Process

open RFAP.ConstructiveGaussian.Gaussian

namespace Ball

/-- Pointwise refinement is the honest order on isolated balls: every reading
of the inner ball is also a reading of the outer ball. -/
def Refines (inner outer : Ball) : Prop :=
  ∀ {value : Gaussian}, inner.Contains value → outer.Contains value

theorem refines_refl (ball : Ball) : Refines ball ball :=
  fun inside => inside

theorem refines_trans {inner middle outer : Ball}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer :=
  fun inside => middleOuter (innerMiddle inside)

/-- Two readings of one squared-radius ball are within four times its native
squared error.  No square root or completed metric point is used. -/
theorem normSq_sub_le_four_radiusSq {ball : Ball} {left right : Gaussian}
    (leftInside : ball.Contains left) (rightInside : ball.Contains right) :
    normSq (left - right) ≤ 4 * ball.radiusSq := by
  have centerRight : normSq (ball.center - right) ≤ ball.radiusSq := by
    have identity : ball.center - right = -(right - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [identity, normSq_neg]
    exact rightInside
  calc
    normSq (left - right) ≤
        2 * (normSq (left - ball.center) +
          normSq (ball.center - right)) :=
      normSq_sub_le_via left ball.center right
    _ ≤ 2 * (ball.radiusSq + ball.radiusSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftInside centerRight) (by decide)
    _ = 4 * ball.radiusSq := by ring1

end Ball

/-- Closed Gaussian-rational balls, using their stored squared radius as the
native precision gauge. -/
def ballRepresentation : FiniteRepresentation where
  Observation := Ball
  Possible ball value := ball.Contains value
  witness ball := ball.center
  witness_possible ball := ball.contains_center
  Refines := Ball.Refines
  refines_refl := Ball.refines_refl
  refines_trans := Ball.refines_trans
  possible_persists refines possible := refines possible
  precisionSq ball := ball.radiusSq
  precisionSq_nonneg ball := ball.radiusSq_nonneg
  boundary := .closed

/-- Closed axis-aligned rational boxes, measured from their fixed lower-left
anchor by the squared diagonal. -/
def boxRepresentation : FiniteRepresentation where
  Observation := Box
  Possible box value := box.Contains value
  witness box := box.anchor
  witness_possible box := box.contains_anchor
  Refines inner outer := inner.Refines outer
  refines_refl := RFAP.Boxes.Box.refines_refl
  refines_trans innerMiddle middleOuter := innerMiddle.trans middleOuter
  possible_persists refines possible := refines.contains possible
  precisionSq box := box.diagonalSq
  precisionSq_nonneg box := box.diagonalSq_nonneg
  boundary := .closed

/-- A boxed raw CCL prefix retains both its ordinary syntax and its finite
nonzero enclosure sidecar. -/
def boxedPrefixRepresentation : FiniteRepresentation where
  Observation := Certificate
  Possible certificate value := certificate.Possible value
  witness certificate := certificate.witness
  witness_possible certificate :=
    ⟨certificate.witness_nonzero, certificate.witness_represented⟩
  Refines inner outer := CCL.BoxedNames.Refines inner outer
  refines_refl := CCL.BoxedNames.Refines.refl
  refines_trans innerMiddle middleOuter := innerMiddle.trans middleOuter
  possible_persists refines possible := refines.possible_persists possible
  precisionSq certificate := certificate.box.diagonalSq
  precisionSq_nonneg certificate := certificate.box.diagonalSq_nonneg
  boundary := .projective

/-- Forget the rectangular geometry of a box while retaining a sound closed
ball.  The native squared gauge is unchanged exactly. -/
def boxToBall : ObservationMap boxRepresentation ballRepresentation where
  map box := CCL.ArithmeticEnclosures.Ball.ofBox box
  covers possible := CCL.ArithmeticEnclosures.Ball.contains_ofBox possible
  coherent := by
    intro inner outer refines
    refine ⟨inner.anchor, ?_, ?_⟩
    · exact CCL.ArithmeticEnclosures.Ball.contains_ofBox
        inner.contains_anchor
    · exact CCL.ArithmeticEnclosures.Ball.contains_ofBox
        (refines.contains inner.contains_anchor)
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by
    simp [ballRepresentation, boxRepresentation,
      CCL.ArithmeticEnclosures.Ball.ofBox]
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 1 }
  costBound _ := 1
  cost_le _ := Nat.le_refl 1

/-- The direct boxed-prefix-to-ball observation map.  It does not claim a
reverse conversion of an arbitrary isolated ball into one raw prefix. -/
def boxedPrefixToBall :
    ObservationMap boxedPrefixRepresentation ballRepresentation where
  map certificate := CCL.ArithmeticEnclosures.Ball.ofBox certificate.box
  covers possible :=
    CCL.ArithmeticEnclosures.Ball.contains_ofBox
      (CCL.BoxedNames.Certificate.possible_inside possible)
  coherent := by
    intro inner outer refines
    refine ⟨inner.box.anchor, ?_, ?_⟩
    · exact CCL.ArithmeticEnclosures.Ball.contains_ofBox
        inner.box.contains_anchor
    · exact CCL.ArithmeticEnclosures.Ball.contains_ofBox
        (refines.box.contains inner.box.contains_anchor)
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by
    simp [boxedPrefixRepresentation, ballRepresentation,
      CCL.ArithmeticEnclosures.Ball.ofBox]
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 1 }
  costBound _ := 1
  cost_le _ := Nat.le_refl 1

/-- Finite indices of one fast-Cauchy approximation.  Later indices refine
earlier ones because their explicitly witnessed tails are smaller. -/
def approximationRepresentation (approximation : Approximation) :
    FiniteRepresentation where
  Observation := Nat
  Possible index value := approximation.Possible index value
  witness index := approximation.sample index
  witness_possible index := approximation.sample_possible index
  Refines inner outer := outer ≤ inner
  refines_refl _ := Nat.le_refl _
  refines_trans innerMiddle middleOuter := middleOuter.trans innerMiddle
  possible_persists refines possible :=
    approximation.possible_persists refines possible
  precisionSq index := approximation.radiusSq index
  precisionSq_nonneg index := approximation.radiusSq_nonneg index
  boundary := .closed

/-- States of a progressive process ordered by direct candidate-predicate
inclusion.  This deliberately avoids inventing a global reachability relation
between heterogeneous state types. -/
def processRepresentation (process : Process) : FiniteRepresentation where
  Observation := process.State
  Possible state value := process.Possible state value
  witness state := (process.witness state).val
  witness_possible state := (process.witness state).property
  Refines inner outer := ∀ {value : Gaussian},
    process.Possible inner value → process.Possible outer value
  refines_refl := by
    intro state value possible
    exact possible
  refines_trans := by
    intro inner middle outer innerMiddle middleOuter value possible
    exact middleOuter (innerMiddle possible)
  possible_persists refines possible := refines possible
  precisionSq state := (process.ball state).radiusSq
  precisionSq_nonneg state := (process.ball state).radiusSq_nonneg
  boundary := .closed

/-- One arbitrary-precision process request realized as a rational ball.  The
reverse reading relation records the explicit four-radius estimate between an
arbitrary point of the output ball and the process's displayed witness. -/
def processToBall (process : Process) :
    FiniteRealizer (processRepresentation process) ballRepresentation where
  translate state request := by
    let refined := process.refine state request.targetSq request.positive
    let output := process.ball refined
    exact
      { source' := refined
        output := output
        source_refines := by
          intro value possible
          exact process.refine_persists state request.targetSq
            request.positive possible
        relates := fun sourceValue targetValue =>
          normSq (targetValue - sourceValue) ≤ 4 * output.radiusSq
        source_to_target := by
          intro sourceValue possible
          refine ⟨sourceValue, process.possible_inside possible, ?_⟩
          rw [sub_self, normSq_zero]
          exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            output.radiusSq_nonneg
        target_to_source := by
          intro targetValue targetPossible
          let sourceValue := (process.witness refined).val
          refine ⟨sourceValue, (process.witness refined).property, ?_⟩
          exact Ball.normSq_sub_le_four_radiusSq targetPossible
            (process.possible_inside (process.witness refined).property)
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change (process.ball refined).radiusSq < request.targetSq + 0
          calc
            (process.ball refined).radiusSq < request.targetSq :=
              process.accurate state request.targetSq request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := 1
            emittedUnits := 0
            arithmeticSteps := 0 }
        costBound := 1
        cost_le := Nat.le_refl 1 }

/-- A finite fast-Cauchy random-access query is a specialization of the
process-to-ball realizer.  Its source schedule consists of exactly one call to
the displayed `refineIndex` modulus. -/
def approximationToBall (approximation : Approximation) :
    FiniteRealizer (approximationRepresentation approximation)
      ballRepresentation where
  translate index request := by
    let refined := approximation.refineIndex index request.targetSq
      request.positive
    let output : Ball :=
      { center := approximation.sample refined
        radiusSq := approximation.radiusSq refined
        radiusSq_nonneg := approximation.radiusSq_nonneg refined }
    exact
      { source' := refined
        output := output
        source_refines := approximation.refineIndex_ge index
          request.targetSq request.positive
        relates := fun sourceValue targetValue =>
          normSq (targetValue - sourceValue) ≤ 4 * output.radiusSq
        source_to_target := by
          intro sourceValue possible
          refine ⟨sourceValue, approximation.possible_inside possible, ?_⟩
          rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
          exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            output.radiusSq_nonneg
        target_to_source := by
          intro targetValue targetPossible
          refine ⟨approximation.sample refined,
            approximation.sample_possible refined, ?_⟩
          exact Ball.normSq_sub_le_four_radiusSq targetPossible
            (approximation.possible_inside
              (approximation.sample_possible refined))
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change approximation.radiusSq refined < request.targetSq + 0
          calc
            approximation.radiusSq refined < request.targetSq :=
              approximation.refineIndex_accurate index request.targetSq
                request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := 1
            emittedUnits := 0
            arithmeticSteps := 0 }
        costBound := 1
        cost_le := Nat.le_refl 1 }

end CCL.FiniteTranslation

import CCL.Bridge.Box
import CCL.Progressive.Coherence

/-!
# Coherent names from deterministic shrinking root tracks

The raw box bridge exposes a productive arithmetic cursor, but its process
state type also contains unrelated winding boxes.  Here we instead follow one
explicit recursive refinement chain.  Its anchors form a finite progressive
approximation because every later box refines every earlier box and its
diagonal is bounded by an explicit quarter-geometric allowance.  This yields
a genuine coherent CCL name without selecting a completed root.
-/

namespace CCL.Riemann.CoherentRoot

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

/-- The initial squared diagonal is a positive finite scale. -/
def scale {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Coordinate :=
  track.initial.box.diagonalSq

theorem scale_positive {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : 0 < scale track := by
  have widthPositive : 0 < track.initial.box.widthX :=
    RFAP.ConstructiveFraction.sub_pos_direct track.initial.proper.1
  have widthSquarePositive : 0 < track.initial.box.widthX ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct widthPositive 2
  have heightSquareNonnegative :
      0 <= track.initial.box.widthY ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  constructor
  · have sumNonnegative :=
      RFAP.ConstructiveFraction.add_le_add_direct
        (RFAP.ConstructiveFraction.le_of_lt_direct widthSquarePositive)
        heightSquareNonnegative
    have zeroIdentity : (0 : Coordinate) + 0 = 0 := by ring1
    rwa [zeroIdentity] at sumNonnegative
  · intro sumNonpositive
    apply widthSquarePositive.2
    have widthLeSum :=
      RFAP.ConstructiveFraction.add_le_add_direct (first :=
          track.initial.box.widthX ^ 2)
        (second := track.initial.box.widthX ^ 2) (third := 0)
        (fourth := track.initial.box.widthY ^ 2) le_rfl
        heightSquareNonnegative
    have widthIdentity :
        track.initial.box.widthX ^ 2 + (0 : Coordinate) =
          track.initial.box.widthX ^ 2 := by ring1
    rw [widthIdentity] at widthLeSum
    exact RFAP.ConstructiveFraction.le_trans
      (track.initial.box.widthX ^ 2)
      (track.initial.box.widthX ^ 2 + track.initial.box.widthY ^ 2) 0
      widthLeSum sumNonpositive

/-- The positive target assigned to the next recursive refinement. -/
def stepTarget {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius (scale track) (index + 1)

theorem stepTarget_positive {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    0 < stepTarget track index :=
  CCL.FiniteGeometric.quarterRadius_pos (scale_positive track) (index + 1)

/-- One explicit nested sequence of winding states. -/
def state {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Nat ->
      WindingOneState polynomial ambient
  | 0 => track.initial
  | index + 1 =>
      track.refine (state track index)
        (CCL.BoxedNameProcess.accuracyRadius (stepTarget track index))
        (CCL.BoxedNameProcess.accuracyRadius_pos
          (stepTarget_positive track index))

theorem state_succ_refines {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    (state track (index + 1)).box.Refines (state track index).box := by
  exact track.nested (state track index)
    (CCL.BoxedNameProcess.accuracyRadius (stepTarget track index))
    (CCL.BoxedNameProcess.accuracyRadius_pos
      (stepTarget_positive track index))

theorem state_refines_of_le {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) {earlier later : Nat}
    (order : earlier <= later) :
    (state track later).box.Refines (state track earlier).box := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  clear order
  induction extra with
  | zero =>
      simpa only [Nat.add_zero] using
        RFAP.Boxes.Box.refines_refl (state track earlier).box
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact (state_succ_refines track (earlier + extra)).trans
        inductionHypothesis

theorem state_diagonal_le {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    (state track index).box.diagonalSq <=
      CCL.FiniteGeometric.quarterRadius (scale track) index := by
  cases index with
  | zero =>
      change track.initial.box.diagonalSq <=
        CCL.FiniteGeometric.quarterRadius track.initial.box.diagonalSq 0
      unfold CCL.FiniteGeometric.quarterRadius
      rw [pow_zero]
      have divideOne : track.initial.box.diagonalSq / 1 =
          track.initial.box.diagonalSq := by
        apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
          (show (1 : Coordinate) ≠ 0 by decide)
        calc
          (track.initial.box.diagonalSq / 1) * 1 =
              track.initial.box.diagonalSq :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 1 (by decide)
          _ = track.initial.box.diagonalSq * 1 :=
            (RFAP.ConstructiveFraction.mul_one_direct _).symm
      rw [divideOne]
  | succ index =>
      have accurate := track.accurate (state track index)
        (CCL.BoxedNameProcess.accuracyRadius (stepTarget track index))
        (CCL.BoxedNameProcess.accuracyRadius_pos
          (stepTarget_positive track index))
      have targetBound := CCL.BoxedNameProcess.accuracyRadius_sq_lt
        (stepTarget_positive track index)
      exact accurate.trans targetBound.le

/-- The anchor sequence with its explicit geometric squared-error modulus. -/
def approximation {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Approximation where
  sample := fun index => (state track index).box.anchor
  radiusSq := fun index =>
    CCL.FiniteGeometric.quarterRadius (scale track) index
  radiusSq_nonneg := fun index =>
    CCL.FiniteGeometric.quarterRadius_nonneg
      (scale_positive track).le index
  later_close := by
    intro earlier later order
    exact ((state track earlier).box.normSq_sub_le_diagonalSq
      ((state_refines_of_le track order).contains
        (state track later).box.contains_anchor)
      (state track earlier).box.contains_anchor).trans
        (state_diagonal_le track earlier)
  refineIndex := fun current target _ =>
    CCL.FiniteGeometric.firstQuarterBelow (scale track) current target
  refineIndex_ge := fun current target _ =>
    CCL.FiniteGeometric.firstQuarterBelow_ge (scale track) current target
  refineIndex_accurate := fun current target positive =>
    CCL.FiniteGeometric.firstQuarterBelow_accurate (scale track)
      (scale_positive track).le current target positive
  centerBound := ambient.normSqBound
  centerBound_nonneg := ambient.normSqBound_nonneg
  sample_bounded := by
    intro index
    exact ambient.normSq_le_normSqBound
      ((state track index).refinesAmbient.contains
        (state track index).box.contains_anchor)

/-- A coherent arithmetic CCL name for the one deterministic root track. -/
def named {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    (approximation track)

/-- Every finite sample is the anchor of the correspondingly indexed nested
winding box. -/
@[simp] theorem approximation_sample {polynomial : GaussianPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (index : Nat) :
    (approximation track).sample index = (state track index).box.anchor := rfl

/-- Every finite state retains winding one, hence represents the same local
root occurrence throughout the deterministic chain. -/
theorem state_winding {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    RFAP.Winding.quadrupledBoxWinding polynomial (state track index).box = 4 :=
  (state track index).rawWindingFour

/-- Coefficient-computed scale for the polynomial residual along the anchor
approximation. -/
def residualScale (polynomial : GaussianPolynomial) (ambient : Box)
    (track : WindingOneTrack polynomial ambient) : Coordinate :=
  RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient * scale track

theorem residualScale_nonneg (polynomial : GaussianPolynomial) (ambient : Box)
    (track : WindingOneTrack polynomial ambient) :
    0 <= residualScale polynomial ambient track :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.PolynomialBounds.denseLipschitzBound_pos polynomial ambient).le
    (scale_positive track).le

/-- At every finite index the displayed rational sample satisfies the
polynomial equation up to an explicit geometrically shrinking residual. -/
theorem sample_residual_le {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval ((approximation track).sample index)) <=
      CCL.FiniteGeometric.quarterRadius
        (residualScale polynomial ambient track) index := by
  have residual :=
    RFAP.LocalExtraction.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      polynomial degreePositive (state track index).refinesAmbient
      (state track index).proper (by
        rw [(state track index).rawWindingFour]
        decide)
  have scaledDiagonal :
      RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
          (state track index).box.diagonalSq <=
        RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
          CCL.FiniteGeometric.quarterRadius (scale track) index :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (state_diagonal_le track index)
      (RFAP.PolynomialBounds.denseLipschitzBound_pos
        polynomial ambient).le
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval ((approximation track).sample index)) <=
        RFAP.LocalExtraction.anchorResidualBound polynomial ambient
          (state track index).box := residual
    _ <= RFAP.PolynomialBounds.denseLipschitzBound polynomial ambient *
          CCL.FiniteGeometric.quarterRadius (scale track) index :=
      scaledDiagonal
    _ = CCL.FiniteGeometric.quarterRadius
          (residualScale polynomial ambient track) index := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      unfold residualScale
      ring1

/-- Pack the coherent root name together with the finite equation certificate
that witnesses its shrinking polynomial residual. -/
structure CertifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) where
  value : CoherentNamed
  value_eq : value = named track
  degreePositive : 0 < polynomial.natDegree
  residual : forall index,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval ((approximation track).sample index)) <=
      CCL.FiniteGeometric.quarterRadius
        (residualScale polynomial ambient track) index

def certifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree) : CertifiedName track where
  value := named track
  value_eq := rfl
  degreePositive := degreePositive
  residual := sample_residual_le track degreePositive

end CCL.Riemann.CoherentRoot

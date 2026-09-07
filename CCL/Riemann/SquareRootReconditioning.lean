import CCL.Riemann.SquareRootContinuationChain
import RFAP.Geometry.GlobalResidual

/-!
# Finite square-root owner reconditioning

A Rouché move preserves the root occurrence, but its freshly extracted box
refines the preceding box.  Iterating only that operation would eventually
trap a long continuation in its first box.  This module supplies the missing
finite reconditioning step.  It takes a sufficiently accurate rational sample
from the continued track, globally assigns a tiny winding-one box around that
sample to one of the two independently isolated target owners, and proves that
the tiny box is still strictly inside the continued owner.

Thus the result contains a displayed common descendant of the old owner and a
fresh global owner.  No root is selected in a completed field, and the entire
assignment is computed from finite residual and box certificates.
-/

namespace CCL.Riemann.SquareRootReconditioning

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian

/-- The degree-two power polynomial at the displayed target parameter. -/
def rootPolynomial (parameter : Gaussian) : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial parameter
    CCL.Riemann.SquareRootSheets.degreeTwo

/-- Its complete, finite degree-two isolation input. -/
def isolationInput {parameter : Gaussian} (parameterNonzero : parameter ≠ 0) :
    RFAP.BoxFTA.Input (rootPolynomial parameter) := by
  exact CCL.PowerMonodromy.isolationInput parameterNonzero
    CCL.Riemann.SquareRootSheets.degreeTwo
    CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo

/-- A small target radius which leaves ample room inside the continued
owner's explicit residual-interior strip. -/
def requestedRadius {parameter : Gaussian} (owner : Owner parameter) :
    Coordinate :=
  owner.track.initial.clearance.residualInteriorRadius / 8

theorem requestedRadius_positive {parameter : Gaussian}
    (owner : Owner parameter) : 0 < requestedRadius owner := by
  exact RFAP.ConstructiveFraction.div_pos_direct
    owner.track.initial.clearance.residualInteriorRadius_pos (by decide)

/-- The three finite residual tests needed for reconditioning: global
localization, local Newton assignment, and remaining inside the source
owner's residual-interior strip. -/
def residualTarget {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Coordinate :=
  min (RFAP.GlobalResidual.outsideResidualThreshold
      (rootPolynomial parameter))
    (min (RFAP.GlobalResidual.insideResidualTarget
        (isolationInput parameterNonzero) (requestedRadius owner))
      (owner.track.initial.clearance.bound / 4))

theorem residualTarget_positive {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    0 < residualTarget parameterNonzero owner := by
  apply lt_min
  · apply RFAP.GlobalResidual.outsideResidualThreshold_pos
    unfold rootPolynomial
    rw [CCL.PowerMonodromy.polynomial_degree]
    exact CCL.Riemann.SquareRootSheets.degreeTwo.positive
  · apply lt_min
    · exact RFAP.GlobalResidual.insideResidualTarget_pos
        (isolationInput parameterNonzero) (requestedRadius_positive owner)
    · exact RFAP.ConstructiveFraction.div_pos_direct
        owner.track.initial.clearance.positive (by decide)

/-- The first deterministic track index meeting all three residual tests. -/
def sampleIndex {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.CoherentRoot.residualScale
      (rootPolynomial parameter) owner.ambient owner.track)
    0 (residualTarget parameterNonzero owner)

/-- The displayed rational anchor used to assign the continued occurrence. -/
def sample {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Gaussian :=
  (CCL.Riemann.CoherentRoot.approximation owner.track).sample
    (sampleIndex parameterNonzero owner)

theorem sample_residual_lt {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    normSq ((rootPolynomial parameter).eval
      (sample parameterNonzero owner)) <
        residualTarget parameterNonzero owner := by
  exact (CCL.Riemann.CoherentRoot.sample_residual_le owner.track (by
    rw [CCL.PowerMonodromy.polynomial_degree]
    exact CCL.Riemann.SquareRootSheets.degreeTwo.positive)
      (sampleIndex parameterNonzero owner)).trans_lt
    (CCL.FiniteGeometric.firstQuarterBelow_accurate
      (CCL.Riemann.CoherentRoot.residualScale
        (rootPolynomial parameter) owner.ambient owner.track)
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (rootPolynomial parameter) owner.ambient owner.track)
      0 (residualTarget parameterNonzero owner)
      (residualTarget_positive parameterNonzero owner))

/-- The selected anchor remains in the initial continued-owner box. -/
theorem sample_inside_owner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    owner.track.initial.box.Contains (sample parameterNonzero owner) := by
  change owner.track.initial.box.Contains
    (CCL.Riemann.CoherentRoot.state owner.track
      (sampleIndex parameterNonzero owner)).box.anchor
  exact (CCL.Riemann.CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le (sampleIndex parameterNonzero owner))).contains
      (CCL.Riemann.CoherentRoot.state owner.track
        (sampleIndex parameterNonzero owner)).box.contains_anchor

/-- A sample below the combined target cannot lie outside the independently
computed large isolation square. -/
theorem sample_inside_largeSquare {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    (RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter)).Contains
      (sample parameterNonzero owner) := by
  by_cases inside :
      (RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter)).Contains
        (sample parameterNonzero owner)
  · exact inside
  · have outsideLower := RFAP.GlobalResidual.outsideResidualThreshold_le
      (p := rootPolynomial parameter) (by
        unfold rootPolynomial
        rw [CCL.PowerMonodromy.polynomial_degree]
        exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
      (sample parameterNonzero owner) inside
    have residualBelowOutside :
        normSq ((rootPolynomial parameter).eval
          (sample parameterNonzero owner)) <
          RFAP.GlobalResidual.outsideResidualThreshold
            (rootPolynomial parameter) :=
      (sample_residual_lt parameterNonzero owner).trans_le
        (min_le_left _ _)
    exact ((not_lt_of_ge outsideLower) residualBelowOutside).elim

theorem sample_residual_lt_insideTarget {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    normSq ((rootPolynomial parameter).eval
      (sample parameterNonzero owner)) <
      RFAP.GlobalResidual.insideResidualTarget
        (isolationInput parameterNonzero) (requestedRadius owner) :=
  (sample_residual_lt parameterNonzero owner).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))

theorem sample_residual_lt_ownerQuarter {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    normSq ((rootPolynomial parameter).eval
      (sample parameterNonzero owner)) <
      owner.track.initial.clearance.bound / 4 :=
  (sample_residual_lt parameterNonzero owner).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))

/-- Global finite localization and deterministic ownership of the continued
occurrence. -/
@[irreducible] def assignment {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) :
    RFAP.GlobalResidual.AssignedResult (isolationInput parameterNonzero)
      (sample parameterNonzero owner) (requestedRadius owner) :=
  RFAP.GlobalResidual.assignInside (isolationInput parameterNonzero)
    (sample parameterNonzero owner)
    (sample_inside_largeSquare parameterNonzero owner)
    (requestedRadius_positive owner)
    (sample_residual_lt_insideTarget parameterNonzero owner)

/-- Strict signed coordinate bounds extracted without a square root from a
squared Euclidean distance bound. -/
private theorem signed_coordinate_bounds_of_normSq_lt_sq
    {delta : Gaussian} {radius : Coordinate} (radiusPositive : 0 < radius)
    (distance : normSq delta < radius ^ 2) :
    -radius < delta.re ∧ delta.re < radius ∧
      -radius < delta.im ∧ delta.im < radius := by
  have realSquare : delta.re ^ 2 < radius ^ 2 :=
    (show delta.re ^ 2 ≤ delta.re ^ 2 + delta.im ^ 2 from
      le_add_of_nonneg_right (RFAP.ConstructiveFraction.sq_nonneg_direct _)).trans_lt
      distance
  have imaginarySquare : delta.im ^ 2 < radius ^ 2 :=
    (show delta.im ^ 2 ≤ delta.re ^ 2 + delta.im ^ 2 from
      le_add_of_nonneg_left (RFAP.ConstructiveFraction.sq_nonneg_direct _)).trans_lt
      distance
  have realUpper := RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le realSquare
  have realNegativeUpper := RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le (a := -delta.re) (by
      calc
        (-delta.re) ^ 2 = delta.re ^ 2 := by ring1
        _ < radius ^ 2 := realSquare)
  have imaginaryUpper := RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
    radiusPositive.le imaginarySquare
  have imaginaryNegativeUpper :=
    RFAP.CauchyResolution.lt_of_sq_lt_sq_of_nonneg
      radiusPositive.le (a := -delta.im) (by
        calc
          (-delta.im) ^ 2 = delta.im ^ 2 := by ring1
          _ < radius ^ 2 := imaginarySquare)
  exact
    ⟨by
      have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
        realNegativeUpper
      simpa only [neg_neg] using negated,
      realUpper,
      by
        have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
          imaginaryNegativeUpper
        simpa only [neg_neg] using negated,
      imaginaryUpper⟩

private theorem assigned_band_distance_lt {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter)
    {z : Gaussian}
    (inside : (assignment parameterNonzero owner).state.box.Contains z) :
    normSq (z - sample parameterNonzero owner) <
      owner.track.initial.clearance.residualInteriorRadius ^ 2 := by
  let radius := owner.track.initial.clearance.residualInteriorRadius
  let epsilon := requestedRadius owner
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      owner.track.initial.clearance.residualInteriorRadius_pos
  have radiusSquarePositive : 0 < radius ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct radiusPositive 2
  have assignedRadiusSquareLe :
      (assignment parameterNonzero owner).radius ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (assignment parameterNonzero owner).radiusPositive.le
      (assignment parameterNonzero owner).radiusLeRequested 2
  have bandLe :
      18 * (assignment parameterNonzero owner).radius ^ 2 ≤
        18 * epsilon ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      assignedRadiusSquareLe (by decide)
  have epsilon_eq : epsilon = (1 / 8 : Coordinate) * radius := by
    dsimp only [epsilon, requestedRadius, radius]
    simp only [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ConstructiveFraction.one_mul]
    rw [RFAP.ConstructiveFraction.mul_comm]
  have scaledStrict : 18 * epsilon ^ 2 < radius ^ 2 := by
    rw [epsilon_eq]
    calc
      18 * ((1 / 8 : Coordinate) * radius) ^ 2 =
          (18 * (1 / 8 : Coordinate) ^ 2) * radius ^ 2 := by
        ring1
      _ < 1 * radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (show (18 : Coordinate) * (1 / 8) ^ 2 < 1 by decide)
          radiusSquarePositive
      _ = radius ^ 2 := by ring1
  calc
    normSq (z - sample parameterNonzero owner) ≤
        18 * (assignment parameterNonzero owner).radius ^ 2 :=
      (assignment parameterNonzero owner).bandNearSample z inside
    _ ≤ 18 * epsilon ^ 2 := bandLe
    _ < radius ^ 2 := scaledStrict

/-- The assigned common descendant is still strictly inside the continued
owner.  This is the same-occurrence half of the reconditioning bridge. -/
theorem assignment_state_strict_owner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    (assignment parameterNonzero owner).state.box.StrictInterior
      owner.track.initial.box := by
  let source := owner.track.initial.box
  let localBox := (assignment parameterNonzero owner).state.box
  let anchor := sample parameterNonzero owner
  let radius := owner.track.initial.clearance.residualInteriorRadius
  have margins := owner.track.initial.clearance.residualInteriorMargins
    (sample_inside_owner parameterNonzero owner)
    (sample_residual_lt_ownerQuarter parameterNonzero owner)
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      owner.track.initial.clearance.residualInteriorRadius_pos
  let lower : Gaussian := ⟨localBox.xLower, localBox.yLower⟩
  let upper : Gaussian := ⟨localBox.xUpper, localBox.yUpper⟩
  have lowerInside : localBox.Contains lower :=
    ⟨le_rfl, localBox.x_valid, le_rfl, localBox.y_valid⟩
  have upperInside : localBox.Contains upper :=
    ⟨localBox.x_valid, le_rfl, localBox.y_valid, le_rfl⟩
  have lowerBounds := signed_coordinate_bounds_of_normSq_lt_sq radiusPositive
    (assigned_band_distance_lt parameterNonzero owner lowerInside)
  have upperBounds := signed_coordinate_bounds_of_normSq_lt_sq radiusPositive
    (assigned_band_distance_lt parameterNonzero owner upperInside)
  exact
    { left := by
        calc
          source.xLower < anchor.re - radius := by
            have := margins.1
            dsimp only [source, anchor, radius] at this ⊢
            have shifted := add_lt_add_right this (-radius)
            dsimp only [source, anchor, radius] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < localBox.xLower := by
            have := lowerBounds.1
            dsimp only [lower, anchor] at this
            have shifted := add_lt_add_right this anchor.re
            simp only [sub_re] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1 <;> ring1
      right := by
        calc
          localBox.xUpper < anchor.re + radius := by
            have := upperBounds.2.1
            dsimp only [upper, anchor] at this
            have shifted := add_lt_add_right this anchor.re
            simp only [sub_re] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1
            ring1
          _ < source.xUpper := by
            simpa only [source, anchor, radius] using margins.2.1
      bottom := by
        calc
          source.yLower < anchor.im - radius := by
            have := margins.2.2.1
            dsimp only [source, anchor, radius] at this ⊢
            have shifted := add_lt_add_right this (-radius)
            dsimp only [source, anchor, radius] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < localBox.yLower := by
            have := lowerBounds.2.2.1
            dsimp only [lower, anchor] at this
            have shifted := add_lt_add_right this anchor.im
            simp only [sub_im] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1 <;> ring1
      top := by
        calc
          localBox.yUpper < anchor.im + radius := by
            have := upperBounds.2.2.2
            dsimp only [upper, anchor] at this
            have shifted := add_lt_add_right this anchor.im
            simp only [sub_im] at shifted
            dsimp only [anchor] at shifted ⊢
            convert shifted using 1
            ring1
          _ < source.yUpper := by
            simpa only [source, anchor, radius] using margins.2.2.2 }

/-- The globally selected canonical owner, repackaged as the owner used by
the continuation chain. -/
def freshOwner {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter)
  track := (isolationInput parameterNonzero).isolation.tracks.get
    (assignment parameterNonzero owner).owner.owner

/-- One of the two canonical global owners at a displayed nonzero radicand.
Unlike `freshOwner`, this presentation exposes the finite owner index and is
therefore suitable for sheet-independent finite minima. -/
def canonicalOwner {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (index : Fin 2) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter)
  track := (isolationInput parameterNonzero).isolation.tracks.get index

/-- Reconditioning always returns one of the two explicitly enumerable
canonical owners.  The selected index is computed by the finite global
assignment procedure; no root choice is hidden in this equality. -/
@[simp] theorem freshOwner_eq_canonicalOwner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (owner : Owner parameter) :
    freshOwner parameterNonzero owner =
      canonicalOwner parameterNonzero
        (assignment parameterNonzero owner).owner.owner :=
  rfl

/-- A complete finite bridge from a continued owner to a fresh global owner.
The assigned track starts strictly inside the old owner; a finite refinement
of that same track starts strictly inside the fresh owner. -/
structure Bridge {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) where
  common : WindingOneTrack (rootPolynomial parameter)
    (RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter))
  commonInitialStrictOwner : common.initial.box.StrictInterior
    owner.track.initial.box
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refined : RFAP.ShrinkingTrack.WindingOneState (rootPolynomial parameter)
    (RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter))
  refined_eq : refined = common.refine common.initial refinementRadius
    refinementRadiusPositive
  refinedStrictFresh : refined.box.StrictInterior
    (freshOwner parameterNonzero owner).track.initial.box

/-- Compute the same-occurrence bridge and hence the fresh owner. -/
@[irreducible] def bridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : Owner parameter) : Bridge parameterNonzero owner := by
  let assigned := assignment parameterNonzero owner
  let radius := RFAP.Maximality.assignmentRadius
    (rootPolynomial parameter)
    (RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter))
    (isolationInput parameterNonzero).isolation
  let radiusPositive := RFAP.Maximality.assignmentRadius_pos
    (rootPolynomial parameter)
    (RFAP.GlobalWinding.largeSquareBox (rootPolynomial parameter))
    (isolationInput parameterNonzero).isolation
  let refined := assigned.track.refine assigned.track.initial radius
    radiusPositive
  exact
    { common := assigned.track
      commonInitialStrictOwner := by
        simpa only [assigned, RFAP.GlobalResidual.AssignedResult.trackInitial]
          using assignment_state_strict_owner parameterNonzero owner
      refinementRadius := radius
      refinementRadiusPositive := radiusPositive
      refined := refined
      refined_eq := rfl
      refinedStrictFresh := by
        simpa only [assigned, radius, radiusPositive, refined, freshOwner]
          using assigned.owner.strict }

end CCL.Riemann.SquareRootReconditioning

import CCL.Riemann.ClearSheetContinuation
import CCL.Riemann.SquareRootReconditioning

/-!
# Path-controlled square-root preparation

This file replaces isolator-shaped preparation by a residual localization
whose final radius is fixed before the owner's sample is read.  The radius is
computed from the global finite isolation data, the clear segment's uniform
degree-two derivative separation, and the requested root diameter.  Reading
the inherited owner is used only to find a sufficiently accurate rational
sample of the same occurrence.
-/

namespace CCL.Riemann.RobustSquareRootPreparation

open CCL.Riemann.BranchCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner

private def rootPolynomialAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) : GaussianPolynomial :=
  CCL.Riemann.SquareRootReconditioning.rootPolynomial
    (polynomial.eval (segment.pointAt parameter))

private def inputAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    RFAP.BoxFTA.Input (rootPolynomialAt segment parameter) :=
  CCL.Riemann.SquareRootReconditioning.isolationInput
    (segment.pointAt_eval_ne_zero parameter inside)

private def parentAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    RFAP.ResidualWinding.ProtectedAmbient
      (rootPolynomialAt segment parameter)
      (RFAP.GlobalWinding.largeSquareBox
        (rootPolynomialAt segment parameter)) :=
  RFAP.GlobalResidual.largeSquareProtectedAmbient
    (inputAt segment parameter inside).degreePositive

/-- Point-independent reference radius supplied by the global finite
isolation square at one base parameter. -/
def radiusReference
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) : Coordinate :=
  RFAP.ResidualWinding.uniformAnchoredRadius
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) 1

theorem radiusReference_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    0 < radiusReference segment parameter inside :=
  RFAP.ResidualWinding.uniformAnchoredRadius_pos
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) (by decide)

/-- Exact residual-localization radius.  The four caps respectively ensure
global localization, admission by the uniform derivative threshold, Taylor
dominance by the uniform derivative margin, and the requested root diameter. -/
def preparationRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) : Coordinate :=
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  min (radiusReference segment parameter inside)
    (min
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
          segment /
        (2 * RFAP.PolynomialBounds.denseLipschitzBound p parent.box))
      (min
        (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
            segment /
          (72 * RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box))
        (CCL.FiniteGeometric.dyadicSquareRadius (rootDiameter / 8))))

theorem preparationRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (_rootDiameterPositive : 0 < rootDiameter) :
    0 < preparationRadius segment parameter inside rootDiameter := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  have thresholdPositive :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold_positive
      segment
  have marginPositive :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment
  have lipschitzPositive :
      0 < RFAP.PolynomialBounds.denseLipschitzBound p parent.box :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos p parent.box
  have taylorPositive :
      0 < RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box :=
    RFAP.PolynomialBounds.denseTaylorRemainderBound_pos p parent.box
  unfold preparationRadius
  exact lt_min (radiusReference_positive segment parameter inside)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct thresholdPositive
        (RFAP.ConstructiveFraction.mul_pos_direct
          (show (0 : Coordinate) < 2 by decide)
          lipschitzPositive))
      (lt_min
        (RFAP.ConstructiveFraction.div_pos_direct marginPositive
          (RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 72) (by decide))
            taylorPositive))
        (CCL.FiniteGeometric.dyadicSquareRadius_positive _)))

theorem preparationRadius_le_reference
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    preparationRadius segment parameter inside rootDiameter ≤
      radiusReference segment parameter inside := by
  unfold preparationRadius
  exact min_le_left _ _

theorem preparationRadius_le_thresholdCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    preparationRadius segment parameter inside rootDiameter ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
          segment /
        (2 * RFAP.PolynomialBounds.denseLipschitzBound p parent.box) := by
  dsimp only
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem preparationRadius_le_taylorCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    preparationRadius segment parameter inside rootDiameter ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment /
        (72 * RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box) := by
  dsimp only
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

theorem preparationRadius_le_diameterCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    preparationRadius segment parameter inside rootDiameter ≤
      CCL.FiniteGeometric.dyadicSquareRadius (rootDiameter / 8) := by
  unfold preparationRadius
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))

/-- Radius of the same-sample common descendant.  It is small relative both
to the old owner's residual-interior strip and to the new centered square. -/
def bridgeRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  min (CCL.Riemann.SquareRootReconditioning.requestedRadius owner)
    ((1 / 4 : Coordinate) *
      preparationRadius segment parameter inside rootDiameter)

theorem bridgeRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < bridgeRadius segment parameter inside owner rootDiameter :=
  lt_min
    (CCL.Riemann.SquareRootReconditioning.requestedRadius_positive owner)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (preparationRadius_positive segment parameter inside
        rootDiameterPositive))

theorem bridgeRadius_le_requested
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    bridgeRadius segment parameter inside owner rootDiameter ≤
      CCL.Riemann.SquareRootReconditioning.requestedRadius owner :=
  min_le_left _ _

theorem bridgeRadius_le_quarterPreparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    bridgeRadius segment parameter inside owner rootDiameter ≤
      (1 / 4 : Coordinate) *
        preparationRadius segment parameter inside rootDiameter :=
  min_le_right _ _

theorem bridgeRadius_le_preparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    bridgeRadius segment parameter inside owner rootDiameter ≤
      preparationRadius segment parameter inside rootDiameter := by
  let radius := preparationRadius segment parameter inside rootDiameter
  exact (bridgeRadius_le_quarterPreparation segment parameter inside owner
    rootDiameter).trans
      (by
        calc
          (1 / 4 : Coordinate) * radius ≤ 1 * radius :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              (by decide)
              (preparationRadius_positive segment parameter inside
                rootDiameterPositive).le
          _ = radius := by ring1)

/-- Residual target used to read the inherited occurrence.  Besides the
global fixed-radius localization test, it retains enough slack for the old
owner, a same-sample local bridge, and the explicit displacement estimate. -/
def sampleResidualTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  let p := rootPolynomialAt segment parameter
  let input := inputAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let localRadius := bridgeRadius segment parameter inside owner rootDiameter
  min (RFAP.GlobalResidual.outsideResidualThreshold p)
    (min (RFAP.GlobalResidual.insideResidualTarget input radius)
      (min (RFAP.GlobalResidual.insideResidualTarget input localRadius)
        (min (owner.track.initial.clearance.bound / 4)
          (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
            segment * radius ^ 2))))

theorem sampleResidualTarget_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < sampleResidualTarget segment parameter inside owner rootDiameter := by
  let p := rootPolynomialAt segment parameter
  let input := inputAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let localRadius :=
    CCL.Riemann.SquareRootReconditioning.requestedRadius owner
  unfold sampleResidualTarget
  apply lt_min
  · exact RFAP.GlobalResidual.outsideResidualThreshold_pos input.degreePositive
  · apply lt_min
    · exact RFAP.GlobalResidual.insideResidualTarget_pos input
        (preparationRadius_positive segment parameter inside
          rootDiameterPositive)
    · apply lt_min
      · exact RFAP.GlobalResidual.insideResidualTarget_pos input
          (bridgeRadius_positive segment parameter inside owner
            rootDiameterPositive)
      · apply lt_min
        · exact RFAP.ConstructiveFraction.div_pos_direct
            owner.track.initial.clearance.positive (by decide)
        · exact RFAP.ConstructiveFraction.mul_pos_direct
            (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
              segment)
            (RFAP.ConstructiveFraction.pow_pos_direct
              (preparationRadius_positive segment parameter inside
                rootDiameterPositive) 2)

/-- First displayed owner sample meeting every fixed-radius and bridge
residual test. -/
def sampleIndex
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.CoherentRoot.residualScale
      (rootPolynomialAt segment parameter) owner.ambient owner.track)
    0 (sampleResidualTarget segment parameter inside owner rootDiameter)

def sample
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  (CCL.Riemann.CoherentRoot.approximation owner.track).sample
    (sampleIndex segment parameter inside owner rootDiameter)

theorem sample_residual_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      sampleResidualTarget segment parameter inside owner rootDiameter := by
  exact (CCL.Riemann.CoherentRoot.sample_residual_le owner.track (by
    rw [CCL.PowerMonodromy.polynomial_degree]
    exact CCL.Riemann.SquareRootSheets.degreeTwo.positive)
      (sampleIndex segment parameter inside owner rootDiameter)).trans_lt
    (CCL.FiniteGeometric.firstQuarterBelow_accurate
      (CCL.Riemann.CoherentRoot.residualScale
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      0 (sampleResidualTarget segment parameter inside owner rootDiameter)
      (sampleResidualTarget_positive segment parameter inside owner
        rootDiameterPositive))

theorem sample_inside_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    owner.track.initial.box.Contains
      (sample segment parameter inside owner rootDiameter) := by
  change owner.track.initial.box.Contains
    (CCL.Riemann.CoherentRoot.state owner.track
      (sampleIndex segment parameter inside owner rootDiameter)).box.anchor
  exact (CCL.Riemann.CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le _)).contains
      (CCL.Riemann.CoherentRoot.state owner.track
        (sampleIndex segment parameter inside owner rootDiameter)).box.contains_anchor

theorem sample_residual_lt_insideTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      RFAP.GlobalResidual.insideResidualTarget
        (inputAt segment parameter inside)
        (preparationRadius segment parameter inside rootDiameter) :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))

theorem sample_residual_lt_bridgeInsideTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      RFAP.GlobalResidual.insideResidualTarget
        (inputAt segment parameter inside)
        (bridgeRadius segment parameter inside owner rootDiameter) :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))

theorem sample_residual_lt_ownerQuarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      owner.track.initial.clearance.bound / 4 :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))

theorem sample_inside_largeSquare
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (RFAP.GlobalWinding.largeSquareBox
      (rootPolynomialAt segment parameter)).Contains
        (sample segment parameter inside owner rootDiameter) := by
  by_cases contained :
      (RFAP.GlobalWinding.largeSquareBox
        (rootPolynomialAt segment parameter)).Contains
          (sample segment parameter inside owner rootDiameter)
  · exact contained
  · have outsideLower := RFAP.GlobalResidual.outsideResidualThreshold_le
      (inputAt segment parameter inside).degreeAtLeastTwo
      (sample segment parameter inside owner rootDiameter) contained
    have residualBelowOutside :=
      (sample_residual_lt segment parameter inside owner
        rootDiameterPositive).trans_le (min_le_left _ _)
    exact ((not_lt_of_ge outsideLower) residualBelowOutside).elim

theorem sample_residual_lt_parentQuarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      (parentAt segment parameter inside).clearance.bound / 4 :=
  (sample_residual_lt_insideTarget segment parameter inside owner
    rootDiameterPositive).trans_le (min_le_left _ _)

/-- Point-specific finite Newton input obtained from the path-controlled
uniform residual request. -/
def anchoredInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ResidualWinding.AnchoredInput
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) := by
  let point := sample segment parameter inside owner rootDiameter
  let radius := preparationRadius segment parameter inside rootDiameter
  have localized :=
    RFAP.ResidualWinding.uniform_residual_strict_and_anchored
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) point
      (sample_inside_largeSquare segment parameter inside owner
        rootDiameterPositive)
      (preparationRadius_positive segment parameter inside
        rootDiameterPositive)
      (sample_residual_lt_insideTarget segment parameter inside owner
        rootDiameterPositive)
  exact RFAP.ResidualWinding.anchoredInputOfResidual
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) point localized.1
    (preparationRadius_positive segment parameter inside
      rootDiameterPositive) localized.2

theorem anchoredInput_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (anchoredInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        preparationRadius segment parameter inside rootDiameter := by
  change RFAP.ResidualWinding.anchoredRadius
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside)
      (sample segment parameter inside owner rootDiameter)
      (preparationRadius segment parameter inside rootDiameter) =
    preparationRadius segment parameter inside rootDiameter
  exact RFAP.ResidualWinding.anchoredRadius_eq_cap_of_le_uniformReference
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside)
    (sample segment parameter inside owner rootDiameter)
    (sample_inside_largeSquare segment parameter inside owner
      rootDiameterPositive)
    (preparationRadius_le_reference segment parameter inside rootDiameter)
    (sample_residual_lt_parentQuarter segment parameter inside owner
      rootDiameterPositive)

/-- Residual seed whose radius is definitionally inherited from the anchored
input and propositionally equal to the path-controlled preparation radius. -/
def seed
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :=
  (anchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).seed (inputAt segment parameter inside).elimination

theorem seed_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        preparationRadius segment parameter inside rootDiameter := by
  change (anchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).radius = _
  exact anchoredInput_radius_eq segment parameter inside owner
    rootDiameterPositive

theorem seed_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).source.anchor =
      sample segment parameter inside owner rootDiameter := by
  rw [seed, RFAP.ResidualWinding.AnchoredInput.seed_source,
    RFAP.ResidualWinding.anchoredSquare_anchor]
  unfold anchoredInput
  rfl

/-- Same-sample anchored input at the smaller bridge radius. -/
def bridgeAnchoredInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ResidualWinding.AnchoredInput
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) := by
  let point := sample segment parameter inside owner rootDiameter
  have localized :=
    RFAP.ResidualWinding.uniform_residual_strict_and_anchored
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) point
      (sample_inside_largeSquare segment parameter inside owner
        rootDiameterPositive)
      (bridgeRadius_positive segment parameter inside owner
        rootDiameterPositive)
      (sample_residual_lt_bridgeInsideTarget segment parameter inside owner
        rootDiameterPositive)
  exact RFAP.ResidualWinding.anchoredInputOfResidual
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside) point localized.1
    (bridgeRadius_positive segment parameter inside owner
      rootDiameterPositive) localized.2

theorem bridgeAnchoredInput_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeAnchoredInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        bridgeRadius segment parameter inside owner rootDiameter := by
  change RFAP.ResidualWinding.anchoredRadius
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside)
      (sample segment parameter inside owner rootDiameter)
      (bridgeRadius segment parameter inside owner rootDiameter) =
    bridgeRadius segment parameter inside owner rootDiameter
  apply RFAP.ResidualWinding.anchoredRadius_eq_cap_of_le_uniformReference
    (inputAt segment parameter inside).squarefree
    (parentAt segment parameter inside)
    (sample segment parameter inside owner rootDiameter)
    (sample_inside_largeSquare segment parameter inside owner
      rootDiameterPositive)
  · exact (bridgeRadius_le_preparation segment parameter inside owner
      rootDiameterPositive).trans
        (preparationRadius_le_reference segment parameter inside rootDiameter)
  · exact (sample_residual_lt_bridgeInsideTarget segment parameter inside owner
      rootDiameterPositive).trans_le (min_le_left _ _)

def bridgeSeed
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :=
  (bridgeAnchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).seed (inputAt segment parameter inside).elimination

theorem bridgeSeed_radius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeSeed segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        bridgeRadius segment parameter inside owner rootDiameter := by
  change (bridgeAnchoredInput segment parameter inside owner rootDiameter
    rootDiameterPositive).radius = _
  exact bridgeAnchoredInput_radius_eq segment parameter inside owner
    rootDiameterPositive

theorem bridgeSeed_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeSeed segment parameter inside owner rootDiameter
        rootDiameterPositive).source.anchor =
      sample segment parameter inside owner rootDiameter := by
  rw [bridgeSeed, RFAP.ResidualWinding.AnchoredInput.seed_source,
    RFAP.ResidualWinding.anchoredSquare_anchor]
  unfold bridgeAnchoredInput
  rfl

/-- Common shrinking track used only to identify the old and robust
occurrences. -/
def bridgeTrack
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ShrinkingTrack.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (RFAP.GlobalWinding.largeSquareBox (rootPolynomialAt segment parameter)) :=
  (bridgeSeed segment parameter inside owner rootDiameter
    rootDiameterPositive).track
      (inputAt segment parameter inside).degreeAtLeastTwo

theorem three_bridgeRadius_lt_ownerInterior
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    3 * bridgeRadius segment parameter inside owner rootDiameter <
      owner.track.initial.clearance.residualInteriorRadius := by
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let interior := owner.track.initial.clearance.residualInteriorRadius
  have interiorPositive : 0 < interior := by
    simpa only [interior] using
      owner.track.initial.clearance.residualInteriorRadius_pos
  have radiusLeRequested : radius ≤
      CCL.Riemann.SquareRootReconditioning.requestedRadius owner :=
    bridgeRadius_le_requested segment parameter inside owner rootDiameter
  have requestedFormula :
      CCL.Riemann.SquareRootReconditioning.requestedRadius owner =
        (1 / 8 : Coordinate) * interior := by
    dsimp only [CCL.Riemann.SquareRootReconditioning.requestedRadius,
      interior]
    simp only [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ConstructiveFraction.one_mul]
    rw [RFAP.ConstructiveFraction.mul_comm]
  calc
    3 * radius ≤
        3 * CCL.Riemann.SquareRootReconditioning.requestedRadius owner :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        radiusLeRequested (by decide)
    _ = (3 * (1 / 8 : Coordinate)) * interior := by
      rw [requestedFormula]
      ring1
    _ < 1 * interior :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (by decide) interiorPositive
    _ = interior := by ring1

/-- The common same-sample band is strictly inside the inherited owner. -/
theorem bridgeTrack_initial_strict_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        owner.track.initial.box := by
  let common := bridgeSeed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let point := sample segment parameter inside owner rootDiameter
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let interior := owner.track.initial.clearance.residualInteriorRadius
  have margins := owner.track.initial.clearance.residualInteriorMargins
    (sample_inside_owner segment parameter inside owner rootDiameter)
    (sample_residual_lt_ownerQuarter segment parameter inside owner
      rootDiameterPositive)
  have bandBounds := common.anchor_band_coordinate_bounds
  have commonAnchor : common.source.anchor = point := by
    dsimp only [common, point]
    exact bridgeSeed_source_anchor segment parameter inside owner
      rootDiameterPositive
  have commonRadius : common.radius = radius := by
    dsimp only [common, radius]
    exact bridgeSeed_radius_eq segment parameter inside owner
      rootDiameterPositive
  have bandLeft : point.re - 3 * radius ≤ common.band.box.xLower := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.1
  have bandRight : common.band.box.xUpper ≤ point.re + 3 * radius := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.2.1
  have bandBottom : point.im - 3 * radius ≤ common.band.box.yLower := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.2.2.1
  have bandTop : common.band.box.yUpper ≤ point.im + 3 * radius := by
    rw [← commonAnchor, ← commonRadius]
    exact bandBounds.2.2.2
  have threeRadiusSmall : 3 * radius < interior :=
    three_bridgeRadius_lt_ownerInterior segment parameter inside owner
      rootDiameter
  have negatedSmall : -interior < -(3 * radius) :=
    RFAP.ConstructiveFraction.neg_lt_neg_direct threeRadiusSmall
  change common.band.box.StrictInterior owner.track.initial.box
  exact
    { left := by
        calc
          owner.track.initial.box.xLower < point.re - interior := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              margins.1 (-interior)
            dsimp only [point, interior] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < point.re - 3 * radius := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              negatedSmall point.re
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.xLower := bandLeft
      right := by
        calc
          common.band.box.xUpper ≤ point.re + 3 * radius := bandRight
          _ < point.re + interior := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              threeRadiusSmall point.re
            convert shifted using 1 <;> ring1
          _ < owner.track.initial.box.xUpper := by
            simpa only [point, interior] using margins.2.1
      bottom := by
        calc
          owner.track.initial.box.yLower < point.im - interior := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              margins.2.2.1 (-interior)
            dsimp only [point, interior] at shifted ⊢
            convert shifted using 1 <;> ring1
          _ < point.im - 3 * radius := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              negatedSmall point.im
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.yLower := bandBottom
      top := by
        calc
          common.band.box.yUpper ≤ point.im + 3 * radius := bandTop
          _ < point.im + interior := by
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              threeRadiusSmall point.im
            convert shifted using 1 <;> ring1
          _ < owner.track.initial.box.yUpper := by
            simpa only [point, interior] using margins.2.2.2 }

theorem two_bridgeRadius_lt_preparationRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    2 * bridgeRadius segment parameter inside owner rootDiameter <
      preparationRadius segment parameter inside rootDiameter := by
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let preparation := preparationRadius segment parameter inside rootDiameter
  have radiusCap : radius ≤ (1 / 4 : Coordinate) * preparation :=
    bridgeRadius_le_quarterPreparation segment parameter inside owner
      rootDiameter
  have preparationPositive : 0 < preparation :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  calc
    2 * radius ≤ 2 * ((1 / 4 : Coordinate) * preparation) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusCap
        (by decide)
    _ = (2 * (1 / 4 : Coordinate)) * preparation := by ring1
    _ < 1 * preparation :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (by decide) preparationPositive
    _ = preparation := by ring1

/-- The common same-sample band is strictly inside the robust centered
square, because the two Newton centers are computed from the same anchor. -/
theorem bridgeSeed_state_strict_centered
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    ((bridgeSeed segment parameter inside owner rootDiameter
        rootDiameterPositive).state
      (inputAt segment parameter inside).degreeAtLeastTwo).box.StrictInterior
        (seed segment parameter inside owner rootDiameter
          rootDiameterPositive).centeredBox := by
  let common := bridgeSeed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let robust := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let radius := bridgeRadius segment parameter inside owner rootDiameter
  let preparation := preparationRadius segment parameter inside rootDiameter
  have commonAnchor : common.source.anchor =
      sample segment parameter inside owner rootDiameter := by
    dsimp only [common]
    exact bridgeSeed_source_anchor segment parameter inside owner
      rootDiameterPositive
  have robustAnchor : robust.source.anchor =
      sample segment parameter inside owner rootDiameter := by
    dsimp only [robust]
    exact seed_source_anchor segment parameter inside owner
      rootDiameterPositive
  have commonRadius : common.radius = radius := by
    dsimp only [common, radius]
    exact bridgeSeed_radius_eq segment parameter inside owner
      rootDiameterPositive
  have robustRadius : robust.radius = preparation := by
    dsimp only [robust, preparation]
    exact seed_radius_eq segment parameter inside owner rootDiameterPositive
  have centersEqual :
      RFAP.LocalExtraction.anchorNewtonCenter
          (rootPolynomialAt segment parameter) common.source =
        RFAP.LocalExtraction.anchorNewtonCenter
          (rootPolynomialAt segment parameter) robust.source := by
    rw [RFAP.LocalExtraction.anchorNewtonCenter_eq,
      RFAP.LocalExtraction.anchorNewtonCenter_eq,
      commonAnchor, robustAnchor]
  have twiceRadiusSmall : 2 * radius < preparation :=
    two_bridgeRadius_lt_preparationRadius segment parameter inside owner
      rootDiameterPositive
  change common.band.box.StrictInterior robust.centeredBox
  unfold RFAP.ResidualWinding.Seed.centeredBox
  unfold RFAP.AffineWinding.centeredSquare
  exact
    { left := by
        calc
          (RFAP.LocalExtraction.anchorNewtonCenter
              (rootPolynomialAt segment parameter) robust.source).re -
                robust.radius <
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re -
                  2 * common.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
              twiceRadiusSmall
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              negated
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.xLower := common.band.left_lower
      right := by
        calc
          common.band.box.xUpper ≤
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re +
                  2 * common.radius := common.band.right_upper
          _ < (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) robust.source).re +
              robust.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              twiceRadiusSmall
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).re
            convert shifted using 1 <;> ring1
      bottom := by
        calc
          (RFAP.LocalExtraction.anchorNewtonCenter
              (rootPolynomialAt segment parameter) robust.source).im -
                robust.radius <
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im -
                  2 * common.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
              twiceRadiusSmall
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              negated
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im
            convert shifted using 1 <;> ring1
          _ ≤ common.band.box.yLower := common.band.bottom_lower
      top := by
        calc
          common.band.box.yUpper ≤
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im +
                  2 * common.radius := common.band.top_upper
          _ < (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) robust.source).im +
              robust.radius := by
            rw [← centersEqual, commonRadius, robustRadius]
            have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
              twiceRadiusSmall
              (RFAP.LocalExtraction.anchorNewtonCenter
                (rootPolynomialAt segment parameter) common.source).im
            convert shifted using 1 <;> ring1 }

theorem preparationRadius_le_one
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) :
    preparationRadius segment parameter inside rootDiameter ≤ 1 :=
  (preparationRadius_le_reference segment parameter inside rootDiameter).trans
    (RFAP.ResidualWinding.uniformAnchoredRadius_bounds
      (inputAt segment parameter inside).squarefree
      (parentAt segment parameter inside) 1).1

theorem seed_source_diagonalSq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).source.diagonalSq =
      2 * preparationRadius segment parameter inside rootDiameter ^ 2 := by
  rw [seed, RFAP.ResidualWinding.AnchoredInput.seed_source,
    RFAP.ResidualWinding.anchoredSquare_diagonalSq,
    anchoredInput_radius_eq segment parameter inside owner
      rootDiameterPositive]

theorem sourceThreshold
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let source := (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).source
    RFAP.LocalExtraction.anchorResidualBound p parent.box source ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
        segment := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let source := (seed segment parameter inside owner rootDiameter
    rootDiameterPositive).source
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p parent.box
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (preparationRadius_le_one segment parameter inside rootDiameter)
        radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have radiusCap :=
    preparationRadius_le_thresholdCap segment parameter inside rootDiameter
  have scaledCap : radius * (2 * lipschitz) ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
        segment :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (RFAP.PolynomialBounds.denseLipschitzBound_pos p parent.box))).1
      radiusCap
  dsimp only
  unfold RFAP.LocalExtraction.anchorResidualBound
  rw [seed_source_diagonalSq segment parameter inside owner
    rootDiameterPositive]
  calc
    lipschitz * (2 * radius ^ 2) ≤ lipschitz * (2 * radius) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusSquareLe (by decide))
        (RFAP.PolynomialBounds.denseLipschitzBound_pos p parent.box).le
    _ = radius * (2 * lipschitz) := by ring1
    _ ≤ CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
          segment := scaledCap

theorem preparationTaylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let radius := preparationRadius segment parameter inside rootDiameter
    2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box *
        radius ^ 2) ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  let taylor := RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (preparationRadius_le_one segment parameter inside rootDiameter)
        radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have radiusCap :=
    preparationRadius_le_taylorCap segment parameter inside rootDiameter
  have coefficientPositive : 0 < (72 : Coordinate) * taylor :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide))
      (RFAP.PolynomialBounds.denseTaylorRemainderBound_pos p parent.box)
  have scaledCap : radius * (72 * taylor) ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment :=
    (RFAP.ConstructiveFraction.le_div_iff_pos coefficientPositive).1 radiusCap
  calc
    2 * (36 * taylor * radius ^ 2) = (72 * taylor) * radius ^ 2 := by ring1
    _ ≤ (72 * taylor) * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusSquareLe
        coefficientPositive.le
    _ = radius * (72 * taylor) := by ring1
    _ ≤ CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment :=
      scaledCap

theorem taylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let radius := (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).radius
    2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box *
        radius ^ 2) ≤
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment := by
  rw [seed_radius_eq segment parameter inside owner rootDiameterPositive]
  exact preparationTaylorSmall segment parameter inside rootDiameterPositive

theorem sample_residual_lt_displacementBudget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment parameter inside owner rootDiameter)) <
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
        preparationRadius segment parameter inside rootDiameter ^ 2 :=
  (sample_residual_lt segment parameter inside owner rootDiameterPositive).trans_le
    ((min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))

theorem displacementSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let source := (seed segment parameter inside owner rootDiameter
      rootDiameterPositive).source
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.LocalExtraction.anchorNewtonCenter p source - source.anchor) ≤
      (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).radius ^ 2 := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := parent.box) segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  have derivativeLower := separation.lower
    (robustSeed.sourceRefines.contains robustSeed.source.contains_anchor)
    (robustSeed.residual.trans
      (sourceThreshold segment parameter inside owner rootDiameterPositive))
  change separation.margin ≤
    RFAP.ConstructiveGaussian.Gaussian.normSq
      ((RFAP.ConstructiveGCD.derivative p).eval
        robustSeed.source.anchor) at derivativeLower
  have derivativeNonzero :
      (RFAP.ConstructiveGCD.derivative p).eval robustSeed.source.anchor ≠ 0 := by
    intro zero
    rw [zero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at derivativeLower
    exact (not_lt_of_ge derivativeLower)
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)
  have derivativePositive : 0 <
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.ConstructiveGCD.derivative p).eval robustSeed.source.anchor) :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos derivativeNonzero
  have inverseBound :
      (RFAP.ConstructiveGaussian.Gaussian.normSq
        ((RFAP.ConstructiveGCD.derivative p).eval
          robustSeed.source.anchor))⁻¹ ≤
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
        segment)⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment) derivativeLower
  dsimp only
  rw [RFAP.LocalExtraction.normSq_anchorNewtonCenter_sub_anchor
    derivativeNonzero]
  have residualBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval robustSeed.source.anchor) ≤
        CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
          radius ^ 2 := by
    rw [seed_source_anchor segment parameter inside owner rootDiameterPositive]
    exact (sample_residual_lt_displacementBudget segment parameter inside owner
      rootDiameterPositive).le
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval robustSeed.source.anchor) *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.ConstructiveGCD.derivative p).eval
            robustSeed.source.anchor))⁻¹ ≤
      (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
          radius ^ 2) *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.ConstructiveGCD.derivative p).eval
            robustSeed.source.anchor))⁻¹ :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct residualBound
        (RFAP.ConstructiveFraction.inv_pos_direct derivativePositive).le
    _ ≤ (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
          radius ^ 2) *
        (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
          segment)⁻¹ :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct inverseBound
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
            segment).le
          (RFAP.ConstructiveFraction.sq_nonneg_direct radius))
    _ = radius ^ 2 := by
      rw [show
        (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment *
            radius ^ 2) *
              (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
                segment)⁻¹ =
          radius ^ 2 *
            (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
              segment *
              (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
                segment)⁻¹) by ring1,
        RFAP.ConstructiveFraction.mul_inv_cancel _
          (CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin_positive
            segment).ne', mul_one]
    _ = robustSeed.radius ^ 2 := by
      rw [seed_radius_eq segment parameter inside owner rootDiameterPositive]

/-- Initial winding-one state on the exact path-controlled centered square. -/
def state
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomialAt segment parameter)
      (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := parent.box) segment parameter inside
  have sourceThreshold' :=
    sourceThreshold segment parameter inside owner rootDiameterPositive
  change RFAP.LocalExtraction.anchorResidualBound p parent.box
      robustSeed.source ≤ separation.threshold at sourceThreshold'
  have taylorSmall' :=
    taylorSmall segment parameter inside owner rootDiameterPositive
  change 2 * (36 *
      RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box *
        robustSeed.radius ^ 2) ≤ separation.margin at taylorSmall'
  let majorant :=
    RFAP.NewtonWinding.separatedNewtonLinearizationMajorant p parent.box
      robustSeed.radius
  exact robustSeed.separatedCenteredStateWithMajorant
    (inputAt segment parameter inside).degreeAtLeastTwo separation
    sourceThreshold'
    (displacementSmall segment parameter inside owner rootDiameterPositive)
    taylorSmall' majorant
    (RFAP.NewtonWinding.separatedNewtonLinearizationMajorant_pos p parent.box
      robustSeed.radiusPositive)
    (fun _z boundary =>
      RFAP.NewtonWinding.newtonLinearization_boundary_le_majorant
        robustSeed.sourceRefines robustSeed.radiusPositive boundary)

theorem state_clearance_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let robustSeed := seed segment parameter inside owner rootDiameter
      rootDiameterPositive
    let separation :=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := parent.box) segment parameter inside
    (state segment parameter inside owner rootDiameter
        rootDiameterPositive).clearance.bound =
      RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
          robustSeed.radius ^ 2 /
        (4 * RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
          p parent.box robustSeed.radius) := by
  let p := rootPolynomialAt segment parameter
  let parent := parentAt segment parameter inside
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := parent.box) segment parameter inside
  have sourceThreshold' :=
    sourceThreshold segment parameter inside owner rootDiameterPositive
  change RFAP.LocalExtraction.anchorResidualBound p parent.box
      robustSeed.source ≤ separation.threshold at sourceThreshold'
  have taylorSmall' :=
    taylorSmall segment parameter inside owner rootDiameterPositive
  change 2 * (36 *
      RFAP.PolynomialBounds.denseTaylorRemainderBound p parent.box *
        robustSeed.radius ^ 2) ≤ separation.margin at taylorSmall'
  let majorant :=
    RFAP.NewtonWinding.separatedNewtonLinearizationMajorant p parent.box
      robustSeed.radius
  let majorantPositive :=
    RFAP.NewtonWinding.separatedNewtonLinearizationMajorant_pos p parent.box
      robustSeed.radiusPositive
  let majorantUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary robustSeed.centeredBox z →
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.NewtonWinding.newtonLinearization p robustSeed.source).eval z) ≤
            majorant := fun _z boundary =>
    RFAP.NewtonWinding.newtonLinearization_boundary_le_majorant
      robustSeed.sourceRefines robustSeed.radiusPositive boundary
  change
    (robustSeed.separatedCenteredStateWithMajorant
      (inputAt segment parameter inside).degreeAtLeastTwo separation
      sourceThreshold'
      (displacementSmall segment parameter inside owner rootDiameterPositive)
      taylorSmall' majorant majorantPositive majorantUpper).clearance.bound = _
  exact
    RFAP.ResidualWinding.Seed.separatedCenteredStateWithMajorant_clearance_bound
      (inputAt segment parameter inside).degreeAtLeastTwo robustSeed separation
      sourceThreshold'
      (displacementSmall segment parameter inside owner rootDiameterPositive)
      taylorSmall' majorant majorantPositive majorantUpper

/-- Total shrinking track restarted from the path-controlled state. -/
def track
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    RFAP.ShrinkingTrack.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (seed segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox :=
  RFAP.ShrinkingTrack.ofInitial
    (inputAt segment parameter inside).degreeAtLeastTwo
    (inputAt segment parameter inside).squarefree
    (inputAt segment parameter inside).elimination
    (state segment parameter inside owner rootDiameter rootDiameterPositive)

/-- Owner carrying the inherited occurrence on the predictable centered
square.  Its ambient is the centered square itself. -/
def prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Owner (polynomial.eval (segment.pointAt parameter)) := by
  let robustSeed := seed segment parameter inside owner rootDiameter
    rootDiameterPositive
  exact
    { parameterNonzero :=
        segment.pointAt_eval_ne_zero parameter inside
      ambient := robustSeed.centeredBox
      track := track segment parameter inside owner rootDiameter
        rootDiameterPositive }

/-- The common descendant is also strictly inside the robust owner's exact
centered initial square. -/
theorem bridgeTrack_initial_strict_prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        (prepared segment parameter inside owner rootDiameter
          rootDiameterPositive).track.initial.box := by
  change
    ((bridgeSeed segment parameter inside owner rootDiameter
        rootDiameterPositive).state
      (inputAt segment parameter inside).degreeAtLeastTwo).box.StrictInterior
        (seed segment parameter inside owner rootDiameter
          rootDiameterPositive).centeredBox
  exact bridgeSeed_state_strict_centered segment parameter inside owner
    rootDiameterPositive

/-- Coefficient-computed upper bound for the Newton linearization at the
path-controlled radius.  It is independent of the inherited owner. -/
def linearizationMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) : Coordinate :=
  RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
    (rootPolynomialAt segment parameter) (parentAt segment parameter inside).box
    (preparationRadius segment parameter inside rootDiameter)

theorem linearizationMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < linearizationMajorant segment parameter inside rootDiameter :=
  RFAP.NewtonWinding.separatedNewtonLinearizationMajorant_pos
    (rootPolynomialAt segment parameter) (parentAt segment parameter inside).box
    (preparationRadius_positive segment parameter inside rootDiameterPositive)

/-- Closed positive clearance formula for the centered restart.  No field of
the inherited owner occurs in this expression. -/
def predictedClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (rootDiameter : Coordinate) : Coordinate :=
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := (parentAt segment parameter inside).box)
      segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  RFAP.NewtonWinding.separatedNewtonDominanceMargin separation radius ^ 2 /
    (4 * linearizationMajorant segment parameter inside rootDiameter)

theorem predictedClearance_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < predictedClearance segment parameter inside rootDiameter := by
  let separation :=
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := (parentAt segment parameter inside).box)
      segment parameter inside
  let radius := preparationRadius segment parameter inside rootDiameter
  have taylor := preparationTaylorSmall segment parameter inside
    rootDiameterPositive
  change 2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound
      (rootPolynomialAt segment parameter)
      (parentAt segment parameter inside).box * radius ^ 2) ≤
        separation.margin at taylor
  have dominancePositive :
      0 < RFAP.NewtonWinding.separatedNewtonDominanceMargin separation radius :=
    RFAP.NewtonWinding.separatedNewtonDominanceMargin_pos separation
      (preparationRadius_positive segment parameter inside
        rootDiameterPositive) taylor
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct dominancePositive 2)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment parameter inside
        rootDiameterPositive))

theorem storedFormula_eq_predictedClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    let p := rootPolynomialAt segment parameter
    let parent := parentAt segment parameter inside
    let robustSeed := seed segment parameter inside owner rootDiameter
      rootDiameterPositive
    let separation :=
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := parent.box) segment parameter inside
    RFAP.NewtonWinding.separatedNewtonDominanceMargin separation
          robustSeed.radius ^ 2 /
        (4 * RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
          p parent.box robustSeed.radius) =
      predictedClearance segment parameter inside rootDiameter := by
  dsimp only
  rw [seed_radius_eq segment parameter inside owner rootDiameterPositive]
  rfl

theorem prepared_clearance_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
        rootDiameterPositive).track.initial.clearance.bound =
      predictedClearance segment parameter inside rootDiameter := by
  change (state segment parameter inside owner rootDiameter
    rootDiameterPositive).clearance.bound = _
  exact (state_clearance_formula segment parameter inside owner
    rootDiameterPositive).trans
      (storedFormula_eq_predictedClearance segment parameter inside owner
        rootDiameterPositive)

theorem prepared_diagonalSq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
        rootDiameterPositive).track.initial.box.diagonalSq =
      8 * preparationRadius segment parameter inside rootDiameter ^ 2 := by
  change (seed segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox.diagonalSq = _
  rw [RFAP.ResidualWinding.Seed.centeredBox_diagonalSq,
    seed_radius_eq segment parameter inside owner rootDiameterPositive]

theorem prepared_diagonal_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq < rootDiameter := by
  let radius := preparationRadius segment parameter inside rootDiameter
  let diameterCap :=
    CCL.FiniteGeometric.dyadicSquareRadius (rootDiameter / 8)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment parameter inside rootDiameterPositive
  have radiusLe :=
    preparationRadius_le_diameterCap segment parameter inside rootDiameter
  have squareLe : radius ^ 2 ≤ diameterCap ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusPositive.le radiusLe 2
  have targetPositive : 0 < rootDiameter / 8 :=
    RFAP.ConstructiveFraction.div_pos_direct rootDiameterPositive (by decide)
  have capSquareLt : diameterCap ^ 2 < rootDiameter / 8 :=
    CCL.FiniteGeometric.dyadicSquareRadius_sq_lt targetPositive
  rw [prepared_diagonalSq segment parameter inside owner
    rootDiameterPositive]
  calc
    8 * radius ^ 2 ≤ 8 * diameterCap ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
        (by decide)
    _ < 8 * (rootDiameter / 8) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide) capSquareLt
    _ = rootDiameter := by
      calc
        8 * (rootDiameter / 8) = (rootDiameter / 8) * 8 :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = rootDiameter :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne rootDiameter 8
            (by decide)

attribute [irreducible] prepared

end CCL.Riemann.RobustSquareRootPreparation

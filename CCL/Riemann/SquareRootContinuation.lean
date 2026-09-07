import CCL.Riemann.SquareRootSheets

/-!
# Finite continuation of a square-root owner across one rational move

The specialized power-monodromy API rebases through equal-norm global
squares.  A general algebraic path does not preserve the norm of its
radicand.  For one sufficiently small rational move we instead enlarge the
ambient box by a finite coordinatewise hull, carry the old owner by Rouché,
and run the existing eliminant-driven Newton-band extractor in that hull.
This yields a fresh globally supported target track without an equal-norm
hypothesis.
-/

namespace CCL.Riemann.SquareRootContinuation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

/-- Smallest displayed axis box containing both supplied boxes. -/
def hull (left right : Box) : Box where
  xLower := min left.xLower right.xLower
  xUpper := max left.xUpper right.xUpper
  yLower := min left.yLower right.yLower
  yUpper := max left.yUpper right.yUpper
  x_valid := (min_le_left _ _).trans
    (left.x_valid.trans (le_max_left _ _))
  y_valid := (min_le_left _ _).trans
    (left.y_valid.trans (le_max_left _ _))

theorem left_refines_hull (left right : Box) : left.Refines (hull left right) :=
  ⟨min_le_left _ _, le_max_left _ _, min_le_left _ _, le_max_left _ _⟩

theorem right_refines_hull (left right : Box) :
    right.Refines (hull left right) :=
  ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩

/-- Common finite ambient for a source track and the target power
polynomial's independently computed global square. -/
def commonAmbient {source : Gaussian} {ambient : Box}
    (_sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (target : Gaussian) : Box :=
  hull ambient
    (RFAP.GlobalWinding.largeSquareBox
      (CCL.PowerMonodromy.polynomial target
        CCL.Riemann.SquareRootSheets.degreeTwo))

/-- Local source owner carried by one constant-parameter Rouché move. -/
def transportedOwner {source target : Gaussian} {ambient : Box}
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    CCL.ProgressivePolynomialRoots.LocalOwner
      (CCL.PowerMonodromy.polynomial target
        CCL.Riemann.SquareRootSheets.degreeTwo) :=
  CCL.PowerMonodromy.transportedOwner
    CCL.Riemann.SquareRootSheets.degreeTwo
    { box := sourceState.box
      proper := sourceState.proper
      clearance := sourceState.clearance
      rawWindingFour := sourceState.rawWindingFour }
    small

/-- The transported owner as a raw target-polynomial state in the common
finite hull. -/
def transportedRawState {source target : Gaussian} {ambient : Box}
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    RFAP.RawSubdivision.RawWindingState
      (CCL.PowerMonodromy.polynomial target
        CCL.Riemann.SquareRootSheets.degreeTwo)
      (commonAmbient sourceState target) := by
  let owner := transportedOwner sourceState small
  exact
    { box := owner.box
      refinesAmbient := by
        change sourceState.box.Refines (hull ambient
          (RFAP.GlobalWinding.largeSquareBox
            (CCL.PowerMonodromy.polynomial target
              CCL.Riemann.SquareRootSheets.degreeTwo)))
        exact sourceState.refinesAmbient.trans
          (left_refines_hull ambient _)
      proper := owner.proper
      clearance := owner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← owner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }

@[simp] theorem transportedRawState_box {source target : Gaussian}
    {ambient : Box}
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    (transportedRawState sourceState small).box = sourceState.box := rfl

/-- Fresh target-polynomial Newton band inside the Rouché-transported owner. -/
def extraction {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :=
  RFAP.NewtonBand.extract
    (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
    (CCL.PowerMonodromy.squarefree targetNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo)
    (CCL.PowerMonodromy.isolationInput targetNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo
      CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo).elimination
    (transportedRawState sourceState small) (epsilon := (1 : Coordinate))
    (by decide)

/-- Fresh globally line-cleared target state in the finite hull. -/
def continuedState {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    WindingOneState
      (CCL.PowerMonodromy.polynomial target
        CCL.Riemann.SquareRootSheets.degreeTwo)
      (commonAmbient sourceState target) := by
  let output := extraction targetNonzero sourceState small
  exact
    { box := output.box
      refinesAmbient := output.refinesAmbient
      proper := output.proper
      clearance := output.clearance
      rawWindingFour := output.rawWindingFour
      ambientLeftClearance := output.ambientLeftClearance
      ambientRightClearance := output.ambientRightClearance
      ambientBottomClearance := output.ambientBottomClearance
      ambientTopClearance := output.ambientTopClearance }

theorem continuedState_refines_source {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    (continuedState targetNonzero sourceState small).box.Refines
      sourceState.box := by
  change (extraction targetNonzero sourceState small).box.Refines sourceState.box
  rw [← transportedRawState_box sourceState small]
  exact (extraction targetNonzero sourceState small).strictCurrent.refines

/-- Complete deterministic shrinking track after one arbitrary-norm small
parameter move. -/
def continuedTrack {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    WindingOneTrack
      (CCL.PowerMonodromy.polynomial target
        CCL.Riemann.SquareRootSheets.degreeTwo)
      (commonAmbient sourceState target) :=
  RFAP.ShrinkingTrack.ofInitial
    (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
    (CCL.PowerMonodromy.squarefree targetNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo)
    (CCL.PowerMonodromy.isolationInput targetNonzero
      CCL.Riemann.SquareRootSheets.degreeTwo
      CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo).elimination
    (continuedState targetNonzero sourceState small)

theorem continuedTrack_initial_refines_source {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    (continuedTrack targetNonzero sourceState small).initial.box.Refines
      sourceState.box :=
  continuedState_refines_source targetNonzero sourceState small

/-- The extracted target owner is not merely nested in the transported
source box: its axis bounds are strictly interior.  This stronger finite fact
identifies the same root occurrence when a continuation step leaves the
displayed parameter unchanged. -/
theorem continuedTrack_initial_strict_source {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceState : WindingOneState
      (CCL.PowerMonodromy.polynomial source
        CCL.Riemann.SquareRootSheets.degreeTwo) ambient)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceState.clearance.bound) :
    (continuedTrack targetNonzero sourceState small).initial.box.StrictInterior
      sourceState.box := by
  change (extraction targetNonzero sourceState small).box.StrictInterior
    sourceState.box
  rw [← transportedRawState_box sourceState small]
  exact (extraction targetNonzero sourceState small).strictCurrent

end CCL.Riemann.SquareRootContinuation

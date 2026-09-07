import CCL.Progressive.OneSidedRational
import FiniteMeasure.OneSidedProcessExamples

/-!
# CCL conversion examples for one-sided rational pairs

The four finite-measure examples are converted here to the ordinary CCL
process interface.  The computations expose exact Gaussian-rational balls
returned by finite squared-error requests.
-/

namespace CCL.ProgressiveOneSidedRationalExamples

open RFAP.ConstructiveGaussian.Gaussian

namespace SquareThree

def process : CCL.ProgressiveEnclosures.Process :=
  FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess

def refinedState : FiniteMeasure.SqrtThree.State :=
  FiniteMeasure.SqrtThree.request FiniteMeasure.SqrtThree.initialState
    (1 / 8)

/-- The square-root-free CCL request converts target `1/7` to gap target
`1/8`; four rational bisections return centre `27/16`. -/
theorem process_refine_eq_refinedState :
    FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess.refine
      FiniteMeasure.OneSidedExamples.SquareThree.located.initial
      (1 / 7) (by decide) = refinedState := by
  rw [FiniteMeasure.LocatedPair.toProcess_refine]
  change FiniteMeasure.SqrtThree.request FiniteMeasure.SqrtThree.initialState
    (CCL.ProgressiveOneSidedRational.gapTarget (1 / 7)) = refinedState
  have gapIdentity :
      CCL.ProgressiveOneSidedRational.gapTarget (1 / 7) = 1 / 8 := by
    decide
  rw [gapIdentity]
  rfl

theorem refined_ball_center :
    (FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess.ball
        refinedState).center.re = 27 / 16 ∧
      (FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess.ball
        refinedState).center.im = 0 := by
  simp only [FiniteMeasure.LocatedPair.toProcess_ball,
    CCL.ProgressiveOneSidedRational.ballOfBound_center_re,
    CCL.ProgressiveOneSidedRational.ballOfBound_center_im,
    FiniteMeasure.OneSidedExamples.SquareThree.located,
    FiniteMeasure.OneSidedExamples.SquareThree.observation, refinedState]
  have data :=
    FiniteMeasure.OneSidedExamples.SquareThree.eighth_request_data
  exact ⟨by simpa only [FiniteMeasure.Bound.sample,
    FiniteMeasure.PairedObservation.bound] using data.1, trivial⟩

theorem requested_ball_accurate :
    (FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess.ball
      (FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess.refine
        FiniteMeasure.OneSidedExamples.SquareThree.located.initial
        (1 / 7) (by decide))).radiusSq < 1 / 7 :=
  FiniteMeasure.OneSidedExamples.SquareThree.located.toProcess.accurate
    FiniteMeasure.OneSidedExamples.SquareThree.located.initial
    (1 / 7) (by decide)

end SquareThree

namespace SquareTwoProbability

def process : CCL.ProgressiveEnclosures.Process :=
  FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess

def refinedState :
    FiniteMeasure.OneSidedExamples.SquareTwoProbability.Stage :=
  .complete

theorem process_refine_eq_refinedState :
    FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.refine
      FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.initial
      (1 / 10) (by decide) = refinedState := by
  rfl

/-- Completing the five-row classifier yields the exact real-axis CCL ball
at `4/5`, with zero squared radius. -/
theorem refined_ball_data :
    (FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.ball
        refinedState).center.re = 4 / 5 ∧
      (FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.ball
        refinedState).center.im = 0 ∧
      (FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.ball
        refinedState).radiusSq = 0 := by
  decide

theorem requested_ball_accurate :
    (FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.ball
      (FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.refine
        FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.initial
        (1 / 10) (by decide))).radiusSq < 1 / 10 :=
  FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.toProcess.accurate
    FiniteMeasure.OneSidedExamples.SquareTwoProbability.located.initial
    (1 / 10) (by decide)

end SquareTwoProbability

namespace FirstArrivalProbability

def process : CCL.ProgressiveEnclosures.Process :=
  FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess

def refinedState :
    FiniteMeasure.OneSidedExamples.FirstArrivalProbability.Stage :=
  .complete

theorem process_refine_eq_refinedState :
    FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.refine
      FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.initial
      (1 / 10) (by decide) = refinedState := by
  rfl

/-- Fully inspecting the eight weighted routes gives the exact real-axis ball
at probability `3/5`. -/
theorem refined_ball_data :
    (FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.ball
        refinedState).center.re = 3 / 5 ∧
      (FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.ball
        refinedState).center.im = 0 ∧
      (FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.ball
        refinedState).radiusSq = 0 := by
  decide

theorem requested_ball_accurate :
    (FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.ball
      (FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.refine
        FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.initial
        (1 / 10) (by decide))).radiusSq < 1 / 10 :=
  FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.toProcess.accurate
    FiniteMeasure.OneSidedExamples.FirstArrivalProbability.located.initial
    (1 / 10) (by decide)

end FirstArrivalProbability

namespace LiouvilleDigits

def process : CCL.ProgressiveEnclosures.Process :=
  FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess

def refinedState : Nat := 2

/-- CCL target `1/9` becomes gap target `1/10`; the finite geometric search
therefore selects the two-digit prefix. -/
theorem process_refine_eq_refinedState :
    FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.refine
      FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.initial
      (1 / 9) (by decide) = refinedState := by
  rw [FiniteMeasure.LocatedPair.toProcess_refine]
  change FiniteMeasure.Geometric.firstQuarterBelow
    1 0 (CCL.ProgressiveOneSidedRational.gapTarget (1 / 9)) = refinedState
  have gapIdentity :
      CCL.ProgressiveOneSidedRational.gapTarget (1 / 9) = 1 / 10 := by
    decide
  rw [gapIdentity]
  exact FiniteMeasure.OneSidedExamples.LiouvilleDigits.tenth_request_index

/-- The two displayed factorial-position digits are both one, so the returned
ball starts at `5/16` and has squared cylinder width `(1/16)²`. -/
theorem refined_ball_data :
    (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
        refinedState).center.re = 5 / 16 ∧
      (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
        refinedState).center.im = 0 ∧
      (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
        refinedState).radiusSq = (1 / 16) ^ 2 := by
  constructor
  · decide
  constructor
  · decide
  · decide

theorem requested_ball_accurate :
    (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
      (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.refine
        FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.initial
        (1 / 9) (by decide))).radiusSq < 1 / 9 :=
  FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.accurate
    FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.initial
    (1 / 9) (by decide)

end LiouvilleDigits

end CCL.ProgressiveOneSidedRationalExamples

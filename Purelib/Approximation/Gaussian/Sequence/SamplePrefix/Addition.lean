module

public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
public import Purelib.Approximation.Gaussian.Name.Arithmetic

/-! # Original paired addition trajectories consuming saved primitive samples -/

public section

namespace Purelib.Approximation.Gaussian.Sequence.SamplePrefix

open Purelib.Approximation.Gaussian

variable {left right : ApproximationData}

/-- Saved input samples preserve the sum process's complete pair of original refinement states at every stage. -/
theorem add_state (first : SamplePrefix left) (second : SamplePrefix right) : ∀ index,
    Process.Sampling.stateAt (Process.add first.view.toProcess second.view.toProcess)
        (show Nat × Nat from (0, 0)) index =
      Process.Sampling.stateAt (Process.add left.toProcess right.toProcess)
        (show Nat × Nat from (0, 0)) index
  | 0 => rfl
  | index + 1 => congrArg
      (fun state : Nat × Nat =>
        (left.refineIndex state.1
          (Request.Basic.Name.additiveInputTarget (Process.Sampling.refinementTarget (index + 1)))
          (Purelib.Data.Rat.Bounds.Quarter.quarter_pos (Process.Sampling.refinementTarget_pos (index + 1))),
        right.refineIndex state.2
          (Request.Basic.Name.additiveInputTarget (Process.Sampling.refinementTarget (index + 1)))
          (Purelib.Data.Rat.Bounds.Quarter.quarter_pos (Process.Sampling.refinementTarget_pos (index + 1)))))
      (first.add_state second index)

/-- The sum of saved execution views reads both exact original input samples at the same original pair of states. -/
theorem add_sample (first : SamplePrefix left) (second : SamplePrefix right) (index : Nat) :
    (Name.Sampling.approximation (first.view.toNamed.add second.view.toNamed)).sample index =
      (Name.Sampling.approximation (left.toNamed.add right.toNamed)).sample index := by
  change first.sample (Process.Sampling.stateAt
      (Process.add first.view.toProcess second.view.toProcess) (show Nat × Nat from (0, 0)) index).1 +
    second.sample (Process.Sampling.stateAt
      (Process.add first.view.toProcess second.view.toProcess) (show Nat × Nat from (0, 0)) index).2 =
    left.sample (Process.Sampling.stateAt
      (Process.add left.toProcess right.toProcess) (show Nat × Nat from (0, 0)) index).1 +
    right.sample (Process.Sampling.stateAt
      (Process.add left.toProcess right.toProcess) (show Nat × Nat from (0, 0)) index).2
  rewrite [first.add_state second index, first.sample_eq, second.sample_eq]
  rfl

end Purelib.Approximation.Gaussian.Sequence.SamplePrefix

end

module
public import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Approximation.Gaussian.Sequence.ApproximationData

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Sequence

public section

/-!
# Finite sampling of a progressive name

Every state below is obtained by one explicitly requested finite refinement.
Its displayed sample is the process's finite rational witness at that state.
The construction never selects or names a value common to all states.
-/

/-- The refined state selected by `stateAt` already meets the target of its own finite index. -/
theorem stateAt_radiusSq_lt (a :
  Gaussian.Sequence.ApproximationData) (index : Nat) :
    a.radiusSq (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index) <
      Gaussian.Process.Sampling.refinementTarget index := by
  cases index with
  | zero =>
      dsimp only [ApproximationData.toProcess, Gaussian.Process.Sampling.stateAt]
      exact a.refineIndex_accurate 0 (Gaussian.Process.Sampling.refinementTarget 0)
        (Gaussian.Process.Sampling.refinementTarget_pos 0)
  | succ index =>
      dsimp only [ApproximationData.toProcess, Gaussian.Process.Sampling.stateAt]
      exact a.refineIndex_accurate (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index)
        (Gaussian.Process.Sampling.refinementTarget (index + 1))
        (Gaussian.Process.Sampling.refinementTarget_pos (index + 1))

/-- The geometric coherent witness and the model sample at the same index are close, with the larger of the two finite
allowances. -/
theorem witness_sample_close (a :
  Gaussian.Sequence.ApproximationData) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (a.sample (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index) - a.sample index) ≤
      max (a.radiusSq index) (Gaussian.Process.Sampling.refinementTarget index) := by
  rcases Nat.le_total index (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index) with order | order
  · exact (a.later_close order).trans (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _)
  · have close := a.later_close order
    have same : Data.Gaussian.Norm.Basic.normSq
        (a.sample (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index) - a.sample index) =
        Data.Gaussian.Norm.Basic.normSq
          (a.sample index - a.sample (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index)) := by
      rw [show a.sample (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index) - a.sample index =
        -(a.sample index - a.sample (Gaussian.Process.Sampling.stateAt a.toProcess (0 : Nat) index)) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
    rw [same]
    exact close.trans ((le_of_lt (a.stateAt_radiusSq_lt index)).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _))

end

end Purelib.Approximation.Gaussian.Sequence.ApproximationData

module
public import Purelib.Approximation.Gaussian.Process.Sampling
public import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Integration.Program.Gaussian.Sampling.Readback

/-! ## Direct refinement-program readings

The public period matrices are names generated from finite refinement
programs.  Sampling such a name does not manufacture a new analytic value:
it asks the originating program for one explicitly indexed later model.  The
two matrix entries may reach different internal indices, so the direct
interface below records both indices independently. -/

open Purelib.Approximation.Gaussian
open Purelib.Integration.Program
/-- Read the exact refinement index reached by the original program's process after the requested sample count. -/
def resampledRefinementIndex
    (program : Gaussian.Basic.RefinementProgram)
    (sampleIndex : Nat) : Nat :=
  Process.Sampling.stateAt program.approximation.toProcess
    (show program.approximation.toProcess.State from (0 : Nat)) sampleIndex

/-- Every retained resampled index is at least the original zero-sample refinement index. -/
theorem resampledRefinementIndex_zero_le
    (program : Gaussian.Basic.RefinementProgram) :
    forall sampleIndex : Nat,
      resampledRefinementIndex program 0 <=
        resampledRefinementIndex program sampleIndex
  | 0 => Nat.le_refl _
  | sampleIndex + 1 => by
      have previous := resampledRefinementIndex_zero_le program
        sampleIndex
      apply previous.trans
      unfold resampledRefinementIndex
      rw [Process.Sampling.stateAt_succ]
      simpa only [Sequence.ApproximationData.toProcess] using
        program.approximation.refineIndex_ge _ _
          (Process.Sampling.refinementTarget_pos (sampleIndex + 1))

end Purelib.Integration.Program.Gaussian.Sampling.Readback

end

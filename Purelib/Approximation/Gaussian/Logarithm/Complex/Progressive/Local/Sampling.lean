module
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sequence
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Sampling

section
@[expose] public section

/-!
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

/-- Every canonical witness of a certified local-logarithm name lies in the one-ninth quadrance disk. -/
theorem inputSample_bound {input :
  Gaussian.Name.Basic.Named} (disk : Domain.Disk input) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (ComplexLog.inputSample input index) ≤ 1 / 9 :=
  disk.possible_normSq (ComplexLog.inputSample_possible_start input index)

/-- Package the original name's canonical witnesses with their retained disk bound and geometric pairwise allowance. -/
def diskSamples (input :
  Gaussian.Name.Basic.Named) (disk : Domain.Disk input) : Sequence.DiskSamples where
  value := ComplexLog.inputSample input
  bound := inputSample_bound disk
  close := Sampling.inputSample_later_close input
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Sampling

end

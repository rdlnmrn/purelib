module
public import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

section
@[expose] public section

/-!
# Core operational congruence for finite sampled quotients

Division is only continuous after a positive denominator lower bound has been
displayed.  This core file packages that constructive fact for the canonical
finite samplers of coherent CCL names.  It does not select completed values:
every quotient below is a quotient of two Gaussian rationals computed at one
finite index.
-/

namespace Purelib.Approximation.Gaussian.Name.Apart.Sampling

/-- Every canonical finite sample of an apart coherent name satisfies the same displayed positive squared-norm lower
bound. -/
theorem sampled_lower (value : Coherent.CoherentNamed) (apart
  : Named.Apart value.name)
    (index : Nat) :
    apart.certificate.lowerSq <=
      Data.Gaussian.Norm.Basic.normSq ((Sampling.approximation value.name).sample index) := by
  exact apart.certificate.lower _
    (value.name.process.possible_inside
      (Gaussian.Process.Sampling.witnessAt_possible value.name.process
        value.name.state index))

/-- Every canonical finite sample of an apart coherent Gaussian name is nonzero. -/
theorem sampled_nonzero (value : Coherent.CoherentNamed)
  (apart : Named.Apart value.name)
    (index : Nat) :
    (Sampling.approximation value.name).sample index ≠ 0 := by
  intro zero
  have positive : 0 <
      Data.Gaussian.Norm.Basic.normSq ((Sampling.approximation value.name).sample index) :=
    apart.certificate.positive.trans_le (sampled_lower value apart index)
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at positive
  exact (lt_irrefl _ positive).elim
end Purelib.Approximation.Gaussian.Name.Apart.Sampling

end

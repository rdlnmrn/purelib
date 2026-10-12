module
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Density.Aligned
public import Purelib.Measure.Content.Density.Existence
import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Content.Equivalence
import Purelib.Measure.Content.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Finite Radon--Nikodym existence

For arbitrary displayed finite contents with decidable payload equality, the
union of their payload tables can be consolidated into a duplicate-free key
list.  Assigning each key its exact singleton mass gives aligned source and
target rows.  Absolute continuity supplies the rowwise zero implication, so
the quotient-density algorithm yields a Radon--Nikodym witness.

The proof below includes the finite histogram reconstruction lemma: summing
singleton masses over any duplicate-free key list covering a displayed atom
table recovers every rational integral.
-/

@[expose] public section

namespace Purelib.Measure.Content.DensityWitness

open Purelib.Measure.AtomicChange (Witness)
section AtomicChange
section Witness

/-- Transport a density witness along evaluation equivalences to the supplied original content owners.

Keep the exact density function and its nonnegativity certificate. Transport all integral equalities through the given
source and target equivalences. -/
def transport {α : Type}
    {alignedSource alignedTarget source target : Content α}
    (witness : Witness alignedSource alignedTarget)
    (sourceEquivalent : Content.EvaluationEquivalent
      alignedSource source)
    (targetEquivalent : Content.EvaluationEquivalent
      alignedTarget target) : Witness source target where
  density := witness.density
  nonnegative := witness.nonnegative
  integral_eq value := by
    calc
      target.integral value = alignedTarget.integral value :=
        (targetEquivalent.integral_eq value).symm
      _ = alignedSource.integral (fun item =>
          witness.density item * value item) := witness.integral_eq value
      _ = source.integral (fun item =>
          witness.density item * value item) :=
        sourceEquivalent.integral_eq _

open Purelib.Measure in
/-- Construct a density witness between the original finite source and target contents from absolute continuity.

Build the aligned singleton-mass change on shared keys, then transport its witness back to these exact original content
owners. -/
def ofAbsolutelyContinuous {α : Type} [DecidableEq α]
    (source target : Content α)
    (continuous : target.AbsolutelyContinuous source) :
    Witness source target :=
  let change := AtomicChange.ofAbsolutelyContinuous source target continuous
  transport change.witness
    (AtomicChange.ofAbsolutelyContinuous_source_evaluationEquivalent
      source target continuous)
    (AtomicChange.ofAbsolutelyContinuous_target_evaluationEquivalent
      source target continuous)

end Witness

end AtomicChange

end Purelib.Measure.Content.DensityWitness

end

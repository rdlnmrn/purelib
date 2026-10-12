module
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Measure.BinaryPrefix.Distribution.Basic
public import Purelib.Measure.BinaryPrefix.Distribution.Consistency
import Purelib.Measure.Coupling.Basic
public import Purelib.Measure.Coupling.Law.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Explicit finite-depth raw-prefix contents

For a supplied raw prefix and natural depth, `rawExtensions` generates the
complete displayed binary frontier below that prefix.  Its total dyadic
content is exactly the prefix weight, independently of the chosen finite
depth.  This is a finite conservation theorem, not a statement about an
infinite bit space.
-/

namespace Purelib.Measure.BinaryPrefix

open Purelib in
open Purelib.Data in
open Purelib.Measure in
/-- Couple the deeper extension law to the earlier law by its exact ancestor map.

The graph joint distribution retains the deeper extension occurrences; ancestor consistency certifies its original
earlier marginal law. -/
def rawExtensionAncestorLawCoupling
    (stem : List.BinaryPrefix.CCLMeasureWord) (depth extra : Nat) :
    Measure.LawCoupling
      (BinaryPrefix.rawExtensionDistribution stem (depth + extra))
      (BinaryPrefix.rawExtensionDistribution stem depth) := by
  let graphWitness := LawCoupling.graph
    (BinaryPrefix.rawExtensionDistribution stem (depth + extra)) (List.BinaryPrefix.rawAncestor extra)
  exact
    { coupling := graphWitness.coupling
      leftEquivalent := graphWitness.leftEquivalent
      rightEquivalent := graphWitness.rightEquivalent.trans
        (BinaryPrefix.rawExtensionDistribution_mapAncestor_evaluationEquivalent
          stem depth extra) }

open Purelib.Data in
open Purelib.Measure in
/-- The retained extension-to-ancestor coupling has zero mismatch for its exact ancestor relation. -/
theorem rawExtensionAncestorLawCoupling_mismatchProbability
    (stem : List.BinaryPrefix.CCLMeasureWord) (depth extra : Nat) :
    (rawExtensionAncestorLawCoupling stem depth extra).mismatchProbability
        (List.BinaryPrefix.rawAncestorRelation extra) = 0 := by
  unfold rawExtensionAncestorLawCoupling
  change
    (Coupling.graph
      (BinaryPrefix.rawExtensionDistribution stem (depth + extra))
      (List.BinaryPrefix.rawAncestor extra)).mismatchProbability
        (List.BinaryPrefix.rawAncestorRelation extra) = 0
  apply Coupling.graph_mismatchProbability_eq_zero
  intro atom member
  unfold List.BinaryPrefix.rawAncestorRelation
  exact decide_eq_true rfl
end Purelib.Measure.BinaryPrefix

end

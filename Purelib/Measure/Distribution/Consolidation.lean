module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Equivalence
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Constructive consolidation of finite atom tables

When equality of payloads is explicitly decidable, repeated payloads can be
merged by finite recursion and rational weight addition.  This is an
executable histogram operation; no quotient or choice of representatives is
used.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat in
/-- Read the exact distribution's probability of the decidable singleton at the supplied payload. -/
def atomMass {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) : Fraction.Rational :=
  source.probability (atomEvent item)

/-- Every singleton mass is nonnegative. -/
theorem atomMass_nonneg {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) :
    0 ≤ source.atomMass item :=
  source.probability_nonneg (atomEvent item)

/-- Every singleton mass is at most one. -/
theorem atomMass_le_one {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) :
    source.atomMass item ≤ 1 :=
  source.probability_le_one (atomEvent item)

/-- Combine repeated payload occurrences into one retained row per payload while preserving their summed weights.

The exact finite consolidation procedure supplies the new list; its total-weight identity certifies normalization. -/
def consolidate {α : Type} [DecidableEq α]
    (source : Distribution α) : Distribution α where
  atoms := consolidateAtoms source.atoms
  total_one := by
    rw [totalWeight_consolidateAtoms, source.total_one]

/-- Consolidation cannot increase the number of retained occurrences. -/
theorem consolidate_atoms_length_le {α : Type} [DecidableEq α]
    (source : Distribution α) :
    source.consolidate.atoms.length ≤ source.atoms.length :=
  consolidateAtoms_length_le source.atoms

/-- The consolidated distribution has no repeated retained payloads. -/
theorem consolidate_noRepeatedPayloads {α : Type} [DecidableEq α]
    (source : Distribution α) :
    NoRepeatedPayloads source.consolidate.atoms :=
  consolidateAtoms_noRepeatedPayloads source.atoms

/-- Consolidation preserves every event probability and observable expectation. -/
theorem consolidate_evaluationEquivalent {α : Type} [DecidableEq α]
    (source : Distribution α) :
    EvaluationEquivalent source.consolidate source where
  probability_eq event := eventWeight_consolidateAtoms event source.atoms
  expectation_eq value :=
    expectationWeight_consolidateAtoms value source.atoms

/-- Consolidation preserves the original probability of each singleton payload. -/
theorem consolidate_atomMass {α : Type} [DecidableEq α]
    (source : Distribution α) (item : α) :
    source.consolidate.atomMass item = source.atomMass item :=
  source.consolidate_evaluationEquivalent.probability_eq (atomEvent item)

/-- Consolidating both sides preserves their retained probability and expectation equivalence. -/
theorem EvaluationEquivalent.consolidate {α : Type} [DecidableEq α]
    {left right : Distribution α}
    (equivalent : EvaluationEquivalent left right) :
    EvaluationEquivalent left.consolidate right.consolidate :=
  (left.consolidate_evaluationEquivalent.trans equivalent).trans
    right.consolidate_evaluationEquivalent.symm

/-- Consolidating an already consolidated distribution preserves all its probability and expectation evaluations. -/
theorem consolidate_consolidate_evaluationEquivalent
    {α : Type} [DecidableEq α] (source : Distribution α) :
    EvaluationEquivalent source.consolidate.consolidate source.consolidate :=
  source.consolidate.consolidate_evaluationEquivalent

end Distribution

end Purelib.Measure

end

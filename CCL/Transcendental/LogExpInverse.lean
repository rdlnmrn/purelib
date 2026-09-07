import CCL.Transcendental.LogBranchCalculus

/-!
# The locally aligned logarithm--exponential inverse

Exponentiation forgets logarithm-branch information.  Consequently the
reverse inverse cannot be global.  The finite datum that distinguishes the
desired local branch is that its computed logarithm minus the supplied input
is operationally the exact zero name, rather than merely having unit
exponential.  From that branch-alignment certificate, ordinary proved CCL
field laws reconstruct the desired equality.

This module makes the unavoidable side condition explicit.  It does not use
an integer branch index, a completed `2πi`, or a global logarithm.
-/

namespace CCL.LogExpInverse

abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

open CCL.OperationalFieldLaws

/-- The coherent exponential input whose logarithm branch is being chosen. -/
def exponentialInput (input : CoherentNamed) : CoherentNamed :=
  CCL.TranscendentalCoherence.exp input.name

/-- Minimal finite local-branch datum for the reverse inverse: the selected
charted logarithm has zero operational discrepancy from the supplied
preimage.  A generic anchored chart supplies only equality after
exponentiation and therefore cannot prove this stronger conclusion. -/
def LocalAlignment (input output : CoherentNamed) : Type :=
  NamedEquivalent
    (CCL.LogBranchCalculus.difference input output).name
    (CCL.ProgressiveTransducer.Named.exact 0)

/-- On the explicitly zero-aligned local branch, computing the logarithm of
the actual CCL exponential returns the original coherent CCL input. -/
def logarithm_exponential_inverse (input : CoherentNamed)
    (branch : AnchoredChart (exponentialInput input))
    (alignment : LocalAlignment input branch.output) :
    NamedEquivalent branch.output.name input.name := by
  let negativeInput :=
    CCL.ProgressiveCoherence.CoherentNamed.neg input
  let discrepancy :=
    CCL.LogBranchCalculus.difference input branch.output
  let zero :=
    CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let discrepancyPlusInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add discrepancy input
  let zeroPlusInput :=
    CCL.ProgressiveCoherence.CoherentNamed.add zero input
  let cancelled :=
    CCL.ProgressiveCoherence.CoherentNamed.add
      negativeInput input
  let branchPlusCancelled :=
    CCL.ProgressiveCoherence.CoherentNamed.add
      branch.output cancelled
  have reassociate : NamedEquivalent discrepancyPlusInput.name
      branchPlusCancelled.name := by
    simpa only [discrepancyPlusInput, discrepancy, negativeInput,
      branchPlusCancelled, cancelled,
      CCL.LogBranchCalculus.difference,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg] using
      coherentAdd_assoc branch.output negativeInput input
  have cancelInput : NamedEquivalent cancelled.name zero.name := by
    simpa only [cancelled, negativeInput, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_neg_left input
  have replaceCancelled : NamedEquivalent branchPlusCancelled.name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        branch.output zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      branch.output branch.output cancelled zero
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        branch.output.name) cancelInput
  have removeZero : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        branch.output zero).name branch.output.name :=
    coherentAdd_zero_right branch.output
  have discrepancyPlusInput_to_branch :
      NamedEquivalent discrepancyPlusInput.name branch.output.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans reassociate
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        replaceCancelled removeZero)
  have alignmentProof : NamedEquivalent discrepancy.name zero.name := by
    simpa only [LocalAlignment, discrepancy, zero,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      alignment
  have replaceDiscrepancy : NamedEquivalent discrepancyPlusInput.name
      zeroPlusInput.name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      discrepancy zero input input alignmentProof
      (CCL.OperationalEquivalence.NamedEquivalent.refl input.name)
  have removeLeadingZero : NamedEquivalent zeroPlusInput.name input.name := by
    simpa only [zeroPlusInput, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_zero_left input
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      discrepancyPlusInput_to_branch)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      replaceDiscrepancy removeLeadingZero)

end CCL.LogExpInverse

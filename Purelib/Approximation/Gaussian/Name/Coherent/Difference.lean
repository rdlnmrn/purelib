module
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Name.Coherent.Difference

open Purelib
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

section
public section

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

open Purelib.Approximation

/-- Operational difference `right - left`, represented as actual addition and negation so all later laws use the proved
CCL arithmetic interface. -/
@[expose] def difference (left right : CoherentNamed) : Coherent.CoherentNamed :=
  CoherentNamed.add right
    (CoherentNamed.neg left)

end

section
public section

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

open Purelib.Approximation

/-- Minimal finite local-branch datum for the reverse inverse: the selected charted logarithm has zero operational
discrepancy from the supplied preimage.

A generic anchored chart supplies only equality after exponentiation and therefore cannot prove this stronger
conclusion. -/
@[expose] def LocalAlignment (input output : CoherentNamed) : Type :=
  Gaussian.Equivalence.NamedEquivalent
    (Approximation.Gaussian.Name.Coherent.Difference.difference input output).name
    (Named.exact 0)

end

public section

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

open Purelib.Approximation

/-! ## Explicitly aligned branch laws -/

/-- Operational equality of two names gives a zero discrepancy by actual CCL addition and negation. -/
@[expose] def difference_zero_of_equivalent (left right : CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent right.name left.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Name.Coherent.Difference.difference left right).name
      (Named.exact 0) := by
  let negativeLeft :=
    CoherentNamed.neg left
  exact NamedEquivalent.trans
    (by
      simpa only [Approximation.Gaussian.Name.Coherent.Difference.difference, negativeLeft,
        CoherentNamed.add,
        CoherentNamed.neg] using
        Congruence.coherentAdd_respects
          right left negativeLeft negativeLeft equivalent
          (NamedEquivalent.refl
            negativeLeft.name))
    (Neg.coherentAdd_neg_right left)

/-- Conversely, a supplied zero discrepancy identifies the two local branch outputs.

This is finite field algebra, not an appeal to global logarithm uniqueness. -/
@[expose] def equivalent_of_difference_zero (left right : CoherentNamed)
    (alignment : Approximation.Gaussian.Name.Coherent.Difference.LocalAlignment left right) :
    Gaussian.Equivalence.NamedEquivalent right.name left.name := by
  let negativeLeft :=
    CoherentNamed.neg left
  let discrepancy := Approximation.Gaussian.Name.Coherent.Difference.difference left right
  let zero := Coherence.exact 0
  let discrepancyPlusLeft :=
    CoherentNamed.add discrepancy left
  let zeroPlusLeft :=
    CoherentNamed.add zero left
  let cancelled :=
    CoherentNamed.add negativeLeft left
  let rightPlusCancelled :=
    CoherentNamed.add right cancelled
  have reassociate : Gaussian.Equivalence.NamedEquivalent discrepancyPlusLeft.name
      rightPlusCancelled.name := by
    simpa only [discrepancyPlusLeft, discrepancy, negativeLeft,
      rightPlusCancelled, cancelled,
      Approximation.Gaussian.Name.Coherent.Difference.difference,
      CoherentNamed.add,
      CoherentNamed.neg] using
      Add.coherentAdd_assoc right negativeLeft left
  have cancelLeft : Gaussian.Equivalence.NamedEquivalent cancelled.name zero.name := by
    simpa only [cancelled, negativeLeft, zero,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_left left
  have replaceCancelled : Gaussian.Equivalence.NamedEquivalent rightPlusCancelled.name
      (CoherentNamed.add right zero).name :=
    Congruence.coherentAdd_respects
      right right cancelled zero
      (NamedEquivalent.refl right.name)
      cancelLeft
  have removeZero : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add right zero).name
      right.name := Add.coherentAdd_zero_right right
  have discrepancyPlusLeft_to_right :
      Gaussian.Equivalence.NamedEquivalent discrepancyPlusLeft.name right.name :=
    NamedEquivalent.trans reassociate
      (NamedEquivalent.trans
        replaceCancelled removeZero)
  have replaceDiscrepancy : Gaussian.Equivalence.NamedEquivalent discrepancyPlusLeft.name
      zeroPlusLeft.name :=
    Congruence.coherentAdd_respects
      discrepancy zero left left alignment
      (NamedEquivalent.refl left.name)
  have removeLeadingZero : Gaussian.Equivalence.NamedEquivalent zeroPlusLeft.name left.name := by
    simpa only [zeroPlusLeft, zero,
      CoherentNamed.add,
      Coherence.exact] using
      Add.coherentAdd_zero_left left
  exact NamedEquivalent.trans
    (NamedEquivalent.symm
      discrepancyPlusLeft_to_right)
    (NamedEquivalent.trans
      replaceDiscrepancy removeLeadingZero)

end

end
end

end Purelib.Approximation.Gaussian.Name.Coherent.Difference

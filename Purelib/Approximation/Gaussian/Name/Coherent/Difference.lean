module
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Coherent.Additive
public import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Name.Coherent.Difference

open Purelib
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Coherent.Additive (coherentNeg_respects)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

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
@[expose] def difference (left right : CoherentNamed) : CoherentNamed :=
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
  NamedEquivalent
    (difference input output).name
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

/-- Operationally compared original operands give operationally compared original ordered differences.

The same stateful addition and negation programs retain both supplied input
comparisons. No coefficient, semantic-value or root-owner equality is used.
-/
def respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (left : NamedEquivalent leftOne.name leftTwo.name) (right : NamedEquivalent rightOne.name rightTwo.name) :
    NamedEquivalent (difference leftOne rightOne).name (difference leftTwo rightTwo).name :=
  Congruence.coherentAdd_respects rightOne rightTwo (CoherentNamed.neg leftOne) (CoherentNamed.neg leftTwo)
    right (coherentNeg_respects leftOne leftTwo left)

/-- A uniform squared-norm bound on actual possible readings of the same original difference process.

The subtype retains its scalar bound and the exact original process/state
predicate. It does not replace either input channel or select a numerical
reading; every actual future canonical sample inherits the supplied bound.
-/
public abbrev Bound (left right : CoherentNamed) :=
  { bound : Rational // ∀ value : Canonical,
    (difference left right).name.process.Possible (difference left right).name.state value →
      normSq value ≤ bound }

/-- One retained difference bound and a finite permission check for its actual requested sampling floor.

The first component certifies actual original readings. The second component
checks the requested left sampling index before that bound can pay a request;
rejection preserves the entire original comparison procedure.
-/
public abbrev Request (left right : CoherentNamed) := Bound left right × (Nat → Bool)

/-- A retained difference bound controls actual sampled distance from the original exact zero.

The canonical witness is possible at the original process state. The supplied
strict scalar allowance therefore bounds this same sample at any two actual
indices, without executing a comparison or selecting another channel.
-/
theorem Bound.close_zero {left right : CoherentNamed} (retained : Bound left right)
    (leftIndex rightIndex : Nat) (target : Rational) (covered : retained.val < target) :
    normSq ((Sampling.approximation (difference left right).name).sample leftIndex -
      (Sampling.approximation (Named.exact 0)).sample rightIndex) < target := by
  change normSq ((Sampling.approximation (difference left right).name).sample leftIndex - 0) < target
  rewrite [Purelib.Data.Gaussian.Basic.sub_zero]
  exact (retained.property _ (Process.Sampling.witnessAt_possible_start
    (difference left right).name.process (difference left right).name.state leftIndex)).trans_lt covered

/-- Operational equality gives zero discrepancy, optionally consuming an actual retained bound on that same process.

An absent bound returns the entire original arithmetic comparison. A supplied
bound is tested against each actual positive target. Success retains the
requested floors and bounds every later original sample; a tighter target
consumes the original comparison at those same starts and tolerance.
-/
@[expose] def difference_zero_of_equivalent (left right : CoherentNamed)
    (equivalent : NamedEquivalent right.name left.name) (cached : Option (Request left right) := none) :
    NamedEquivalent
      (difference left right).name
      (Named.exact 0) := by
  let negativeLeft := CoherentNamed.neg left
  let original := NamedEquivalent.trans
    (Congruence.coherentAdd_respects
      right left negativeLeft negativeLeft equivalent
      (NamedEquivalent.refl negativeLeft.name))
    (Neg.coherentAdd_neg_right left)
  match cached with
  | none => exact original
  | some retained =>
      exact ⟨fun leftStart rightStart target positive =>
        if covered : retained.1.val < target ∧ retained.2 leftStart = true then
          { leftIndex := leftStart
            rightIndex := rightStart
            left_ge := Nat.le_refl _
            right_ge := Nat.le_refl _
            close := fun {leftLater rightLater} _leftOrder _rightOrder =>
              retained.1.close_zero leftLater rightLater target covered.1 }
        else original.compare leftStart rightStart target positive⟩

/-- The absent bound preserves the complete original discrepancy-zero comparison and its actual payments. -/
theorem difference_zero_of_equivalent_none (left right : CoherentNamed)
    (equivalent : NamedEquivalent right.name left.name) :
    difference_zero_of_equivalent left right equivalent none =
      (let negativeLeft := CoherentNamed.neg left
       NamedEquivalent.trans
         (Congruence.coherentAdd_respects right left negativeLeft negativeLeft equivalent
           (NamedEquivalent.refl negativeLeft.name))
         (Neg.coherentAdd_neg_right left)) := rfl

/-- A covered bound pays the original requested floors on the same complete difference and exact-zero channels. -/
theorem difference_zero_of_equivalent_covered (left right : CoherentNamed)
    (equivalent : NamedEquivalent right.name left.name) (retained : Request left right)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target)
    (covered : retained.1.val < target) (paid : retained.2 leftStart = true) :
    ((difference_zero_of_equivalent left right equivalent (some retained)).compare
      leftStart rightStart target positive).leftIndex = leftStart ∧
    ((difference_zero_of_equivalent left right equivalent (some retained)).compare
      leftStart rightStart target positive).rightIndex = rightStart := by
  unfold difference_zero_of_equivalent
  dsimp only
  rewrite [dif_pos (And.intro covered paid)]
  exact ⟨rfl, rfl⟩

/-- An uncovered bound returns the whole original comparison at the unchanged request, including all payment fields. -/
theorem difference_zero_of_equivalent_fallback (left right : CoherentNamed)
    (equivalent : NamedEquivalent right.name left.name) (retained : Request left right)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target)
    (uncovered : ¬ retained.1.val < target) :
    (difference_zero_of_equivalent left right equivalent (some retained)).compare
      leftStart rightStart target positive =
    (difference_zero_of_equivalent left right equivalent none).compare
      leftStart rightStart target positive := by
  unfold difference_zero_of_equivalent
  dsimp only
  rewrite [dif_neg (fun allowed => uncovered allowed.1)]
  rfl

/-- Rejected source-floor coverage consumes the whole original comparison at the same starts and tolerance. -/
theorem difference_zero_of_equivalent_unpaid (left right : CoherentNamed)
    (equivalent : NamedEquivalent right.name left.name) (retained : Request left right)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target)
    (unpaid : retained.2 leftStart ≠ true) :
    (difference_zero_of_equivalent left right equivalent (some retained)).compare
      leftStart rightStart target positive =
    (difference_zero_of_equivalent left right equivalent none).compare
      leftStart rightStart target positive := by
  unfold difference_zero_of_equivalent
  dsimp only
  rewrite [dif_neg (fun allowed => unpaid allowed.2)]
  rfl

/-- Conversely, a supplied zero discrepancy identifies the two local branch outputs.

This is finite field algebra, not an appeal to global logarithm uniqueness. -/
@[expose] def equivalent_of_difference_zero (left right : CoherentNamed)
    (alignment : LocalAlignment left right) :
    NamedEquivalent right.name left.name := by
  let negativeLeft :=
    CoherentNamed.neg left
  let discrepancy := difference left right
  let zero := Coherence.exact 0
  let discrepancyPlusLeft :=
    CoherentNamed.add discrepancy left
  let zeroPlusLeft :=
    CoherentNamed.add zero left
  let cancelled :=
    CoherentNamed.add negativeLeft left
  let rightPlusCancelled :=
    CoherentNamed.add right cancelled
  have reassociate : NamedEquivalent discrepancyPlusLeft.name
      rightPlusCancelled.name := Add.coherentAdd_assoc right negativeLeft left
  have cancelLeft : NamedEquivalent cancelled.name zero.name := Neg.coherentAdd_neg_left left
  have replaceCancelled : NamedEquivalent rightPlusCancelled.name
      (CoherentNamed.add right zero).name :=
    Congruence.coherentAdd_respects
      right right cancelled zero
      (NamedEquivalent.refl right.name)
      cancelLeft
  have removeZero : NamedEquivalent
      (CoherentNamed.add right zero).name
      right.name := Add.coherentAdd_zero_right right
  have discrepancyPlusLeft_to_right :
      NamedEquivalent discrepancyPlusLeft.name right.name :=
    NamedEquivalent.trans reassociate
      (NamedEquivalent.trans
        replaceCancelled removeZero)
  have replaceDiscrepancy : NamedEquivalent discrepancyPlusLeft.name
      zeroPlusLeft.name :=
    Congruence.coherentAdd_respects
      discrepancy zero left left alignment
      (NamedEquivalent.refl left.name)
  have removeLeadingZero : NamedEquivalent zeroPlusLeft.name left.name := Add.coherentAdd_zero_left left
  exact NamedEquivalent.trans
    (NamedEquivalent.symm
      discrepancyPlusLeft_to_right)
    (NamedEquivalent.trans
      replaceDiscrepancy removeLeadingZero)

end

end
end

end Purelib.Approximation.Gaussian.Name.Coherent.Difference

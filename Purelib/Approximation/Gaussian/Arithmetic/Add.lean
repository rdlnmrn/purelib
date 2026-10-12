module
public import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence

namespace Purelib.Approximation.Gaussian.Arithmetic.Add

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Name

section
public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

end

section
public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

/-- Actual stateful addition is operationally commutative. -/
@[expose] def coherentAdd_comm (left right : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add left.name right.name)
      (Named.add right.name left.name) :=
  NamedEquivalent.trans
    (Bridge.coherentAdd_toNamed left right)
    (NamedEquivalent.trans
      (Equivalence.approximationEquivalent_toNamed
        (Equivalence.approximationEquivalentOfSamplesEq
          (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name)
          (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation right.name left.name)
          (by
            intro index
            rw [Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample,
              Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
            exact Data.Gaussian.Basic.add_comm _ _)))
      (NamedEquivalent.symm
        (Bridge.coherentAdd_toNamed right left)))

/-- Actual stateful addition is operationally associative. Both process trees normalize to one explicit three-input
equal-index sampler. -/
@[expose] def coherentAdd_assoc (left middle right : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Named.add
          left.name middle.name)
        right.name)
      (Named.add
        left.name
        (Named.add
          middle.name right.name)) := by
  let leftSource :=
    Sampling.approximation left.name
  let rightSource :=
    Sampling.approximation right.name
  let leftMiddle := Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation left.name middle.name
  let middleRight := Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation middle.name right.name
  let triple := Sampling.sampledTripleSumApproximation left.name middle.name right.name
  let sampledLeft :=
    CoherentNamed.ofApproximation
      leftSource
  let sampledRight :=
    CoherentNamed.ofApproximation
      rightSource
  let canonicalLeftMiddle :=
    CoherentNamed.ofApproximation
      leftMiddle
  let canonicalMiddleRight :=
    CoherentNamed.ofApproximation
      middleRight
  have normalizeLeft : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Named.add
          left.name middle.name)
        right.name)
      (Named.add
        canonicalLeftMiddle.name sampledRight.name) :=
    Congruence.coherentAdd_respects
      (CoherentNamed.add left middle)
      canonicalLeftMiddle right sampledRight
      (Bridge.coherentAdd_toNamed left middle)
      (Equivalence.named_toSamplingNamed right.name)
  have leftPointwise : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        canonicalLeftMiddle.name sampledRight.name)
      triple.toNamed :=
    Sampling.addToNamed_equivalent_pointwise leftMiddle rightSource triple
      (by intro index; rfl)
  have normalizeRight : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        left.name
        (Named.add
          middle.name right.name))
      (Named.add
        sampledLeft.name canonicalMiddleRight.name) :=
    Congruence.coherentAdd_respects left sampledLeft
      (CoherentNamed.add middle right)
      canonicalMiddleRight
      (Equivalence.named_toSamplingNamed left.name)
      (Bridge.coherentAdd_toNamed middle right)
  have rightPointwise : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        sampledLeft.name canonicalMiddleRight.name)
      triple.toNamed :=
    Sampling.addToNamed_equivalent_pointwise leftSource middleRight triple (by
      intro index
      rw [Sampling.sampledTripleSumApproximation_sample,
        Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
      exact Data.Gaussian.Basic.add_assoc _ _ _)
  exact NamedEquivalent.trans
    normalizeLeft
    (NamedEquivalent.trans
      leftPointwise
      (NamedEquivalent.trans
        (NamedEquivalent.symm
          rightPointwise)
        (NamedEquivalent.symm
          normalizeRight)))

/-- Adding the terminating exact zero on the right changes no finite operational observation of a coherent CCL name. -/
@[expose] def coherentAdd_zero_right (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add input.name
        (Named.exact 0))
      input.name := by
  let zero := Coherence.exact 0
  let inputApproximation :=
    Sampling.approximation input.name
  have pointwise : Gaussian.Equivalence.NamedEquivalent
      (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation input.name zero.name).toNamed
      inputApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation input.name zero.name)
        inputApproximation
        (by
          intro index
          rw [Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
          change inputApproximation.sample index + 0 =
            inputApproximation.sample index
          exact Data.Gaussian.Basic.add_zero _))
  exact NamedEquivalent.trans
    (by
      simpa only [zero, Coherence.exact,
        Coherence.exact] using
        Bridge.coherentAdd_toNamed input zero)
    (NamedEquivalent.trans pointwise
      (NamedEquivalent.symm
        (Equivalence.named_toSamplingNamed input.name)))

/-- Adding the terminating exact zero on the left changes no finite operational observation of a coherent CCL name. -/
@[expose] def coherentAdd_zero_left (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Named.exact 0) input.name)
      input.name :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Arithmetic.Add.coherentAdd_comm (Coherence.exact 0) input)
    (Approximation.Gaussian.Arithmetic.Add.coherentAdd_zero_right input)

end

public section

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Adding a channel with retained operational zero identity on the right preserves the left channel's operational
value. -/
@[expose] def addRightZero (left right : Coherent.CoherentNamed) (zero : Zero.ZeroIdentity right) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.add left right).name left.name :=
  NamedEquivalent.trans
    (Congruence.coherentAdd_respects left left right
      (Coherence.exact 0)
      (NamedEquivalent.refl _) zero)
    (Approximation.Gaussian.Arithmetic.Add.coherentAdd_zero_right left)

/-- Adding a channel with retained operational zero identity on the left preserves the right channel's operational
value. -/
@[expose] def addLeftZero (left right : Coherent.CoherentNamed) (zero : Zero.ZeroIdentity left) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.add left right).name right.name :=
  NamedEquivalent.trans
    (Congruence.coherentAdd_respects left
      (Coherence.exact 0) right right zero
      (NamedEquivalent.refl _))
    (Approximation.Gaussian.Arithmetic.Add.coherentAdd_zero_left right)

end

end
end

end Purelib.Approximation.Gaussian.Arithmetic.Add

module
public import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Arithmetic.Distributive

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication
open Purelib.Approximation.Gaussian.Sequence.Name

public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

/-- Actual stateful multiplication distributes over actual addition.

The proof normalizes both expression trees to one explicit equal-index sampler. -/
@[expose] def coherentMul_add_left (left middle right : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul left.name
        (Named.add
          middle.name right.name))
      (Named.add
        (Named.mul
          left.name middle.name)
        (Named.mul
          left.name right.name)) := by
  let leftSource :=
    Sampling.approximation left.name
  let middleRight := Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation middle.name right.name
  let leftMiddle := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left.name middle.name
  let leftRight := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left.name right.name
  let common :=
    Sampling.sampledLeftDistributiveApproximation left.name middle.name right.name
  let sampledLeft :=
    CoherentNamed.ofApproximation
      leftSource
  let canonicalMiddleRight :=
    CoherentNamed.ofApproximation
      middleRight
  let canonicalLeftMiddle :=
    CoherentNamed.ofApproximation
      leftMiddle
  let canonicalLeftRight :=
    CoherentNamed.ofApproximation
      leftRight
  have normalizeProduct : Gaussian.Equivalence.NamedEquivalent
      (Named.mul left.name
        (Named.add
          middle.name right.name))
      (Named.mul
        sampledLeft.name canonicalMiddleRight.name) :=
    Congruence.coherentMul_respects left sampledLeft
      (CoherentNamed.add middle right)
      canonicalMiddleRight
      (Equivalence.named_toSamplingNamed left.name)
      (Bridge.coherentAdd_toNamed middle right)
  have productPointwise : Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        sampledLeft.name canonicalMiddleRight.name)
      common.toNamed :=
    Bridge.mulToNamed_equivalent_pointwise leftSource middleRight common (by
      intro index
      rw [Sampling.sampledLeftDistributiveApproximation_sample,
        Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample]
      exact (Data.Gaussian.Basic.left_distrib _ _ _).symm)
  have normalizeSum : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Named.mul
          left.name middle.name)
        (Named.mul
          left.name right.name))
      (Named.add
        canonicalLeftMiddle.name canonicalLeftRight.name) :=
    Congruence.coherentAdd_respects
      (CoherentNamed.mul left middle)
      canonicalLeftMiddle
      (CoherentNamed.mul left right)
      canonicalLeftRight
      (Bridge.coherentMul_toNamed left middle)
      (Bridge.coherentMul_toNamed left right)
  have sumPointwise : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        canonicalLeftMiddle.name canonicalLeftRight.name)
      common.toNamed :=
    Sampling.addToNamed_equivalent_pointwise leftMiddle leftRight common
      (by intro index; rfl)
  exact NamedEquivalent.trans
    normalizeProduct
    (NamedEquivalent.trans
      productPointwise
      (NamedEquivalent.trans
        (NamedEquivalent.symm
          sumPointwise)
        (NamedEquivalent.symm
          normalizeSum)))

/-- The symmetric right-distributive law follows through finite operational commutativity and the proved
left-distributive normalization. -/
@[expose] def coherentAdd_mul_right (left middle right : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Named.add
          left.name middle.name)
        right.name)
      (Named.add
        (Named.mul left.name right.name)
        (Named.mul
          middle.name right.name)) := by
  let sum := CoherentNamed.add left middle
  let rightLeft :=
    CoherentNamed.mul right left
  let leftRight :=
    CoherentNamed.mul left right
  let rightMiddle :=
    CoherentNamed.mul right middle
  let middleRight :=
    CoherentNamed.mul middle right
  exact NamedEquivalent.trans
    (Laws.coherentMul_comm sum right)
    (NamedEquivalent.trans
      (Approximation.Gaussian.Arithmetic.Distributive.coherentMul_add_left right left middle)
      (Congruence.coherentAdd_respects rightLeft leftRight rightMiddle middleRight
        (Laws.coherentMul_comm right left)
        (Laws.coherentMul_comm right middle)))

end

end Purelib.Approximation.Gaussian.Arithmetic.Distributive

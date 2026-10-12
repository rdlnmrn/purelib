module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Sequence

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication
open Purelib.Approximation.Gaussian.Sequence.Name

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

/-- Actual multiplication of coherent CCL names is operationally commutative. The proof compares their common
equal-index product samples. -/
@[expose] def coherentMul_comm (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        left.name right.name)
      (Named.mul
        right.name left.name) :=
  NamedEquivalent.trans
    (Bridge.coherentMul_toNamed left right)
    (NamedEquivalent.trans
      (Equivalence.approximationEquivalent_toNamed
        (Equivalence.approximationEquivalentOfSamplesEq
          (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left.name right.name)
          (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation right.name left.name)
          (by
            intro index
            rw [Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample,
              Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample]
            exact Data.Gaussian.Basic.mul_comm _ _)))
      (NamedEquivalent.symm
        (Bridge.coherentMul_toNamed right left)))

/-- Actual multiplication of three coherent CCL names is operationally associative.

Both process trees are reduced, by finite congruence, to the same equal-index triple-product approximation. -/
@[expose] def coherentMul_assoc (left middle right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Named.mul
          left.name middle.name)
        right.name)
      (Named.mul
        left.name
        (Named.mul
          middle.name right.name)) := by
  let leftSource := Sampling.approximation left.name
  let middleSource :=
    Sampling.approximation middle.name
  let rightSource :=
    Sampling.approximation right.name
  let leftMiddle := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation left.name middle.name
  let middleRight := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation middle.name right.name
  let triple := Gaussian.Sequence.Arithmetic.Product.sampledTripleApproximation left.name middle.name right.name
  let sampledLeft : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      leftSource
  let sampledRight : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      rightSource
  let canonicalLeftMiddle : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      leftMiddle
  let canonicalMiddleRight : Coherent.CoherentNamed :=
    CoherentNamed.ofApproximation
      middleRight
  have normalizeLeft :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          (Named.mul
            left.name middle.name)
          right.name)
        (Named.mul
          canonicalLeftMiddle.name sampledRight.name) :=
    Congruence.coherentMul_respects
      (CoherentNamed.mul left middle)
      canonicalLeftMiddle right sampledRight
      (Bridge.coherentMul_toNamed left middle)
      (Equivalence.named_toSamplingNamed right.name)
  have leftPointwise :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          canonicalLeftMiddle.name sampledRight.name)
        triple.toNamed :=
    Bridge.mulToNamed_equivalent_pointwise leftMiddle rightSource triple
      (by intro index; rfl)
  have normalizeRight :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          left.name
          (Named.mul
            middle.name right.name))
        (Named.mul
          sampledLeft.name canonicalMiddleRight.name) :=
    Congruence.coherentMul_respects left sampledLeft
      (CoherentNamed.mul middle right)
      canonicalMiddleRight
      (Equivalence.named_toSamplingNamed left.name)
      (Bridge.coherentMul_toNamed middle right)
  have rightPointwise :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          sampledLeft.name canonicalMiddleRight.name)
        triple.toNamed :=
    Bridge.mulToNamed_equivalent_pointwise leftSource middleRight triple (by
      intro index
      rw [Gaussian.Sequence.Arithmetic.Product.sampledTripleApproximation_sample,
        Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample]
      exact Data.Gaussian.Basic.mul_assoc _ _ _)
  exact NamedEquivalent.trans
    normalizeLeft
    (NamedEquivalent.trans
      leftPointwise
      (NamedEquivalent.trans
        (NamedEquivalent.symm
          rightPointwise)
        (NamedEquivalent.symm
          normalizeRight)))

/-- The two square trees can be interleaved constructively: `(left*left)*(right*right)` and `(left*right)*(left*right)`
are operationally equivalent for coherent CCL names. -/
@[expose] def coherentMul_squares_interchange (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Named.mul
          left.name left.name)
        (Named.mul
          right.name right.name))
      (Named.mul
        (Named.mul
          left.name right.name)
        (Named.mul
          left.name right.name)) := by
  let leftRight :=
    CoherentNamed.mul left right
  let rightLeft :=
    CoherentNamed.mul right left
  let rightSquare :=
    CoherentNamed.mul right right
  let leftRightRight :=
    CoherentNamed.mul leftRight right
  let rightLeftRight :=
    CoherentNamed.mul rightLeft right
  let leftRightSquare :=
    CoherentNamed.mul left rightSquare
  let rightLeftProduct :=
    CoherentNamed.mul rightLeft right
  let rightLeftRightAssociated :=
    CoherentNamed.mul right leftRight
  have first := Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc left left rightSquare
  have innerSecond : Gaussian.Equivalence.NamedEquivalent leftRightSquare.name leftRightRight.name :=
    NamedEquivalent.symm
      (Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc left right right)
  have second :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          left.name leftRightSquare.name)
        (Named.mul
          left.name leftRightRight.name) :=
    Congruence.coherentMul_respects left left leftRightSquare leftRightRight
      (NamedEquivalent.refl left.name)
      innerSecond
  have innerThird : Gaussian.Equivalence.NamedEquivalent leftRightRight.name rightLeftRight.name :=
    Congruence.coherentMul_respects leftRight rightLeft right right
      (Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm left right)
      (NamedEquivalent.refl right.name)
  have third :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          left.name leftRightRight.name)
        (Named.mul
          left.name rightLeftRight.name) :=
    Congruence.coherentMul_respects left left leftRightRight rightLeftRight
      (NamedEquivalent.refl left.name)
      innerThird
  have innerFourth :
      Gaussian.Equivalence.NamedEquivalent rightLeftProduct.name rightLeftRightAssociated.name :=
    Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc right left right
  have fourth :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          left.name rightLeftProduct.name)
        (Named.mul
          left.name rightLeftRightAssociated.name) :=
    Congruence.coherentMul_respects left left rightLeftProduct rightLeftRightAssociated
      (NamedEquivalent.refl left.name)
      innerFourth
  have fifth :
      Gaussian.Equivalence.NamedEquivalent
        (Named.mul
          left.name rightLeftRightAssociated.name)
        (Named.mul
          leftRight.name leftRight.name) :=
    NamedEquivalent.symm
      (Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc left right leftRight)
  exact NamedEquivalent.trans first
    (NamedEquivalent.trans second
      (NamedEquivalent.trans third
        (NamedEquivalent.trans fourth
          fifth)))

/-- Move a coherent scalar past a coefficient in a nested product up to named equivalence. -/
@[expose] public def coherentMul_left_comm
    (coefficient scalar value : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul coefficient
        (Name.Coherent.CoherentNamed.mul scalar value)).name
      (Name.Coherent.CoherentNamed.mul scalar
        (Name.Coherent.CoherentNamed.mul coefficient value)).name := by
  let coefficientScalar :=
    Name.Coherent.CoherentNamed.mul coefficient scalar
  let scalarCoefficient :=
    Name.Coherent.CoherentNamed.mul scalar coefficient
  apply Equivalence.NamedEquivalent.trans
    (middle := Name.Basic.Named.mul
      (Name.Basic.Named.mul coefficient.name scalar.name) value.name)
  · exact Equivalence.NamedEquivalent.symm (by
      simpa only [coefficientScalar,
        Name.Coherent.CoherentNamed.mul] using
        Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc
          coefficient scalar value)
  · apply Equivalence.NamedEquivalent.trans
    · exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        coefficientScalar scalarCoefficient value value
        (by
            simpa only [coefficientScalar, scalarCoefficient, Name.Coherent.CoherentNamed.mul]
              using Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm coefficient scalar)
        (Equivalence.NamedEquivalent.refl value.name)
    · exact (by
        simpa only [scalarCoefficient,
          Name.Coherent.CoherentNamed.mul] using
          Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc
            scalar coefficient value)

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws

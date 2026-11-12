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
@[expose] def coherentMul_comm (left right : CoherentNamed) :
    NamedEquivalent
      (Named.mul
        left.name right.name)
      (Named.mul
        right.name left.name) :=
  NamedEquivalent.trans
    (Bridge.coherentMul_toNamed left right)
    (NamedEquivalent.trans
      (Equivalence.approximationEquivalent_toNamed
        (Equivalence.approximationEquivalentOfSamplesEq
          (Arithmetic.Product.sampledProductApproximation left.name right.name)
          (Arithmetic.Product.sampledProductApproximation right.name left.name)
          (by
            intro index
            rw [Arithmetic.Product.sampledProductApproximation_sample,
              Arithmetic.Product.sampledProductApproximation_sample]
            exact Data.Gaussian.Basic.mul_comm _ _)))
      (NamedEquivalent.symm
        (Bridge.coherentMul_toNamed right left)))

/-- Actual multiplication of three coherent CCL names is operationally associative.

Both process trees are reduced, by finite congruence, to the same equal-index triple-product approximation. -/
@[expose] def coherentMul_assoc (left middle right : CoherentNamed) :
    NamedEquivalent
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
  let leftMiddle := Arithmetic.Product.sampledProductApproximation left.name middle.name
  let middleRight := Arithmetic.Product.sampledProductApproximation middle.name right.name
  let triple := Arithmetic.Product.sampledTripleApproximation left.name middle.name right.name
  let sampledLeft : CoherentNamed :=
    CoherentNamed.ofApproximation
      leftSource
  let sampledRight : CoherentNamed :=
    CoherentNamed.ofApproximation
      rightSource
  let canonicalLeftMiddle : CoherentNamed :=
    CoherentNamed.ofApproximation
      leftMiddle
  let canonicalMiddleRight : CoherentNamed :=
    CoherentNamed.ofApproximation
      middleRight
  have normalizeLeft :
      NamedEquivalent
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
      NamedEquivalent
        (Named.mul
          canonicalLeftMiddle.name sampledRight.name)
        triple.toNamed :=
    Bridge.mulToNamed_equivalent_pointwise leftMiddle rightSource triple
      (by intro index; rfl)
  have normalizeRight :
      NamedEquivalent
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
      NamedEquivalent
        (Named.mul
          sampledLeft.name canonicalMiddleRight.name)
        triple.toNamed :=
    Bridge.mulToNamed_equivalent_pointwise leftSource middleRight triple (by
      intro index
      rw [Arithmetic.Product.sampledTripleApproximation_sample,
        Arithmetic.Product.sampledProductApproximation_sample]
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

/-- Interchange four retained factors through operational associativity and commutativity.

The two product trees retain the same original four channels; their finite
comparison certificate accounts for the different association of refinements. -/
@[expose] def coherentMul_interchange (first second third fourth : CoherentNamed) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.mul first second) (CoherentNamed.mul third fourth)).name
      (CoherentNamed.mul (CoherentNamed.mul first third) (CoherentNamed.mul second fourth)).name :=
  NamedEquivalent.trans (coherentMul_assoc first second (CoherentNamed.mul third fourth))
    (NamedEquivalent.trans
      (Congruence.coherentMul_respects first first
        (CoherentNamed.mul second (CoherentNamed.mul third fourth))
        (CoherentNamed.mul third (CoherentNamed.mul second fourth))
        (NamedEquivalent.refl first.name)
        (NamedEquivalent.trans (NamedEquivalent.symm (coherentMul_assoc second third fourth))
          (NamedEquivalent.trans
            (Congruence.coherentMul_respects (CoherentNamed.mul second third) (CoherentNamed.mul third second)
              fourth fourth (coherentMul_comm second third) (NamedEquivalent.refl fourth.name))
            (coherentMul_assoc third second fourth))))
      (NamedEquivalent.symm (coherentMul_assoc first third (CoherentNamed.mul second fourth))))

/-- The two square trees can be interleaved constructively: `(left*left)*(right*right)` and `(left*right)*(left*right)`
are operationally equivalent for coherent CCL names. -/
@[expose] def coherentMul_squares_interchange (left right : CoherentNamed) :
    NamedEquivalent
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
  have first := coherentMul_assoc left left rightSquare
  have innerSecond : NamedEquivalent leftRightSquare.name leftRightRight.name :=
    NamedEquivalent.symm
      (coherentMul_assoc left right right)
  have second :
      NamedEquivalent
        (Named.mul
          left.name leftRightSquare.name)
        (Named.mul
          left.name leftRightRight.name) :=
    Congruence.coherentMul_respects left left leftRightSquare leftRightRight
      (NamedEquivalent.refl left.name)
      innerSecond
  have innerThird : NamedEquivalent leftRightRight.name rightLeftRight.name :=
    Congruence.coherentMul_respects leftRight rightLeft right right
      (coherentMul_comm left right)
      (NamedEquivalent.refl right.name)
  have third :
      NamedEquivalent
        (Named.mul
          left.name leftRightRight.name)
        (Named.mul
          left.name rightLeftRight.name) :=
    Congruence.coherentMul_respects left left leftRightRight rightLeftRight
      (NamedEquivalent.refl left.name)
      innerThird
  have innerFourth :
      NamedEquivalent rightLeftProduct.name rightLeftRightAssociated.name :=
    coherentMul_assoc right left right
  have fourth :
      NamedEquivalent
        (Named.mul
          left.name rightLeftProduct.name)
        (Named.mul
          left.name rightLeftRightAssociated.name) :=
    Congruence.coherentMul_respects left left rightLeftProduct rightLeftRightAssociated
      (NamedEquivalent.refl left.name)
      innerFourth
  have fifth :
      NamedEquivalent
        (Named.mul
          left.name rightLeftRightAssociated.name)
        (Named.mul
          leftRight.name leftRight.name) :=
    NamedEquivalent.symm
      (coherentMul_assoc left right leftRight)
  exact NamedEquivalent.trans first
    (NamedEquivalent.trans second
      (NamedEquivalent.trans third
        (NamedEquivalent.trans fourth
          fifth)))

/-- Move a coherent scalar past a coefficient in a nested product up to named equivalence. -/
@[expose] public def coherentMul_left_comm
    (coefficient scalar value : CoherentNamed) :
    NamedEquivalent
      (CoherentNamed.mul coefficient
        (CoherentNamed.mul scalar value)).name
      (CoherentNamed.mul scalar
        (CoherentNamed.mul coefficient value)).name := by
  let coefficientScalar :=
    CoherentNamed.mul coefficient scalar
  let scalarCoefficient :=
    CoherentNamed.mul scalar coefficient
  apply NamedEquivalent.trans
    (middle := Named.mul
      (Named.mul coefficient.name scalar.name) value.name)
  · exact NamedEquivalent.symm (by
      simpa only [coefficientScalar,
        CoherentNamed.mul] using
        coherentMul_assoc
          coefficient scalar value)
  · apply NamedEquivalent.trans
    · exact Congruence.coherentMul_respects
        coefficientScalar scalarCoefficient value value
        (by
            simpa only [coefficientScalar, scalarCoefficient, CoherentNamed.mul]
              using coherentMul_comm coefficient scalar)
        (NamedEquivalent.refl value.name)
    · exact (by
        simpa only [scalarCoefficient,
          CoherentNamed.mul] using
          coherentMul_assoc
            scalar coefficient value)

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws

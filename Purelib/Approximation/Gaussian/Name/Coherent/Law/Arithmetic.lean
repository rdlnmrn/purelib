module
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Arithmetic.Distributive
public import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic

open Purelib
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

public section

/-!
# Operational laws at the persistent CCL-prefix layer

Operational equivalence compares two finite approximation programs by a
computed pair of later natural indices for every positive rational target.
This file carries that comparison all the way to persistent raw CCL cursors.
The two cursors may follow different displayed finite request schedules and
may emit different redundant words.  Each word nevertheless extends its own
earlier prefix, retains exact parser semantics for its certified origin, and
ends in a cylinder of the requested squared-chordal diameter.

The `BitLaw` wrapper then exposes the established arithmetic and exp/log laws
at precisely this bit-producing interface.  It does not identify completed
values or quantify over an infinite bitstream.
-/

open Purelib.Approximation

/-! ## Congruence of progressive constructors -/

/-- Lift operational equivalence in both coherent operands to an addition law at the retained CCL-prefix interface. -/
@[expose] def addition_respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne.name rightTwo.name) :
    Law.Basic.BitLaw
      (CoherentNamed.add leftOne rightOne)
      (CoherentNamed.add leftTwo rightTwo) :=
  BitLaw.ofEquivalent
    (Congruence.coherentAdd_respects
      leftOne leftTwo rightOne rightTwo leftEquivalent rightEquivalent)

/-- Negation respects operational equality.

The proof uses only the already proved finite CCL additive laws: add the opposite input, cancel it to the exact rational
zero, and reassociate. -/
@[expose] def negation_respects (left right : CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name) :
    Law.Basic.BitLaw
      (CoherentNamed.neg left)
      (CoherentNamed.neg right) := by
  let leftNeg :=
    CoherentNamed.neg left
  let rightNeg :=
    CoherentNamed.neg right
  let zero := Coherence.exact 0
  let leftCross :=
    CoherentNamed.add leftNeg right
  have replaceRight : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        leftNeg left).name leftCross.name :=
    Congruence.coherentAdd_respects
      leftNeg leftNeg left right
      (NamedEquivalent.refl
        leftNeg.name) equivalent
  have cancelLeft : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        leftNeg left).name zero.name := by
    simpa only [leftNeg, zero,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_left left
  have crossZero : Gaussian.Equivalence.NamedEquivalent leftCross.name zero.name :=
    NamedEquivalent.trans
      (NamedEquivalent.symm
        replaceRight) cancelLeft
  have begin : Gaussian.Equivalence.NamedEquivalent leftNeg.name
      (CoherentNamed.add
        leftNeg zero).name :=
    NamedEquivalent.symm
      (Add.coherentAdd_zero_right leftNeg)
  have insertCancellation : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        leftNeg zero).name
      (CoherentNamed.add leftNeg
        (CoherentNamed.add
          right rightNeg)).name :=
    Congruence.coherentAdd_respects
      leftNeg leftNeg zero
      (CoherentNamed.add right rightNeg)
      (NamedEquivalent.refl
        leftNeg.name)
      (NamedEquivalent.symm
        (by
          simpa only [rightNeg, zero,
            CoherentNamed.add,
            CoherentNamed.neg,
            Coherence.exact] using
            Neg.coherentAdd_neg_right right))
  have reassociate : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add leftNeg
        (CoherentNamed.add
          right rightNeg)).name
      (CoherentNamed.add
        leftCross rightNeg).name := by
    exact NamedEquivalent.symm
      (by
        simpa only [leftCross,
          CoherentNamed.add] using
          Add.coherentAdd_assoc
            leftNeg right rightNeg)
  have replaceCross : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        leftCross rightNeg).name
      (CoherentNamed.add
        zero rightNeg).name :=
    Congruence.coherentAdd_respects
      leftCross zero rightNeg rightNeg crossZero
      (NamedEquivalent.refl
        rightNeg.name)
  have finish : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        zero rightNeg).name rightNeg.name := by
    simpa only [zero,
      CoherentNamed.add,
      Coherence.exact] using
      Add.coherentAdd_zero_left rightNeg
  exact BitLaw.ofEquivalent
    (NamedEquivalent.trans begin
      (NamedEquivalent.trans
        insertCancellation
        (NamedEquivalent.trans
          reassociate
          (NamedEquivalent.trans
            replaceCross finish))))

/-- Lift operational equivalence in both coherent operands to a subtraction law at the retained CCL-prefix interface. -/
@[expose] def subtraction_respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne.name rightTwo.name) :
    Law.Basic.BitLaw
      (CoherentNamed.sub leftOne rightOne)
      (CoherentNamed.sub leftTwo rightTwo) := by
  let negativeLaw := Approximation.Gaussian.Name.Coherent.Law.Arithmetic.negation_respects rightOne rightTwo
    rightEquivalent
  let additiveLaw := Approximation.Gaussian.Name.Coherent.Law.Arithmetic.addition_respects leftOne leftTwo
    (CoherentNamed.neg rightOne)
    (CoherentNamed.neg rightTwo)
    leftEquivalent negativeLaw.equivalent
  exact additiveLaw

/-- Lift operational equivalence in both coherent operands to a multiplication law at the retained CCL-prefix interface.
-/
@[expose] def multiplication_respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne.name rightTwo.name) :
    Law.Basic.BitLaw
      (CoherentNamed.mul leftOne rightOne)
      (CoherentNamed.mul leftTwo rightTwo) :=
  BitLaw.ofEquivalent
    (Congruence.coherentMul_respects
      leftOne leftTwo rightOne rightTwo leftEquivalent rightEquivalent)

/-- Coherent addition is commutative at the retained CCL-prefix interface. -/
@[expose] def addition_commutative (left right : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.add left right)
      (CoherentNamed.add right left) :=
  BitLaw.ofEquivalent (Add.coherentAdd_comm left right)

/-- Coherent addition is associative at the retained CCL-prefix interface. -/
@[expose] def addition_associative (left middle right : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.add
        (CoherentNamed.add left middle)
        right)
      (CoherentNamed.add left
        (CoherentNamed.add middle right)) :=
  BitLaw.ofEquivalent (Add.coherentAdd_assoc left middle right)

/-- Coherent multiplication is commutative at the retained CCL-prefix interface. -/
@[expose] def multiplication_commutative (left right : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.mul left right)
      (CoherentNamed.mul right left) :=
  BitLaw.ofEquivalent
    (Laws.coherentMul_comm left right)

/-- Coherent multiplication is associative at the retained CCL-prefix interface. -/
@[expose] def multiplication_associative (left middle right : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.mul
        (CoherentNamed.mul left middle)
        right)
      (CoherentNamed.mul left
        (CoherentNamed.mul middle right)) :=
  BitLaw.ofEquivalent
    (Laws.coherentMul_assoc
      left middle right)

/-- Coherent multiplication distributes over addition at the retained CCL-prefix interface. -/
@[expose] def multiplication_distributive (left middle right : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.mul left
        (CoherentNamed.add middle right))
      (CoherentNamed.add
        (CoherentNamed.mul left middle)
        (CoherentNamed.mul left right)) :=
  BitLaw.ofEquivalent (Distributive.coherentMul_add_left left middle right)

/-- Adding exact zero on the right preserves the original coherent name at the CCL-prefix interface. -/
@[expose] def additive_zero (input : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.add input
        (Coherence.exact 0)) input :=
  BitLaw.ofEquivalent (Add.coherentAdd_zero_right input)

/-- Adding a coherent name to its stateful negation gives exact zero at the CCL-prefix interface. -/
@[expose] def additive_inverse (input : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.add input
        (CoherentNamed.neg input))
      (Coherence.exact 0) :=
  BitLaw.ofEquivalent (Neg.coherentAdd_neg_right input)

/-- Multiplying by exact one on the right preserves the original coherent name at the CCL-prefix interface. -/
@[expose] def multiplicative_unit (input : CoherentNamed) :
    Law.Basic.BitLaw
      (CoherentNamed.mul input
        (Coherence.exact 1)) input :=
  BitLaw.ofEquivalent (Mul.coherentMul_one_right input)

end

end Purelib.Approximation.Gaussian.Name.Coherent.Law.Arithmetic

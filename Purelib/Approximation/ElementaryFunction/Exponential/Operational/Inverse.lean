module
import Purelib.Approximation.Gaussian.Arithmetic.Exact
import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Congruence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.ElementaryFunction.Exponential.Operational.Inverse

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

public section

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

open Purelib.Approximation

/-- The total CCL exponential of an additive inverse is a two-sided operational multiplicative inverse: this statement
only compares finite process observations and names the exact rational `1` explicitly. -/
@[expose] def automaticExp_neg_mul (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Exponential.Progressive.Range.Name.named
          (Named.neg input.name))
        (Exponential.Progressive.Range.Name.named input.name))
      (Named.exact 1) := by
  let negative := CoherentNamed.neg input
  let sum := CoherentNamed.add negative input
  let zero := Coherence.exact 0
  have sumZero : Gaussian.Equivalence.NamedEquivalent sum.name zero.name := by
    simpa only [sum, negative, zero, Coherence.exact,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherent.CoherentNamed.Coherence.exact] using
      Neg.coherentAdd_neg_left input
  exact NamedEquivalent.trans
    (Exponential.Progressive.Range.Addition.automaticExp_add negative input)
    (NamedEquivalent.trans
      (Exponential.Progressive.Range.Congruence.automaticExp_respects sum zero sumZero)
      Exponential.Progressive.Range.Exact.automaticExp_zero)

/-- The symmetric product order is operationally one as well. -/
@[expose] def automaticExp_mul_neg (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Exponential.Progressive.Range.Name.named input.name)
        (Exponential.Progressive.Range.Name.named
          (Named.neg input.name)))
      (Named.exact 1) := by
  let positiveExp := Exponential.Progressive.Range.Coherent.exp input.name
  let negativeExp :=
    Exponential.Progressive.Range.Coherent.exp
      (Named.neg input.name)
  exact NamedEquivalent.trans
    (by
      simpa only [positiveExp, negativeExp,
        Exponential.Progressive.Range.Coherent.exp] using
        Laws.coherentMul_comm positiveExp negativeExp)
    (Approximation.ElementaryFunction.Exponential.Operational.Inverse.automaticExp_neg_mul input)

/-- The total finite-request exponential cannot be operationally equivalent to the terminating exact zero name.

If it were, multiplication by the independently constructed `exp (-x)` process would make the exact finite names `0` and
`1` operationally equivalent. -/
theorem automaticExp_not_equivalent_zero (input : CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named input.name)
      (Named.exact 0) → False := by
  intro expZero
  let negative := CoherentNamed.neg input
  let negativeExp := Exponential.Progressive.Range.Coherent.exp negative.name
  let positiveExp := Exponential.Progressive.Range.Coherent.exp input.name
  let zero := Coherence.exact 0
  have productZero : Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        negativeExp.name positiveExp.name)
      (Named.exact 0) := by
    exact NamedEquivalent.trans
      (Congruence.coherentMul_respects negativeExp negativeExp positiveExp zero
        (NamedEquivalent.refl
          negativeExp.name)
        (by
          simpa only [positiveExp, zero, Coherence.exact,
            Exponential.Progressive.Range.Coherent.exp,
            Coherent.CoherentNamed.Coherence.exact] using
            expZero))
      (Mul.coherentMul_zero_right negativeExp)
  have productOne : Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        negativeExp.name positiveExp.name)
      (Named.exact 1) := by
    simpa only [negativeExp, positiveExp, negative,
      Exponential.Progressive.Range.Coherent.exp,
      CoherentNamed.neg] using
      Approximation.ElementaryFunction.Exponential.Operational.Inverse.automaticExp_neg_mul input
  exact Exact.exactZero_not_equivalent_exactOne
    (NamedEquivalent.trans
      (NamedEquivalent.symm productZero)
      productOne)

end

end Purelib.Approximation.ElementaryFunction.Exponential.Operational.Inverse

module

public import Purelib.Polynomial.Multivariate.Sparse
public import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Arithmetic.Distributive
import Purelib.Approximation.Gaussian.Coherent.Additive

/-!
# Operational interpretation of finite sparse Gaussian polynomials

The original finitely indexed coherent channels interpret the exponent vectors.
Every arithmetic certificate compares actual retained names by finite requests;
scalar equality of coherent process records is neither required nor asserted.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Coherent

namespace Monomial

/-- Interpret the exponent vector with the original coherent variable channels. -/
@[expose] def denote : {arity : Nat} → Monomial arity → (Fin arity → CoherentNamed) → CoherentNamed
  | 0, .nil, _ => Coherence.exact 1
  | _ + 1, .cons exponent tail, environment =>
      CoherentNamed.mul (Power.namedPower (environment 0) exponent)
        (denote tail (fun index => environment index.succ))

/-- The zero exponent vector is operationally the exact unit channel. -/
def denote_zero (arity : Nat) (environment : Fin arity → CoherentNamed) :
    NamedEquivalent (denote (zero arity) environment).name (Coherence.exact 1).name := by
  induction arity with
  | zero => exact NamedEquivalent.refl _
  | succ arity ih =>
      exact NamedEquivalent.trans
        (Mul.coherentMul_one_left (denote (zero arity) (fun index => environment index.succ)))
        (ih (fun index => environment index.succ))

/-- The degree-one exponent vector is operationally its original indexed channel. -/
def denote_atom (arity : Nat) (index : Fin arity) (environment : Fin arity → CoherentNamed) :
    NamedEquivalent (denote (atom arity index) environment).name (environment index).name := by
  induction arity with
  | zero => exact Fin.elim0 index
  | succ arity ih =>
      refine Fin.cases ?_ ?_ index
      · exact NamedEquivalent.trans
          (Product.Congruence.coherentMul_respects (Power.namedPower (environment 0) 1) (environment 0)
            (denote (zero arity) (fun index => environment index.succ)) (Coherence.exact 1)
            (Power.namedPower_one (environment 0)) (denote_zero arity _))
          (Mul.coherentMul_one_right (environment 0))
      · intro tailIndex
        exact NamedEquivalent.trans
          (Mul.coherentMul_one_left (denote (atom arity tailIndex) (fun index => environment index.succ)))
          (ih tailIndex (fun index => environment index.succ))

/-- Addition of exponent vectors is operational multiplication of the original monomial channels. -/
def denote_add : {arity : Nat} → (left right : Monomial arity) →
    (environment : Fin arity → CoherentNamed) →
    NamedEquivalent (denote (add left right) environment).name
      (CoherentNamed.mul (denote left environment) (denote right environment)).name
  | 0, .nil, .nil, _ => NamedEquivalent.symm (Mul.coherentMul_one_right (Coherence.exact 1))
  | _ + 1, .cons first tail, .cons second remaining, environment =>
      NamedEquivalent.trans
        (Product.Congruence.coherentMul_respects (Power.namedPower (environment 0) (first + second))
          (CoherentNamed.mul (Power.namedPower (environment 0) first) (Power.namedPower (environment 0) second))
          (denote (add tail remaining) (fun index => environment index.succ))
          (CoherentNamed.mul (denote tail (fun index => environment index.succ))
            (denote remaining (fun index => environment index.succ)))
          (Power.namedPower_add (environment 0) first second) (denote_add tail remaining _))
        (Product.Laws.coherentMul_interchange (Power.namedPower (environment 0) first)
          (Power.namedPower (environment 0) second) (denote tail (fun index => environment index.succ))
          (denote remaining (fun index => environment index.succ)))

/-- Monomial interpretation respects explicit pointwise comparisons of the original environments. -/
def denote_respects : {arity : Nat} → (monomial : Monomial arity) →
    (left right : Fin arity → CoherentNamed) →
    (∀ index, NamedEquivalent (left index).name (right index).name) →
    NamedEquivalent (denote monomial left).name (denote monomial right).name
  | 0, .nil, _, _, _ => NamedEquivalent.refl _
  | _ + 1, .cons exponent tail, left, right, equivalent =>
      Product.Congruence.coherentMul_respects (Power.namedPower (left 0) exponent)
        (Power.namedPower (right 0) exponent) (denote tail (fun index => left index.succ))
        (denote tail (fun index => right index.succ))
        (Power.namedPower_respects (left 0) (right 0) (equivalent 0) exponent)
        (denote_respects tail _ _ (fun index => equivalent index.succ))

end Monomial

namespace Term

/-- Interpret one coefficient and monomial with the retained original coherent channels. -/
@[expose] def denote {arity : Nat} (environment : Fin arity → CoherentNamed) (term : Term Gaussian arity) :
    CoherentNamed := CoherentNamed.mul (Coherence.exact term.coefficient) (term.monomial.denote environment)

/-- A term with exact zero coefficient is operationally exact zero. -/
def denote_zero {arity : Nat} (environment : Fin arity → CoherentNamed) (term : Term Gaussian arity)
    (zero : term.coefficient = 0) : NamedEquivalent (denote environment term).name (Coherence.exact 0).name := by
  unfold denote
  rewrite [zero]
  exact Mul.coherentMul_zero_left (term.monomial.denote environment)

/-- Multiplication of two retained terms preserves the original operational product. -/
def denote_product {arity : Nat} (environment : Fin arity → CoherentNamed)
    (left right : Term Gaussian arity) :
    NamedEquivalent
      (denote environment ⟨Monomial.add left.monomial right.monomial, left.coefficient * right.coefficient⟩).name
      (CoherentNamed.mul (denote environment left) (denote environment right)).name :=
  NamedEquivalent.trans
    (Product.Congruence.coherentMul_respects (Coherence.exact (left.coefficient * right.coefficient))
      (CoherentNamed.mul (Coherence.exact left.coefficient) (Coherence.exact right.coefficient))
      ((Monomial.add left.monomial right.monomial).denote environment)
      (CoherentNamed.mul (left.monomial.denote environment) (right.monomial.denote environment))
      (NamedEquivalent.symm (Exact.Arithmetic.exact_mul left.coefficient right.coefficient))
      (Monomial.denote_add left.monomial right.monomial environment))
    (Product.Laws.coherentMul_interchange (Coherence.exact left.coefficient) (Coherence.exact right.coefficient)
      (left.monomial.denote environment) (right.monomial.denote environment))

/-- Combining two coefficients of the same retained monomial preserves their operational sum. -/
def denote_combined {arity : Nat} (environment : Fin arity → CoherentNamed)
    (monomial : Monomial arity) (first second : Gaussian) :
    NamedEquivalent (denote environment ⟨monomial, first + second⟩).name
      (CoherentNamed.add (denote environment ⟨monomial, first⟩) (denote environment ⟨monomial, second⟩)).name :=
  NamedEquivalent.trans
    (Product.Congruence.coherentMul_respects (Coherence.exact (first + second))
      (CoherentNamed.add (Coherence.exact first) (Coherence.exact second))
      (monomial.denote environment) (monomial.denote environment)
      (NamedEquivalent.symm (Exact.Arithmetic.exact_add first second))
      (NamedEquivalent.refl (monomial.denote environment).name))
    (Distributive.coherentAdd_mul_right (Coherence.exact first) (Coherence.exact second)
      (monomial.denote environment))

/-- Term interpretation respects explicit pointwise comparisons of both original environments. -/
def denote_respects {arity : Nat} (term : Term Gaussian arity)
    (left right : Fin arity → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    NamedEquivalent (denote left term).name (denote right term).name :=
  Product.Congruence.coherentMul_respects (Coherence.exact term.coefficient) (Coherence.exact term.coefficient)
    (term.monomial.denote left) (term.monomial.denote right)
    (NamedEquivalent.refl _) (Monomial.denote_respects term.monomial left right equivalent)

/-- Negating a retained term coefficient gives its actual operational additive inverse. -/
def denote_negated {arity : Nat} (environment : Fin arity → CoherentNamed) (term : Term Gaussian arity) :
    NamedEquivalent (denote environment ⟨term.monomial, -term.coefficient⟩).name
      (CoherentNamed.neg (denote environment term)).name :=
  Mul.coherentMul_neg_left_constant term.coefficient (term.monomial.denote environment)

end Term

namespace Terms

/-- Interpret the original finite term list with coherent addition and exact zero. -/
@[expose] def denote {arity : Nat} (environment : Fin arity → CoherentNamed) : List (Term Gaussian arity) →
    CoherentNamed
  | [] => Coherence.exact 0
  | first :: remaining => CoherentNamed.add (first.denote environment) (denote environment remaining)

/-- Finite term-list interpretation respects the two retained environments' explicit comparisons. -/
def denote_respects {arity : Nat} (terms : List (Term Gaussian arity))
    (left right : Fin arity → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    NamedEquivalent (denote left terms).name (denote right terms).name := by
  induction terms with
  | nil => exact NamedEquivalent.refl _
  | cons first remaining ih =>
      exact Sum.Congruence.coherentAdd_respects (first.denote left) (first.denote right)
        (denote left remaining) (denote right remaining) (Term.denote_respects first left right equivalent) ih

/-- Canonical insertion preserves the operational sum of the inserted term and original list.

The coefficient-zero and cancellation branches retain exact zero comparisons;
sorting only composes the original associative and commutative sum laws. -/
def denote_insert {arity : Nat} (environment : Fin arity → CoherentNamed) (term : Term Gaussian arity)
    (terms : List (Term Gaussian arity)) :
    NamedEquivalent (denote environment (insert term terms)).name
      (CoherentNamed.add (term.denote environment) (denote environment terms)).name := by
  induction terms with
  | nil =>
      unfold insert
      split
      · rename_i zero
        exact NamedEquivalent.symm
          (NamedEquivalent.trans
            (Sum.Congruence.coherentAdd_respects (term.denote environment) (Coherence.exact 0)
              (Coherence.exact 0) (Coherence.exact 0) (term.denote_zero environment zero) (NamedEquivalent.refl _))
            (Add.coherentAdd_zero_left (Coherence.exact 0)))
      · exact NamedEquivalent.refl _
  | cons first remaining ih =>
      unfold insert
      split
      · rename_i zero
        exact NamedEquivalent.symm
          (NamedEquivalent.trans
            (Sum.Congruence.coherentAdd_respects (term.denote environment) (Coherence.exact 0)
              (denote environment (first :: remaining)) (denote environment (first :: remaining))
              (term.denote_zero environment zero) (NamedEquivalent.refl _))
            (Add.coherentAdd_zero_left (denote environment (first :: remaining))))
      · split
        · exact NamedEquivalent.refl _
        · split
          · rename_i same
            have combine := Term.denote_combined environment first.monomial term.coefficient first.coefficient
            split
            · rename_i cancel
              have vanishes := Term.denote_zero environment
                (⟨first.monomial, term.coefficient + first.coefficient⟩ : Term Gaussian arity) cancel
              have zeroPair := NamedEquivalent.trans (NamedEquivalent.symm combine) vanishes
              have dropPair := NamedEquivalent.trans
                (Sum.Congruence.coherentAdd_respects
                  (CoherentNamed.add (Term.denote environment ⟨first.monomial, term.coefficient⟩)
                    (Term.denote environment ⟨first.monomial, first.coefficient⟩)) (Coherence.exact 0)
                  (denote environment remaining) (denote environment remaining) zeroPair (NamedEquivalent.refl _))
                (Add.coherentAdd_zero_left (denote environment remaining))
              have result := NamedEquivalent.trans
                (NamedEquivalent.symm (Add.coherentAdd_assoc
                  (Term.denote environment ⟨first.monomial, term.coefficient⟩)
                  (Term.denote environment ⟨first.monomial, first.coefficient⟩) (denote environment remaining)))
                dropPair
              exact NamedEquivalent.symm
                (by simpa only [Term.denote, same, denote, CoherentNamed.add] using result)
            · have result := NamedEquivalent.trans
                (Sum.Congruence.coherentAdd_respects
                  (Term.denote environment ⟨first.monomial, term.coefficient + first.coefficient⟩)
                  (CoherentNamed.add (Term.denote environment ⟨first.monomial, term.coefficient⟩)
                    (Term.denote environment ⟨first.monomial, first.coefficient⟩))
                  (denote environment remaining) (denote environment remaining) combine (NamedEquivalent.refl _))
                (Add.coherentAdd_assoc (Term.denote environment ⟨first.monomial, term.coefficient⟩)
                  (Term.denote environment ⟨first.monomial, first.coefficient⟩) (denote environment remaining))
              simpa only [Term.denote, same, denote, CoherentNamed.add] using result
          · exact NamedEquivalent.trans
              (Sum.Congruence.coherentAdd_respects (first.denote environment) (first.denote environment)
                (denote environment (insert term remaining))
                (CoherentNamed.add (term.denote environment) (denote environment remaining))
                (NamedEquivalent.refl _) ih)
              (NamedEquivalent.trans
                (Additive.coherentAdd_swap_assoc (first.denote environment) (term.denote environment)
                  (denote environment remaining))
                (Add.coherentAdd_assoc (term.denote environment) (first.denote environment)
                  (denote environment remaining)))

/-- Accumulation preserves the operational sum of the original input and retained accumulator. -/
def denote_accumulate {arity : Nat} (environment : Fin arity → CoherentNamed)
    (input result : List (Term Gaussian arity)) :
    NamedEquivalent (denote environment (accumulate input result)).name
      (CoherentNamed.add (denote environment input) (denote environment result)).name := by
  induction input generalizing result with
  | nil => exact NamedEquivalent.symm (Add.coherentAdd_zero_left (denote environment result))
  | cons first remaining ih =>
      exact NamedEquivalent.trans (ih (insert first result))
        (NamedEquivalent.trans
          (Sum.Congruence.coherentAdd_respects (denote environment remaining) (denote environment remaining)
            (denote environment (insert first result))
            (CoherentNamed.add (first.denote environment) (denote environment result))
            (NamedEquivalent.refl _) (denote_insert environment first result))
          (Additive.coherentAdd_swap_assoc (denote environment remaining) (first.denote environment)
            (denote environment result)))

/-- Term convolution preserves the operational product and retained accumulator.

Every product occurrence uses the original term and its original remaining
input; canonical insertion consumes the same finite coefficient calculation. -/
def denote_multiplyTerm {arity : Nat} (environment : Fin arity → CoherentNamed)
    (term : Term Gaussian arity) (input result : List (Term Gaussian arity)) :
    NamedEquivalent (denote environment (multiplyTerm term input result)).name
      (CoherentNamed.add (CoherentNamed.mul (term.denote environment) (denote environment input))
        (denote environment result)).name := by
  induction input generalizing result with
  | nil =>
      exact NamedEquivalent.symm
        (NamedEquivalent.trans
          (Sum.Congruence.coherentAdd_respects (CoherentNamed.mul (term.denote environment) (Coherence.exact 0))
            (Coherence.exact 0) (denote environment result) (denote environment result)
            (Mul.coherentMul_zero_right (term.denote environment)) (NamedEquivalent.refl _))
          (Add.coherentAdd_zero_left (denote environment result)))
  | cons first remaining ih =>
      let productTerm : Term Gaussian arity :=
        ⟨Monomial.add term.monomial first.monomial, term.coefficient * first.coefficient⟩
      let headProduct := CoherentNamed.mul (term.denote environment) (first.denote environment)
      let tailProduct := CoherentNamed.mul (term.denote environment) (denote environment remaining)
      let resultValue := denote environment result
      have inserted : NamedEquivalent (denote environment (insert productTerm result)).name
          (CoherentNamed.add headProduct resultValue).name :=
        NamedEquivalent.trans (denote_insert environment productTerm result)
          (Sum.Congruence.coherentAdd_respects (productTerm.denote environment) headProduct resultValue resultValue
            (Term.denote_product environment term first) (NamedEquivalent.refl _))
      have combine : NamedEquivalent (CoherentNamed.add (CoherentNamed.add headProduct tailProduct) resultValue).name
          (CoherentNamed.add (CoherentNamed.mul (term.denote environment)
            (CoherentNamed.add (first.denote environment) (denote environment remaining))) resultValue).name :=
        Sum.Congruence.coherentAdd_respects (CoherentNamed.add headProduct tailProduct)
          (CoherentNamed.mul (term.denote environment)
            (CoherentNamed.add (first.denote environment) (denote environment remaining))) resultValue resultValue
          (NamedEquivalent.symm (Distributive.coherentMul_add_left (term.denote environment)
            (first.denote environment) (denote environment remaining))) (NamedEquivalent.refl _)
      exact NamedEquivalent.trans (ih (insert productTerm result))
        (NamedEquivalent.trans
          (Sum.Congruence.coherentAdd_respects tailProduct tailProduct
            (denote environment (insert productTerm result)) (CoherentNamed.add headProduct resultValue)
            (NamedEquivalent.refl _) inserted)
          (NamedEquivalent.trans (Additive.coherentAdd_swap_assoc tailProduct headProduct resultValue) combine))

/-- Complete finite convolution preserves the original operational polynomial product. -/
def denote_multiply {arity : Nat} (environment : Fin arity → CoherentNamed)
    (left right result : List (Term Gaussian arity)) :
    NamedEquivalent (denote environment (multiply left right result)).name
      (CoherentNamed.add (CoherentNamed.mul (denote environment left) (denote environment right))
        (denote environment result)).name := by
  induction left generalizing result with
  | nil =>
      exact NamedEquivalent.symm
        (NamedEquivalent.trans
          (Sum.Congruence.coherentAdd_respects (CoherentNamed.mul (Coherence.exact 0) (denote environment right))
            (Coherence.exact 0) (denote environment result) (denote environment result)
            (Mul.coherentMul_zero_left (denote environment right)) (NamedEquivalent.refl _))
          (Add.coherentAdd_zero_left (denote environment result)))
  | cons first remaining ih =>
      let headProduct := CoherentNamed.mul (first.denote environment) (denote environment right)
      let tailProduct := CoherentNamed.mul (denote environment remaining) (denote environment right)
      let resultValue := denote environment result
      have combine : NamedEquivalent (CoherentNamed.add (CoherentNamed.add headProduct tailProduct) resultValue).name
          (CoherentNamed.add (CoherentNamed.mul
            (CoherentNamed.add (first.denote environment) (denote environment remaining))
            (denote environment right)) resultValue).name :=
        Sum.Congruence.coherentAdd_respects (CoherentNamed.add headProduct tailProduct)
          (CoherentNamed.mul (CoherentNamed.add (first.denote environment) (denote environment remaining))
            (denote environment right)) resultValue resultValue
          (NamedEquivalent.symm (Distributive.coherentAdd_mul_right (first.denote environment)
            (denote environment remaining) (denote environment right))) (NamedEquivalent.refl _)
      exact NamedEquivalent.trans (ih (multiplyTerm first right result))
        (NamedEquivalent.trans
          (Sum.Congruence.coherentAdd_respects tailProduct tailProduct
            (denote environment (multiplyTerm first right result)) (CoherentNamed.add headProduct resultValue)
            (NamedEquivalent.refl _) (denote_multiplyTerm environment first right result))
          (NamedEquivalent.trans (Additive.coherentAdd_swap_assoc tailProduct headProduct resultValue) combine))

/-- Negating the finite coefficient list preserves actual operational negation of its retained sum. -/
def denote_negated {arity : Nat} (environment : Fin arity → CoherentNamed)
    (terms : List (Term Gaussian arity)) :
    NamedEquivalent (denote environment (terms.map (fun term => ⟨term.monomial, -term.coefficient⟩))).name
      (CoherentNamed.neg (denote environment terms)).name := by
  induction terms with
  | nil => exact Additive.zero_equivalent_neg_zero
  | cons first remaining ih =>
      let head := first.denote environment
      let tail := denote environment remaining
      let negativeHead := Term.denote environment ⟨first.monomial, -first.coefficient⟩
      let negativeTail := denote environment (remaining.map (fun term => ⟨term.monomial, -term.coefficient⟩))
      have headLaw : NamedEquivalent negativeHead.name (CoherentNamed.neg head).name :=
        Term.denote_negated environment first
      have tailLaw : NamedEquivalent negativeTail.name (CoherentNamed.neg tail).name := ih
      have replace : NamedEquivalent (CoherentNamed.add negativeHead negativeTail).name
          (CoherentNamed.add (CoherentNamed.neg head) (CoherentNamed.neg tail)).name :=
        Sum.Congruence.coherentAdd_respects negativeHead (CoherentNamed.neg head)
          negativeTail (CoherentNamed.neg tail) headLaw tailLaw
      have combine : NamedEquivalent
          (CoherentNamed.add (CoherentNamed.neg head) (CoherentNamed.neg tail)).name
          (CoherentNamed.neg (CoherentNamed.add head tail)).name := Additive.coherentNeg_add head tail
      exact NamedEquivalent.trans replace combine

end Terms

namespace Sparse

/-- Interpret the canonical term list using the original retained Gaussian channels. -/
@[expose] def denote {arity : Nat} (environment : Fin arity → CoherentNamed) (polynomial : Sparse Gaussian arity) :
    CoherentNamed := Terms.denote environment polynomial.terms

/-- Canonicalizing an arbitrary finite term list preserves its original operational sum. -/
def denote_ofTerms {arity : Nat} (environment : Fin arity → CoherentNamed) (terms : List (Term Gaussian arity)) :
    NamedEquivalent (denote environment (ofTerms terms)).name (Terms.denote environment terms).name :=
  NamedEquivalent.trans (Terms.denote_accumulate environment terms [])
    (Add.coherentAdd_zero_right (Terms.denote environment terms))

/-- A canonical scalar polynomial is operationally its retained exact Gaussian coefficient. -/
def denote_constant {arity : Nat} (environment : Fin arity → CoherentNamed) (value : Gaussian) :
    NamedEquivalent (denote environment (constant value)).name (Coherence.exact value).name :=
  NamedEquivalent.trans (denote_ofTerms environment [⟨Monomial.zero arity, value⟩])
    (NamedEquivalent.trans (Add.coherentAdd_zero_right (Term.denote environment ⟨Monomial.zero arity, value⟩))
      (NamedEquivalent.trans
        (Product.Congruence.coherentMul_respects (Coherence.exact value) (Coherence.exact value)
          ((Monomial.zero arity).denote environment) (Coherence.exact 1)
          (NamedEquivalent.refl _) (Monomial.denote_zero arity environment))
        (Mul.coherentMul_one_right (Coherence.exact value))))

/-- A canonical degree-one polynomial is operationally the original indexed Gaussian channel. -/
def denote_atom {arity : Nat} (environment : Fin arity → CoherentNamed) (index : Fin arity) :
    NamedEquivalent (denote environment (atom index)).name (environment index).name :=
  NamedEquivalent.trans (denote_ofTerms environment [⟨Monomial.atom arity index, 1⟩])
    (NamedEquivalent.trans (Add.coherentAdd_zero_right (Term.denote environment ⟨Monomial.atom arity index, 1⟩))
      (NamedEquivalent.trans (Mul.coherentMul_one_left ((Monomial.atom arity index).denote environment))
        (Monomial.denote_atom arity index environment)))

/-- Canonical addition preserves the original two operational polynomial readings. -/
def denote_add {arity : Nat} (environment : Fin arity → CoherentNamed) (left right : Sparse Gaussian arity) :
    NamedEquivalent (denote environment (add left right)).name
      (CoherentNamed.add (denote environment left) (denote environment right)).name :=
  Terms.denote_accumulate environment left.terms right.terms

/-- Canonical coefficient negation preserves actual negation of the retained polynomial channel. -/
def denote_neg {arity : Nat} (environment : Fin arity → CoherentNamed) (input : Sparse Gaussian arity) :
    NamedEquivalent (denote environment (neg input)).name (CoherentNamed.neg (denote environment input)).name := by
  let negativeTerms : List (Term Gaussian arity) :=
    input.terms.map (fun term => ⟨term.monomial, -term.coefficient⟩)
  have normalized := denote_ofTerms environment negativeTerms
  have negative := Terms.denote_negated environment input.terms
  exact NamedEquivalent.trans normalized negative

/-- Canonical subtraction preserves the actual operational difference of both retained inputs. -/
def denote_sub {arity : Nat} (environment : Fin arity → CoherentNamed) (left right : Sparse Gaussian arity) :
    NamedEquivalent (denote environment (sub left right)).name
      (CoherentNamed.add (denote environment left) (CoherentNamed.neg (denote environment right))).name :=
  NamedEquivalent.trans (denote_add environment left (neg right))
    (Sum.Congruence.coherentAdd_respects (denote environment left) (denote environment left)
      (denote environment (neg right)) (CoherentNamed.neg (denote environment right))
      (NamedEquivalent.refl _) (denote_neg environment right))

/-- Complete canonical convolution preserves the actual product of both original polynomial channels. -/
def denote_mul {arity : Nat} (environment : Fin arity → CoherentNamed) (left right : Sparse Gaussian arity) :
    NamedEquivalent (denote environment (mul left right)).name
      (CoherentNamed.mul (denote environment left) (denote environment right)).name :=
  NamedEquivalent.trans (Terms.denote_multiply environment left.terms right.terms [])
    (Add.coherentAdd_zero_right (CoherentNamed.mul (denote environment left) (denote environment right)))

/-- Canonical finite powers preserve the original operational repeated-multiplication channel. -/
def denote_pow {arity : Nat} (environment : Fin arity → CoherentNamed) (input : Sparse Gaussian arity) :
    (exponent : Nat) → NamedEquivalent (denote environment (pow input exponent)).name
      (Power.namedPower (denote environment input) exponent).name
  | 0 => denote_constant environment 1
  | exponent + 1 => NamedEquivalent.trans (denote_mul environment input (pow input exponent))
      (NamedEquivalent.trans
        (Product.Congruence.coherentMul_respects (denote environment input) (denote environment input)
          (denote environment (pow input exponent)) (Power.namedPower (denote environment input) exponent)
          (NamedEquivalent.refl _) (denote_pow environment input exponent))
        (Product.Laws.coherentMul_comm (denote environment input)
          (Power.namedPower (denote environment input) exponent)))

/-- Equal retained canonical forms give a comparison of their original operational interpretations. -/
def denote_of_terms_eq {arity : Nat} (environment : Fin arity → CoherentNamed)
    {left right : Sparse Gaussian arity} (same : left.terms = right.terms) :
    NamedEquivalent (denote environment left).name (denote environment right).name := by
  unfold denote
  rewrite [same]
  exact NamedEquivalent.refl _

/-- Sparse interpretation transports explicit pointwise comparisons between the original environments. -/
def denote_respects {arity : Nat} (polynomial : Sparse Gaussian arity)
    (left right : Fin arity → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (left index).name (right index).name) :
    NamedEquivalent (denote left polynomial).name (denote right polynomial).name :=
  Terms.denote_respects polynomial.terms left right equivalent

end Sparse

end Purelib.Polynomial.Multivariate

end

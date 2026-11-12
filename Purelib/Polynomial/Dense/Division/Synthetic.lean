module
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.GetD

import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Synthetic division of descending ring coefficients

The original recurrence retains the leading coefficient as the next quotient
entry and propagates its value at the displayed root. The final scalar is the
same Horner remainder, with a pointwise linear-factor evaluation certificate.
-/

open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Division.Synthetic

variable {K : Type*} [CommRing K]

/-- Compute the synthetic quotient and remainder for a descending ring coefficient list.

The original leading coefficient is retained as each quotient entry.
The same root propagates the next leading value along the original tail,
and the final scalar is the retained Horner remainder. -/
@[expose] public def syntheticAux (root leading : K) :
    List K → List K × K
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := Synthetic.syntheticAux root (leading * root +
        coefficient) remaining
      (leading :: result.1, result.2)

/-- Certify the original synthetic quotient length, remainder and linear-factor identity.

The retained quotient has exactly the original tail length. Its remainder
is evaluation at the supplied root, and each displayed argument evaluates
the original list as the same linear factor times quotient plus remainder. -/
public theorem syntheticAux_spec (root leading : K)
    (remaining : List K) :
    let result := syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = Basic.DensePolynomial.evalCoeffs root (leading :: remaining) ∧
      ∀ x : K,
        Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
          (x - root) * Basic.DensePolynomial.evalCoeffs x result.1 + result.2 := by
  induction remaining generalizing leading with
  | nil =>
      constructor
      · rfl
      constructor
      · change leading = Basic.DensePolynomial.evalCoeffs root [leading]
        rw [Basic.DensePolynomial.evalCoeffs_cons]
        rfl
      · intro x
        change Basic.DensePolynomial.evalCoeffs x [leading] =
          (x - root) * Basic.DensePolynomial.evalCoeffs x [] + leading
        rw [Basic.DensePolynomial.evalCoeffs_cons,
          Basic.DensePolynomial.evalCoeffs_nil, mul_zero, zero_add]
        rfl
  | cons coefficient remaining inductionHypothesis =>
      let nextLeading := leading * root + coefficient
      let recursive := syntheticAux root nextLeading remaining
      have recursiveSpec := inductionHypothesis nextLeading
      change recursive.1.length = remaining.length ∧
        recursive.2 = Basic.DensePolynomial.evalCoeffs root (nextLeading :: remaining) ∧
        ∀ x : K,
          Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) =
            (x - root) * Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 =
            Basic.DensePolynomial.evalCoeffs root (leading :: coefficient :: remaining) ∧
          ∀ x : K,
            Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              (x - root) * Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2
      constructor
      · simp only [List.length_cons]
        exact congrArg Nat.succ recursiveSpec.1
      constructor
      · rw [Basic.DensePolynomial.evalCoeffs_cons]
        simp only [List.foldl_cons]
        rw [← Basic.DensePolynomial.evalCoeffs_cons root nextLeading remaining]
        exact recursiveSpec.2.1
      · intro x
        have recursiveFactor := recursiveSpec.2.2 x
        calc
          Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              leading * x ^ (remaining.length + 1) +
                coefficient * x ^ remaining.length +
                Basic.DensePolynomial.evalCoeffs x remaining := by
            rw [Basic.DensePolynomial.evalCoeffs_cons_expansion x leading (coefficient :: remaining),
              Basic.DensePolynomial.evalCoeffs_cons_expansion x coefficient remaining]
            simp only [List.length_cons]
            ring0
          _ = (x - root) * (leading * x ^ remaining.length) +
                Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) := by
            rw [Basic.DensePolynomial.evalCoeffs_cons_expansion x nextLeading remaining, pow_succ]
            dsimp only [nextLeading]
            ring0
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2) := by
            rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  Basic.DensePolynomial.evalCoeffs x recursive.1) + recursive.2 := by
            ring0
          _ = (x - root) * Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [Basic.DensePolynomial.evalCoeffs_cons_expansion, recursiveSpec.1]

/-- Reassemble a descending source table from its synthetic quotient and remainder.

Each retained quotient coefficient supplies one original leading slot. The
next quotient coefficient, or the final remainder, loses the previous root
multiple. The complete retained tail is computed once at each structural step.
-/
@[expose] public def reassemble (root : K) : List K → K → List K
  | [], remainder => [remainder]
  | leading :: remaining, remainder =>
      let retained := reassemble root remaining remainder
      leading :: (retained.headD 0 - leading * root) :: retained.tail

/-- Reassembly always retains the final remainder slot, even for an empty quotient. -/
public theorem reassemble_nonempty (root : K) (quotient : List K) (remainder : K) :
    reassemble root quotient remainder ≠ [] := by
  cases quotient <;> intro equal <;> cases equal

/-- Reassembly has exactly one more coefficient slot than its original quotient. -/
public theorem reassemble_length (root : K) (quotient : List K) (remainder : K) :
    (reassemble root quotient remainder).length = quotient.length + 1 := by
  induction quotient with
  | nil => rfl
  | cons leading remaining previous =>
      cases shape : reassemble root remaining remainder with
      | nil => exact False.elim (reassemble_nonempty root remaining remainder shape)
      | cons coefficient tail =>
          rewrite [shape] at previous
          change (leading ::
            ((reassemble root remaining remainder).headD 0 - leading * root) ::
            (reassemble root remaining remainder).tail).length = _
          rewrite [shape]
          exact congrArg Nat.succ previous

/-- Reassembling the original synthetic scan recovers every source coefficient literally. -/
public theorem reassemble_syntheticAux (root leading : K) (remaining : List K) :
    reassemble root (syntheticAux root leading remaining).1
      (syntheticAux root leading remaining).2 = leading :: remaining := by
  induction remaining generalizing leading with
  | nil => rfl
  | cons coefficient remaining previous =>
      change leading ::
          ((reassemble root (syntheticAux root (leading * root + coefficient) remaining).1
            (syntheticAux root (leading * root + coefficient) remaining).2).headD 0 - leading * root) ::
          (reassemble root (syntheticAux root (leading * root + coefficient) remaining).1
            (syntheticAux root (leading * root + coefficient) remaining).2).tail = _
      rewrite [previous (leading * root + coefficient)]
      change leading :: ((leading * root + coefficient - leading * root) :: remaining) = _
      exact congrArg (List.cons leading) (congrArg (fun value => value :: remaining) (by ring0))

set_option genInjectivity false in
/-- A retained synthetic quotient and Horner remainder for the original polynomial and root.

The exact coefficient count and pointwise linear-factor reconstruction hold
over a commutative ring, including rings with zero divisors. No leading
coefficient is inverted and no polynomial representative is normalized.
-/
public structure Result (polynomial : Basic.DensePolynomial K) (root : K) where
  /-- The actual retained descending quotient coefficients. -/
  quotient : Basic.DensePolynomial K
  /-- The same synthetic scan's final scalar accumulator. -/
  remainder : K
  /-- Synthetic division removes exactly one coefficient slot when the source is nonempty. -/
  quotient_length : quotient.coeffs.length = polynomial.coeffs.length - 1
  /-- The actual quotient and remainder recover every original coefficient, including the empty-source case. -/
  coefficient_reconstruction : polynomial.coeffs =
    if polynomial.coeffs.isEmpty then [] else reassemble root quotient.coeffs remainder
  /-- The same retained remainder is the original source's Horner reading at the root. -/
  remainder_eval : remainder = polynomial.eval root
  /-- Every supplied point reconstructs the source from the retained quotient and remainder. -/
  eval_eq : ∀ point, polynomial.eval point = (point - root) * quotient.eval point + remainder

constructive_injectivity Result

/-- A nonempty original source is recovered literally from its same retained quotient and remainder. -/
public theorem Result.reassemble_eq {polynomial : Basic.DensePolynomial K} {root : K}
    (result : Result polynomial root) (nonempty : polynomial.coeffs ≠ []) :
    reassemble root result.quotient.coeffs result.remainder = polynomial.coeffs := by
  cases source : polynomial.coeffs with
  | nil => exact False.elim (nonempty source)
  | cons leading remaining =>
      have retained := result.coefficient_reconstruction
      rewrite [source] at retained
      exact retained.symm

/-- Construct a certified root inverse from the same quotient and an inverse of the original constant reading.

The retained quotient is evaluated at zero once. Its negative constant
reading times the supplied constant inverse is the returned scalar, whose
unit equation follows from the same original division certificate.
-/
@[expose] public def Result.rootInverse {polynomial : Basic.DensePolynomial K} {root : K}
    (result : Result polynomial root) (remainderZero : result.remainder = 0)
    (constantInverse : K) (constantUnit : polynomial.eval 0 * constantInverse = 1) :
    {inverse : K // root * inverse = 1} :=
  let quotientZero := result.quotient.eval 0
  let inverse := -quotientZero * constantInverse
  ⟨inverse, by
    have reconstruction := result.eval_eq 0
    rewrite [remainderZero] at reconstruction
    calc
      root * inverse = polynomial.eval 0 * constantInverse := by
        rewrite [reconstruction]
        dsimp only [inverse, quotientZero]
        ring0
      _ = 1 := constantUnit⟩

/-- A normalized positive-degree source retains its leading slot in the same actual quotient. -/
public theorem Result.quotient_shape [DecidableEq K] {polynomial : Basic.DensePolynomial K} {root : K}
    (result : Result polynomial root) (normalized : polynomial.normalize = polynomial)
    (positive : 0 < polynomial.natDegree) :
    ∃ tail, result.quotient.coeffs = polynomial.leadingCoeff :: tail ∧ tail.length + 1 = polynomial.natDegree := by
  have count : result.quotient.coeffs.length = polynomial.natDegree := by
    apply result.quotient_length.trans
    change polynomial.coeffs.length - 1 = polynomial.normalize.coeffs.length - 1
    rewrite [normalized]
    rfl
  have nonempty : polynomial.coeffs ≠ [] := by
    intro empty
    have impossible := positive
    change 0 < polynomial.normalize.coeffs.length - 1 at impossible
    rewrite [normalized, empty] at impossible
    exact Nat.not_lt_zero 0 impossible
  cases shape : result.quotient.coeffs with
  | nil =>
      rewrite [shape] at count
      have zero : polynomial.natDegree = 0 := count.symm
      exact False.elim (Nat.not_lt_zero 0 (zero ▸ positive))
  | cons leading tail =>
      have recovery := result.reassemble_eq nonempty
      have heads := congrArg (fun coefficients : List K => coefficients.headD 0) recovery
      rewrite [shape] at heads
      change leading = polynomial.coeffs.headD 0 at heads
      have originalHead : polynomial.leadingCoeff = polynomial.coeffs.headD 0 := by
        change polynomial.normalize.coeffs.headD 0 = polynomial.coeffs.headD 0
        rewrite [normalized]
        rfl
      refine ⟨tail, congrArg (fun value => value :: tail) (heads.trans originalHead.symm), ?_⟩
      rewrite [shape] at count
      exact count

/-- The actual quotient of a normalized positive-degree source is already normalized. -/
public theorem Result.quotient_normalized [DecidableEq K] {polynomial : Basic.DensePolynomial K} {root : K}
    (result : Result polynomial root) (normalized : polynomial.normalize = polynomial)
    (positive : 0 < polynomial.natDegree) (leadingNonzero : polynomial.leadingCoeff ≠ 0) :
    result.quotient.normalize = result.quotient := by
  obtain ⟨tail, shape, _⟩ := result.quotient_shape normalized positive
  apply Basic.DensePolynomial.ext
  change result.quotient.coeffs.dropWhile (· = 0) = result.quotient.coeffs
  rewrite [shape, Purelib.Data.List.DropWhile.cons_of_false
    (fun value : K => decide (value = 0)) polynomial.leadingCoeff tail (decide_eq_false leadingNonzero)]
  rfl

/-- The same quotient retains the original leading coefficient without inverting any scalar. -/
public theorem Result.quotient_leadingCoeff [DecidableEq K] {polynomial : Basic.DensePolynomial K} {root : K}
    (result : Result polynomial root) (normalized : polynomial.normalize = polynomial)
    (positive : 0 < polynomial.natDegree) (leadingNonzero : polynomial.leadingCoeff ≠ 0) :
    result.quotient.leadingCoeff = polynomial.leadingCoeff := by
  obtain ⟨tail, shape, _⟩ := result.quotient_shape normalized positive
  change result.quotient.normalize.coeffs.headD 0 = polynomial.leadingCoeff
  rewrite [result.quotient_normalized normalized positive leadingNonzero, shape]
  rfl

/-- The same quotient lowers the original natural degree by exactly one. -/
public theorem Result.quotient_degree [DecidableEq K] {polynomial : Basic.DensePolynomial K} {root : K}
    (result : Result polynomial root) (normalized : polynomial.normalize = polynomial)
    (positive : 0 < polynomial.natDegree) (leadingNonzero : polynomial.leadingCoeff ≠ 0) :
    result.quotient.natDegree + 1 = polynomial.natDegree := by
  obtain ⟨tail, shape, count⟩ := result.quotient_shape normalized positive
  change (result.quotient.normalize.coeffs.length - 1) + 1 = polynomial.natDegree
  rewrite [result.quotient_normalized normalized positive leadingNonzero, shape]
  exact count

/-- Divide once by the displayed monic linear factor and retain its certified quotient and remainder.

The source list supplies the initial Horner coefficient and each later scan
step. Both reconstruction certificates consume that same retained result.
-/
@[expose] public def divide (polynomial : Basic.DensePolynomial K) (root : K) : Result polynomial root :=
  match source : polynomial.coeffs with
  | [] =>
      { quotient := ⟨[]⟩
        remainder := 0
        quotient_length := by rewrite [source]; rfl
        coefficient_reconstruction := by rewrite [source]; rfl
        remainder_eval := by change 0 = Basic.DensePolynomial.evalCoeffs root polynomial.coeffs; rewrite [source]; rfl
        eval_eq := by
          intro point
          change Basic.DensePolynomial.evalCoeffs point polynomial.coeffs = (point - root) * 0 + 0
          rewrite [source, Basic.DensePolynomial.evalCoeffs_nil, mul_zero, add_zero]
          rfl }
  | leading :: remaining =>
      let retained := syntheticAux root leading remaining
      have certificate := syntheticAux_spec root leading remaining
      { quotient := ⟨retained.1⟩
        remainder := retained.2
        quotient_length := by rewrite [source]; exact certificate.1
        coefficient_reconstruction := by
          rewrite [source]
          exact (reassemble_syntheticAux root leading remaining).symm
        remainder_eval := by
          change retained.2 = Basic.DensePolynomial.evalCoeffs root polynomial.coeffs
          rewrite [source]
          exact certificate.2.1
        eval_eq := by
          intro point
          change Basic.DensePolynomial.evalCoeffs point polynomial.coeffs =
            (point - root) * Basic.DensePolynomial.evalCoeffs point retained.1 + retained.2
          rewrite [source]
          exact certificate.2.2 point }

/-- A nonconstant displayed source retains its leading coefficient as the first quotient coefficient.

The quotient tail is the actual next synthetic scan on the propagated leading
accumulator. The identity retains the original coefficient order.
-/
public theorem divide_cons_cons (root leading coefficient : K) (remaining : List K) :
    (divide ⟨leading :: coefficient :: remaining⟩ root).quotient.coeffs =
      leading :: (divide ⟨(leading * root + coefficient) :: remaining⟩ root).quotient.coeffs := rfl

open Purelib.Data.List (getD)

/-- Every actual quotient slot is the original Horner reading of its same source prefix. -/
private theorem syntheticAux_getD (root : K) : ∀ (remaining : List K) (leading : K)
    (index : Fin remaining.length),
    getD (syntheticAux root leading remaining).1 index.val 0 =
      Basic.DensePolynomial.evalCoeffs root ((leading :: remaining).take (index.val + 1)) := by
  intro remaining
  induction remaining with
  | nil => intro leading index; exact Fin.elim0 index
  | cons coefficient remaining previous =>
      intro leading index
      cases index with
      | mk index bound =>
          cases index with
          | zero =>
              change leading = Basic.DensePolynomial.evalCoeffs root [leading]
              rewrite [Basic.DensePolynomial.evalCoeffs_cons]
              rfl
          | succ index =>
              have retained := previous (leading * root + coefficient)
                ⟨index, Nat.lt_of_succ_lt_succ bound⟩
              change getD (syntheticAux root (leading * root + coefficient) remaining).1 index 0 =
                Basic.DensePolynomial.evalCoeffs root (leading :: coefficient :: remaining.take index)
              have prefixEq : Basic.DensePolynomial.evalCoeffs root
                  (leading :: coefficient :: remaining.take index) =
                  Basic.DensePolynomial.evalCoeffs root ((leading * root + coefficient) :: remaining.take index) := by
                rewrite [Basic.DensePolynomial.evalCoeffs_cons root leading,
                  Basic.DensePolynomial.evalCoeffs_cons root (leading * root + coefficient)]
                rfl
              exact retained.trans prefixEq.symm

/-- A bounded coefficient of the original quotient is its original source-prefix Horner evaluation.

Slot `j` uses exactly the first `j+1` descending source coefficients. The
source remainder is excluded, so every prefix stays within the source degree
when its original coefficient table is normalized.
-/
public theorem quotient_getD_eq_eval_take (polynomial : Basic.DensePolynomial K) (root : K)
    (index : Fin (polynomial.coeffs.length - 1)) :
    getD (divide polynomial root).quotient.coeffs index.val 0 =
      Basic.DensePolynomial.evalCoeffs root (polynomial.coeffs.take (index.val + 1)) := by
  cases polynomial with
  | mk coefficients =>
      cases coefficients with
      | nil => exact Fin.elim0 index
      | cons leading remaining => exact syntheticAux_getD root remaining leading index

end Purelib.Polynomial.Dense.Division.Synthetic

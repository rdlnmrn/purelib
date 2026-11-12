module
import Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
import Purelib.Data.List.Reverse
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
public import Purelib.Polynomial.Dense.Bivariate.Resultant
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Polynomial.Dense.Leading

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Bivariate.Basic

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Gaussian.Basic

open Purelib.Data

open Purelib.Polynomial

public section

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Shape

/-! ## Finite leading-term invariant -/

/-- The triangular parameter-degree invariant of an ascending reflected coefficient table.

The table has degree plus one entries; its head has the exact leading term, while all later coefficients have strictly
smaller parameter degree. -/
structure ReflectedShape (coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial)
    (degree : Nat) (leading : Canonical) : Prop where
  /-- The retained ascending coefficient table has exactly degree plus one entries. -/ length_eq : coefficients.length =
    degree + 1
  /-- The constant outer coefficient has the retained exact parameter degree and leader. -/ headLeading :
    Leading.LeadingTerm (coefficients.headD 0) degree leading
  /-- Every later outer coefficient has strictly smaller parameter degree. -/ tailBelow : ∀ coefficient ∈
    coefficients.tail,
    Leading.DegreeBelow coefficient degree

namespace ReflectedShape

/-- Transport a finite reflected-shape certificate across its three
displayed parameters without generated congruence for the predicate. -/
theorem of_equal {coefficients otherCoefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial}
    {degree otherDegree : Nat} {leading otherLeading : Canonical}
    (coefficientsEqual : coefficients = otherCoefficients)
    (degreeEqual : degree = otherDegree)
    (leadingEqual : leading = otherLeading)
    (shape : ReflectedShape otherCoefficients otherDegree otherLeading) :
    ReflectedShape coefficients degree leading := by
  cases coefficientsEqual
  cases degreeEqual
  cases leadingEqual
  exact shape

end ReflectedShape

/-- The reflected tail step adds one coefficient to its ascending input list. -/
private theorem reflectedTailStep_length (previous : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    ∀ coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial,
      (Basic.SeparatedVariables.reflectedTailStep previous coefficients).length =
        coefficients.length + 1
  | [] => rfl
  | _ :: remaining => by
      simp only [Basic.SeparatedVariables.reflectedTailStep, List.length_cons]
      rw [reflectedTailStep_length]

/-- A reflected tail step keeps its coefficients below the next parameter degree.

The retained predecessor has the supplied weak bound, and every original tail
entry has its strict bound. Each same-occurrence product and difference inherits
its resulting strict bound through the finite recursive tail. -/
private theorem reflectedTailStep_below
    {degree : Nat} {previous : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (previousBound : Leading.DegreeAtMost previous degree) :
    ∀ coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial,
      (∀ coefficient ∈ coefficients, Leading.DegreeBelow coefficient degree) →
      ∀ output ∈ Basic.SeparatedVariables.reflectedTailStep previous coefficients,
        Leading.DegreeBelow output (degree + 1)
  | [], _, output, membership => by
      change output ∈ [-previous] at membership
      have equal := Data.List.Membership.mem_singleton.mp membership
      cases equal
      exact Leading.DegreeBelow.neg previousBound.toBelowSucc
  | current :: remaining, bounded, output, membership => by
      change output ∈
        (Multiplication.Coordinate.SeparatedVariables.twiceShift current - previous) ::
          Basic.SeparatedVariables.reflectedTailStep current remaining at membership
      rcases Data.List.Membership.mem_cons.mp membership with first | later
      · subst output
        apply Leading.DegreeBelow.sub
        · exact Leading.DegreeBelow.mono
            (Leading.DegreeBelow.atMostMul Dense.Gaussian.Coefficients.Constants.twiceParameter_leading.atMost
              (bounded current List.mem_cons_self))
            (Nat.le_of_eq (Nat.add_comm 1 degree))
        · exact previousBound.toBelowSucc
      · exact reflectedTailStep_below
          (bounded current (List.mem_cons_self)).toAtMost remaining
          (fun coefficient member => bounded coefficient
            (List.mem_cons_of_mem _ member)) output later

/-- A reflected Horner step raises its degree and doubles its leading scalar.

The original head leading term and strictly smaller tail coefficients certify
the same updated finite table. Its first entry retains the supplied Gaussian
constant correction and doubled parameter product. -/
theorem reflectedStep_shape
    {coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial} {degree : Nat}
    {leading : Canonical} (shape : ReflectedShape coefficients degree leading)
    (coefficient : Canonical) :
    ReflectedShape (Basic.SeparatedVariables.reflectedStep coefficients coefficient)
      (degree + 1)
      (2 * leading) := by
  cases coefficients with
  | nil =>
      have impossible : 0 = degree + 1 := shape.length_eq
      change 0 = Nat.succ degree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      have headLeading : Leading.LeadingTerm head degree leading :=
        shape.headLeading
      have headBound := headLeading.atMost
      have tailBound : ∀ polynomial ∈ tail,
          Leading.DegreeBelow polynomial degree := shape.tailBelow
      refine
        { length_eq := ?_
          headLeading := ?_
          tailBelow := ?_ }
      · simp only [Basic.SeparatedVariables.reflectedStep, List.length_cons,
          reflectedTailStep_length]
        simpa only [List.length_cons] using congrArg Nat.succ shape.length_eq
      · change Leading.LeadingTerm
          (Multiplication.Coordinate.SeparatedVariables.twiceShift head -
            Coefficients.Constants.SeparatedVariables.parameterConstant (-Canonical.conj
            coefficient))
          (degree + 1) (2 * leading)
        apply Leading.LeadingTerm.subBelow
        · exact Leading.LeadingTerm.of_equal rfl (Nat.add_comm degree 1) rfl
            (Leading.LeadingTerm.mul Coefficients.Constants.twiceParameter_leading headLeading)
        · exact Leading.DegreeBelow.mono
            (Coefficients.Constants.parameterConstant_atMost (-Canonical.conj
              coefficient)).toBelowSucc
            (Nat.succ_le_succ (Nat.zero_le degree))
      · exact reflectedTailStep_below headBound tail tailBound

/-- The reflected coefficient fold preserves its triangular shape while updating degree and leading coefficient.

An initial shape certificate controls the retained ascending table. Each
coefficient adds one to its degree and applies the same leading-coefficient
update, so the final degree increases by the consumed list length. -/
private theorem foldl_reflectedShape :
    ∀ (coefficients : List Canonical) (state : List
      Basic.CanonicalCoefficients.CoefficientPolynomial)
      (degree : Nat) (leading : Canonical),
      ReflectedShape state degree leading →
      ReflectedShape (coefficients.foldl Basic.SeparatedVariables.reflectedStep
        state)
        (degree + coefficients.length)
        (coefficients.foldl Basic.reflectedLeadingStep leading)
  | [], _, degree, _, shape =>
      ReflectedShape.of_equal rfl (Nat.add_zero degree) rfl shape
  | coefficient :: remaining, state, degree, leading, shape => by
      have next := reflectedStep_shape shape coefficient
      have final := foldl_reflectedShape remaining
        (Basic.SeparatedVariables.reflectedStep state coefficient) (degree + 1)
        (Basic.reflectedLeadingStep leading coefficient) next
      have degreeEqual : degree + (remaining.length + 1) =
          degree + 1 + remaining.length := by
        rw [Nat.add_assoc, Nat.add_comm 1 remaining.length]
      exact ReflectedShape.of_equal rfl degreeEqual rfl final

/-- A nonzero Gaussian polynomial yields its original triangular reflected shape.

The original normalized head and tail initialize and update the same finite
Horner table. Its retained degree and computed reflected leading scalar certify
that table without selecting a replacement coefficient list. -/
theorem reflectedCoefficients_shape (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    ReflectedShape (Basic.SeparatedVariables.reflectedCoefficients p) p.natDegree
      (Basic.reflectedLeading p) := by
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have contradiction : p.normalize.coeffs.isEmpty = false := nonzero
      rw [coefficients] at contradiction
      exact Bool.noConfusion contradiction
  | cons leading remaining =>
      have leadingNonzero : leading ≠ 0 := by
        have retained := Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
        change p.normalize.coeffs.headD 0 ≠ 0 at retained
        have headEqual : p.normalize.coeffs.headD 0 = leading := by
          rewrite [coefficients]
          exact Eq.refl _
        exact fun equal => retained (headEqual.trans equal)
      have initial : ReflectedShape
          [Coefficients.Constants.SeparatedVariables.parameterConstant (Canonical.conj
            leading)] 0 (Canonical.conj leading) := by
        refine
          { length_eq := rfl
            headLeading := ?_
            tailBelow := ?_ }
        · exact Coefficients.Constants.parameterConstant_leading
            (Canonical.conj_ne_zero leadingNonzero)
        · intro coefficient membership
          cases membership
      have folded := foldl_reflectedShape remaining
        [Coefficients.Constants.SeparatedVariables.parameterConstant (Canonical.conj
          leading)] 0 (Canonical.conj leading) initial
      have degreeEq : p.natDegree = remaining.length := by
        change p.normalize.coeffs.length - 1 = remaining.length
        rewrite [coefficients]
        exact Eq.refl _
      have coefficientsEqual : Basic.SeparatedVariables.reflectedCoefficients p =
          remaining.foldl Basic.SeparatedVariables.reflectedStep
            [Coefficients.Constants.SeparatedVariables.parameterConstant (Canonical.conj
              leading)] := by
        unfold Basic.SeparatedVariables.reflectedCoefficients
        rw [coefficients]
      have fullDegreeEqual : p.natDegree = 0 + remaining.length :=
        degreeEq.trans (Nat.zero_add remaining.length).symm
      have leadingEqual : Basic.reflectedLeading p =
          remaining.foldl Basic.reflectedLeadingStep (Canonical.conj
            leading) := by
        unfold Basic.reflectedLeading
        rw [coefficients]
      exact ReflectedShape.of_equal coefficientsEqual fullDegreeEqual
        leadingEqual folded

/-- Read a reflected outer coefficient from its retained ascending table.

The original descending table reverses back to its same ascending entries.
Its natural coordinate returns the original zero polynomial beyond that table. -/
@[simp] theorem outerCoeff_reflected (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (index : Nat) :
    Resultant.outerCoeff (Basic.SeparatedVariables.reflected p)
      index =
      Data.List.getD (Basic.SeparatedVariables.reflectedCoefficients p) index 0 :=
        by
  unfold Resultant.outerCoeff
    Basic.SeparatedVariables.reflected
  rewrite [Data.List.Reverse.reverse_reverse]
  exact Eq.refl _

/-- A coefficient degree ceiling bounds each retained indexed read.

The original table and natural coordinate select an entry with the supplied
bound, or the original zero fallback when that coordinate lies beyond the table. -/
private theorem getD_atMost_of_all (degree : Nat) :
    ∀ (coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial) (index : Nat),
      (∀ coefficient ∈ coefficients, Leading.DegreeAtMost coefficient degree) →
      Leading.DegreeAtMost (Data.List.getD coefficients index 0) degree
  | [], _, _ => Leading.DegreeAtMost.zero degree
  | coefficient :: _, 0, bounded =>
      bounded coefficient List.mem_cons_self
  | coefficient :: remaining, index + 1, bounded =>
      getD_atMost_of_all degree remaining index
        (fun output membership => bounded output
          (List.mem_cons_of_mem coefficient membership))

/-- A strict coefficient degree bound bounds each retained indexed read.

The original finite table and natural coordinate retain the supplied entry
certificate; the same zero fallback supplies its strict bound beyond the table. -/
private theorem getD_below_of_all (degree : Nat) :
    ∀ (coefficients : List Basic.CanonicalCoefficients.CoefficientPolynomial) (index : Nat),
      (∀ coefficient ∈ coefficients, Leading.DegreeBelow coefficient degree) →
      Leading.DegreeBelow (Data.List.getD coefficients index 0) degree
  | [], _, _ => Leading.DegreeBelow.zero degree
  | coefficient :: _, 0, bounded =>
      bounded coefficient List.mem_cons_self
  | coefficient :: remaining, index + 1, bounded =>
      getD_below_of_all degree remaining index
        (fun output membership => bounded output
          (List.mem_cons_of_mem coefficient membership))

/-- Every reflected outer coefficient has parameter degree at most the source degree.

The source polynomial must have a false zero test. Its triangular reflected
shape bounds the head by its exact degree and every tail entry by a strict
bound; an index beyond the table reads the zero polynomial. -/
theorem reflectedCoeff_atMost (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (index : Nat) :
    Leading.DegreeAtMost
      (Resultant.outerCoeff (Basic.SeparatedVariables.reflected p)
        index)
      p.natDegree := by
  apply Leading.DegreeAtMost.of_equal (outerCoeff_reflected p index) rfl
  have shape := reflectedCoefficients_shape p nonzero
  cases coefficients : Basic.SeparatedVariables.reflectedCoefficients p with
  | nil =>
      have impossible := shape.length_eq
      rw [coefficients] at impossible
      change 0 = Nat.succ p.natDegree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      cases index with
      | zero =>
          have headEqual :
              (Basic.SeparatedVariables.reflectedCoefficients p).headD 0 = head :=
                by
            rw [coefficients]
            rfl
          exact (Leading.LeadingTerm.of_equal headEqual.symm rfl rfl
            shape.headLeading).atMost
      | succ index =>
          apply getD_atMost_of_all p.natDegree tail index
          intro coefficient membership
          apply Leading.DegreeBelow.toAtMost
          apply shape.tailBelow coefficient
          rw [coefficients]
          exact membership

/-- Every positive outer coefficient has parameter degree strictly below the source degree.

The source polynomial must have a false zero test. The positive index reads
from the tail of its triangular reflected table, whose entries have the stated
strict bound; zero padding preserves that bound beyond the table. -/
theorem reflectedCoeff_below_of_pos (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (index : Nat) :
    Leading.DegreeBelow
      (Resultant.outerCoeff (Basic.SeparatedVariables.reflected p)
        (index + 1))
      p.natDegree := by
  apply Leading.DegreeBelow.of_equal (outerCoeff_reflected p (index + 1)) rfl
  have shape := reflectedCoefficients_shape p nonzero
  cases coefficients : Basic.SeparatedVariables.reflectedCoefficients p with
  | nil =>
      have impossible := shape.length_eq
      rw [coefficients] at impossible
      change 0 = Nat.succ p.natDegree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      apply getD_below_of_all p.natDegree tail index
      intro coefficient membership
      apply shape.tailBelow coefficient
      rw [coefficients]
      exact membership

/-- The constant outer coefficient has the source degree and computed reflected leading coefficient.

The source polynomial must have a false zero test. The head of its retained
ascending reflected table carries the exact leading-term certificate, and
outer-coordinate zero reads that same head. -/
theorem reflectedCoeff_zero_leading (p : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    Leading.LeadingTerm
      (Resultant.outerCoeff (Basic.SeparatedVariables.reflected p)
        0)
      p.natDegree (Basic.reflectedLeading p) := by
  apply Leading.LeadingTerm.of_equal (outerCoeff_reflected p 0) rfl rfl
  have shape := reflectedCoefficients_shape p nonzero
  cases coefficients : Basic.SeparatedVariables.reflectedCoefficients p with
  | nil =>
      have impossible := shape.length_eq
      rw [coefficients] at impossible
      change 0 = Nat.succ p.natDegree at impossible
      exact Nat.noConfusion impossible
  | cons head tail =>
      have headEqual : (Basic.SeparatedVariables.reflectedCoefficients p).headD 0 =
        head := by
        rw [coefficients]
        rfl
      exact Leading.LeadingTerm.of_equal headEqual.symm rfl rfl shape.headLeading
end Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Shape

end

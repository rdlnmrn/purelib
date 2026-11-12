module

public import Purelib.Approximation.Gaussian.Name.Coherent.Power.Composition
public import Purelib.Approximation.Gaussian.Division.Cancellation
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Original square equations and retained reciprocal powers

An original sheet square comparison and the complete cache equality of its
actual reciprocal remove two factors from the original reciprocal power.
Coefficient reductions use the existing retained polynomial normalization
and exact finite arithmetic, preserving both original process trees.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Power

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

/-- The square of the identical cached reciprocal cancels the original sheet's exact square value. -/
def reciprocalSquare_mul_cancel (sheet reciprocal : CoherentNamed) (apart : Named.Apart sheet.name)
    (cached : reciprocal = (Coherence.exact 1).div sheet apart) (parameter : Canonical)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact parameter).name) :
    NamedEquivalent ((namedPower reciprocal 2).mul (Coherence.exact parameter)).name (Coherence.exact 1).name := by
  have inverse := Division.Cancellation.reciprocal_mul_cancel sheet apart
  rewrite [← cached] at inverse
  have pair : NamedEquivalent ((reciprocal.mul reciprocal).mul (sheet.mul sheet)).name
      (Coherence.exact 1).name :=
    (Product.Laws.coherentMul_interchange reciprocal reciprocal sheet sheet).trans
      ((Product.Congruence.coherentMul_respects (reciprocal.mul sheet) (Coherence.exact 1)
        (reciprocal.mul sheet) (Coherence.exact 1) inverse inverse).trans
          (Exact.Arithmetic.exact_mul 1 1))
  exact
    (Product.Congruence.coherentMul_respects (namedPower reciprocal 2) (reciprocal.mul reciprocal)
      (Coherence.exact parameter) (sheet.mul sheet) (namedPower_two reciprocal) square.symm).trans pair

/-- Multiplying an original reciprocal power by the retained exact square value removes two original factors.

The complete original reciprocal cache and original sheet square comparison
remain inputs. The finite exponent decomposition and operational product
laws establish agreement without identifying any selected rational readings.
-/
def reciprocalPower_square_mul_cancel (sheet reciprocal : CoherentNamed) (apart : Named.Apart sheet.name)
    (cached : reciprocal = (Coherence.exact 1).div sheet apart) (parameter : Canonical)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact parameter).name) (exponent : Nat) :
    NamedEquivalent ((namedPower reciprocal (exponent + 2)).mul (Coherence.exact parameter)).name
      (namedPower reciprocal exponent).name :=
  (Product.Congruence.coherentMul_respects (namedPower reciprocal (exponent + 2))
    ((namedPower reciprocal exponent).mul (namedPower reciprocal 2))
    (Coherence.exact parameter) (Coherence.exact parameter)
    (namedPower_add reciprocal exponent 2) (NamedEquivalent.refl _)).trans
      ((Product.Laws.coherentMul_assoc (namedPower reciprocal exponent) (namedPower reciprocal 2)
        (Coherence.exact parameter)).trans
          ((Product.Congruence.coherentMul_respects (namedPower reciprocal exponent)
            (namedPower reciprocal exponent) ((namedPower reciprocal 2).mul (Coherence.exact parameter))
            (Coherence.exact 1) (NamedEquivalent.refl _)
            (reciprocalSquare_mul_cancel sheet reciprocal apart cached parameter square)).trans
              (Mul.coherentMul_one_right (namedPower reciprocal exponent))))

/-- Exact original coefficient multiplication and subtraction have their displayed scalar difference as provenance. -/
private def exact_coefficient_difference (first last parameter : Canonical) :
    NamedEquivalent
      (CoherentNamed.add ((Coherence.exact first).mul (Coherence.exact parameter))
        (CoherentNamed.neg (Coherence.exact last))).name
      (Coherence.exact (first * parameter - last)).name :=
  (Sum.Congruence.coherentAdd_respects ((Coherence.exact first).mul (Coherence.exact parameter))
    (Coherence.exact (first * parameter)) (CoherentNamed.neg (Coherence.exact last))
    (Coherence.exact (-last)) (Exact.Arithmetic.exact_mul first parameter)
    (Neg.exactNeg last)).trans
      (NamedEquivalent.transport rfl
        (congrArg (fun value : Canonical => (Coherence.exact value).name) (by ring1))
        (Exact.Arithmetic.exact_add (first * parameter) (-last)))

/-- The original coefficient difference times a reciprocal power agrees with its independently retained two terms.

The original square equation moves the first term to its two-lower exponent.
The existing normalization compares the original multiplication and signed
addition trees before exact coefficient arithmetic collapses their scalar data.
-/
def reciprocalPower_coefficient_difference (sheet reciprocal : CoherentNamed) (apart : Named.Apart sheet.name)
    (cached : reciprocal = (Coherence.exact 1).div sheet apart) (parameter first last : Canonical)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact parameter).name) (exponent : Nat) :
    NamedEquivalent
      ((Coherence.exact (first * parameter - last)).mul (namedPower reciprocal (exponent + 2))).name
      (CoherentNamed.add ((Coherence.exact first).mul (namedPower reciprocal exponent))
        (CoherentNamed.neg ((Coherence.exact last).mul (namedPower reciprocal (exponent + 2))))).name := by
  let power := namedPower reciprocal (exponent + 2)
  let bindings : Fin 4 → CoherentNamed := Data.Fin.cases (Coherence.exact first)
    (Data.Fin.cases (Coherence.exact last) (Data.Fin.cases (Coherence.exact parameter) (fun _ => power)))
  let a := Normalized.atom bindings 0
  let b := Normalized.atom bindings 1
  let f := Normalized.atom bindings 2
  let u := Normalized.atom bindings 3
  let left := ((a.mul f).sub b).mul u
  let right := (a.mul (u.mul f)).sub (b.mul u)
  have forms : left.form.terms = right.form.terms := by
    dsimp only [left, right, a, b, f, u]
    simp only [Normalized.mul_form, Normalized.sub_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  have normalized := left.compare right forms
  have firstReduced : NamedEquivalent
      ((Coherence.exact first).mul (power.mul (Coherence.exact parameter))).name
      ((Coherence.exact first).mul (namedPower reciprocal exponent)).name :=
    Product.Congruence.coherentMul_respects (Coherence.exact first) (Coherence.exact first)
      (power.mul (Coherence.exact parameter)) (namedPower reciprocal exponent) (NamedEquivalent.refl _)
      (reciprocalPower_square_mul_cancel sheet reciprocal apart cached parameter square exponent)
  have result := normalized.trans
    (Sum.Congruence.coherentAdd_respects
      ((Coherence.exact first).mul (power.mul (Coherence.exact parameter)))
      ((Coherence.exact first).mul (namedPower reciprocal exponent))
      (CoherentNamed.neg ((Coherence.exact last).mul power))
      (CoherentNamed.neg ((Coherence.exact last).mul power)) firstReduced (NamedEquivalent.refl _))
  exact (Product.Congruence.coherentMul_respects (Coherence.exact (first * parameter - last))
    (CoherentNamed.add ((Coherence.exact first).mul (Coherence.exact parameter))
      (CoherentNamed.neg (Coherence.exact last))) power power
    (exact_coefficient_difference first last parameter).symm (NamedEquivalent.refl _)).trans result

end Purelib.Approximation.Gaussian.Name.Coherent.Power

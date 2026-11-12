module

public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Arithmetic.Distributive
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Original coherent scaling and finite coefficient combinations

The original scale constructor retains its actual multiplication process.
Operational field laws compare nested scaling, signed scaling and common
factor sums with their exact scalar coefficient combinations. The finite
normalization uses original channel bindings, without replacing their readings.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Power

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

/-- Nested original scaling agrees with scaling by the exact product of its retained coefficients. -/
def scale_scale (first second : Canonical) (value : CoherentNamed) :
    NamedEquivalent (scale first (scale second value)).name (scale (first * second) value).name :=
  (Product.Laws.coherentMul_assoc (Coherence.exact first) (Coherence.exact second) value).symm.trans
    (Product.Congruence.coherentMul_respects ((Coherence.exact first).mul (Coherence.exact second))
      (Coherence.exact (first * second)) value value (Exact.Arithmetic.exact_mul first second)
      (NamedEquivalent.refl _))

/-- Two original scaled copies of the same retained channel agree with their exact coefficient-sum scaling. -/
def scale_add (first second : Canonical) (value : CoherentNamed) :
    NamedEquivalent (CoherentNamed.add (scale first value) (scale second value)).name
      (scale (first + second) value).name :=
  (Distributive.coherentAdd_mul_right (Coherence.exact first) (Coherence.exact second) value).symm.trans
    (Product.Congruence.coherentMul_respects (CoherentNamed.add (Coherence.exact first) (Coherence.exact second))
      (Coherence.exact (first + second)) value value (Exact.Arithmetic.exact_add first second)
      (NamedEquivalent.refl _))

/-- Negating an original scaled channel agrees with scaling that identical channel by the negated coefficient. -/
def scale_neg (coefficient : Canonical) (value : CoherentNamed) :
    NamedEquivalent (CoherentNamed.neg (scale coefficient value)).name (scale (-coefficient) value).name := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases (Coherence.exact coefficient) (fun _ => value)
  let a := Normalized.atom bindings 0
  let u := Normalized.atom bindings 1
  let left := (a.mul u).neg
  let right := a.neg.mul u
  have forms : left.form.terms = right.form.terms := by
    dsimp only [left, right, a, u]
    simp only [Normalized.neg_form, Normalized.mul_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  exact (left.compare right forms).trans
    (Product.Congruence.coherentMul_respects (CoherentNamed.neg (Coherence.exact coefficient))
      (Coherence.exact (-coefficient)) value value (Neg.exactNeg coefficient) (NamedEquivalent.refl _))

/-- An original signed difference of two scaled copies agrees with scaling by the exact coefficient difference. -/
def scale_sub (first second : Canonical) (value : CoherentNamed) :
    NamedEquivalent (CoherentNamed.add (scale first value) (CoherentNamed.neg (scale second value))).name
      (scale (first - second) value).name :=
  (Sum.Congruence.coherentAdd_respects (scale first value) (scale first value)
    (CoherentNamed.neg (scale second value)) (scale (-second) value) (NamedEquivalent.refl _)
    (scale_neg second value)).trans
      (NamedEquivalent.transport rfl
        (congrArg (fun coefficient : Canonical => (scale coefficient value).name) (by ring1))
        (scale_add first (-second) value))

end Purelib.Approximation.Gaussian.Name.Coherent.Power

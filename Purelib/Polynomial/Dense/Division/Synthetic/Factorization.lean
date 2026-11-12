module

public import Purelib.Polynomial.Dense.Division.Synthetic.Map
public import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Polynomial.Dense.Reflection

/-!
# Exact coefficient factorization through synthetic division

The original quotient and remainder reconstruct the original normalized
coefficient table using the original polynomial multiplication. Equality is
reflected through one finite shift algebra, including over coefficient rings
with zero divisors; equality of ordinary scalar evaluations is not assumed
to determine a coefficient table.
-/

namespace Purelib.Polynomial.Dense.Division.Synthetic

open Basic (DensePolynomial)
open Purelib.Algebra.Monogenic

variable {K : Type*} [CommRing K] [DecidableEq K]

/-- The actual synthetic quotient and remainder reconstruct the original normalized coefficient table. -/
public theorem factorization (polynomial : DensePolynomial K) (root : K) :
    polynomial.normalize =
      ((⟨[1, -root]⟩ : DensePolynomial K) * (divide polynomial root).quotient +
        DensePolynomial.constant (divide polynomial root).remainder).normalize := by
  apply Reflection.normalize_eq
  let reconstructed := (⟨[1, -root]⟩ : DensePolynomial K) * (divide polynomial root).quotient +
    DensePolynomial.constant (divide polynomial root).remainder
  let dimension := Nat.max polynomial.coeffs.length reconstructed.coeffs.length + 1
  let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
  let function := Cyclic.Element.scalar cyclic
  let point := Cyclic.Element.root cyclic
  change (Map.map function polynomial).eval point = (Map.map function reconstructed).eval point
  have retained := (divide (Map.map function polynomial) (function root)).eval_eq point
  rewrite [map_quotient function (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic),
    map_remainder function (Cyclic.Element.scalar_zero cyclic) (Cyclic.Element.scalar_add cyclic)
      (Cyclic.Element.scalar_mul cyclic)] at retained
  have linear : (Map.map function (⟨[1, -root]⟩ : DensePolynomial K)).eval point =
      point - function root := by
    change (0 * point + function 1) * point + function (-root) = point - function root
    have one : function 1 = 1 := Cyclic.Element.scalar_one cyclic
    have negative : function (-root) = -function root := Cyclic.Element.scalar_neg cyclic root
    rewrite [zero_mul, zero_add, one, negative, one_mul]
    exact (sub_eq_add_neg point (function root)).symm
  dsimp only [reconstructed]
  rewrite [Map.map_add function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ same => Cyclic.Element.scalar_injective cyclic same)
      (Cyclic.Element.scalar_add cyclic),
    Map.map_mul function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ same => Cyclic.Element.scalar_injective cyclic same)
      (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic),
    Map.map_constant, DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_constant, linear]
  exact retained

/-- At an exact root, the original normalized coefficient table is the actual monic linear factor times its quotient. -/
public theorem factorization_of_root (polynomial : DensePolynomial K) (root : K)
    (vanishes : polynomial.eval root = 0) :
    polynomial.normalize =
      (⟨[1, -root]⟩ : DensePolynomial K) * (divide polynomial root).quotient := by
  apply Eq.trans (b := ((⟨[1, -root]⟩ : DensePolynomial K) * (divide polynomial root).quotient).normalize)
    ?_ (DensePolynomial.normalize_mul _ _)
  let product := (⟨[1, -root]⟩ : DensePolynomial K) * (divide polynomial root).quotient
  have remainderZero := (divide polynomial root).remainder_eval.trans vanishes
  have original := factorization polynomial root
  rewrite [remainderZero] at original
  apply original.trans
  apply Reflection.normalize_eq
  let dimension := Nat.max (product + DensePolynomial.constant 0).coeffs.length product.coeffs.length + 1
  let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
  let function := Cyclic.Element.scalar cyclic
  let point := Cyclic.Element.root cyclic
  change (Map.map function (product + DensePolynomial.constant 0)).eval point = (Map.map function product).eval point
  have zero : function 0 = 0 := Cyclic.Element.scalar_zero cyclic
  rewrite [Map.map_add function zero (fun _ _ same => Cyclic.Element.scalar_injective cyclic same)
      (Cyclic.Element.scalar_add cyclic),
    Map.map_constant, zero, DensePolynomial.eval_add, DensePolynomial.eval_constant, add_zero]
  rfl

end Purelib.Polynomial.Dense.Division.Synthetic

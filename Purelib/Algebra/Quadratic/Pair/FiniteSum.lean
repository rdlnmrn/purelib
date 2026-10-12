module

public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Algebra.Quadratic.Pair.Basic

/-!
# Bounded quadratic-pair sums

The original prefix recursion retains the same finite count and term order.
Scalar embedding and both pair coordinates commute with that finite sum.
-/

namespace Purelib.Algebra.Quadratic.Pair.FiniteSum

open Purelib.Algebra.FiniteSum
open _root_.Purelib.Algebra.Quadratic (Pair)

/-- Scalar embedding commutes with an explicitly bounded finite sum.

The scalar sum and the quadratic-pair sum use the same bound and scalar input function over a commutative ring. -/
public theorem prefixSum_quadraticPair_scalar
    {R : Type*} [CommRing R]
    (radialSquare : R) (count : Nat) (term : Nat → R) :
    Prefix.prefixSum count (fun index =>
        Pair.scalar (radialSquare := radialSquare)
          (term index)) =
      Pair.scalar
        (Prefix.prefixSum count term) := by
  induction count generalizing term with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        Pair.scalar (term 0) +
            Prefix.prefixSum count (fun index =>
              Pair.scalar (term (index + 1))) =
          Pair.scalar
            (term 0 + Prefix.prefixSum count
              (fun index => term (index + 1)))
      rw [inductionHypothesis, Pair.scalar_add]

/-- A bounded sum of quadratic pairs sums each coordinate separately.

The real and imaginary coordinate sums retain the same natural bound and input functions. -/
public theorem finitePrefixSum_quadraticPair_coordinates
    {R : Type*} [CommRing R]
    (count : Nat) (real imaginary : Nat → R) :
    Prefix.prefixSum count (fun index =>
        (⟨real index, imaginary index⟩ : Pair R 1)) =
      ⟨Prefix.prefixSum count real,
        Prefix.prefixSum count imaginary⟩ := by
  induction count generalizing real imaginary with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        ⟨real 0, imaginary 0⟩ +
            Prefix.prefixSum count (fun index =>
              (⟨real (index + 1), imaginary (index + 1)⟩ :
                Pair R 1)) =
          ⟨real 0 + Prefix.prefixSum count
              (fun index => real (index + 1)),
            imaginary 0 + Prefix.prefixSum count
              (fun index => imaginary (index + 1))⟩
      rw [inductionHypothesis]
      rfl

end Purelib.Algebra.Quadratic.Pair.FiniteSum

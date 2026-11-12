module

public import Purelib.Algebra.Quadratic.Pair.Gaussian
public import Purelib.Algebra.Quadratic.Pair.Norm

/-!
# Operational norm factorization at an original quadratic generator

The original pair and its algebraic conjugate multiply to their mapped scalar
norm under the supplied degree-two generator equation. A nonzero scalar norm
also certifies multiplication with the interpreted explicit inverse.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

variable {K : Type} {parameter : K}

/-- The interpreted original pair and its algebraic conjugate compare to the exact mapped norm. -/
@[noinline, nospecialize] def denote_norm [CommRing K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (value : Pair K parameter) :
    NamedEquivalent (CoherentNamed.mul (denote coefficient generator value)
      (denote coefficient generator value.conjugate)).name (Coherence.exact (coefficient value.norm)).name := by
  have comparison := denote_mul coefficient add_eq mul_eq sub_eq generator identity value value.conjugate
  rewrite [value.product_conjugate] at comparison
  exact NamedEquivalent.trans comparison (denote_scalar coefficient zero_eq generator value.norm)

/-- The interpreted pair multiplied by its interpreted explicit inverse compares to the exact unit channel. -/
@[noinline, nospecialize] def denote_inverse [ExplicitField K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0) (one_eq : coefficient 1 = 1)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (value : Pair K parameter) (nonzero : value.norm ≠ 0) :
    NamedEquivalent (CoherentNamed.mul (denote coefficient generator value)
      (denote coefficient generator value.inverse)).name (Coherence.exact 1).name := by
  have comparison := denote_mul coefficient add_eq mul_eq sub_eq generator identity value value.inverse
  rewrite [value.mul_inverse nonzero] at comparison
  have unit := denote_scalar (parameter := parameter) coefficient zero_eq generator (1 : K)
  change NamedEquivalent (denote coefficient generator (1 : Pair K parameter)).name
    (Coherence.exact (coefficient 1)).name at unit
  rewrite [one_eq] at unit
  exact NamedEquivalent.trans comparison unit

end Purelib.Algebra.Quadratic.Pair.Gaussian

end

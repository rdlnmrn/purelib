module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Norm
public import Purelib.Approximation.Gaussian.Division.Prepared.Factor
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse

/-!
# Finite preparation and actual division at a retained quadratic generator

The original pair norm factorization computes the first operand's finite
apartness observation. A nonzero mapped norm therefore prepares the same
interpreted source, and operational inversion compares with the actual
division through its retained apart denominator presentation.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Division

variable {K : Type} {parameter : K}

/-- Observe both original interpreted factors once and compute a finite positive first-factor lower bound. -/
@[noinline, nospecialize] def observe_norm [CommRing K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (value : Pair K parameter) (nonzero : coefficient value.norm ≠ 0) :
    Prepared.Factor.Observation (denote coefficient generator value)
      (denote coefficient generator value.conjugate) (coefficient value.norm) :=
  Prepared.Factor.observe (denote coefficient generator value) (denote coefficient generator value.conjugate)
    (coefficient value.norm) nonzero (denote_norm coefficient zero_eq add_eq mul_eq sub_eq generator identity value)

/-- The original interpreted explicit inverse agrees with actual division by the same retained prepared denominator. -/
@[noinline, nospecialize] def reciprocal_equivalent [ExplicitField K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0) (one_eq : coefficient 1 = 1)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (value : Pair K parameter) (nonzero : value.norm ≠ 0)
    (prepared : Prepared (denote coefficient generator value)) :
    NamedEquivalent (prepared.quotient (Coherence.exact 1)).name
      (denote coefficient generator value.inverse).name :=
  prepared.reciprocal_equivalent_of_product (denote coefficient generator value.inverse)
    (denote_inverse coefficient zero_eq one_eq add_eq mul_eq sub_eq generator identity value nonzero)

end Purelib.Algebra.Quadratic.Pair.Gaussian

end

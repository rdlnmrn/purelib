module

public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Power.Composition
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Arithmetic.Distributive
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Tactic.Ring

/-!
# Quadratic pairs at an original coherent generator

The original pair ring has generator square minus its parameter. Its two
coordinates are interpreted by a supplied exact Gaussian coefficient map and
one retained coherent channel. Arithmetic comparisons use that channel's
degree-two invocation of the general finite-power equation.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Coherent

variable {K : Type} {parameter : K}

/-- Interpret the original pair coordinates at a supplied exact coefficient map and original generator. -/
@[expose] def denote (coefficient : K → Canonical) (generator : CoherentNamed)
    (value : Pair K parameter) : CoherentNamed :=
  CoherentNamed.add (Coherence.exact (coefficient value.re))
    (CoherentNamed.mul (Coherence.exact (coefficient value.im)) generator)

/-- Transport an interpreted pair along the supplied comparison of its two retained generators. -/
@[noinline, nospecialize] def denote_transport (coefficient : K → Canonical) (first second : CoherentNamed)
    (equivalent : NamedEquivalent first.name second.name) (value : Pair K parameter) :
    NamedEquivalent (denote coefficient first value).name (denote coefficient second value).name :=
  Sum.Congruence.coherentAdd_respects
    (Coherence.exact (coefficient value.re)) (Coherence.exact (coefficient value.re))
    (CoherentNamed.mul (Coherence.exact (coefficient value.im)) first)
    (CoherentNamed.mul (Coherence.exact (coefficient value.im)) second) (NamedEquivalent.refl _)
    (Product.Congruence.coherentMul_respects (Coherence.exact (coefficient value.im))
      (Coherence.exact (coefficient value.im)) first second (NamedEquivalent.refl _) equivalent)

/-- Scalar multiplication realizes the original pair scaling at the same retained generator. -/
@[noinline, nospecialize] def denote_scale [Mul K] (coefficient : K → Canonical)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (generator : CoherentNamed) (factor : K) (value : Pair K parameter) :
    NamedEquivalent (CoherentNamed.mul (Coherence.exact (coefficient factor))
      (denote coefficient generator value)).name (denote coefficient generator (Pair.scale factor value)).name := by
  let scalar := Coherence.exact (coefficient factor)
  let real := Coherence.exact (coefficient value.re)
  let imaginary := Coherence.exact (coefficient value.im)
  have realProduct := Exact.Arithmetic.exact_mul (coefficient factor) (coefficient value.re)
  rewrite [← mul_eq factor value.re] at realProduct
  have imaginaryProduct := Exact.Arithmetic.exact_mul (coefficient factor) (coefficient value.im)
  rewrite [← mul_eq factor value.im] at imaginaryProduct
  exact NamedEquivalent.trans (Distributive.coherentMul_add_left scalar real (CoherentNamed.mul imaginary generator))
    (Sum.Congruence.coherentAdd_respects (CoherentNamed.mul scalar real)
      (Coherence.exact (coefficient (factor * value.re)))
      (CoherentNamed.mul scalar (CoherentNamed.mul imaginary generator))
      (CoherentNamed.mul (Coherence.exact (coefficient (factor * value.im))) generator) realProduct
      (NamedEquivalent.trans (Product.Laws.coherentMul_assoc scalar imaginary generator).symm
        (Product.Congruence.coherentMul_respects (CoherentNamed.mul scalar imaginary)
          (Coherence.exact (coefficient (factor * value.im))) generator generator imaginaryProduct
          (NamedEquivalent.refl _))))

/-- A zero pair is operationally zero when the supplied coefficient map preserves zero. -/
@[noinline, nospecialize] def denote_zero [Zero K] (coefficient : K → Canonical) (zero_eq : coefficient 0 = 0)
    (generator : CoherentNamed) :
    NamedEquivalent (denote coefficient generator (0 : Pair K parameter)).name (Coherence.exact 0).name := by
  change NamedEquivalent
    (CoherentNamed.add (Coherence.exact (coefficient 0))
      (CoherentNamed.mul (Coherence.exact (coefficient 0)) generator)).name _
  rewrite [zero_eq]
  exact NamedEquivalent.trans
    (Sum.Congruence.coherentAdd_respects (Coherence.exact 0) (Coherence.exact 0)
      (CoherentNamed.mul (Coherence.exact 0) generator) (Coherence.exact 0)
      (NamedEquivalent.refl _) (Mul.coherentMul_zero_left generator))
    (Add.coherentAdd_zero_right (Coherence.exact 0))

/-- The formal generator compares to the actual original generator under an exact unital coefficient map. -/
@[noinline, nospecialize] def denote_generator [Zero K] [One K] (coefficient : K → Canonical)
    (zero_eq : coefficient 0 = 0) (one_eq : coefficient 1 = 1) (generator : CoherentNamed) :
    NamedEquivalent (denote coefficient generator (Pair.generator : Pair K parameter)).name generator.name := by
  change NamedEquivalent
    (CoherentNamed.add (Coherence.exact (coefficient 0))
      (CoherentNamed.mul (Coherence.exact (coefficient 1)) generator)).name generator.name
  rewrite [zero_eq, one_eq]
  exact NamedEquivalent.trans
    (Add.coherentAdd_zero_left (CoherentNamed.mul (Coherence.exact 1) generator))
    (Mul.coherentMul_one_left generator)

/-- A scalar pair compares to its exact mapped scalar without replacing the retained generator. -/
@[noinline, nospecialize] def denote_scalar [Zero K] (coefficient : K → Canonical) (zero_eq : coefficient 0 = 0)
    (generator : CoherentNamed) (value : K) :
    NamedEquivalent (denote coefficient generator (Pair.scalar value : Pair K parameter)).name
      (Coherence.exact (coefficient value)).name := by
  change NamedEquivalent
    (CoherentNamed.add (Coherence.exact (coefficient value))
      (CoherentNamed.mul (Coherence.exact (coefficient 0)) generator)).name _
  rewrite [zero_eq]
  exact NamedEquivalent.trans
    (Sum.Congruence.coherentAdd_respects (Coherence.exact (coefficient value))
      (Coherence.exact (coefficient value)) (CoherentNamed.mul (Coherence.exact 0) generator)
      (Coherence.exact 0) (NamedEquivalent.refl _) (Mul.coherentMul_zero_left generator))
    (Add.coherentAdd_zero_right (Coherence.exact (coefficient value)))

/-- Addition of interpreted original pairs compares to interpretation of their original coordinate sum. -/
@[noinline, nospecialize] def denote_add [Add K] (coefficient : K → Canonical)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (generator : CoherentNamed) (left right : Pair K parameter) :
    NamedEquivalent (CoherentNamed.add (denote coefficient generator left)
      (denote coefficient generator right)).name (denote coefficient generator (left + right)).name := by
  let a := Coherence.exact (coefficient left.re)
  let b := Coherence.exact (coefficient left.im)
  let c := Coherence.exact (coefficient right.re)
  let d := Coherence.exact (coefficient right.im)
  have scalarPart := Exact.Arithmetic.exact_add (coefficient left.re) (coefficient right.re)
  rewrite [← add_eq left.re right.re] at scalarPart
  have linearPart := NamedEquivalent.trans
    (NamedEquivalent.symm (Distributive.coherentAdd_mul_right b d generator))
    (Product.Congruence.coherentMul_respects (CoherentNamed.add b d)
      (Coherence.exact (coefficient left.im + coefficient right.im)) generator generator
      (Exact.Arithmetic.exact_add (coefficient left.im) (coefficient right.im)) (NamedEquivalent.refl _))
  rewrite [← add_eq left.im right.im] at linearPart
  exact NamedEquivalent.trans
    (Additive.coherentAdd_interchange a (CoherentNamed.mul b generator) c (CoherentNamed.mul d generator))
    (Sum.Congruence.coherentAdd_respects (CoherentNamed.add a c)
      (Coherence.exact (coefficient (left.re + right.re)))
      (CoherentNamed.add (CoherentNamed.mul b generator) (CoherentNamed.mul d generator))
      (CoherentNamed.mul (Coherence.exact (coefficient (left.im + right.im))) generator)
      scalarPart linearPart)

/-- Stateful negation compares to the original coordinatewise pair negation. -/
@[noinline, nospecialize] def denote_neg [CommRing K] (coefficient : K → Canonical) (zero_eq : coefficient 0 = 0)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (generator : CoherentNamed) (value : Pair K parameter) :
    NamedEquivalent (CoherentNamed.neg (denote coefficient generator value)).name
      (denote coefficient generator (-value)).name := by
  have cancellation := denote_add coefficient add_eq generator value (-value)
  rewrite [_root_.add_neg_cancel value] at cancellation
  exact NamedEquivalent.symm (Additive.equivalent_neg_of_add_zero
    (denote coefficient generator value) (denote coefficient generator (-value))
    (NamedEquivalent.trans cancellation (denote_zero coefficient zero_eq generator)))

/-- Original pair multiplication agrees operationally with its interpretation at the retained square equation.

The supplied coefficient map preserves the three displayed scalar operations.
The generator equation has coefficient minus the mapped original pair parameter,
so its sign convention is retained without creating another pair ring. -/
@[noinline, nospecialize] def denote_mul [Mul K] [Sub K] [Add K] (coefficient : K → Canonical)
    (add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second)
    (mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second)
    (sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second)
    (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-coefficient parameter))
    (left right : Pair K parameter) :
    NamedEquivalent (CoherentNamed.mul (denote coefficient generator left)
      (denote coefficient generator right)).name (denote coefficient generator (left * right)).name := by
  let a := Coherence.exact (coefficient left.re)
  let b := Coherence.exact (coefficient left.im)
  let c := Coherence.exact (coefficient right.re)
  let d := Coherence.exact (coefficient right.im)
  let br := CoherentNamed.mul b generator
  let dr := CoherentNamed.mul d generator
  let ac := CoherentNamed.mul a c
  let adr := CoherentNamed.mul a dr
  let brc := CoherentNamed.mul br c
  let brdr := CoherentNamed.mul br dr
  have square : NamedEquivalent (CoherentNamed.mul generator generator).name
      (Coherence.exact (-coefficient parameter)).name :=
    NamedEquivalent.trans (NamedEquivalent.symm (Power.namedPower_two generator)) identity
  have productSquare := NamedEquivalent.trans
    (Product.Laws.coherentMul_interchange b generator d generator)
    (NamedEquivalent.trans
      (Product.Congruence.coherentMul_respects (CoherentNamed.mul b d)
        (Coherence.exact (coefficient left.im * coefficient right.im))
        (CoherentNamed.mul generator generator) (Coherence.exact (-coefficient parameter))
        (Exact.Arithmetic.exact_mul (coefficient left.im) (coefficient right.im)) square)
      (Exact.Arithmetic.exact_mul (coefficient left.im * coefficient right.im) (-coefficient parameter)))
  have scalarPart := NamedEquivalent.trans
    (Sum.Congruence.coherentAdd_respects ac
      (Coherence.exact (coefficient left.re * coefficient right.re)) brdr
      (Coherence.exact ((coefficient left.im * coefficient right.im) * (-coefficient parameter)))
      (Exact.Arithmetic.exact_mul (coefficient left.re) (coefficient right.re)) productSquare)
    (Exact.Arithmetic.exact_add (coefficient left.re * coefficient right.re)
      ((coefficient left.im * coefficient right.im) * (-coefficient parameter)))
  have real_eq : coefficient (left * right).re = coefficient left.re * coefficient right.re +
      (coefficient left.im * coefficient right.im) * (-coefficient parameter) := by
    change coefficient (left.re * right.re - parameter * left.im * right.im) = _
    rewrite [sub_eq, mul_eq, mul_eq, mul_eq]
    ring0
  rewrite [← real_eq] at scalarPart
  have firstLinear := NamedEquivalent.trans (NamedEquivalent.symm (Product.Laws.coherentMul_assoc a d generator))
    (Product.Congruence.coherentMul_respects (CoherentNamed.mul a d)
      (Coherence.exact (coefficient left.re * coefficient right.im)) generator generator
      (Exact.Arithmetic.exact_mul (coefficient left.re) (coefficient right.im)) (NamedEquivalent.refl _))
  have secondLinear := NamedEquivalent.trans (Product.Laws.coherentMul_assoc b generator c)
    (NamedEquivalent.trans
      (Product.Congruence.coherentMul_respects b b (CoherentNamed.mul generator c)
        (CoherentNamed.mul c generator) (NamedEquivalent.refl _) (Product.Laws.coherentMul_comm generator c))
      (NamedEquivalent.trans (NamedEquivalent.symm (Product.Laws.coherentMul_assoc b c generator))
        (Product.Congruence.coherentMul_respects (CoherentNamed.mul b c)
          (Coherence.exact (coefficient left.im * coefficient right.re)) generator generator
          (Exact.Arithmetic.exact_mul (coefficient left.im) (coefficient right.re)) (NamedEquivalent.refl _))))
  let ad := Coherence.exact (coefficient left.re * coefficient right.im)
  let bc := Coherence.exact (coefficient left.im * coefficient right.re)
  have linearPart := NamedEquivalent.trans
    (Sum.Congruence.coherentAdd_respects adr (CoherentNamed.mul ad generator) brc
      (CoherentNamed.mul bc generator) firstLinear secondLinear)
    (NamedEquivalent.trans (NamedEquivalent.symm (Distributive.coherentAdd_mul_right ad bc generator))
      (Product.Congruence.coherentMul_respects (CoherentNamed.add ad bc)
        (Coherence.exact (coefficient left.re * coefficient right.im + coefficient left.im * coefficient right.re))
        generator generator
        (Exact.Arithmetic.exact_add (coefficient left.re * coefficient right.im)
          (coefficient left.im * coefficient right.re)) (NamedEquivalent.refl _)))
  have imaginary_eq : coefficient (left * right).im =
      coefficient left.re * coefficient right.im + coefficient left.im * coefficient right.re := by
    change coefficient (left.re * right.im + left.im * right.re) = _
    rewrite [add_eq, mul_eq, mul_eq]
    rfl
  rewrite [← imaginary_eq] at linearPart
  exact NamedEquivalent.trans (Distributive.coherentAdd_mul_right a br (CoherentNamed.add c dr))
    (NamedEquivalent.trans
      (Sum.Congruence.coherentAdd_respects (CoherentNamed.mul a (CoherentNamed.add c dr))
        (CoherentNamed.add ac adr) (CoherentNamed.mul br (CoherentNamed.add c dr))
        (CoherentNamed.add brc brdr) (Distributive.coherentMul_add_left a c dr)
        (Distributive.coherentMul_add_left br c dr))
      (NamedEquivalent.trans
        (Sum.Congruence.coherentAdd_respects (CoherentNamed.add ac adr) (CoherentNamed.add ac adr)
          (CoherentNamed.add brc brdr) (CoherentNamed.add brdr brc) (NamedEquivalent.refl _)
          (Add.coherentAdd_comm brc brdr))
        (NamedEquivalent.trans (Additive.coherentAdd_interchange ac adr brdr brc)
          (Sum.Congruence.coherentAdd_respects (CoherentNamed.add ac brdr)
            (Coherence.exact (coefficient (left * right).re)) (CoherentNamed.add adr brc)
            (CoherentNamed.mul (Coherence.exact (coefficient (left * right).im)) generator)
            scalarPart linearPart))))

end Purelib.Algebra.Quadratic.Pair.Gaussian

end

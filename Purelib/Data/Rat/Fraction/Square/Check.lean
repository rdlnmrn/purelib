module

public import Purelib.Data.Rat.Fraction.Square
public import Purelib.Data.Nat.SquareRoot.Check
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Multiplication
-- The exposed inspection retains the original integer sign-complement certificate.
public import Purelib.Data.Int.Order
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact rational-square decisions

Canonical rational squares have squared numerator magnitudes and squared
positive denominators. Two certified natural floors therefore either construct
an exact rational root or retain a specific coordinate obstruction excluding
every rational root. Negative numerators give a separate sign obstruction.
-/

public section

namespace Purelib.Data.Rat.Fraction.Square

open Purelib.Data
open Purelib.Data.Nat

/-- Squaring a reduced rational squares its original numerator magnitude. -/
theorem numerator (value : Rational) : (square value).num.natAbs = value.num.natAbs ^ 2 := by
  change (value.num * value.num).natAbs = value.num.natAbs ^ 2
  rewrite [Int.Arithmetic.natAbs_mul, Multiplication.pow_two]
  rfl

/-- Squaring a reduced rational squares its original positive denominator. -/
theorem denominator (value : Rational) : (square value).den = value.den ^ 2 :=
  (Multiplication.pow_two value.den).symm

/-- A negative canonical numerator excludes every rational square root. -/
theorem not_square_of_negative {value : Rational} (negative : value.num < 0) :
    ∀ candidate : Rational, candidate * candidate ≠ value := by
  intro candidate same
  have numbers : candidate.num * candidate.num = value.num :=
    congrArg Rational.num ((square_eq_mul candidate).trans same)
  have nonnegative : 0 ≤ value.num := numbers ▸ Int.Order.mul_self_nonneg candidate.num
  exact (Int.Order.lt_iff_le_and_not_ge.mp negative).2 nonnegative

/-- A nonsquare numerator magnitude excludes every rational square root. -/
theorem not_square_of_numerator {value : Rational}
    (excludes : ∀ candidate : Nat, candidate ^ 2 ≠ value.num.natAbs) :
    ∀ candidate : Rational, candidate * candidate ≠ value := by
  intro candidate same
  exact excludes candidate.num.natAbs ((numerator candidate).symm.trans
    (congrArg (fun rational : Rational => rational.num.natAbs) ((square_eq_mul candidate).trans same)))

/-- A nonsquare canonical denominator excludes every rational square root. -/
theorem not_square_of_denominator {value : Rational}
    (excludes : ∀ candidate : Nat, candidate ^ 2 ≠ value.den) :
    ∀ candidate : Rational, candidate * candidate ≠ value := by
  intro candidate same
  exact excludes candidate.den ((denominator candidate).symm.trans
    (congrArg Rational.den ((square_eq_mul candidate).trans same)))

/-- An exact root of a positive natural denominator is strictly positive. -/
theorem denominator_positive {value : Rational} (root : Nat) (same : root ^ 2 = value.den) : 0 < root := by
  apply Nat.pos_of_ne_zero
  intro zero
  have vanishes : 0 = value.den := by
    calc
      0 = root ^ 2 := by rewrite [zero]; rfl
      _ = value.den := same
  exact Nat.ne_of_gt value.den_pos vanishes.symm

/-- Construct a canonical rational from the actual retained natural numerator and denominator roots. -/
@[expose] def candidate (numeratorRoot denominatorRoot : Nat) (positive : 0 < denominatorRoot) : Rational :=
  normalize ⟨Int.ofNat numeratorRoot, denominatorRoot, positive⟩

/-- Exact roots of both canonical coordinates construct an exact rational square root.

Normalization consumes the retained natural roots once. Its original cross
identity, squared directly over integers, proves the canonical square equation. -/
theorem candidate_square (value : Rational) (nonnegative : 0 ≤ value.num)
    (numeratorRoot denominatorRoot : Nat)
    (numeratorSquare : numeratorRoot ^ 2 = value.num.natAbs)
    (denominatorSquare : denominatorRoot ^ 2 = value.den) :
    let root := candidate numeratorRoot denominatorRoot (denominator_positive denominatorRoot denominatorSquare)
    root * root = value := by
  let positive := denominator_positive denominatorRoot denominatorSquare
  let root := candidate numeratorRoot denominatorRoot positive
  have numeratorDisplay : value.num = (numeratorRoot : Int) * (numeratorRoot : Int) := by
    have natural : numeratorRoot * numeratorRoot = value.num.natAbs :=
      (Multiplication.pow_two numeratorRoot).symm.trans numeratorSquare
    calc
      value.num = (value.num.natAbs : Int) := (Int.Order.natAbs_of_nonneg nonnegative).symm
      _ = ((numeratorRoot * numeratorRoot : Nat) : Int) := congrArg Int.ofNat natural.symm
      _ = (numeratorRoot : Int) * (numeratorRoot : Int) := rfl
  have denominatorDisplay : (value.den : Int) = (denominatorRoot : Int) * (denominatorRoot : Int) := by
    have natural : denominatorRoot * denominatorRoot = value.den :=
      (Multiplication.pow_two denominatorRoot).symm.trans denominatorSquare
    exact (congrArg Int.ofNat natural).symm
  have cross := normalize_equivalent (⟨Int.ofNat numeratorRoot, denominatorRoot, positive⟩ : RawFraction)
  change root.num * (denominatorRoot : Int) = (numeratorRoot : Int) * (root.den : Int) at cross
  change root * root = value
  rewrite [← square_eq_mul root]
  apply eq_of_cross
  change root.num * root.num * (value.den : Int) = value.num * ((root.den * root.den : Nat) : Int)
  calc
    root.num * root.num * (value.den : Int) =
        (root.num * (denominatorRoot : Int)) * (root.num * (denominatorRoot : Int)) := by
      rewrite [denominatorDisplay]
      ring1
    _ = ((numeratorRoot : Int) * (root.den : Int)) *
        ((numeratorRoot : Int) * (root.den : Int)) := congrArg (fun integer : Int => integer * integer) cross
    _ = value.num * ((root.den * root.den : Nat) : Int) := by
      rewrite [numeratorDisplay, _root_.Int.natCast_mul]
      ring1

set_option genInjectivity false in
/-- An exact cached rational root or a specific canonical-coordinate obstruction excluding every root. -/
inductive Outcome (value : Rational) where
  /-- Retain both computed natural floors, the canonical root and its exact recipe and square equation. -/
  | square (numeratorFloor : SquareRoot.Output value.num.natAbs)
      (numeratorSquare : numeratorFloor.root ^ 2 = value.num.natAbs)
      (denominatorFloor : SquareRoot.Output value.den)
      (denominatorSquare : denominatorFloor.root ^ 2 = value.den)
      (root : Rational)
      (root_eq : root = candidate numeratorFloor.root denominatorFloor.root
        (denominator_positive denominatorFloor.root denominatorSquare))
      (same : root * root = value)
  /-- A negative numerator is the proved sign obstruction. -/
  | negative (negative : value.num < 0) (excludes : ∀ candidate : Rational, candidate * candidate ≠ value)
  /-- Retain the original numerator floor and its unequal square, excluding every rational root. -/
  | numerator (floor : SquareRoot.Output value.num.natAbs) (different : floor.root ^ 2 ≠ value.num.natAbs)
      (excludes : ∀ candidate : Rational, candidate * candidate ≠ value)
  /-- Retain the completed numerator work and the original denominator's unequal floor square. -/
  | denominator (numeratorFloor : SquareRoot.Output value.num.natAbs)
      (numeratorSquare : numeratorFloor.root ^ 2 = value.num.natAbs)
      (floor : SquareRoot.Output value.den) (different : floor.root ^ 2 ≠ value.den)
      (excludes : ∀ candidate : Rational, candidate * candidate ≠ value)

constructive_injectivity Outcome

set_option genInjectivity false in
/-- A complete rational-square inspection retaining the original canonical rational as executable data. -/
structure Inspection (original : Rational) where
  /-- The actual canonical rational inspected by the procedure. -/
  value : Rational
  /-- The retained value is the entire original rational record. -/
  value_eq : value = original
  /-- The cached root or precise obstruction at the same retained input. -/
  outcome : Outcome value

constructive_injectivity Inspection

/-- Transport the retained outcome to the original rational without repeating coordinate inspection. -/
@[expose] def Inspection.result {original : Rational} (inspection : Inspection original) : Outcome original :=
  inspection.value_eq ▸ inspection.outcome

/-- Read the actual cached root, with every obstruction retaining an absent root reading. -/
@[expose] def Outcome.root? {value : Rational} : Outcome value → Option Rational
  | .square _ _ _ _ root _ _ => some root
  | .negative _ _ => none
  | .numerator _ _ _ => none
  | .denominator _ _ _ _ _ => none

/-- Absence of a root reading consumes the outcome's retained all-input exclusion. -/
theorem Outcome.not_square_of_missing {value : Rational} (outcome : Outcome value)
    (missing : outcome.root? = none) : ∀ candidate : Rational, candidate * candidate ≠ value := by
  cases outcome with
  | square numeratorFloor numeratorSquare denominatorFloor denominatorSquare root root_eq same => cases missing
  | negative negative excludes => exact excludes
  | numerator floor different excludes => exact excludes
  | denominator numeratorFloor numeratorSquare floor different excludes => exact excludes

/-- A selected cached root satisfies the exact square equation retained by its original outcome. -/
theorem Outcome.square_of_root {value : Rational} (outcome : Outcome value) (candidate : Rational)
    (known : outcome.root? = some candidate) : candidate * candidate = value := by
  cases outcome with
  | square numeratorFloor numeratorSquare denominatorFloor denominatorSquare root root_eq same =>
      have selected : root = candidate := Option.some.inj known
      cases selected
      exact same
  | negative negative excludes => cases known
  | numerator floor different excludes => cases known
  | denominator numeratorFloor numeratorSquare floor different excludes => cases known

/-- Read the cached root at the original rational input owner. -/
@[expose] def Inspection.root? {original : Rational} (inspection : Inspection original) : Option Rational :=
  inspection.result.root?

/-- The actual selected root reading squares to the same original rational inspected by this certificate. -/
theorem Inspection.square_of_root {original : Rational} (inspection : Inspection original) (candidate : Rational)
    (known : inspection.root? = some candidate) : candidate * candidate = original :=
  inspection.result.square_of_root candidate known

/-- An inspection without a cached root excludes every rational root of its original input. -/
theorem Inspection.not_square_of_missing {original : Rational} (inspection : Inspection original)
    (missing : inspection.root? = none) : ∀ candidate : Rational, candidate * candidate ≠ original :=
  inspection.result.not_square_of_missing missing

/-- Inspect canonical coordinates once, returning a cached root or a complete rational-root exclusion. -/
@[expose] def inspect (value : Rational) : Inspection value :=
  let outcome := if negative : value.num < 0 then
      Outcome.negative negative (not_square_of_negative negative)
    else
      let numerator := SquareRoot.inspect value.num.natAbs
      match numerator.result with
      | .nonsquare floor different excludes =>
          Outcome.numerator floor different (not_square_of_numerator excludes)
      | .square numeratorFloor numeratorSquare =>
          let denominator := SquareRoot.inspect value.den
          match denominator.result with
          | .nonsquare floor different excludes =>
              Outcome.denominator numeratorFloor numeratorSquare floor different (not_square_of_denominator excludes)
          | .square denominatorFloor denominatorSquare =>
              let root := candidate numeratorFloor.root denominatorFloor.root
                (denominator_positive denominatorFloor.root denominatorSquare)
              Outcome.square numeratorFloor numeratorSquare denominatorFloor denominatorSquare root rfl
                (candidate_square value (Int.Order.le_of_not_lt negative)
                  _ _ numeratorSquare denominatorSquare)
  ⟨value, rfl, outcome⟩

end Purelib.Data.Rat.Fraction.Square

end

module

public import Purelib.Polynomial.Elimination.Separated.Replay
public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Conjugation
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
public import Purelib.Data.List.GetD
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Inverse.Prepared
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Polynomial.Elimination.Separated.Cubic

open Purelib.Data
open Purelib.Data.List (getD)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.LinearAlgebra.Matrix.Inverse.Scaled
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian

/-- Cancel the redundant terms in the cubic binomial denominator.

The equality is a polynomial identity and therefore includes zero denominators
and arbitrary complex coefficients.
-/
private theorem denominator_eq (c d h : Canonical) :
    let hSquared := h * h
    let a := 3 * h
    let b := -(3 * hSquared)
    let k := hSquared * h + c + d
    let aSquared := a * a
    let bSquared := b * b
    let kSquared := k * k
    kSquared * k + 3 * c * a * b * k +
      c * c * aSquared * a - c * bSquared * b =
      kSquared * k - 27 * c * d * (hSquared * h) := by
  dsimp only
  ring0

/-- Propose a unit column for an actual cubic coefficient table.

The default factors the original binomial denominator without a nonzero
assumption. The optional general request uses the original finite Euclidean
computation for the reflected and
original polynomials. Only its actual nonzero constant common factor supplies
a proposed column. Every proposal still requires the original matrix checker.
-/
@[expose] def propose? (p : CoefficientPolynomial) (parameter : Rational)
    (generalCubic : Bool := false) :
    Option (GaussianColumn.Vector Canonical (p.natDegree + p.natDegree)) :=
  match p.normalize.coeffs with
  | [leading, quadratic, linear, constant] =>
      if generalCubic && (quadratic != 0 || linear != 0) then
        if leading = 0 then none else
          let reflected := Substitution.Affine.composeLine (Conjugation.conjugate p)
            (2 * Gaussian.Cast.Path.ofCoordinate parameter) (-1)
          let result := GCD.extendedGCD reflected p
          match result.gcd.coeffs with
          | [unit] =>
              if unit = 0 then none else
                let reciprocal := unit⁻¹
                let left := result.left.coeffs.reverse
                let right := result.right.coeffs.reverse
                some (Vector.Basic.vectorOfFn fun row =>
                  if row.val < 3 then reciprocal * getD left row.val 0
                  else reciprocal * getD right (row.val - 3) 0)
          | _ => none
      else if leading = 0 ∨ quadratic ≠ 0 ∨ linear ≠ 0 then none else
        let leadingInverse := leading⁻¹
        let conjugateInverse := (Canonical.conj leading)⁻¹
        let c := constant * leadingInverse
        let d := Canonical.conj constant * conjugateInverse
        let h := 2 * Gaussian.Cast.Path.ofCoordinate parameter
        let hSquared := h * h
        let hCubed := hSquared * h
        let a := 3 * h
        let b := -(3 * hSquared)
        let k := hCubed + c + d
        let aSquared := a * a
        let bSquared := b * b
        let kSquared := k * k
        let x := kSquared + c * a * b
        let y := -(b * k) - c * aSquared
        let z := bSquared - a * k
        let denominator := kSquared * k - 27 * c * d * hCubed
        let reciprocal := Canonical.preparedInverse denominator
        let leftScale := reciprocal * conjugateInverse
        let rightScale := reciprocal * leadingInverse
        let leftZero := leftScale * x
        let leftOne := leftScale * y
        let leftTwo := leftScale * z
        let rightZero := rightScale * (x - a * y - b * z)
        let rightOne := rightScale * (y - a * z)
        let rightTwo := rightScale * z
        some (Vector.Basic.vectorOfFn fun row =>
          match row.val with
          | 0 => leftZero
          | 1 => leftOne
          | 2 => leftTwo
          | 3 => rightZero
          | 4 => rightOne
          | 5 => rightTwo
          | _ => 0)
  | _ => none

/-- The prepared proposal returns the complete original cubic candidate for every coefficient table and parameter.

Only the denominator reciprocal consumes its certified original norm cache.
The original coefficient gate, all six ordered values, total zero behavior
and every unavailable branch remain in the complete expression on the right.
-/
theorem propose?_eq_original (p : CoefficientPolynomial) (parameter : Rational) :
    propose? p parameter =
      match p.normalize.coeffs with
      | [leading, quadratic, linear, constant] =>
          if leading = 0 ∨ quadratic ≠ 0 ∨ linear ≠ 0 then none else
            let leadingInverse := leading⁻¹
            let conjugateInverse := (Canonical.conj leading)⁻¹
            let c := constant * leadingInverse
            let d := Canonical.conj constant * conjugateInverse
            let h := 2 * Gaussian.Cast.Path.ofCoordinate parameter
            let hSquared := h * h
            let a := 3 * h
            let b := -(3 * hSquared)
            let k := hSquared * h + c + d
            let aSquared := a * a
            let bSquared := b * b
            let kSquared := k * k
            let x := kSquared + c * a * b
            let y := -(b * k) - c * aSquared
            let z := bSquared - a * k
            let denominator := kSquared * k + 3 * c * a * b * k +
              c * c * aSquared * a - c * bSquared * b
            let reciprocal := denominator⁻¹
            let leftScale := reciprocal * conjugateInverse
            let rightScale := reciprocal * leadingInverse
            let leftZero := leftScale * x
            let leftOne := leftScale * y
            let leftTwo := leftScale * z
            let rightZero := rightScale * (x - a * y - b * z)
            let rightOne := rightScale * (y - a * z)
            let rightTwo := rightScale * z
            some (Vector.Basic.vectorOfFn fun row =>
              match row.val with
              | 0 => leftZero
              | 1 => leftOne
              | 2 => leftTwo
              | 3 => rightZero
              | 4 => rightOne
              | 5 => rightTwo
              | _ => 0)
      | _ => none := by
  unfold propose?
  split
  next leading quadratic linear constant shapeEq =>
    rewrite [Bool.false_and,
      if_neg (show ¬ ((false : Bool) = true) from fun h => Bool.noConfusion h)]
    split
    · rfl
    ·
      let leadingInverse := leading⁻¹
      let conjugateInverse := (Canonical.conj leading)⁻¹
      let c := constant * leadingInverse
      let d := Canonical.conj constant * conjugateInverse
      let h := 2 * Gaussian.Cast.Path.ofCoordinate parameter
      let hSquared := h * h
      let a := 3 * h
      let b := -(3 * hSquared)
      let k := hSquared * h + c + d
      let aSquared := a * a
      let bSquared := b * b
      let kSquared := k * k
      let x := kSquared + c * a * b
      let y := -(b * k) - c * aSquared
      let z := bSquared - a * k
      let denominator := kSquared * k + 3 * c * a * b * k +
        c * c * aSquared * a - c * bSquared * b
      exact congrArg (fun reciprocal : Canonical =>
        let leftScale := reciprocal * conjugateInverse
        let rightScale := reciprocal * leadingInverse
        let leftZero := leftScale * x
        let leftOne := leftScale * y
        let leftTwo := leftScale * z
        let rightZero := rightScale * (x - a * y - b * z)
        let rightOne := rightScale * (y - a * z)
        let rightTwo := rightScale * z
        some (Vector.Basic.vectorOfFn fun row =>
          match row.val with
          | 0 => leftZero
          | 1 => leftOne
          | 2 => leftTwo
          | 3 => rightZero
          | 4 => rightOne
          | 5 => rightTwo
          | _ => 0))
        ((congrArg Canonical.preparedInverse (denominator_eq c d h).symm).trans
          (Canonical.preparedInverse_eq denominator))
  next => rfl

set_option genInjectivity false in
/-- Retain a cubic proposal's original input, availability and checked outcome.

Absence keeps the actual normalized coefficient table. Rejection retains the
proposed vector and failed original matrix equation. Acceptance retains the
original checked column and its agreement with the proposed vector.
-/
inductive Attempt (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (generalCubic : Bool := false) where
  /-- The actual coefficient shape supplied no cubic proposal. -/
  | unavailable (coefficients : List Canonical)
      (coefficients_eq : coefficients = p.normalize.coeffs)
      (absent : propose? p parameter generalCubic = none)
  /-- The cubic proposal failed the original six-row matrix equation. -/
  | rejected (values : GaussianColumn.Vector Canonical (p.natDegree + p.natDegree))
      (proposed : propose? p parameter generalCubic = some values)
      (failure : Replay.Invalid p positive parameter values)
  /-- The cubic proposal solves the original matrix equation. -/
  | accepted (column : Replay.Column p positive parameter)
      (proposed : propose? p parameter generalCubic = some column.values)

constructive_injectivity Attempt

/-- Check an available cubic candidate against the original separated matrix.

Every original row is checked by `Replay.check`. No assumption about a
nonvanishing denominator or a real coefficient is used as a substitute.
-/
@[expose] def attempt (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (generalCubic : Bool := false) :
    Attempt p positive parameter generalCubic :=
  match proposed : propose? p parameter generalCubic with
  | none => .unavailable p.normalize.coeffs rfl proposed
  | some values =>
      match checked : Replay.check p positive parameter values with
      | .error failure => .rejected values proposed failure
      | .ok column => .accepted column (by
          have values_eq : column.values = values := by
            unfold Replay.check at checked
            dsimp only at checked
            split at checked
            · cases checked
              rfl
            · contradiction
          rewrite [values_eq]
          exact proposed)

/-- A false request retains the original complete binomial proposal procedure. -/
theorem propose?_default (p : CoefficientPolynomial) (parameter : Rational) :
    propose? p parameter false =
  match p.normalize.coeffs with
  | [leading, quadratic, linear, constant] =>
      if leading = 0 ∨ quadratic ≠ 0 ∨ linear ≠ 0 then none else
        let leadingInverse := leading⁻¹
        let conjugateInverse := (Canonical.conj leading)⁻¹
        let c := constant * leadingInverse
        let d := Canonical.conj constant * conjugateInverse
        let h := 2 * Gaussian.Cast.Path.ofCoordinate parameter
        let hSquared := h * h
        let a := 3 * h
        let b := -(3 * hSquared)
        let k := hSquared * h + c + d
        let aSquared := a * a
        let bSquared := b * b
        let kSquared := k * k
        let x := kSquared + c * a * b
        let y := -(b * k) - c * aSquared
        let z := bSquared - a * k
        let denominator := kSquared * k + 3 * c * a * b * k +
          c * c * aSquared * a - c * bSquared * b
        let reciprocal := denominator⁻¹
        let leftScale := reciprocal * conjugateInverse
        let rightScale := reciprocal * leadingInverse
        let leftZero := leftScale * x
        let leftOne := leftScale * y
        let leftTwo := leftScale * z
        let rightZero := rightScale * (x - a * y - b * z)
        let rightOne := rightScale * (y - a * z)
        let rightTwo := rightScale * z
        some (Vector.Basic.vectorOfFn fun row =>
          match row.val with
          | 0 => leftZero
          | 1 => leftOne
          | 2 => leftTwo
          | 3 => rightZero
          | 4 => rightOne
          | 5 => rightTwo
          | _ => 0)
  | _ => none := propose?_eq_original p parameter

/-- The default attempt retains the entire original checked branch and failure data. -/
theorem attempt_default (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) :
    attempt p positive parameter false =
      match proposed : propose? p parameter with
      | none => .unavailable p.normalize.coeffs rfl proposed
      | some values =>
          match checked : Replay.check p positive parameter values with
          | .error failure => .rejected values proposed failure
          | .ok column => .accepted column (by
              have values_eq : column.values = values := by
                unfold Replay.check at checked
                dsimp only at checked
                split at checked
                · cases checked
                  rfl
                · contradiction
              rewrite [values_eq]
              exact proposed) := (rfl)

end Purelib.Polynomial.Elimination.Separated.Cubic

end

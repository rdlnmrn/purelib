module

public import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Data.Gaussian.Cast
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Square
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
Direct unit-column proposals for real quadratics with no linear term.
The retained source polynomial and coordinate still index the original
separated Sylvester equation. Every proposal passes through its complete
checker before becoming an original normalized-cofactor certificate.
-/

public section

namespace Purelib.Polynomial.Elimination.Separated.Quadratic

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated

set_option genInjectivity false in
/-- A retained original quadratic whose normalized coefficients are real and have no linear term. -/
structure Shape (p : CoefficientPolynomial) where
  /-- The original leading Gaussian coefficient. -/ leading : Gaussian.Basic.Canonical
  /-- The original constant Gaussian coefficient. -/ constant : Gaussian.Basic.Canonical
  /-- The actual original natural degree is two. -/ degree_eq : p.natDegree = 2
  /-- The displayed coefficients are the original normalized coefficient table. -/
  coefficients_eq : p.normalize.coeffs = [leading, 0, constant]
  /-- The leading coefficient has zero imaginary coordinate. -/ leading_real : leading.im = 0
  /-- The constant coefficient has zero imaginary coordinate. -/ constant_real : constant.im = 0

constructive_injectivity Shape

/-- Recognize the real quadratic shape from the actual original degree and normalized coefficients.

Failure to recognize this elementary shape only means that this proposal rule
does not apply. It establishes no obstruction to the original general solver.
-/
@[expose] def shape (p : CoefficientPolynomial) : Option (Shape p) :=
  if degree : p.natDegree = 2 then
    match coefficients : p.normalize.coeffs with
    | [leading, middle, constant] =>
        if middleZero : middle = 0 then
          if leadingReal : leading.im = 0 then
            if constantReal : constant.im = 0 then
              some ⟨leading, constant, degree, by
                rewrite [middleZero] at coefficients
                exact coefficients, leadingReal, constantReal⟩
            else none
          else none
        else none
    | _ => none
  else none

/-- Materialize a quadratic unit-column proposal with its common rational factors retained once.

The first two entries multiply the reflected polynomial and the final two
multiply the lifted polynomial. Vanishing denominators still produce a finite
proposal; the complete original matrix equation decides its validity.
-/
@[expose] def Shape.propose {p : CoefficientPolynomial} (source : Shape p)
    (parameter : Fraction.Rational) :
    Data.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree) :=
  let four := Fraction.Cast.fromInt 4
  let three := Fraction.Cast.fromInt 3
  let denominator := four * (source.constant.re + source.leading.re * Fraction.square parameter)
  let common := denominator⁻¹
  let linear := common / parameter
  let reflectedConstant := Gaussian.Cast.Path.ofCoordinate common
  let reflectedLinear := Gaussian.Cast.Path.ofCoordinate linear
  let liftedConstant := Gaussian.Cast.Path.ofCoordinate (three * common)
  let liftedLinear := Gaussian.Cast.Path.ofCoordinate (-linear)
  Vector.Basic.vectorOfFn fun row =>
    if row.val = 0 then reflectedConstant
    else if row.val = 1 then reflectedLinear
    else if row.val = 2 then liftedConstant
    else liftedLinear

/-- The direct parameter square preserves the complete original proposal vector at every source and coordinate.

The reciprocal and all four retained entries are identical, including zero
coordinates and singular denominators. Consequently the complete matrix
checker receives the same original vector before deciding success or rejection.
-/
theorem Shape.propose_eq {p : CoefficientPolynomial} (source : Shape p) (parameter : Fraction.Rational) :
    source.propose parameter =
      let four := Fraction.Cast.fromInt 4
      let three := Fraction.Cast.fromInt 3
      let denominator := four * (source.constant.re + source.leading.re * (parameter * parameter))
      let common := denominator⁻¹
      let linear := common / parameter
      let reflectedConstant := Gaussian.Cast.Path.ofCoordinate common
      let reflectedLinear := Gaussian.Cast.Path.ofCoordinate linear
      let liftedConstant := Gaussian.Cast.Path.ofCoordinate (three * common)
      let liftedLinear := Gaussian.Cast.Path.ofCoordinate (-linear)
      Vector.Basic.vectorOfFn (n := p.natDegree + p.natDegree) fun row =>
        if row.val = 0 then reflectedConstant
        else if row.val = 1 then reflectedLinear
        else if row.val = 2 then liftedConstant
        else liftedLinear := by
  unfold Shape.propose
  rewrite [Fraction.square_eq_mul parameter]
  rfl

set_option genInjectivity false in
/-- The complete finite outcome of the quadratic proposal rule on an original separated system.

An unavailable rule retains the actual normalized coefficients and its exact
selection equation. Rejection retains the displayed original shape, proposed
vector and failed matrix equation. Success retains the original checked column.
-/
inductive Attempt (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) where
  /-- The rule did not recognize the retained original coefficient shape. -/
  | unavailable (coefficients : List Gaussian.Basic.Canonical)
      (coefficients_eq : coefficients = p.normalize.coeffs) (notSelected : shape p = none)
  /-- A recognized quadratic proposal failed the complete original equation. -/
  | rejected (source : Shape p)
      (values : Data.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree))
      (values_eq : values = source.propose parameter)
      (failure : Replay.Invalid p positive parameter values)
  /-- The proposed vector passed the original equation and is retained in its checked column. -/
  | accepted (source : Shape p) (column : Replay.Column p positive parameter)
      (values_eq : column.values = source.propose parameter)

constructive_injectivity Attempt

/-- Check the direct proposal against the same complete original separated Sylvester equation. -/
@[expose] def attempt (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) : Attempt p positive parameter :=
  match selected : shape p with
  | none => .unavailable p.normalize.coeffs rfl selected
  | some source =>
      let values := source.propose parameter
      match checked : Replay.check p positive parameter values with
      | .error failure => .rejected source values rfl failure
      | .ok column => .accepted source column (by
          unfold Replay.check at checked
          dsimp only at checked
          split at checked
          · cases checked
            rfl
          · cases checked)

end Purelib.Polynomial.Elimination.Separated.Quadratic

end

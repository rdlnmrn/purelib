module

import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Elimination.Axis.Cuts

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.Inverse.Check
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Geometry.Rational.Box.Intervals
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
/-! Exact restoration of the canonical safe-cut grid. Saved reciprocals are
checked against the original Bézout majorants by multiplication. The finite
cut search and majorant arithmetic remain validation work; neither alternative
cuts nor merely sufficient clearance bounds identify the original grid. -/
@[expose] public section

namespace Purelib.Polynomial.Clearance.Box.Grid.Four.Replay

open Purelib.RootIsolation.Isolation.AxisSafeCuts
open Purelib.Polynomial.Clearance.Pair.Bezout (bezoutSqMajorant bezoutSqMajorant_pos)

set_option genInjectivity false in
/-- Saved coordinates and scalar clearance bounds of a canonical four-cell grid.

The record contains proposed replay data; the checker must establish exact equality with the original safe cuts and
reciprocal majorants. -/
structure Data where
  /-- The saved vertical cut coordinate. -/ x : Fraction.Rational
  /-- The saved horizontal cut coordinate. -/ y : Fraction.Rational
  /-- The saved scalar bound of the vertical line clearance. -/ vertical : Fraction.Rational
  /-- The saved scalar bound of the horizontal line clearance. -/ horizontal : Fraction.Rational

constructive_injectivity Data

set_option genInjectivity false in
/-- A witnessed failure to reproduce a canonical grid coordinate or reciprocal clearance bound.

Every case retains the unequal operands and a proof of the failed equality. -/
inductive Invalid where
  /-- The saved coordinate differs from the expected coordinate; true tags the vertical axis. -/ | coordinate (vertical
    : Bool) (actual expected : Fraction.Rational) (different : actual ≠ expected)
  /-- The saved bound times its original majorant differs from one, with the exact computed product retained. -/ |
    reciprocal (vertical : Bool) (bound majorant product : Fraction.Rational)
      (product_eq : product = bound * majorant) (different : product ≠ 1)

constructive_injectivity Invalid

/-- Check that a saved coordinate equals the canonical safe coordinate.

Return the saved value with its exact equality, or retain the differing coordinates and axis tag. -/
def checkCoordinate (vertical : Bool) (actual expected :
  Fraction.Rational) :
    Except Invalid {value : Fraction.Rational // value = expected} :=
  if same : actual = expected then .ok ⟨actual, same⟩
  else .error (.coordinate vertical actual expected same)

/-- Check a saved reciprocal bound by multiplying it by the positive original majorant.

Success certifies equality to one divided by that majorant; failure retains the computed product and its inequality to
one. -/
def checkReciprocal (vertical : Bool) (bound majorant :
  Fraction.Rational) (positive : 0 < majorant) :
    Except Invalid {value : Fraction.Rational // value = 1 / majorant} :=
  let product := bound * majorant
  if same : product = 1 then .ok ⟨bound, Data.Rat.Inverse.Check.reciprocal_eq bound majorant positive same⟩
  else .error (.reciprocal vertical bound majorant product rfl same)

variable {p : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical)} {degreeBound : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) (box :
    Box) (proper : box.Proper)

/-- A retained four-cell grid together with exact equality to the original eliminant-based grid construction. -/
abbrev Checked := {grid :
  Clearance.Box.Grid.Four.Basic.ClearFourGrid p box // grid = Clearance.Box.Grid.Four.Elimination.buildClearFourGrid
  elimination box proper}

/-- Record the original grid's two safe coordinates and its two scalar line-clearance bounds. -/
def capture : Data :=
  let grid := Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination box proper
  ⟨grid.xCut, grid.yCut, grid.verticalClearance.bound, grid.horizontalClearance.bound⟩

/-- Supplying the original scalar bound preserves the entire line certificate;
its remaining fields are proofs. No division is evaluated by this adapter. -/
def vertical (x : Fraction.Rational) (safe :
  elimination.vertical.eval x ≠ 0)
    (bound : Fraction.Rational)
    (same : bound = (Clearance.Box.Line.Bezout.verticalOfCoprime p box x (elimination.vertical_coprime x safe)).bound) :
    Clearance.Box.Line.Basic.VerticalLineClearance p box x where
  bound := bound
  positive := by rw [same]; exact (Clearance.Box.Line.Bezout.verticalOfCoprime p box x (elimination.vertical_coprime x
    safe)).positive
  lower := by intro y lower upper; rw [same]; exact (Clearance.Box.Line.Bezout.verticalOfCoprime p box x
    (elimination.vertical_coprime x safe)).lower y lower upper

/-- Restoring the original vertical scalar bound reproduces the entire original vertical line-clearance certificate. -/
theorem vertical_eq (x : Fraction.Rational) (safe :
  elimination.vertical.eval x ≠ 0)
    (bound : Fraction.Rational)
    (same : bound = (Clearance.Box.Line.Bezout.verticalOfCoprime p box x (elimination.vertical_coprime x safe)).bound) :
    Clearance.Box.Grid.Four.Replay.vertical elimination box x safe bound same =
      Clearance.Box.Line.Bezout.verticalOfCoprime p box x (elimination.vertical_coprime x safe) := by
  cases same
  rfl

/-- Restore the horizontal line-clearance certificate using a scalar equal to its original bound.

The adapter retains that supplied scalar and transports the original positivity and lower-bound proofs without
evaluating division. -/
def horizontal (y : Fraction.Rational) (safe :
  elimination.horizontal.eval y ≠ 0)
    (bound : Fraction.Rational)
    (same : bound = (Clearance.Box.Line.Bezout.horizontalOfCoprime p box y (elimination.horizontal_coprime y
      safe)).bound) :
    Clearance.Box.Line.Basic.HorizontalLineClearance p box y where
  bound := bound
  positive := by rw [same]; exact (Clearance.Box.Line.Bezout.horizontalOfCoprime p box y (elimination.horizontal_coprime
    y safe)).positive
  lower := by intro x lower upper; rw [same]; exact (Clearance.Box.Line.Bezout.horizontalOfCoprime p box y
    (elimination.horizontal_coprime y safe)).lower x lower upper

/-- Restoring the original horizontal scalar bound reproduces the entire original horizontal line-clearance certificate.
-/
theorem horizontal_eq (y : Fraction.Rational) (safe :
  elimination.horizontal.eval y ≠ 0)
    (bound : Fraction.Rational)
    (same : bound = (Clearance.Box.Line.Bezout.horizontalOfCoprime p box y (elimination.horizontal_coprime y
      safe)).bound) :
    Clearance.Box.Grid.Four.Replay.horizontal elimination box y safe bound same =
      Clearance.Box.Line.Bezout.horizontalOfCoprime p box y (elimination.horizontal_coprime y safe) := by
  cases same
  rfl

/-- Return the exact original grid, or retain the unequal scalar operands. -/
def check (data : Data) : Except
  Invalid (Checked elimination box proper) := do
  let x ← checkCoordinate true data.x (Elimination.Axis.Cuts.verticalSafeCoordinate
    elimination box proper)
  let y ← checkCoordinate false data.y (Elimination.Axis.Cuts.horizontalSafeCoordinate
    elimination box proper)
  have xSpec : elimination.vertical.eval x.val ≠ 0 ∧ box.xLower < x.val ∧ x.val < box.xUpper := by
    rw [x.property]
    exact Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination box proper
  have ySpec : elimination.horizontal.eval y.val ≠ 0 ∧ box.yLower < y.val ∧ y.val < box.yUpper := by
    rw [y.property]
    exact Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination box proper
  let vx := elimination.vertical_coprime x.val xSpec.1
  let hy := elimination.horizontal_coprime y.val ySpec.1
  let vb ← checkReciprocal true data.vertical (bezoutSqMajorant vx
    (Box.Intervals.verticalInterval box))
    (Clearance.Pair.Bezout.bezoutSqMajorant_pos vx (Box.Intervals.verticalInterval box))
  let hb ← checkReciprocal false data.horizontal (bezoutSqMajorant hy
    (Box.Intervals.horizontalInterval box))
    (Clearance.Pair.Bezout.bezoutSqMajorant_pos hy (Box.Intervals.horizontalInterval box))
  let grid : Clearance.Box.Grid.Four.Basic.ClearFourGrid p box :=
    ⟨x.val, y.val, ⟨xSpec.2.1.le, xSpec.2.2.le⟩, ⟨ySpec.2.1.le, ySpec.2.2.le⟩,
      Clearance.Box.Grid.Four.Replay.vertical elimination box x.val xSpec.1 vb.val vb.property,
      Clearance.Box.Grid.Four.Replay.horizontal elimination box y.val ySpec.1 hb.val hb.property⟩
  return ⟨grid, by
    dsimp only [grid]
    rw [vertical_eq, horizontal_eq]
    rcases x with ⟨x, xEq⟩
    rcases y with ⟨y, yEq⟩
    dsimp only at *
    cases xEq
    cases yEq
    rfl⟩

end Purelib.Polynomial.Clearance.Box.Grid.Four.Replay

end

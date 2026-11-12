module

import TestPurelib.Polynomial.Recurrence.Boundary
import Purelib.Polynomial.Recurrence.Boundary.NormalForm
import Purelib.Polynomial.Recurrence.Mode.Hermite
import Purelib.LinearAlgebra.Matrix.NormalForm.Truncation
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Tactic.QuotientFreeOmega

/-!
# Actual coupled startup coordinates through the finite shift factorization

The original two root modes produce the literal coupled row [1,1/2]. The
original Hermite constructor supplies its actual initial coordinates, which
the derived boundary factorization transports without an elimination rank or
boundary-basis premise. Zero shifts retain zero-root transient columns.
-/

namespace TestPurelib.Polynomial.Recurrence.Boundary.NormalForm

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Recurrence.Mode
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

/-- The original two inside root blocks retain their positive single multiplicities. -/
private def blocks : List (Block Rational) := [⟨1 / 4, 1, by decide⟩, ⟨1 / 2, 1, by decide⟩]

/-- The same finite root-difference inverse table uses the original two indices. -/
private def differences : SquareMatrix Rational blocks.length :=
  .cons (.cons 0 (.cons (-4) .nil)) (.cons (.cons 4 (.cons 0 .nil)) .nil)

/-- Every original distinct-root difference multiplies its actual retained inverse to one. -/
private theorem difference_units : ∀ first second : Fin blocks.length, first ≠ second →
    (Hermite.point blocks first - Hermite.point blocks second) * differences first second = 1 := by decide +kernel

/-- The actual original word selects each of the two root blocks once. -/
private def word : List (Fin blocks.length) := [⟨0, by decide⟩, ⟨1, by decide⟩]

/-- The original general-ring constructor computes its actual complete Hermite inverse. -/
private def basis : Hermite blocks differences word := Hermite.prepare blocks differences difference_units word

/-- Both original mode windows have exactly the horizon needed by the first recurrence row. -/
private def values : Vec (Vec Rational 5) 2 :=
  .cons (Mode.window (1 / 4) 0 5) (.cons (Mode.window (1 / 2) 0 5) .nil)

/-- The actual finite mode transition is diagonal at these original root scalars. -/
private def step : SquareMatrix Rational 2 :=
  .cons (.cons (1 / 4) (.cons 0 .nil)) (.cons (.cons 0 (.cons (1 / 2) .nil)) .nil)

/-- The original finite windows follow that same transition at every available successor. -/
private theorem transition : Boundary.Transition values step := by
  intro index inside
  have range : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega0
  rcases range with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Both actual mode columns satisfy the original cubic coefficient equation at the retained startup index. -/
private theorem equations : Boundary.Equations Boundary.coupled 1 values := by
  unfold Boundary.Equations
  decide +kernel

/-- The same original finite triangular constructor supplies the actual root-unit transition inverse. -/
private def stepInverse := Triangular.inverseUpper step (by unfold Triangular.IsUpper; decide +kernel)
  (.cons 4 (.cons 2 .nil)) (by decide +kernel)

/-- The original inverse-power constructor computes the third power of the same cached first inverse. -/
private theorem inverse_cube_first : (stepInverse.val.power stepInverse.property 3).inverse 0 0 = 64 := by
  decide +kernel

/-- Its second diagonal cube is eight, independently of the startup factorization proof. -/
private theorem inverse_cube_second : (stepInverse.val.power stepInverse.property 3).inverse 1 1 = 8 := by
  decide +kernel

/-- The cached initial row is precisely the first original retained Hermite row. -/
private theorem initial_eq : Boundary.initial values 1 = Rectangular.takeRows (by decide : 1 ≤ 2) basis.matrix := by
  apply Rectangular.ext
  decide +kernel

/-- Initial coordinates come from the original full Hermite inverse, with no rank premise. -/
private def initialForm : NormalForm (Boundary.initial values 1) :=
  NormalForm.ofEq initial_eq.symm (NormalForm.ofInitialRows (by decide) basis.inverse basis.inverse_scalar)

/-- The derived finite factorization transports those same coordinates to the actual original boundary row. -/
private def normal : NormalForm (Boundary.matrix Boundary.coupled 1 values) :=
  Boundary.ofInitial Boundary.coupled 1 values step stepInverse.val stepInverse.property transition
    (by decide +kernel) equations (-4) (by decide +kernel) initialForm

/-- The actual original boundary matrix retains coefficient one. -/
private theorem first_entry : Boundary.matrix Boundary.coupled 1 values 0 0 = 1 := by decide +kernel

/-- Its actual coupled second coefficient is one half. -/
private theorem second_entry : Boundary.matrix Boundary.coupled 1 values 0 1 = 1 / 2 := by decide +kernel

/-- The original shift derivation produces one actual image coordinate. -/
private theorem rank : normal.rank = 1 := by decide +kernel

/-- The constructed original kernel basis uses first coefficient minus one. -/
private theorem kernel_first : normal.kernelVector (.cons 1 .nil) 0 = -1 := by decide +kernel

/-- Its second coefficient is two, satisfying the same literal coupled boundary equation. -/
private theorem kernel_second : normal.kernelVector (.cons 1 .nil) 1 = 2 := by decide +kernel

/-- Half of the actual retained free coordinate gives the normalized coupled witness. -/
private def halfWitness : Vec Rational 2 := normal.kernelVector (.cons (1 / 2) .nil)

/-- The normalized coupled witness is the literal half-coordinate combination of the same computed kernel basis. -/
private theorem half_basis : halfWitness = Rectangular.apply normal.kernelBasis (.cons (1 / 2) .nil) :=
  normal.kernelVector_eq_basis _

/-- Its first original mode coefficient is minus one half. -/
private theorem half_first : halfWitness 0 = -1 / 2 := by decide +kernel

/-- Its second original mode coefficient is one. -/
private theorem half_second : halfWitness 1 = 1 := by decide +kernel

/-- The same original coupled boundary matrix annihilates that reconstructed half-coordinate witness. -/
private theorem half_kernel : Rectangular.apply (Boundary.matrix Boundary.coupled 1 values) halfWitness =
    .cons 0 .nil := normal.matrix_kernelVector _

/-- Reading the normalized coupled witness recovers the same original free coordinate one half. -/
private theorem half_coordinates : normal.kernelCoordinates halfWitness = .cons (1 / 2) .nil :=
  normal.kernelCoordinates_kernelVector _

/-- The same computed source and complement coordinate counts give defect minus one. -/
private theorem defect : normal.defect = -1 := by decide +kernel

/-- A zero shift retains its original zero-root transient without a root-unit or inverse premise. -/
private def transient := Boundary.zeroShift Boundary.z (.cons (Mode.window (0 : Rational) 0 3) .nil)

/-- The actual zero-shift transient has its full one-dimensional source kernel. -/
private theorem transient_kernel : transient.kernelDimension = 1 := by decide +kernel

/-- Its complementary-target minus kernel count has the original positive-monomial sign. -/
private theorem transient_defect : transient.defect = -1 := by decide +kernel

/-- An empty original mode bank retains both actual target equations without unit premises. -/
private theorem empty_defect : (Boundary.emptyColumns (horizon := 3) Boundary.one 2).defect = 2 := by decide +kernel

end TestPurelib.Polynomial.Recurrence.Boundary.NormalForm

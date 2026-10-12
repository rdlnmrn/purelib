module
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Nat

/-!
# Divisibility of a natural cube by seven

The original remainder procedure reduces the displayed cube to its seven
possible residue classes. Only the zero residue can produce a cube divisible
by seven; its original quotient supplies the resulting divisibility witness.
-/

public section
namespace Purelib.NumberTheory.Divisibility.Seven.Cube

/-- If seven divides a displayed natural cube, it divides its base.

The proof retains the original natural remainder and checks all seven residue
classes. The zero-remainder certificate returns the original quotient as its factor.
-/
theorem seven_dvd_of_seven_dvd_cube {value : Nat}
    (divides : 7 ∣ value * value * value) : 7 ∣ value := by
  have cubeZero := Divisibility.mod_eq_zero_of_dvd divides
  have reducedSquare : (value * value) % 7 = (value % 7 * (value % 7)) % 7 :=
    (Remainder.Arithmetic.mul_mod_left value value 7).symm.trans
      (Remainder.Arithmetic.mul_mod_right (value % 7) value 7).symm
  have cubeReduction :
      (value * value * value) % 7 = (value % 7 * (value % 7) * (value % 7)) % 7 :=
    calc
      _ = ((value * value) % 7 * value) % 7 :=
        (Remainder.Arithmetic.mul_mod_left (value * value) value 7).symm
      _ = ((value % 7 * (value % 7)) % 7 * value) % 7 :=
        congrArg (fun residue : Nat => (residue * value) % 7) reducedSquare
      _ = (value % 7 * (value % 7) * value) % 7 :=
        Remainder.Arithmetic.mul_mod_left (value % 7 * (value % 7)) value 7
      _ = (value % 7 * (value % 7) * (value % 7)) % 7 :=
        (Remainder.Arithmetic.mul_mod_right (value % 7 * (value % 7)) value 7).symm
  have reducedCubeZero := cubeReduction.symm.trans cubeZero
  have remainderLt : value % 7 < 7 := Nat.mod_lt value (by decide)
  have residues :
      value % 7 = 0 ∨ value % 7 = 1 ∨ value % 7 = 2 ∨
        value % 7 = 3 ∨ value % 7 = 4 ∨ value % 7 = 5 ∨ value % 7 = 6 := by
    clear divides cubeZero reducedSquare cubeReduction reducedCubeZero
    omega0
  rcases residues with zero | one | two | three | four | five | six
  · exact Divisibility.of_mod_eq_zero zero
  · have impossible : (1 * 1 * 1 : Nat) % 7 = 0 :=
      (congrArg (fun residue : Nat => (residue * residue * residue) % 7) one).symm.trans reducedCubeZero
    exact False.elim ((by decide : (1 * 1 * 1 : Nat) % 7 ≠ 0) impossible)
  · have impossible : (2 * 2 * 2 : Nat) % 7 = 0 :=
      (congrArg (fun residue : Nat => (residue * residue * residue) % 7) two).symm.trans reducedCubeZero
    exact False.elim ((by decide : (2 * 2 * 2 : Nat) % 7 ≠ 0) impossible)
  · have impossible : (3 * 3 * 3 : Nat) % 7 = 0 :=
      (congrArg (fun residue : Nat => (residue * residue * residue) % 7) three).symm.trans reducedCubeZero
    exact False.elim ((by decide : (3 * 3 * 3 : Nat) % 7 ≠ 0) impossible)
  · have impossible : (4 * 4 * 4 : Nat) % 7 = 0 :=
      (congrArg (fun residue : Nat => (residue * residue * residue) % 7) four).symm.trans reducedCubeZero
    exact False.elim ((by decide : (4 * 4 * 4 : Nat) % 7 ≠ 0) impossible)
  · have impossible : (5 * 5 * 5 : Nat) % 7 = 0 :=
      (congrArg (fun residue : Nat => (residue * residue * residue) % 7) five).symm.trans reducedCubeZero
    exact False.elim ((by decide : (5 * 5 * 5 : Nat) % 7 ≠ 0) impossible)
  · have impossible : (6 * 6 * 6 : Nat) % 7 = 0 :=
      (congrArg (fun residue : Nat => (residue * residue * residue) % 7) six).symm.trans reducedCubeZero
    exact False.elim ((by decide : (6 * 6 * 6 : Nat) % 7 ≠ 0) impossible)

end Purelib.NumberTheory.Divisibility.Seven.Cube

module

import Purelib.Polynomial.Recurrence.Boundary.Constant
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Actual constant-source boundary coordinates and finite recurrence completeness

The Gaussian constant three has two genuine complementary target coordinates
and no source coordinates at shift two. Zero rows retain the original empty
case. A nonzero nilpotent coefficient algebra also supplies a constant unit,
so finite recurrence cancellation is not restricted to fields.
-/

namespace TestPurelib.Polynomial.Recurrence.Boundary.Constant

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Recurrence.Boundary (Constant)
open Purelib.Algebra.Quadratic (Pair)

/-- The original Gaussian source is the nonzero constant three. -/
private def source : DensePolynomial Canonical := ⟨[3]⟩

/-- Two original startup rows retain the original empty-column normal form and leading inverse one third. -/
private def constant := Constant.prepare source 2 (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (⟨1 / 3, 0⟩ : Canonical) (by decide +kernel)

/-- The actual source-derived horizon and original coordinate dimensions have the constant-symbol sign. -/
private theorem dimensions : constant.count = 3 ∧ constant.normal.rank = 0 ∧
    constant.normal.kernelDimension = 0 ∧ constant.normal.cokernelDimension = 2 ∧ constant.normal.defect = 2 :=
  by decide +kernel

/-- The actual original kernel basis has no source rows or free columns. -/
private theorem kernel_basis : constant.normal.kernelBasis = (.nil : Vec (Vec Canonical 0) 0) := rfl

/-- The original kernel constructor preserves its unique actual empty source vector. -/
private theorem kernel_vector : constant.normal.kernelVector .nil = (.nil : Vec Canonical 0) := rfl

/-- The original image basis has two actual target rows and no image columns. -/
private theorem image_basis :
    constant.normal.imageBasis = (.cons .nil (.cons .nil .nil) : Vec (Vec Canonical 0) 2) := rfl

/-- Both actual original complementary columns are precisely the independent target coordinate vectors. -/
private theorem complement_basis :
    constant.normal.complementBasis 0 ⟨0, by rewrite [constant.rank_eq]; decide +kernel⟩ = 1 ∧
      constant.normal.complementBasis 0 ⟨1, by rewrite [constant.rank_eq]; decide +kernel⟩ = 0 ∧
      constant.normal.complementBasis 1 ⟨0, by rewrite [constant.rank_eq]; decide +kernel⟩ = 0 ∧
      constant.normal.complementBasis 1 ⟨1, by rewrite [constant.rank_eq]; decide +kernel⟩ = 1 := by decide +kernel

/-- Reconstructing actual complementary coordinates preserves the independent literal vector. -/
private theorem complement_vector :
    constant.normal.complementVector (.cons 2 (.cons 5 .nil)) = (.cons 2 (.cons 5 .nil) : Vec Canonical 2) := by
  apply vector_ext
  intro index
  have entries : ∀ index : Fin 2,
      constant.normal.complementVector (.cons 2 (.cons 5 .nil)) index =
        (.cons 2 (.cons 5 .nil) : Vec Canonical 2) index := by decide +kernel
  exact entries index

/-- A nonzero value after the first retained reading fails the complete original constant recurrence. -/
private theorem all_starts_required :
    ¬ Boundary.Equations source 3 (.cons (.cons 0 (.cons 5 (.cons 0 .nil))) .nil) := by
  intro equations
  have same := constant.solution_zero (.cons 0 (.cons 5 (.cons 0 .nil))) equations
  have zero := vector_eq_at same ⟨1, by decide⟩
  change (5 : Canonical) = 0 at zero
  exact (by decide +kernel : (5 : Canonical) ≠ 0) zero

/-- Every actual finite solution of the original Gaussian constant three is its same zero vector. -/
private theorem complete (values : Vec Canonical 4)
    (equations : Boundary.Equations source 4 (.cons values .nil)) : values = vectorOfFn (fun _ => 0) :=
  constant.solution_zero values equations

/-- Zero original startup rows need only the singleton source coefficient horizon. -/
private def zero := Constant.prepare source 0 (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (⟨1 / 3, 0⟩ : Canonical) (by decide +kernel)

/-- The actual zero-row constant boundary has no kernel, complement or signed defect. -/
private theorem zero_dimensions : zero.count = 1 ∧ zero.normal.kernelDimension = 0 ∧
    zero.normal.cokernelDimension = 0 ∧ zero.normal.defect = 0 := by decide +kernel

/-- The original coefficient carrier has a nonzero square-zero element. -/
private abbrev Dual := Pair Canonical 0

/-- The same original nonzero nilpotent witnesses genuine zero divisors. -/
private def nilpotent : Dual := Pair.generator

/-- The actual nilpotent does not vanish although its square does. -/
private theorem zero_divisor : nilpotent ≠ 0 ∧ nilpotent * nilpotent = 0 := by decide +kernel

/-- The actual constant coefficient one plus the nilpotent is a unit in that same original ring. -/
private def dualSource : DensePolynomial Dual := ⟨[1 + nilpotent]⟩

/-- The original unit inverse one minus the nilpotent prepares the same complete constant recurrence. -/
private def dual := Constant.prepare dualSource 2 (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (1 - nilpotent) (by decide +kernel)

/-- Leading-unit cancellation proves every original finite solution zero even over this coefficient ring. -/
private theorem dual_complete (values : Vec Dual 3)
    (equations : Boundary.Equations dualSource 3 (.cons values .nil)) : values = vectorOfFn (fun _ => 0) :=
  dual.solution_zero values equations

/-- Checked same original caches restore the complete constant construction without another normal-form producer. -/
private theorem restore : Constant.ofNormal source 2 constant.normalized constant.nonzero constant.degreeZero
    constant.leadingInverse constant.leadingUnit constant.count constant.count_eq constant.normal constant.normal_eq =
      constant := rfl

end TestPurelib.Polynomial.Recurrence.Boundary.Constant

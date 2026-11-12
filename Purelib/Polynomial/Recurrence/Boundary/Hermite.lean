module

public import Purelib.Polynomial.Recurrence.Boundary.NormalForm
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Rectangle
public import Purelib.Polynomial.Dense.Roots.Units
public import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Polynomial.Recurrence.Mode.Roots
import Purelib.Data.List.Reverse
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original recurrence-boundary coordinates from retained root blocks

The actual original startup rows consume one retained rectangular Hermite
cache. The unshifted case requires no root units. Positive shifts retain
the same per-block quotient-derived units and the same original shift inverse
that transport those actual rows to their finite coordinate normal form.
-/

public section

namespace Purelib.Polynomial.Recurrence.Boundary

open Purelib.Polynomial
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] [DecidableEq K]
variable {polynomial : DensePolynomial K}

namespace Hermite

set_option genInjectivity false in
/-- The actual transport cache for zero or positive original startup shifts.

An unshifted rectangle needs no root inverse. A shifted rectangle retains
the original block-unit table and the same prepared shift, including its
exact producer equality on the original occurrence cache.
-/
inductive Transport (bank : Bank polynomial) {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (readings : Mode.Hermite.Rectangle bank.blocks bank.differenceInverses word rows count) where
  /-- No startup equations require a root inverse at shift zero. -/
  | unshifted (zero : rows = 0)
  /-- An empty original source word needs no root inverse at any startup shift. -/
  | empty (zero : word = [])
  /-- Positive startup transport retains the same original units and prepared shift. -/
  | shifted (units : bank.Units) (step : Mode.Hermite.Shift bank.blocks word readings.occurrences)
      (step_eq : step = Mode.Hermite.Shift.prepare bank.blocks word readings.occurrences
        (units.wordInverses word) (units.word_units word))

constructive_injectivity Transport

end Hermite

set_option genInjectivity false in
/-- Retained coordinates for the actual original polynomial's truncated boundary rows.

The original bank fixes the source and selected bounded root word. Its one
rectangular reading cache supplies the actual boundary columns and existing
normal form. The identity-block size follows from the computed transforms,
without an input rank, basis, or independent boundary factorization premise.
-/
structure Hermite (bank : Bank polynomial) (word : List (Fin bank.blocks.length)) (rows count : Nat) where
  /-- The one retained completed original basis and selected finite columns. -/
  readings : Mode.Hermite.Rectangle bank.blocks bank.differenceInverses word rows count
  /-- The actual absence or retained original unit transport for these same readings. -/
  transport : Hermite.Transport bank readings
  /-- The cached actual original truncated boundary matrix. -/
  boundary : Rectangular K rows word.length
  /-- These same retained columns produce the original source's actual startup rows. -/
  boundary_eq : boundary = matrix polynomial rows readings.values
  /-- The existing original coordinate normal form of that exact boundary cache. -/
  normal : NormalForm boundary
  /-- Its constructed identity-block size is the smaller actual dimension. -/
  rank_eq : normal.rank = Nat.min rows word.length

constructive_injectivity Hermite

namespace Hermite

/-- Combining the retained original mode columns reads the actual startup matrix on the same coefficients. -/
theorem startup_eq {bank : Bank polynomial} {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (retained : Hermite bank word rows count) (coefficients : Vec K word.length) :
    Recurrence.boundary polynomial rows
        (Rectangular.apply (Rectangular.transpose retained.readings.values) coefficients) =
      Rectangular.apply retained.boundary coefficients :=
  (matrix_apply polynomial rows retained.readings.values coefficients).trans
    (congrArg (fun matrix => Rectangular.apply matrix coefficients) retained.boundary_eq.symm)

/-- Every finite combination of the same admissible original columns satisfies all fully contained source rows.

The multiplicity bounds concern the original word, including repeated and
zero roots. The companion checks only coefficient rows wholly inside the
supplied horizon; the finite zero fallback imposes no extra right boundary.
-/
theorem horizon_satisfies {bank : Bank polynomial} {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (retained : Hermite bank word rows count) (companion : Dense.Companion polynomial)
    (admissible : ∀ column : Fin word.length,
      countBefore (word[column.val]'column.isLt) word column.val <
        (bank.block (word[column.val]'column.isLt)).multiplicity)
    (coefficients : Vec K word.length) :
    companion.Satisfies (Rectangular.apply (Rectangular.transpose retained.readings.values) coefficients) := by
  apply companion.satisfies_apply
  intro column
  have same : Rectangular.column (Rectangular.transpose retained.readings.values) column =
      Mode.window (bank.block (word[column.val]'column.isLt)).point
        (retained.readings.occurrences.orders column) count := by
    apply vector_ext
    intro index
    rewrite [Rectangular.column_at, Rectangular.transpose_apply, retained.readings.values_at, Mode.window_at]
    rfl
  rewrite [same]
  apply Mode.bank_window_satisfies bank companion
  rewrite [retained.readings.occurrences.order_spec]
  exact admissible column

/-- Every actual free boundary coordinate gives a zero-left startup solution and all fully contained tail rows. -/
theorem kernel_solution {bank : Bank polynomial} {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (retained : Hermite bank word rows count) (companion : Dense.Companion polynomial)
    (admissible : ∀ column : Fin word.length,
      countBefore (word[column.val]'column.isLt) word column.val <
        (bank.block (word[column.val]'column.isLt)).multiplicity)
    (coordinates : Vec K (word.length - retained.normal.rank)) :
    Recurrence.boundary polynomial rows (Rectangular.apply (Rectangular.transpose retained.readings.values)
        (retained.normal.kernelVector coordinates)) = vectorOfFn (fun _ => 0) ∧
      companion.Satisfies (Rectangular.apply (Rectangular.transpose retained.readings.values)
        (retained.normal.kernelVector coordinates)) := by
  constructor
  · exact (retained.startup_eq _).trans (retained.normal.matrix_kernelVector coordinates)
  · exact retained.horizon_satisfies companion admissible _

/-- Zero original startup rows recover exactly the same free normal-form coordinates of the supplied combination. -/
theorem kernel_coordinates {bank : Bank polynomial} {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (retained : Hermite bank word rows count) (coefficients : Vec K word.length)
    (startup : Recurrence.boundary polynomial rows
      (Rectangular.apply (Rectangular.transpose retained.readings.values) coefficients) = vectorOfFn (fun _ => 0)) :
    retained.normal.kernelVector (retained.normal.kernelCoordinates coefficients) = coefficients :=
  retained.normal.kernelVector_coordinates coefficients ((retained.startup_eq coefficients).symm.trans startup)

/-- Original zero-left startup conditions are exactly reconstruction from the same computed free coordinates. -/
theorem kernel_iff {bank : Bank polynomial} {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (retained : Hermite bank word rows count) (coefficients : Vec K word.length) :
    Recurrence.boundary polynomial rows
        (Rectangular.apply (Rectangular.transpose retained.readings.values) coefficients) = vectorOfFn (fun _ => 0) ↔
      retained.normal.kernelVector (retained.normal.kernelCoordinates coefficients) = coefficients := by
  constructor
  · exact retained.kernel_coordinates coefficients
  · intro recovered
    exact (retained.startup_eq coefficients).trans ((retained.normal.kernel_iff coefficients).mpr recovered)

/-- Original bounded root occurrences satisfy every available original startup polynomial equation.

The same normalized source identity preserves the supplied original table.
Each finite reading uses its actual cached root and occurrence order, whose
bound is the original block's retained multiplicity.
-/
theorem equations (bank : Bank polynomial) (normalized : polynomial.normalize = polynomial)
    {word : List (Fin bank.blocks.length)} {rows count : Nat}
    (readings : Mode.Hermite.Rectangle bank.blocks bank.differenceInverses word rows count)
    (room : rows + polynomial.coeffs.reverse.length ≤ count)
    (admissible : ∀ column : Fin word.length,
      countBefore (word[column.val]'column.isLt) word column.val <
        (bank.block (word[column.val]'column.isLt)).multiplicity) :
    Equations polynomial rows readings.values := by
  intro index column
  let original := word[column.val]'column.isLt
  have orderBound : readings.occurrences.orders column < (bank.block original).multiplicity := by
    rw [readings.occurrences.order_spec]
    exact admissible column
  have zero := Mode.bank_coefficientRow bank original (readings.occurrences.orders column) orderBound index.val
  rewrite [normalized] at zero
  have coefficientRow := Mode.coefficientRow_reverse polynomial.coeffs.reverse (bank.block original).point
    (readings.occurrences.orders column) index.val
  rewrite [Reverse.reverse_reverse] at coefficientRow
  calc
    _ = sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
        getD polynomial.coeffs.reverse coefficient.val 0 *
          Mode.entry (bank.block original).point (readings.occurrences.orders column)
            (index.val + coefficient.val)) := by
      apply sumFin_congr
      intro coefficient
      have inside : index.val + coefficient.val < count := by
        have firstBound := index.isLt
        have secondBound := coefficient.isLt
        omega0
      rw [readings.reading_at _ inside column]
      rfl
    _ = Mode.coefficientRow polynomial.coeffs (bank.block original).point
        (readings.occurrences.orders column) index.val := coefficientRow.symm
    _ = 0 := zero

/-- Construct an actual empty-column boundary cache without any constant or root inverse premise.

The original empty-word rectangle and original empty boundary producer retain
all target coordinates as a complement, at every requested startup shift.
-/
@[expose] def prepareEmpty (bank : Bank polynomial) (rows count : Nat) (room : rows ≤ count) :
    Hermite bank [] rows count :=
  let readings := Mode.Hermite.Rectangle.prepare bank.blocks bank.differenceInverses bank.difference_unit
    [] rows count room
  let boundary := matrix polynomial rows readings.values
  let normal : NormalForm boundary := emptyColumns polynomial rows
  { readings := readings
    transport := .empty rfl
    boundary := boundary
    boundary_eq := rfl
    normal := normal
    rank_eq := by cases rows <;> rfl }

/-- Construct an actual unshifted boundary cache without any constant or root inverse premise. -/
@[expose] def prepareZero (bank : Bank polynomial) (word : List (Fin bank.blocks.length)) (count : Nat) :
    Hermite bank word 0 count :=
  let readings := Mode.Hermite.Rectangle.prepare bank.blocks bank.differenceInverses bank.difference_unit
    word 0 count (Nat.zero_le count)
  let boundary := matrix polynomial 0 readings.values
  let normal := zeroShift polynomial readings.values
  { readings := readings
    transport := .unshifted rfl
    boundary := boundary
    boundary_eq := rfl
    normal := normal
    rank_eq := rfl }

/-- Construct the actual positive-shift boundary normal form from the original root bank.

The original normalized polynomial table is retained unchanged. One original
block-unit cache supplies every repeated mode occurrence, and one prepared
shift transports the actual startup rows through their proved factorization.
All recurrence equations and rectangular coordinates are constructed from
the original bank, without a final rank or basis premise.
-/
@[expose] def preparePositive (bank : Bank polynomial) (normalized : polynomial.normalize = polynomial)
    (word : List (Fin bank.blocks.length)) (shift count : Nat)
    (room : shift + 1 + polynomial.coeffs.reverse.length ≤ count)
    (admissible : ∀ column : Fin word.length,
      countBefore (word[column.val]'column.isLt) word column.val <
        (bank.block (word[column.val]'column.isLt)).multiplicity)
    (constantInverse : K) (constantUnit : polynomial.eval 0 * constantInverse = 1) :
    Hermite bank word (shift + 1) count := by
  have initialRoom : shift + 1 ≤ count := Nat.le_trans (Nat.le_add_right _ _) room
  let readings := Mode.Hermite.Rectangle.prepare bank.blocks bank.differenceInverses bank.difference_unit
    word (shift + 1) count initialRoom
  let units := Bank.Units.prepare bank constantInverse (by rw [polynomial.eval_normalize]; exact constantUnit)
  let step := Mode.Hermite.Shift.prepare bank.blocks word readings.occurrences
    (units.wordInverses word) (units.word_units word)
  let boundary := matrix polynomial (shift + 1) readings.values
  let initialNormal := NormalForm.ofEq readings.initial_eq readings.normal
  have originalConstant : getD polynomial.coeffs.reverse 0 0 * constantInverse = 1 := by
    rw [← polynomial.eval_at_zero]
    exact constantUnit
  let normal := ofInitial polynomial (shift + 1) readings.values step.matrix step.inverse step.inverse_scalar
    (readings.follows step) room (equations bank normalized readings room admissible)
    constantInverse originalConstant initialNormal
  exact
    { readings := readings
      transport := .shifted units step rfl
      boundary := boundary
      boundary_eq := rfl
      normal := normal
      rank_eq := (ofInitial_rank _ _ _ _ _ _ _ _ _ _ _ _).trans
        ((NormalForm.ofEq_rank readings.initial_eq readings.normal).trans readings.rank_eq) }

end Hermite

end Purelib.Polynomial.Recurrence.Boundary

end

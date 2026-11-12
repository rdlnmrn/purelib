module

import Purelib.Polynomial.Recurrence.Mode.Inverse
import Purelib.Polynomial.Recurrence.Mode.Hermite.Shift.Inverse
import Purelib.Polynomial.Recurrence.Mode.Hermite.Solution
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import Purelib.Tactic.Ring

/-!
# Negative powers of the original Gaussian Jordan shift

The retained original three-occurrence shift has root two. Its actual
inverse cubed agrees with the original reciprocal-root mode coefficients,
including both nontrivial strict-upper entries. The same original inside
request bounds those inverse coefficients at its computed late index.
-/

namespace TestPurelib.Polynomial.Recurrence.Mode.Inverse

open Purelib.Algebra.Quadratic
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List (Occurrences)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Recurrence.Mode
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Matrix

/-- The original exterior root retains three original confluent occurrences. -/
private def blocks : List (Block Canonical) := [⟨2, 3, by decide⟩]

/-- The same original block expansion fixes every repeated-root coordinate. -/
private def word : List (Fin blocks.length) := Word.expand blocks

/-- The same original occurrence producer retains predecessor coordinates once. -/
private def occurrences : Occurrences word := Occurrences.prepare word

/-- The actual physical Gaussian reciprocal is shared by every repeated occurrence. -/
private def inverses : Vec Canonical word.length := vectorOfFn fun _ => 1 / 2

/-- The supplied physical reciprocal satisfies the same original root-unit equation. -/
private theorem units : ∀ index : Fin word.length,
    Hermite.point blocks (word[index.val]'index.isLt) * inverses index = 1 := by decide +kernel

/-- The original shift and original triangular inverse are retained unchanged. -/
private def shift : Hermite.Shift blocks word occurrences :=
  Hermite.Shift.prepare blocks word occurrences inverses units

/-- The complete third inverse power has the literal original reciprocal-mode coefficients. -/
private theorem third_power : ∀ row column : Fin word.length,
    Arithmetic.power shift.inverse.inverse 3 row column =
      if row.val ≤ column.val then inverseEntry (1 / 2 : Canonical) (column.val - row.val) 3 else 0 := by
  decide +kernel

/-- The third power's second superdiagonal has its independently calculated nonzero value. -/
private theorem second_superdiagonal : inverseEntry (1 / 2 : Canonical) 2 3 = 3 / 16 := by decide +kernel

/-- The third power's first superdiagonal retains the negative original coefficient. -/
private theorem first_superdiagonal : inverseEntry (1 / 2 : Canonical) 1 3 = -(3 / 16) := by decide +kernel

/-- The original split quadratic ring has a generator whose square is four. -/
private abbrev Split := Pair Canonical (-4)

/-- The original quadratic generator is retained without any field structure. -/
private def splitGenerator : Split := Pair.generator

/-- The same two formal roots retain two occurrences each. -/
private def splitBlocks : List (Block Split) :=
  [⟨2 + splitGenerator, 2, by decide⟩, ⟨2 - splitGenerator, 2, by decide⟩]

/-- The original root-difference inverse is a unit even though neither individual root is a unit. -/
private def splitDifferences : Purelib.LinearAlgebra.Matrix Split splitBlocks.length := matrixOfFn fun row column =>
  if row = column then 0 else if row.val = 0 then Pair.scalar (1 / 8 : Canonical) * splitGenerator
    else -(Pair.scalar (1 / 8 : Canonical) * splitGenerator)

/-- The same original difference table satisfies all distinct-tag unit equations. -/
private theorem splitUnits : ∀ first second : Fin splitBlocks.length, first ≠ second →
    (Hermite.point splitBlocks first - Hermite.point splitBlocks second) * splitDifferences first second = 1 := by
  decide +kernel

/-- The original split roots factor the same degree-four source with a genuine double zero. -/
private def splitPolynomial : DensePolynomial Split := ⟨[1, -8, 16, 0, 0]⟩

/-- The literal original bank verifies the full repeated-root source in the same zero-divisor ring. -/
private def splitBank : Bank splitPolynomial where
  blocks := splitBlocks
  count_eq := by decide +kernel
  monicProduct := product splitBlocks
  product_eq := rfl
  factorization := by decide +kernel
  differenceInverses := splitDifferences
  difference_unit := splitUnits

/-- The retained formal occurrences interleave both original root blocks. -/
private def splitWord : List (Fin splitBlocks.length) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩]

/-- One original Hermite construction retains the same formal roots, word, predecessor cache and inverse. -/
private def splitBasis : Hermite splitBank.blocks splitBank.differenceInverses splitWord :=
  Hermite.prepare splitBank.blocks splitBank.differenceInverses splitBank.difference_unit splitWord

/-- The exact Gaussian component selects the generator value two. -/
private def component (value : Split) : Canonical := value.re + 2 * value.im

/-- The nonzero opposite component annihilates the formal exterior root. -/
private theorem splitProduct : (2 + splitGenerator) * (2 - splitGenerator) = 0 := by decide +kernel

/-- That opposite formal component is genuinely nonzero in the original ring. -/
private theorem splitOtherNonzero : (2 - splitGenerator : Split) ≠ 0 := by decide +kernel

/-- The original formal exterior root has no global inverse despite its exterior Gaussian component. -/
private theorem splitNonunit (inverse : Split) : (2 + splitGenerator) * inverse ≠ 1 := by
  intro unit
  have zero : (2 - splitGenerator : Split) = 0 := by
    calc
      _ = 1 * (2 - splitGenerator : Split) := (_root_.one_mul _).symm
      _ = ((2 + splitGenerator) * inverse) * (2 - splitGenerator) :=
        congrArg (fun value : Split => value * (2 - splitGenerator)) unit.symm
      _ = inverse * ((2 + splitGenerator) * (2 - splitGenerator)) := by ring0
      _ = 0 := by rewrite [splitProduct]; ring0
  exact splitOtherNonzero zero

/-- The original tag with positive Gaussian component is the only selected exterior block. -/
private def selected (index : Fin splitBlocks.length) : Bool := index.val == 0

/-- Exercise one partial physical inverse while the same original formal transition remains noninvertible. -/
private def checkPartial : IO Unit := do
  let roots := vectorOfFn (fun index : Fin splitBlocks.length => component (Hermite.point splitBlocks index))
  let reciprocals := vectorOfFn (fun index : Fin splitBlocks.length =>
    if selected index = true then Field.inv (roots index) else 0)
  let transition := Hermite.Shift.transition (fun index => roots index) splitWord splitBasis.occurrences
  let partialInverse := Hermite.Shift.inversePower (fun index => reciprocals index) selected splitWord
    splitBasis.occurrences 3
  let projector := Hermite.Shift.projection (K := Canonical) selected splitWord
  let coefficients : Vec Canonical splitWord.length := .cons 1 (.cons (-1) (.cons 0 (.cons 0 .nil)))
  let physicalPower := Arithmetic.power transition 3
  let shifted := Rectangular.apply physicalPower coefficients
  let formalCoefficients := Vec.map (fun value => (Pair.scalar value : Split)) coefficients
  let lateRows := splitBasis.horizonFrom 3 splitWord.length
  let formalValues := Rectangular.apply lateRows formalCoefficients
  let extracted := splitBasis.coordinates formalValues
  have _ := splitBasis.coordinates_horizonFrom 3 formalCoefficients
  have rootRead : ∀ tag, component (Hermite.point splitBlocks tag) = roots tag := by
    intro tag
    exact (vectorOfFn_apply (fun index : Fin splitBlocks.length =>
      component (Hermite.point splitBlocks index)) tag).symm
  have transitionRead := Hermite.Shift.map_transition_at component (by decide +kernel) (by decide +kernel)
    (Hermite.point splitBlocks) (fun tag => roots tag) rootRead splitWord splitBasis.occurrences
  have _ := transitionRead
  for index in List.ofFn (fun index : Fin splitWord.length => index) do
    unless component (extracted index) == shifted index do
      throw (IO.userError "the same original formal inverse lost its physical late-coordinate readback")
  let invisible : Vec Split splitWord.length := .cons (2 - splitGenerator) (.cons 0 (.cons 0 (.cons 0 .nil)))
  let invisibleValues := Rectangular.apply lateRows invisible
  for index in List.ofFn (fun index : Fin splitWord.length => index) do
    unless component (invisibleValues index) == 0 do
      throw (IO.userError "a nonzero formal coefficient was incorrectly declared physically observable")
  let recovered := Rectangular.apply partialInverse shifted
  have reciprocalUnits : ∀ column : Fin splitWord.length, selected (splitWord[column.val]'column.isLt) = true →
      reciprocals (splitWord[column.val]'column.isLt) * roots (splitWord[column.val]'column.isLt) = 1 := by
    decide +kernel
  have _ := Hermite.Shift.inversePower_apply (fun index => roots index) (fun index => reciprocals index)
    selected splitWord splitBasis.occurrences reciprocalUnits 3 coefficients
  for index in List.ofFn (fun index : Fin splitWord.length => index) do
    let expected := if selected (splitWord[index.val]'index.isLt) = true then coefficients index else 0
    unless recovered index == expected && Rectangular.apply projector coefficients index == expected do
      throw (IO.userError "the original partial inverse mixed an inside or zero-root block into recovery")
  let request := InverseRequest.prepare 16 (by decide +kernel) splitWord.length (1 / 100) (by decide +kernel)
  let late := Hermite.Shift.inversePower (fun index => reciprocals index) selected splitWord
    splitBasis.occurrences request.index
  have actualReciprocals : ∀ tag, selected tag = true → reciprocals tag = Field.inv (roots tag) := by
    intro tag chosen
    rewrite [vectorOfFn_apply, if_pos chosen]
    rfl
  have outside : ∀ tag, selected tag = true → (16 : Rational) ≤ Norm.Basic.normSq (roots tag) := by
    decide +kernel
  for row in List.ofFn (fun index : Fin splitWord.length => index) do
    for column in List.ofFn (fun index : Fin splitWord.length => index) do
      have _ := Hermite.Shift.inversePower_bound splitWord request (fun index => roots index)
        (fun index => reciprocals index) selected splitBasis.occurrences actualReciprocals outside
        request.index (Nat.le_refl _) row column
      unless decide ((late row column).normSq ≤ (1 / 100 : Rational)) do
        throw (IO.userError "the actual selected inverse matrix exceeded its original common finite request")
  unless (component (2 - splitGenerator)).normSq == 0 && decide ((2 - splitGenerator : Split) ≠ 0) do
    throw (IO.userError "a nonzero formal coefficient was incorrectly treated as a nonzero physical component")
  Purelib.System.IO.println "Partial physical recovery: formal nonunit roots, inside zero, interleaved repeated blocks."

/-- Run actual original inverse-power equality and its original computed finite inside requests. -/
public def run : IO Unit := do
  checkPartial
  let power := Arithmetic.power shift.inverse.inverse 3
  for row in List.ofFn (fun row : Fin word.length => row) do
    for column in List.ofFn (fun column : Fin word.length => column) do
      let expected := if row.val ≤ column.val then
        inverseEntry (1 / 2 : Canonical) (column.val - row.val) 3 else 0
      unless power row column == expected do
        throw (IO.userError "the actual original inverse Jordan power lost its reciprocal-mode coefficient")
  let request := InverseRequest.prepare 4 (by decide +kernel) 3 (1 / 100) (by decide +kernel)
  let inverse := Field.inv (2 : Canonical)
  have _ := request.restore
  for order in List.ofFn (fun order : Fin 3 => order) do
    have _ := request.bound (2 : Canonical) (by decide +kernel) order request.index (Nat.le_refl _)
    let value := inverseEntry inverse order.val request.index
    unless decide (value.normSq ≤ (1 / 100 : Rational)) do
      throw (IO.userError "the original inside request failed to bound its negative Jordan coefficient")
  Purelib.System.IO.println "Original inverse Jordan cube: diagonal1/8, first-3/16, second3/16; \
    reciprocal-mode requests paid."

end TestPurelib.Polynomial.Recurrence.Mode.Inverse

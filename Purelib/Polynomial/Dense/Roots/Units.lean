module

public import Purelib.Polynomial.Dense.Roots.Bank
public import Purelib.Polynomial.Dense.Division.Synthetic
public import Purelib.Data.Vector.Basic
public import Purelib.Data.List.DependentProduct
public import Purelib.Polynomial.Recurrence.Mode.Roots
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained units of original root blocks

Each original block retains one actual synthetic division and its certified
root inverse. Ordered mode words read that same finite cache, including when
several generalized coordinates use the same original block.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Bank

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Polynomial.Recurrence
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Division

variable {K : Type*} [CommRing K] [DecidableEq K]
variable {polynomial : DensePolynomial K}

set_option genInjectivity false in
/-- One original block's actual synthetic quotient and its retained root unit.

The normalized original polynomial and original bounded block index fix the
division owner. The same quotient certifies that the displayed root is a
unit, with no field or reduced-ring premise.
-/
structure RootUnit (bank : Bank polynomial) (index : Fin bank.blocks.length) where
  /-- The one retained original division at this exact original block root. -/
  division : Synthetic.Result polynomial.normalize (bank.block index).point
  /-- The same retained scan has zero remainder at this original root. -/
  remainder_zero : division.remainder = 0
  /-- The retained inverse and its original block-root unit equation. -/
  inverse : {value : K // (bank.block index).point * value = 1}

constructive_injectivity RootUnit

/-- The original dependent product retaining one root unit at each original block index.

The original bounded list family fixes every cached division owner. Its
structural product stores each produced entry once and reads the same
entry directly, with no positional wrapper or rebuilt quotient fields.
-/
abbrev Units (bank : Bank polynomial) := DependentProduct bank.blocks (RootUnit bank)

namespace Units

variable {bank : Bank polynomial}

/-- Read the same retained dependent entry at its original bounded block index. -/
@[expose] def get (retained : Units bank) (index : Fin bank.blocks.length) : RootUnit bank index :=
  DependentProduct.get bank.blocks retained index

/-- Read an original block's cached inverse scalar. -/
@[expose] def inverseAt (retained : Units bank) (index : Fin bank.blocks.length) : K :=
  (retained.get index).inverse.val

/-- The cached scalar inverts the same original block root. -/
theorem unitAt (retained : Units bank) (index : Fin bank.blocks.length) :
    (bank.block index).point * retained.inverseAt index = 1 :=
  (retained.get index).inverse.property

/-- Select the same cached block inverses in an original finite mode-word order. -/
@[expose] def wordInverses (retained : Units bank) (word : List (Fin bank.blocks.length)) : Vec K word.length :=
  vectorOfFn fun column => retained.inverseAt (word[column.val]'column.isLt)

/-- A repeated mode occurrence reads its same original block's retained inverse. -/
theorem wordInverses_at (retained : Units bank) (word : List (Fin bank.blocks.length))
    (column : Fin word.length) :
    retained.wordInverses word column = retained.inverseAt (word[column.val]'column.isLt) :=
  vectorOfFn_apply _ _

/-- Every selected inverse is a unit for the same original mode-word root. -/
theorem word_units (retained : Units bank) (word : List (Fin bank.blocks.length))
    (column : Fin word.length) :
    (bank.block (word[column.val]'column.isLt)).point * retained.wordInverses word column = 1 := by
  rw [wordInverses_at]
  exact retained.unitAt _

/-- Divide once per original block and retain its same quotient-derived root inverse.

The original normalized polynomial's constant inverse is shared by all blocks.
Each block scan and quotient-at-zero reading is computed once, before any
mode-word selection or repeated occurrence reads the retained table.
-/
@[expose] def prepare (bank : Bank polynomial) (constantInverse : K)
    (constantUnit : polynomial.normalize.eval 0 * constantInverse = 1) :
    Units bank :=
  let source := polynomial.normalize
  DependentProduct.ofFn bank.blocks fun index : Fin bank.blocks.length =>
    let division := Synthetic.divide source (bank.block index).point
    have zero : division.remainder = 0 := Mode.bank_synthetic_remainder bank index division
    let inverse := division.rootInverse zero constantInverse constantUnit
    { division := division, remainder_zero := zero, inverse := inverse }

end Units

end Purelib.Polynomial.Dense.Roots.Bank

end

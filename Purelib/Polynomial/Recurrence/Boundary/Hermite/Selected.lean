module

public import Purelib.Polynomial.Recurrence.Boundary.Hermite
public import Purelib.Polynomial.Dense.Roots.Word.Selection
public import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Boundary coordinates of labelled original root blocks

The actual original block labels produce the selected coordinate word and
its multiplicity certificates. The same retained selection then supplies
the original boundary construction, without caller-supplied word counts or
occurrence bounds. No geometric meaning of the labels is assumed here.
-/

public section

namespace Purelib.Polynomial.Recurrence.Boundary.Hermite

open Purelib.Data renaming Vector → Vec
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots

variable {K : Type*} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K}

set_option genInjectivity false in
/-- The original retained block selection and the actual boundary coordinates on its same computed word.

The original labels and complete word remain in the selection cache. Its
computed selected indices and certified multiplicities determine the exact
source coordinates of the retained original boundary normal form.
-/
structure Selected (bank : Bank polynomial) (rows count : Nat) where
  /-- The actual original labels, word caches and certified weighted count. -/
  selection : Word.Selection bank
  /-- The same computed selected word supplies every actual boundary column. -/
  result : Hermite bank selection.word rows count

constructive_injectivity Selected

namespace Selected

variable {bank : Bank polynomial} {rows count : Nat}

/-- The actual selected boundary's identity-block size uses its computed original weighted coordinate count. -/
theorem rank_count (retained : Selected bank rows count) :
    retained.result.normal.rank = Nat.min rows retained.selection.count := by
  rw [← retained.selection.length_eq]
  exact retained.result.rank_eq

/-- The actual complementary-target minus kernel dimension is rows minus the computed original selected count.

The original normal form first supplies its independent kernel and complement
coordinates. Their dimension difference is then read back through the same
selection's proved word length, rather than defined from the labels.
-/
theorem defect_count (retained : Selected bank rows count) :
    retained.result.normal.defect = (rows : Int) - (retained.selection.count : Int) := by
  rw [retained.result.normal.defect_eq, retained.selection.length_eq]

/-- Retain an actual empty selection and the original empty-column boundary cache.

The displayed equality concerns the already computed selected word. No
expansion or filter is repeated and no constant or root inverse is required.
-/
@[expose] def ofEmpty (selection : Word.Selection bank) (empty : selection.word = [])
    (rows count : Nat) (room : rows ≤ count) : Selected bank rows count :=
  { selection := selection
    result := empty.symm ▸ prepareEmpty bank rows count room }

/-- Construct zero-shift coordinates from the same retained selection without any root inverse premise. -/
@[expose] def ofSelectionZero (selection : Word.Selection bank) (count : Nat) : Selected bank 0 count :=
  { selection := selection
    result := Hermite.prepareZero bank selection.word count }

/-- Construct the actual positive-shift boundary normal form from the same retained selection.

The original labels, full word, filter and weighted count remain unchanged.
An empty retained word uses the original empty-column constructor directly;
otherwise its original admissibility certificate supplies the original
positive-shift construction. No selection, count or word expansion is repeated.
-/
@[expose] def ofSelectionPositive (selection : Word.Selection bank)
    (normalized : polynomial.normalize = polynomial) (shift count : Nat)
    (room : shift + 1 + polynomial.coeffs.reverse.length ≤ count)
    (constantInverse : K) (constantUnit : polynomial.eval 0 * constantInverse = 1) :
    Selected bank (shift + 1) count :=
  if empty : selection.word = [] then
    ofEmpty selection empty (shift + 1) count (Nat.le_trans (Nat.le_add_right _ _) room)
  else
    { selection := selection
      result := Hermite.preparePositive bank normalized selection.word shift count room selection.admissible
        constantInverse constantUnit }

/-- Zero-shift construction retains the complete original selection unchanged. -/
theorem ofSelectionZero_selection (selection : Word.Selection bank) (count : Nat) :
    (ofSelectionZero selection count).selection = selection := rfl

/-- Positive-shift construction retains the complete original selection in both actual branches. -/
theorem ofSelectionPositive_selection (selection : Word.Selection bank)
    (normalized : polynomial.normalize = polynomial) (shift count : Nat)
    (room : shift + 1 + polynomial.coeffs.reverse.length ≤ count)
    (constantInverse : K) (constantUnit : polynomial.eval 0 * constantInverse = 1) :
    (ofSelectionPositive selection normalized shift count room constantInverse constantUnit).selection = selection := by
  unfold ofSelectionPositive
  split <;> rfl

/-- Select the actual original blocks once and construct zero-shift coordinates without root inverses. -/
@[expose] def prepareZero (bank : Bank polynomial) (labels : Vec Bool bank.blocks.length) (count : Nat) :
    Selected bank 0 count :=
  let selection := Word.Selection.prepare bank labels
  ofSelectionZero selection count

/-- Select the original root coordinates once and construct their actual positive-shift normal form.

The same original producer computes one selection and delegates to its
retained-selection constructor. Both original empty and nonempty branches
preserve their complete boundary records and constant-unit hypotheses.
-/
@[expose] def preparePositive (bank : Bank polynomial) (normalized : polynomial.normalize = polynomial)
    (labels : Vec Bool bank.blocks.length) (shift count : Nat)
    (room : shift + 1 + polynomial.coeffs.reverse.length ≤ count)
    (constantInverse : K) (constantUnit : polynomial.eval 0 * constantInverse = 1) :
    Selected bank (shift + 1) count :=
  let selection := Word.Selection.prepare bank labels
  ofSelectionPositive selection normalized shift count room constantInverse constantUnit

/-- A retained original selection gives the complete same zero-shift result as the original label producer. -/
theorem ofSelectionZero_eq_prepare (labels : Vec Bool bank.blocks.length) (selection : Word.Selection bank)
    (selectionEq : selection = Word.Selection.prepare bank labels) (count : Nat) :
    ofSelectionZero selection count = prepareZero bank labels count := by
  cases selectionEq
  rfl

/-- A retained original selection gives the complete same positive-shift result as the original label producer. -/
theorem ofSelectionPositive_eq_prepare (labels : Vec Bool bank.blocks.length) (selection : Word.Selection bank)
    (selectionEq : selection = Word.Selection.prepare bank labels)
    (normalized : polynomial.normalize = polynomial) (shift count : Nat)
    (room : shift + 1 + polynomial.coeffs.reverse.length ≤ count)
    (constantInverse : K) (constantUnit : polynomial.eval 0 * constantInverse = 1) :
    ofSelectionPositive selection normalized shift count room constantInverse constantUnit =
      preparePositive bank normalized labels shift count room constantInverse constantUnit := by
  cases selectionEq
  rfl

end Selected

end Purelib.Polynomial.Recurrence.Boundary.Hermite

end

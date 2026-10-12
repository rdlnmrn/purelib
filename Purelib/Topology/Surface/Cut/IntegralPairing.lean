module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Division
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Cut.BoundaryWord
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Init.Data.Int.Lemmas
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Vector.Basic
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Integer pairing from the actual signed cut occurrences

Each paired generator occurs once in each orientation. Its total coefficient
therefore vanishes, making the alternating area coefficient even. The cached
integer paired block is accompanied by the complete remaining matrix; mixed
terms involving physical boundary edges must not silently disappear.
-/

namespace Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib
open Purelib.Algebra
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Data.Int

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Topology.Surface.Word.Pairing
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)

namespace Word

variable {count : Nat}

/-- Sum the ordered coordinate cross terms of an original coefficient word.

Every original head row is multiplied by the retained remaining column
total, then added to the same recursive suffix sum. The order of the
supplied finite coefficient rows determines these cross terms. -/
@[expose] def orderedAt : List (Pairing.Coefficients count) → Fin count → Fin count → Int
  | [], _, _ => 0
  | letter :: rest, row, column => letter row * Pairing.totalAt rest column +
    Purelib.Topology.Surface.Cut.IntegralPairing.Word.orderedAt rest row column

open Purelib.Topology.Surface.Cut.IntegralPairing in
/-- Distinct signed coordinates express pairing as twice the ordered contribution.

The product of the original two total coefficients is subtracted from that
contribution. Each retained signed letter has zero product at the two
distinct coordinates, so the original ordered suffix sum gives the equality. -/
theorem pairing_eq_twice_ordered (word : List (SignedWord.SignedGenerator count)) {row column : Fin count} (different :
  row ≠ column) :
    Pairing.pairingAt (word.map SignedGenerator.coefficients) row column =
      2 * Word.orderedAt (word.map SignedGenerator.coefficients) row column -
        Pairing.totalAt (word.map SignedGenerator.coefficients) row * Pairing.totalAt (word.map
          SignedGenerator.coefficients) column := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      rw [List.map_cons, Pairing.pairingAt, Word.orderedAt, Pairing.totalAt, Pairing.totalAt, ih]
      calc
        _ = (2 * (letter.coefficients row * Pairing.totalAt (rest.map SignedGenerator.coefficients) column +
              Word.orderedAt (rest.map SignedGenerator.coefficients) row column) -
            (letter.coefficients row + Pairing.totalAt (rest.map SignedGenerator.coefficients) row) *
              (letter.coefficients column + Pairing.totalAt (rest.map SignedGenerator.coefficients) column)) +
            letter.coefficients row * letter.coefficients column := by ring1
        _ = _ := by rw [letter.coefficients_mul_of_ne different, Int.add_zero]

end Word

section CutBoundaryWord

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

namespace CutBoundaryWord

/-- Read the exact positive and negative generator counts from the retained cyclic word. -/
theorem occurrences_eq (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count) (reversed :
  Bool) :
    SignedGenerator.occurrences ⟨index, reversed⟩ word.letters =
      if reversed && word.alphabet.oneSided index then 0 else 1 := by
  rw [word.letters_eq]
  exact word.alphabet.occurrences_eq index reversed

end CutBoundaryWord

namespace CutBoundaryWord

open Purelib.Topology.Surface.Cut.IntegralPairing in
/-- The retained total is one on physical generators and zero on paired generators. -/
theorem total_eq_oneSided (word : BoundaryWord.CutBoundaryWord labels edges) (index : Fin word.alphabet.count) :
    word.signature.total index = if word.alphabet.oneSided index then 1 else 0 := by
  rw [word.signature.total_eq, word.coefficients_eq, SignedGenerator.total_eq_counts,
    CutBoundaryWord.occurrences_eq word, CutBoundaryWord.occurrences_eq word]
  cases word.alphabet.oneSided index <;> decide

end CutBoundaryWord

namespace CutBoundaryWord

/-- Every alternating-matrix entry in a paired row is exactly divisible by two.

The original paired row has zero total coefficient. At distinct coordinates,
the signed-word pairing is twice its retained ordered contribution, so the
original integer quotient cancels the nonzero factor two exactly. -/
theorem matrix_even_of_paired (word : BoundaryWord.CutBoundaryWord labels edges)
    (row column : Fin word.alphabet.count)
    (paired : word.alphabet.oneSided row = false) :
    2 * (word.signature.matrix row column / 2) = word.signature.matrix row column := by
  by_cases same : row = column
  · cases same
    rw [word.signature.diagonal]
    rfl
  · have total : Pairing.totalAt (word.letters.map SignedGenerator.coefficients) row = 0 := by
      rw [← word.coefficients_eq, ← word.signature.total_eq, CutBoundaryWord.total_eq_oneSided word, paired]
      rfl
    rw [word.signature.matrix_eq, word.coefficients_eq,
      Word.pairing_eq_twice_ordered word.letters same, total,
      Arithmetic.zero_mul, Arithmetic.sub_zero]
    rw [Division.mul_ediv_cancel_left _ (by decide : (2 : Int) ≠ 0)]

-- Retain the original IntegralPairing.CutBoundaryWord.IntegralPairing owner name.

end CutBoundaryWord

set_option genInjectivity false in
/-- Retain the integral paired block and all remaining physical boundary interactions.

The cached paired block halves entries with two paired generator coordinates.
The residual matrix retains every original signature entry minus twice that
same paired entry, including interactions with physical boundary coordinates. -/
structure CutBoundaryWord (word : BoundaryWord.CutBoundaryWord labels edges) where
  /-- Cached integral block supported on pairs of two-sided generator coordinates. -/ paired : Pairing.IntegralMatrix
    word.alphabet.count
  /-- Paired entries halve the original area matrix; entries touching one-sided generators vanish. -/ paired_eq : ∀ row
    column, paired row column =
    if word.alphabet.oneSided row || word.alphabet.oneSided column then 0 else word.signature.matrix row column / 2
  /-- Cached matrix of all interactions left after removing twice the paired block. -/ remaining :
    Pairing.IntegralMatrix word.alphabet.count
  /-- Each residual entry is the original signature entry minus twice the paired entry. -/ remaining_eq : ∀ row column,
    remaining row column = word.signature.matrix row column - 2 * paired row column

constructive_injectivity CutBoundaryWord

namespace CutBoundaryWord

-- These methods belong to the same retained repeated owner name.

section
open Purelib.Topology.Surface.Cut.IntegralPairing
/-- Cache the halved paired block and the complete remaining interaction matrix.

The original area signature is reused, and all entries involving one-sided generators remain in the residual matrix. -/
@[expose] def build (word : BoundaryWord.CutBoundaryWord labels edges) : CutBoundaryWord word :=
  let paired := LinearAlgebra.Matrix.matrixOfFn fun row column =>
    if word.alphabet.oneSided row || word.alphabet.oneSided column then 0 else word.signature.matrix row column / 2
  { paired := paired
    paired_eq := fun row column => LinearAlgebra.Matrix.matrixOfFn_apply _ row column
    remaining := LinearAlgebra.Matrix.matrixOfFn fun row column => word.signature.matrix row
      column - 2 * paired row column
    remaining_eq := fun row column => LinearAlgebra.Matrix.matrixOfFn_apply _ row column }

/-- Twice a fully paired entry recovers its original cached area-matrix coefficient. -/
theorem paired_twice {word : BoundaryWord.CutBoundaryWord labels edges} (pairing : CutBoundaryWord word)
    (row column : Fin word.alphabet.count) (first : word.alphabet.oneSided row = false) (last : word.alphabet.oneSided
      column = false) :
    2 * pairing.paired row column = word.signature.matrix row column := by
  rw [pairing.paired_eq, first, last]
  exact CutBoundaryWord.matrix_even_of_paired word row column first

end

/-- The retained paired integral block is skew-symmetric.

At two paired coordinates, exact factor-two certificates and the original
signature's skew equation identify the two retained entries by scalar
cancellation. Entries touching physical coordinates are both zero. -/
theorem paired_skew {word : BoundaryWord.CutBoundaryWord labels edges}
    (pairing : CutBoundaryWord word) (row column : Fin word.alphabet.count) :
    pairing.paired row column = -pairing.paired column row := by
  cases first : word.alphabet.oneSided row <;> cases last : word.alphabet.oneSided column
  · have forward := pairing.paired_twice row column first last
    have backward := pairing.paired_twice column row last first
    have negated : (2 : Int) * -pairing.paired column row =
        -(2 * pairing.paired column row) :=
      (Arithmetic.mul_comm _ _).trans ((Arithmetic.neg_mul _ _).trans
        (congrArg (fun entry : Int => -entry) (Arithmetic.mul_comm _ _)))
    have equal : (2 : Int) * pairing.paired row column =
        2 * -pairing.paired column row :=
      forward.trans ((word.signature.skew row column).trans
        ((congrArg (fun entry : Int => -entry) backward).symm.trans negated.symm))
    exact Arithmetic.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0) equal
  all_goals rw [pairing.paired_eq, pairing.paired_eq, first, last]; rfl

/-- The residual matrix vanishes where both generator coordinates are paired.

The same paired-entry certificate recovers the original signature entry
when doubled. Its retained residual equation therefore subtracts two equal
original integers and gives zero directly. -/
theorem remaining_paired_zero {word : BoundaryWord.CutBoundaryWord labels edges}
    (pairing : CutBoundaryWord word)
    (row column : Fin word.alphabet.count)
    (first : word.alphabet.oneSided row = false)
    (last : word.alphabet.oneSided column = false) :
    pairing.remaining row column = 0 :=
  (pairing.remaining_eq row column).trans
    (Arithmetic.sub_eq_zero_of_eq (pairing.paired_twice row column first last).symm)

/-- Every diagonal entry of the paired block is zero.

Skew symmetry makes the retained diagonal equal to its own negation.
Doubling that same integer gives zero, and cancellation of the nonzero
factor two forces the original diagonal entry to vanish. -/
theorem paired_diagonal {word : BoundaryWord.CutBoundaryWord labels edges}
    (pairing : CutBoundaryWord word) (index : Fin word.alphabet.count) :
    pairing.paired index index = 0 := by
  have skew := pairing.paired_skew index index
  have twice : (2 : Int) * pairing.paired index index = 0 :=
    (Arithmetic.ofNat_succ_mul 1 _).trans
      ((congrArg (fun entry => entry + pairing.paired index index) (Int.one_mul _)).trans
        ((congrArg (fun entry => entry + pairing.paired index index) skew).trans
          (Arithmetic.neg_add_cancel _)))
  exact Arithmetic.eq_of_mul_eq_mul_left (by decide : (2 : Int) ≠ 0)
    (twice.trans (Int.mul_zero 2).symm)

open Purelib.Topology.Surface.Cut.IntegralPairing
/-- The base case of handle reduction needs no matrix evaluation: with at most one paired generator, skew-symmetry
forces its whole paired block to zero. -/
theorem paired_zero_of_unique {word : BoundaryWord.CutBoundaryWord labels edges} (pairing :
  CutBoundaryWord word)
    (candidate : Fin word.alphabet.count)
    (only : ∀ index, word.alphabet.oneSided index = false → index = candidate)
    (row column : Fin word.alphabet.count) : pairing.paired row column = 0 := by
  cases first : word.alphabet.oneSided row <;> cases last : word.alphabet.oneSided column
  · rw [only row first, only column last]
    exact pairing.paired_diagonal candidate
  all_goals rw [pairing.paired_eq, first, last]; rfl

/-- Every diagonal entry of the residual block is zero. -/
theorem remaining_diagonal {word : BoundaryWord.CutBoundaryWord labels edges} (pairing : CutBoundaryWord
  word) (index : Fin word.alphabet.count) :
    pairing.remaining index index = 0 := by
  rw [pairing.remaining_eq, word.signature.diagonal, pairing.paired_diagonal]
  rfl

/-- The complete residual interaction matrix is skew-symmetric. -/
theorem remaining_skew {word : BoundaryWord.CutBoundaryWord labels edges} (pairing : CutBoundaryWord
  word) (row column : Fin word.alphabet.count) :
    pairing.remaining row column = -pairing.remaining column row := by
  rw [pairing.remaining_eq, pairing.remaining_eq, word.signature.skew row column, pairing.paired_skew row column]
  ring1

/-- The original area contraction is twice its paired-block contraction plus the full residual contraction. -/
theorem contract_eq {word : BoundaryWord.CutBoundaryWord labels edges} (pairing : CutBoundaryWord word)
    (values : Fin word.alphabet.count → Stokes.PrimitivePoint) :
    Pairing.contract (fun row column => word.signature.matrix row column) values =
      2 * Pairing.contract (fun row column => pairing.paired row column) values +
        Pairing.contract (fun row column => pairing.remaining row column) values := by
  have pointwise (row column : Fin word.alphabet.count) :
      word.signature.matrix row column = pairing.paired row column + pairing.paired row column + pairing.remaining row
        column := by
    rw [pairing.remaining_eq]
    ring1
  have expanded : Pairing.contract (fun row column => word.signature.matrix row column) values =
      Pairing.contract (fun row column => pairing.paired row column + pairing.paired row column + pairing.remaining row
        column) values := by
    unfold Pairing.contract
    apply FiniteSum.Fin.sumFin_congr; intro row
    apply FiniteSum.Fin.sumFin_congr; intro column
    dsimp only
    rw [pointwise]
  rw [expanded, Pairing.contract_add, Pairing.contract_add]
  ring1

end CutBoundaryWord

end CutBoundaryWord

end Purelib.Topology.Surface.Cut.IntegralPairing

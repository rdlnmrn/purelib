module

public import Purelib.Data.Vector.Basic
public import Purelib.Curves.Hyperelliptic.Topology.Cells
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Topology.Surface.CellularHomology
public import Init.Data.Fin.Lemmas
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Tactic.Ring
public import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Topology.BranchedCover.Double

public section

/-!
# Cellular `H₁` of the odd-degree hyperelliptic attaching model

For `2g+2` ramified vertices, an edge chain consists of two coefficients on
every equatorial base edge.  The vertex-cycle condition says that the sum of
the two sheet coefficients is constant around the polygon.  Three independent
face boundaries remove that constant and one reference coefficient in each
parity class.  The remaining tail has exactly `2g` freely displayed integral
coordinates.

The proofs below are explicit finite coordinate calculations.  They show that
every cycle is a canonical representative plus a face boundary and that a
canonical representative can be a boundary only when all its coordinates
vanish.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology

open Purelib.Curves.Hyperelliptic.Topology.Cells (oddFaceSheet)
open Purelib.Topology.BranchedCover.Double.Attachment (Face sheetZero sheetOne sheet_eq_zero_or_one)

/-- The twice-genus-plus-two base-edge count of the odd-degree attaching polygon. -/
abbrev EdgeCount (genus : Nat) := 2 * genus + 2
/-- The twice-genus number of free integral homology coordinates. -/
abbrev TailRank (genus : Nat) := 2 * genus
/-- An executable integral vector indexed by the original base edges. -/
abbrev EdgeVector (genus : Nat) :=
  Data.Vector Int (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)

/-- An executable integral vector of the free homology tail coordinates. -/
abbrev TailVector (genus : Nat) :=
  Data.Vector Int (Curves.Hyperelliptic.Topology.OddCellularHomology.TailRank genus)

set_option genInjectivity false in
/-- Integral coefficients on the two lifted copies of every base edge. -/
structure EdgeChain (genus : Nat) where
  /-- The retained integral coefficients on the zero-sheet lifted edges. -/ sheetZero :
    Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeVector genus
  /-- The retained integral coefficients on the one-sheet lifted edges. -/ sheetOne :
    Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeVector genus

constructive_injectivity EdgeChain

namespace EdgeChain

/-- Pointwise equality of both retained sheet coefficient vectors identifies an edge chain. -/
theorem ext {genus : Nat} {left right : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus}
    (zeroEqual : forall index, left.sheetZero index = right.sheetZero index)
    (oneEqual : forall index, left.sheetOne index = right.sheetOne index) :
    left = right := by
  cases left with
  | mk leftZero leftOne =>
      cases right with
      | mk rightZero rightOne =>
          have zeroVector : leftZero = rightZero := Data.Vector.Basic.vector_ext zeroEqual
          have oneVector : leftOne = rightOne := Data.Vector.Basic.vector_ext oneEqual
          cases zeroVector
          cases oneVector
          rfl

/-- Add two edge chains coefficientwise on both original sheet families. -/
@[expose] def add {genus : Nat} (left right : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) :
  Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index =>
    left.sheetZero index + right.sheetZero index
  sheetOne := Data.Vector.Basic.vectorOfFn fun index =>
    left.sheetOne index + right.sheetOne index

/-- The edge chain with zero coefficient on both lifts of every base edge. -/
@[expose] def zero (genus : Nat) : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun _ => 0
  sheetOne := Data.Vector.Basic.vectorOfFn fun _ => 0

/-- Multiply both retained sheet coefficient vectors by an integral scalar. -/
@[expose] def scale {genus : Nat} (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) (scalar :
  Int) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index => scalar * chain.sheetZero index
  sheetOne := Data.Vector.Basic.vectorOfFn fun index => scalar * chain.sheetOne index

/-- Adding edge chains adds their zero-sheet coefficient at each original edge. -/
@[simp] theorem add_sheetZero {genus : Nat} (left right : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain
  genus)
    (index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (left.add right).sheetZero index =
      left.sheetZero index + right.sheetZero index := by
  unfold OddCellularHomology.EdgeChain.add
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Adding edge chains adds their one-sheet coefficient at each original edge. -/
@[simp] theorem add_sheetOne {genus : Nat} (left right : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain
  genus)
    (index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (left.add right).sheetOne index =
      left.sheetOne index + right.sheetOne index := by
  unfold OddCellularHomology.EdgeChain.add
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Scaling an edge chain multiplies each zero-sheet coefficient by the retained scalar. -/
@[simp] theorem scale_sheetZero {genus : Nat} (scalar : Int)
    (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) (index : Fin
      (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (chain.scale scalar).sheetZero index = scalar * chain.sheetZero index := by
  unfold OddCellularHomology.EdgeChain.scale
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Scaling an edge chain multiplies each one-sheet coefficient by the retained scalar. -/
@[simp] theorem scale_sheetOne {genus : Nat} (scalar : Int)
    (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) (index : Fin
      (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (chain.scale scalar).sheetOne index = scalar * chain.sheetOne index := by
  unfold OddCellularHomology.EdgeChain.scale
  rw [Data.Vector.Basic.vectorOfFn_apply]

end EdgeChain

set_option genInjectivity false in
/-- The cellular vertex-cycle condition for the connected ramified polygon. -/
structure Cycle {genus : Nat} (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) : Type where
  /-- The sum of the two lifted coefficients is constant around the original base polygon. -/ total_eq : forall index :
    Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus),
    chain.sheetZero index + chain.sheetOne index =
      chain.sheetZero 0 + chain.sheetOne 0

constructive_injectivity Cycle

/-- Edge chain of one explicitly attached face. -/
@[expose] def faceChain {genus : Nat} (face : Attachment.Face) :
  Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index =>
    if oddFaceSheet face index = sheetZero then 1 else 0
  sheetOne := Data.Vector.Basic.vectorOfFn fun index =>
    if oddFaceSheet face index = Attachment.sheetOne then 1 else 0

/-- Exactly one lift of each base edge occurs in the retained face attachment. -/
theorem faceChain_total (face : Attachment.Face) {genus : Nat}
    (index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain face).sheetZero index +
      (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain face).sheetOne index = 1 := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  rcases sheet_eq_zero_or_one (oddFaceSheet face index) with equal | equal
  · rw [equal, if_pos rfl]
    have different : sheetZero ≠ sheetOne := by
      intro impossible
      have values := congrArg Fin.val impossible
      change (0 : Nat) = 1 at values
      omega0
    rw [if_neg different]
    omega0
  · rw [equal, if_pos rfl]
    have different : Attachment.sheetOne ≠ sheetZero := by
      intro impossible
      have values := congrArg Fin.val impossible
      change (1 : Nat) = 0 at values
      omega0
    rw [if_neg different]
    omega0

/-- The explicit attached face chain satisfies the constant-total vertex-cycle condition. -/
@[expose] def faceCycle {genus : Nat} (face : Attachment.Face) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.Cycle (Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      (genus := genus) face) where
  total_eq := by
    intro index
    rw [Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_total,
      Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_total]

/-- The upper hemisphere face with zero sheet lift. -/
@[expose] def upperZeroFace : Face := ⟨.upper, sheetZero⟩
/-- The upper hemisphere face with one sheet lift. -/
@[expose] def upperOneFace : Face := ⟨.upper, sheetOne⟩
/-- The lower hemisphere face with zero sheet lift. -/
@[expose] def lowerZeroFace : Face := ⟨.lower, sheetZero⟩
/-- The lower hemisphere face with one sheet lift. -/
@[expose] def lowerOneFace : Face := ⟨.lower, sheetOne⟩

/-- The two explicit sheet labels are distinct. -/
theorem sheetZero_ne_sheetOne : sheetZero ≠ sheetOne := by
  intro equal
  have valueEqual := congrArg Fin.val equal
  change (0 : Nat) = 1 at valueEqual
  omega0

/-- The one-sheet label differs from the zero-sheet label. -/
theorem sheetOne_ne_sheetZero : Attachment.sheetOne ≠ sheetZero := by
  intro equal
  exact Curves.Hyperelliptic.Topology.OddCellularHomology.sheetZero_ne_sheetOne equal.symm

/-- The span of three independent attached faces. The fourth face is their negative sum after orienting the two
hemispheres oppositely. -/
@[expose] def boundaryCombination (genus : Nat) (evenWeight oddWeight totalWeight : Int) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index =>
    if index.val % 2 = 0 then evenWeight else oddWeight
  sheetOne := Data.Vector.Basic.vectorOfFn fun index =>
    if index.val % 2 = 0 then oddWeight + totalWeight
    else evenWeight + totalWeight

/-- The upper zero-sheet attaching word is the displayed combination of the three independent boundary generators. -/
theorem faceChain_upperZero (genus : Nat) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
      Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.upperZeroFace =
      Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus 1 1 (-1) := by
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext <;> intro index
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.upperZeroFace oddFaceSheet
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
    · rw [if_neg even]
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.upperZeroFace oddFaceSheet
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply,
      if_neg Curves.Hyperelliptic.Topology.OddCellularHomology.sheetZero_ne_sheetOne]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
      decide
    · rw [if_neg even]
      decide

/-- The upper one-sheet attaching word is the total boundary generator. -/
theorem faceChain_upperOne (genus : Nat) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
      Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.upperOneFace =
      Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus 0 0 1 := by
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext <;> intro index
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.upperOneFace oddFaceSheet
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply,
      if_neg Curves.Hyperelliptic.Topology.OddCellularHomology.sheetOne_ne_sheetZero]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
    · rw [if_neg even]
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.upperOneFace oddFaceSheet
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply, if_pos rfl]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
      ring1
    · rw [if_neg even]
      ring1

/-- The lower zero face follows the canonical alternating lower sheet. -/
private theorem lowerZeroFace_sheet {genus : Nat}
    (index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    oddFaceSheet Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace index = Cells.oddLowerSheet index := by
  rfl

/-- The lower one face follows the toggled canonical alternating lower sheet. -/
private theorem lowerOneFace_sheet {genus : Nat}
    (index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    oddFaceSheet Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace index = Attachment.toggleSheet
      (Cells.oddLowerSheet index) := by
  rfl

/-- The alternating lower zero-sheet word is the even-parity generator. -/
theorem faceChain_lowerZero (genus : Nat) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
      Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace =
      Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus 1 0 0 := by
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext <;> intro index
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace_sheet, Cells.oddLowerSheet, if_pos even,
        if_pos rfl]
      rw [if_pos even]
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace_sheet, Cells.oddLowerSheet, if_neg even,
        if_neg Curves.Hyperelliptic.Topology.OddCellularHomology.sheetOne_ne_sheetZero]
      rw [if_neg even]
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace_sheet, Cells.oddLowerSheet, if_pos even,
        if_neg Curves.Hyperelliptic.Topology.OddCellularHomology.sheetZero_ne_sheetOne]
      rw [if_pos even]
      ring1
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace_sheet, Cells.oddLowerSheet, if_neg even,
        if_pos rfl]
      rw [if_neg even]
      ring1

/-- The alternating lower one-sheet word is the odd-parity generator. -/
theorem faceChain_lowerOne (genus : Nat) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
      Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace =
      Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus 0 1 0 := by
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext <;> intro index
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace_sheet, Cells.oddLowerSheet, if_pos even,
        Attachment.toggleSheet_zero, if_neg Curves.Hyperelliptic.Topology.OddCellularHomology.sheetOne_ne_sheetZero]
      rw [if_pos even]
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace_sheet, Cells.oddLowerSheet, if_neg even,
        Attachment.toggleSheet_one, if_pos rfl]
      rw [if_neg even]
  · unfold Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace_sheet, Cells.oddLowerSheet, if_pos even,
        Attachment.toggleSheet_zero, if_pos rfl]
      rw [if_pos even]
      ring1
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace_sheet, Cells.oddLowerSheet, if_neg even,
        Attachment.toggleSheet_one, if_neg Curves.Hyperelliptic.Topology.OddCellularHomology.sheetZero_ne_sheetOne]
      rw [if_neg even]
      ring1

/-- With the two hemispheres oppositely oriented, the complete boundary of the four actual attached faces cancels edge
by edge. This is the signed cellular surface identity behind the finite Stokes pairing. -/
theorem upperFaceChains_eq_lowerFaceChains (genus : Nat) :
    (Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
      Curves.Hyperelliptic.Topology.OddCellularHomology.upperZeroFace).add
        (Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
          Curves.Hyperelliptic.Topology.OddCellularHomology.upperOneFace) =
      (Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
        Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace).add
        (Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
          Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace) := by
  rw [Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_upperZero,
    Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_upperOne,
    Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_lowerZero,
      Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_lowerOne]
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext <;> intro index
  · simp only [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetZero]
    unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    simp only [Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · simp only [if_pos even, -eq_self, -iff_self]
      rfl
    · simp only [if_neg even, -eq_self, -iff_self]
      rfl
  · simp only [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetOne]
    unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    simp only [Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · simp only [if_pos even, -eq_self, -iff_self]
      rfl
    · simp only [if_neg even, -eq_self, -iff_self]
      rfl

/-- Every displayed boundary combination is literally an integral linear combination of three of the four attached face
words. -/
theorem boundaryCombination_eq_faceCombination (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight totalWeight
      =
      ((Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
        Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace).scale evenWeight).add
        (((Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
          Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace).scale oddWeight).add
          ((Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
            Curves.Hyperelliptic.Topology.OddCellularHomology.upperOneFace).scale totalWeight)) := by
  rw [Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_lowerZero,
    Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_lowerOne,
    Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain_upperOne]
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext <;> intro index
  · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetZero,
      Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.scale_sheetZero,
      Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetZero,
        Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.scale_sheetZero,
      Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.scale_sheetZero]
    unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    repeat' rw [Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · repeat' rw [if_pos even]
      ring1
    · repeat' rw [if_neg even]
      ring1
  · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetOne,
      Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.scale_sheetOne,
      Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetOne,
        Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.scale_sheetOne,
      Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.scale_sheetOne]
    unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
    repeat' rw [Data.Vector.Basic.vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · repeat' rw [if_pos even]
      ring1
    · repeat' rw [if_neg even]
      ring1
/-- The zero-sheet coefficient at the first parity reference is the even boundary weight. -/
@[simp] theorem boundaryCombination_sheetZero_zero (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight
      totalWeight).sheetZero 0 =
      evenWeight := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The zero-sheet coefficient at the second parity reference is the odd boundary weight. -/
@[simp] theorem boundaryCombination_sheetZero_one (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight
      totalWeight).sheetZero 1 =
      oddWeight := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The retained edge chain is an explicit integral combination of the three independent face-boundary coordinates. -/
@[expose] def IsBoundary {genus : Nat} (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) :
  Prop :=
  exists evenWeight oddWeight totalWeight : Int,
    chain = Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight totalWeight

/-- Boundary membership stated directly as the span of concrete attached face words. -/
@[expose] def IsFaceBoundary {genus : Nat} (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) :
  Prop :=
  exists evenWeight oddWeight totalWeight : Int,
    chain =
      ((Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
        Curves.Hyperelliptic.Topology.OddCellularHomology.lowerZeroFace).scale evenWeight).add
        (((Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
          Curves.Hyperelliptic.Topology.OddCellularHomology.lowerOneFace).scale oddWeight).add
          ((Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus)
            Curves.Hyperelliptic.Topology.OddCellularHomology.upperOneFace).scale totalWeight))

/-- Coordinate boundary membership is equivalent to membership in the explicit span of the retained attached face words.
-/
theorem isBoundary_iff_isFaceBoundary {genus : Nat}
    (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.IsBoundary chain <->
      Curves.Hyperelliptic.Topology.OddCellularHomology.IsFaceBoundary chain := by
  constructor
  · rintro ⟨evenWeight, oddWeight, totalWeight, equal⟩
    exact ⟨evenWeight, oddWeight, totalWeight,
      equal.trans (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_eq_faceCombination genus _ _
        _)⟩
  · rintro ⟨evenWeight, oddWeight, totalWeight, equal⟩
    exact ⟨evenWeight, oddWeight, totalWeight,
      equal.trans (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_eq_faceCombination genus _ _
        _).symm⟩

/-- Every edge of a boundary combination has the same total coefficient, the sum of its three weights. -/
@[simp] theorem boundaryCombination_total (genus : Nat)
    (evenWeight oddWeight totalWeight : Int)
    (index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight
      totalWeight).sheetZero index +
        (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight
          totalWeight).sheetOne index =
      evenWeight + oddWeight + totalWeight := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  by_cases even : index.val % 2 = 0
  · rw [if_pos even, if_pos even]
    ring1
  · rw [if_neg even, if_neg even]
    ring1

/-- Every explicit boundary combination satisfies the vertex-cycle condition. -/
@[expose] def boundaryCombination_cycle (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.Cycle
      (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight totalWeight)
      where
  total_eq := by
    intro index
    rw [Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_total,
      Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_total]

/-- The first two edge positions are parity references; the remaining `2g` positions are the free homology coordinates.
-/
@[expose] def coordinates {genus : Nat} (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus) :
  Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus :=
  Data.Vector.Basic.vectorOfFn fun index =>
    chain.sheetZero index.succ.succ -
      if index.val % 2 = 0 then chain.sheetZero 0 else chain.sheetZero 1

/-- Canonical total-zero cycle with zero reference coefficients.

The first two edge positions are zero on the first sheet, followed in order
by the supplied tail coordinates. The second sheet retains their negatives. -/
@[expose] def representative {genus : Nat} (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector
  genus) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus :=
  let zeroCoefficients : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeVector genus :=
    Data.Vector.Basic.vectorOfFn fun position =>
      Data.Fin.cases 0
        (fun afterZero => Data.Fin.cases 0 (fun index => coordinate index) afterZero)
        position
  { sheetZero := zeroCoefficients
    sheetOne := Data.Vector.Basic.vectorOfFn fun position => -zeroCoefficients position }

/-- The canonical representative has zero coefficient at its first parity reference. -/
@[simp] theorem representative_sheetZero_zero {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate).sheetZero 0 = 0 := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.representative
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The canonical representative has zero coefficient at its second parity reference. -/
@[simp] theorem representative_sheetZero_one {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate).sheetZero 1 = 0 := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.representative
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The canonical representative retains each free tail coordinate literally. -/
@[simp] theorem representative_sheetZero_tail {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) (index : Fin
      (Curves.Hyperelliptic.Topology.OddCellularHomology.TailRank genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate).sheetZero index.succ.succ =
      coordinate index := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.representative
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The canonical representative has opposite coefficients on its two sheet lifts. -/
@[simp] theorem representative_sheetOne {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) (index : Fin
      (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate).sheetOne index =
      -(Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate).sheetZero index := by
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.representative
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Opposite sheet coefficients make the canonical representative a cellular cycle. -/
@[expose] def representative_cycle {genus : Nat} (coordinate :
  Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.Cycle
      (Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate) where
  total_eq := by
    intro index
    rw [Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetOne,
      Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetOne]
    ring1

/-- Reading the homology coordinates of the canonical representative returns the original tail vector. -/
theorem coordinates_representative {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates
      (Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate) = coordinate := by
  apply Data.Vector.Basic.vector_ext
  intro index
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates
  rw [Data.Vector.Basic.vectorOfFn_apply,
    Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_tail]
  by_cases even : index.val % 2 = 0
  · rw [if_pos even, Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_zero]
    ring1
  · rw [if_neg even, Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_one]
    ring1

/-- Every explicit face-boundary combination has zero free homology coordinates. -/
theorem coordinates_boundaryCombination (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates
      (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight
      totalWeight) =
      Data.Vector.Basic.vectorOfFn fun _ : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.TailRank genus) => 0
        := by
  apply Data.Vector.Basic.vector_ext
  intro index
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rw [Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_sheetZero_zero,
    Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_sheetZero_one]
  unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  have parity : (index.val + 2) % 2 = index.val % 2 := by omega0
  change (if (index.val + 2) % 2 = 0 then evenWeight else oddWeight) -
      (if index.val % 2 = 0 then evenWeight else oddWeight) = 0
  rw [parity]
  ring1

/-- Every cellular cycle is its canonical free representative plus an explicit combination of the three independent face
boundaries. -/
theorem cycle_decomposition {genus : Nat} (chain : Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain genus)
    (cycle : Curves.Hyperelliptic.Topology.OddCellularHomology.Cycle chain) :
    let coordinate := Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates chain
    let evenWeight := chain.sheetZero 0
    let oddWeight := chain.sheetZero 1
    let totalWeight := chain.sheetZero 0 + chain.sheetOne 0 -
      evenWeight - oddWeight
    chain = (Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate).add
      (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus evenWeight oddWeight totalWeight) :=
        by
  dsimp only
  apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext
  · intro position
    refine Data.Fin.cases_induction ?_ (fun afterZero =>
      Data.Fin.cases_induction ?_ (fun index => ?_) afterZero) position
    · rewrite [show (⟨0, Nat.zero_lt_succ (2 * genus + 1)⟩ : Fin (2 * genus + 2)) = 0 from rfl]
      rw [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetZero,
        Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_zero,
        Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_sheetZero_zero]
      ring1
    · rw [show (⟨0, Nat.zero_lt_succ (2 * genus)⟩ : Fin (2 * genus + 1)).succ = (1 : Fin (2 * genus + 2)) from rfl,
        Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetZero,
        Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_one,
        Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_sheetZero_one]
      ring1
    · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetZero,
        Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_tail]
      unfold Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates
        Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
      rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
      have parity : (index.val + 2) % 2 = index.val % 2 := by omega0
      change chain.sheetZero index.succ.succ =
        (chain.sheetZero index.succ.succ -
          if index.val % 2 = 0 then chain.sheetZero 0 else chain.sheetZero 1) +
        (if (index.val + 2) % 2 = 0 then chain.sheetZero 0
          else chain.sheetZero 1)
      rw [parity]
      by_cases even : index.val % 2 = 0
      · rw [if_pos even]
        ring1
      · rw [if_neg even]
        ring1
  · intro position
    rw [Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.add_sheetOne,
      Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetOne]
    have totalAt := cycle.total_eq position
    have boundaryTotal := Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_total genus
      (chain.sheetZero 0) (chain.sheetZero 1)
      (chain.sheetZero 0 + chain.sheetOne 0 -
        chain.sheetZero 0 - chain.sheetZero 1) position
    have zeroCoordinateEqual :
        chain.sheetZero position =
          (Curves.Hyperelliptic.Topology.OddCellularHomology.representative
            (Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates chain)).sheetZero position +
            (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
              (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position := by
      refine Data.Fin.cases_induction ?_ (fun afterZero =>
        Data.Fin.cases_induction ?_ (fun index => ?_) afterZero) position
      · rewrite [show (⟨0, Nat.zero_lt_succ (2 * genus + 1)⟩ : Fin (2 * genus + 2)) = 0 from rfl]
        rw [Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_zero,
          Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_sheetZero_zero]
        ring1
      · rw [show (⟨0, Nat.zero_lt_succ (2 * genus)⟩ : Fin (2 * genus + 1)).succ = (1 : Fin (2 * genus + 2)) from rfl,
          Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_one,
          Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination_sheetZero_one]
        ring1
      · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_tail]
        unfold Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates
          Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
        rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
        have parity : (index.val + 2) % 2 = index.val % 2 := by omega0
        change chain.sheetZero index.succ.succ =
          (chain.sheetZero index.succ.succ -
            if index.val % 2 = 0 then chain.sheetZero 0 else chain.sheetZero 1) +
          (if (index.val + 2) % 2 = 0 then chain.sheetZero 0
            else chain.sheetZero 1)
        rw [parity]
        by_cases even : index.val % 2 = 0
        · rw [if_pos even]
          ring1
        · rw [if_neg even]
          ring1
    have boundaryTotalSimplified :
        (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
          (chain.sheetZero 1)
            (chain.sheetZero 0 + chain.sheetOne 0 -
              chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position +
          (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
            (chain.sheetZero 1)
            (chain.sheetZero 0 + chain.sheetOne 0 -
              chain.sheetZero 0 - chain.sheetZero 1)).sheetOne position =
        chain.sheetZero 0 + chain.sheetOne 0 := by
      rw [boundaryTotal]
      ring1
    calc
      chain.sheetOne position =
          (chain.sheetZero 0 + chain.sheetOne 0) -
            chain.sheetZero position := by
              rw [← totalAt]
              ring1
      _ = ((Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
        (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position +
            (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
              (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetOne position) -
          ((Curves.Hyperelliptic.Topology.OddCellularHomology.representative
            (Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates chain)).sheetZero position +
            (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
              (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position) := by
              rw [boundaryTotalSimplified, zeroCoordinateEqual]
      _ = -(Curves.Hyperelliptic.Topology.OddCellularHomology.representative
        (Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates chain)).sheetZero position +
          (Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination genus (chain.sheetZero 0)
            (chain.sheetZero 1)
            (chain.sheetZero 0 + chain.sheetOne 0 -
              chain.sheetZero 0 - chain.sheetZero 1)).sheetOne position := by
              ring1

/-- A canonical representative is a face boundary only when every free coordinate vanishes. -/
theorem representative_boundary_iff_coordinates_zero {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.OddCellularHomology.TailVector genus) :
    Curves.Hyperelliptic.Topology.OddCellularHomology.IsBoundary
      (Curves.Hyperelliptic.Topology.OddCellularHomology.representative coordinate) <->
      coordinate = Data.Vector.Basic.vectorOfFn (fun _ : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.TailRank
        genus) => 0) := by
  constructor
  · intro boundary
    rcases boundary with ⟨evenWeight, oddWeight, totalWeight, equal⟩
    have coordinateEqual := congrArg Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates equal
    rw [Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates_representative,
      Curves.Hyperelliptic.Topology.OddCellularHomology.coordinates_boundaryCombination] at coordinateEqual
    exact coordinateEqual
  · intro coordinateZero
    subst coordinate
    have zeroSheet : forall index : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus),
        (Curves.Hyperelliptic.Topology.OddCellularHomology.representative (Data.Vector.Basic.vectorOfFn
          (fun _ : Fin (Curves.Hyperelliptic.Topology.OddCellularHomology.TailRank genus) => 0))).sheetZero index = 0 :=
            by
      intro index
      refine Data.Fin.cases_induction ?_ (fun afterZero =>
        Data.Fin.cases_induction ?_ (fun tail => ?_) afterZero) index
      · rewrite [show (⟨0, Nat.zero_lt_succ (2 * genus + 1)⟩ : Fin (2 * genus + 2)) = 0 from rfl]
        rw [Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_zero]
      · rw [show (⟨0, Nat.zero_lt_succ (2 * genus)⟩ : Fin (2 * genus + 1)).succ = (1 : Fin (2 * genus + 2)) from rfl,
          Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_one]
      · rw [Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetZero_tail,
          Data.Vector.Basic.vectorOfFn_apply]
    exact ⟨0, 0, 0, by
      apply Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeChain.ext
      · intro index
        rw [zeroSheet]
        unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
        rw [Data.Vector.Basic.vectorOfFn_apply]
        split <;> rfl
      · intro index
        rw [Curves.Hyperelliptic.Topology.OddCellularHomology.representative_sheetOne, zeroSheet]
        unfold Curves.Hyperelliptic.Topology.OddCellularHomology.boundaryCombination
        rw [Data.Vector.Basic.vectorOfFn_apply]
        split <;> rfl⟩

end Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology

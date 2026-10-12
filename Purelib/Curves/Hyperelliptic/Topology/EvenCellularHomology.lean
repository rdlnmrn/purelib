module

import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Topology.Cells
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology
import Purelib.Topology.Surface.CellularHomology
public import Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology
import Purelib.Data.Fin
import Init.Data.Fin.Basic
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Topology.BranchedCover.Double

open Purelib.Topology.Surface

public section

/-!
# Cellular homology of the even-degree hyperelliptic model

The even-degree polygon has one additional terminal base edge at the two
unramified points over infinity.  A cellular cycle has the same coefficient
on that terminal edge as on edge zero, separately on each sheet.  Deleting
the terminal edge therefore identifies its cycle group constructively with
the odd-model cycle group.  The inverse explicitly restores the two terminal
coefficients, and the actual even face words are carried to the odd face
words under this identification.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology

/-- The even-model base edge count, including the terminal edge at unramified infinity. -/
abbrev EdgeCount (genus : Nat) := 2 * genus + 3
/-- The finite vector of integral coefficients on the original even-model base edges. -/
abbrev EdgeVector (genus : Nat) :=
  Data.Vector Int (Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeCount genus)

set_option genInjectivity false in
/-- Integral coefficients on all lifted even-model edges. -/
structure EdgeChain (genus : Nat) where
  /-- The original integral edge coefficients on sheet zero. -/ sheetZero :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeVector genus
  /-- The original integral edge coefficients on sheet one. -/ sheetOne :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeVector genus

constructive_injectivity EdgeChain

namespace EdgeChain

/-- Pointwise equality of both sheet coefficient vectors determines the same edge chain. -/
theorem ext {genus : Nat} {left right : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus}
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

/-- Add the original integral edge coefficients separately on each labelled sheet. -/
@[expose] def add {genus : Nat} (left right : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus) :
  Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index =>
    left.sheetZero index + right.sheetZero index
  sheetOne := Data.Vector.Basic.vectorOfFn fun index =>
    left.sheetOne index + right.sheetOne index

/-- Multiply every retained sheet-edge coefficient by the same integer. -/
@[expose] def scale {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus) (scalar :
  Int) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index => scalar * chain.sheetZero index
  sheetOne := Data.Vector.Basic.vectorOfFn fun index => scalar * chain.sheetOne index

/-- Sheet-zero coefficients of chain addition are the original pointwise sums. -/
@[simp] theorem add_sheetZero {genus : Nat} (left right : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus)
    (index : Fin (Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeCount genus)) :
    (left.add right).sheetZero index =
      left.sheetZero index + right.sheetZero index := by
  unfold EvenCellularHomology.EdgeChain.add
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Sheet-one coefficients of chain addition are the original pointwise sums. -/
@[simp] theorem add_sheetOne {genus : Nat} (left right : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus)
    (index : Fin (Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeCount genus)) :
    (left.add right).sheetOne index =
      left.sheetOne index + right.sheetOne index := by
  unfold EvenCellularHomology.EdgeChain.add
  rw [Data.Vector.Basic.vectorOfFn_apply]

end EdgeChain

set_option genInjectivity false in
/-- Exact vertex-boundary equations: totals agree at every ramified vertex, and the two sheet coefficients close
separately at unramified infinity. -/
structure Cycle {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus) : Type where
  /-- The sum of the two sheet coefficients is constant across all original base edges. -/ total_eq : forall index : Fin
    (Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeCount genus),
    chain.sheetZero index + chain.sheetOne index =
      chain.sheetZero 0 + chain.sheetOne 0
  /-- The terminal sheet-zero coefficient equals its edge-zero coefficient. -/ closesZero : chain.sheetZero (Fin.last (2
    * genus + 2)) =
    chain.sheetZero 0
  /-- The terminal sheet-one coefficient equals its edge-zero coefficient. -/ closesOne : chain.sheetOne (Fin.last (2 *
    genus + 2)) =
    chain.sheetOne 0

constructive_injectivity Cycle

/-- Delete the terminal edge at infinity. -/
@[expose] def restrict {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus) :
    OddCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index => chain.sheetZero index.castSucc
  sheetOne := Data.Vector.Basic.vectorOfFn fun index => chain.sheetOne index.castSucc

/-- Restore the terminal edge by copying the edge-zero coefficient on each sheet. -/
@[expose] def extend {genus : Nat} (chain : OddCellularHomology.EdgeChain genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun position =>
    Data.Fin.lastCases (chain.sheetZero 0)
      (fun index => chain.sheetZero index)
      position
  sheetOne := Data.Vector.Basic.vectorOfFn fun position =>
    Data.Fin.lastCases (chain.sheetOne 0)
      (fun index => chain.sheetOne index)
      position

/-- Deleting the terminal edge preserves each original sheet-zero nonterminal coefficient. -/
@[simp] theorem restrict_sheetZero {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero index = chain.sheetZero
      index.castSucc := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Deleting the terminal edge preserves each original sheet-one nonterminal coefficient. -/
@[simp] theorem restrict_sheetOne {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetOne index = chain.sheetOne
      index.castSucc := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Extension preserves the original nonterminal sheet-zero coefficient. -/
@[simp] theorem extend_sheetZero_castSucc {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain).sheetZero index.castSucc = chain.sheetZero
      index := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.lastCases_castSucc]

/-- Extension preserves the original nonterminal sheet-one coefficient. -/
@[simp] theorem extend_sheetOne_castSucc {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain).sheetOne index.castSucc = chain.sheetOne
      index := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.lastCases_castSucc]

/-- The extended terminal sheet-zero coefficient copies the original edge-zero coefficient. -/
@[simp] theorem extend_sheetZero_last {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain).sheetZero (Fin.last (2 * genus + 2)) =
      chain.sheetZero 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.lastCases_last]

/-- The extended terminal sheet-one coefficient copies the original edge-zero coefficient. -/
@[simp] theorem extend_sheetOne_last {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain).sheetOne (Fin.last (2 * genus + 2)) =
      chain.sheetOne 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Fin.lastCases_last]

/-- Extension preserves the original sheet-zero coefficient at edge zero. -/
@[simp] theorem extend_sheetZero_zero {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain).sheetZero 0 = chain.sheetZero 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
  rw [Data.Vector.Basic.vectorOfFn_apply]
  change Data.Fin.lastCases (chain.sheetZero 0)
    (fun index => chain.sheetZero index)
    (Fin.castSucc (0 : Fin (2 * genus + 2))) = chain.sheetZero 0
  rw [Data.Fin.lastCases_castSucc]

/-- Extension preserves the original sheet-one coefficient at edge zero. -/
@[simp] theorem extend_sheetOne_zero {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain).sheetOne 0 = chain.sheetOne 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
  rw [Data.Vector.Basic.vectorOfFn_apply]
  change Data.Fin.lastCases (chain.sheetOne 0)
    (fun index => chain.sheetOne index)
    (Fin.castSucc (0 : Fin (2 * genus + 2))) = chain.sheetOne 0
  rw [Data.Fin.lastCases_castSucc]

/-- Deleting the restored terminal edge recovers the original odd-model chain. -/
@[simp] theorem restrict_extend {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain) = chain := by
  apply OddCellularHomology.EdgeChain.ext <;> intro index
  · rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetZero,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_castSucc]
  · rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetOne,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_castSucc]

/-- The separate sheet-closing equations recover an even-model cycle after restriction and extension. -/
theorem extend_restrict_of_cycle {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus)
    (cycle : Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle chain) :
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain) = chain := by
  apply Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.ext <;> intro position
  · rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_last,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetZero]
      change chain.sheetZero 0 =
        chain.sheetZero (Fin.last (2 * genus + 2))
      exact cycle.closesZero.symm
    · subst position
      rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_castSucc,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetZero]
  · rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_last,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetOne]
      change chain.sheetOne 0 =
        chain.sheetOne (Fin.last (2 * genus + 2))
      exact cycle.closesOne.symm
    · subst position
      rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_castSucc,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetOne]

/-- Delete the terminal edge while retaining the cycle equations on the original odd-model edges. -/
@[expose] def restrict_cycle {genus : Nat} {chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus}
    (cycle : Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle chain) :
    OddCellularHomology.Cycle (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain) where
  total_eq := by
    intro index
    rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetZero,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetOne,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetZero,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_sheetOne]
    exact cycle.total_eq index.castSucc

/-- Restore the terminal coefficients and prove the resulting even-model chain is a cycle. -/
@[expose] def extend_cycle {genus : Nat}
    {chain : OddCellularHomology.EdgeChain genus}
    (cycle : OddCellularHomology.Cycle chain) : Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend chain) where
  total_eq := by
    intro position
    rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_last,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_last,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_zero,
          Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_zero]
    · subst position
      rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_castSucc,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_castSucc,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_zero,
          Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_zero]
      exact cycle.total_eq index
  closesZero := by
    rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_last,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_zero]
  closesOne := by
    rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_last,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_zero]

/-- Restoring the terminal coefficients commutes with addition of original odd-model chains. -/
theorem extend_add {genus : Nat}
    (left right : OddCellularHomology.EdgeChain genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.extend (left.add right) =
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend left).add
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend right) := by
  apply Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.ext <;> intro position
  · rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      simp only [-eq_self, -iff_self, Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_last,
        OddCellularHomology.EdgeChain.add_sheetZero,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.add_sheetZero]
      rfl
    · subst position
      simp only [-eq_self, -iff_self, Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_castSucc,
        OddCellularHomology.EdgeChain.add_sheetZero,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.add_sheetZero]
      rfl
  · rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      simp only [-eq_self, -iff_self, Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_last,
        OddCellularHomology.EdgeChain.add_sheetOne,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.add_sheetOne]
      rfl
    · subst position
      simp only [-eq_self, -iff_self, Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_castSucc,
        OddCellularHomology.EdgeChain.add_sheetOne,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.add_sheetOne]
      rfl

/-! ## Agreement with the actual even attaching words -/

/-- The integral even-model boundary word of the displayed original lifted face. -/
@[expose] def faceChain {genus : Nat} (face : Attachment.Face) :
  Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus where
  sheetZero := Data.Vector.Basic.vectorOfFn fun index =>
    if Cells.evenFaceSheet face index = Attachment.sheetZero then 1 else 0
  sheetOne := Data.Vector.Basic.vectorOfFn fun index =>
    if Cells.evenFaceSheet face index = Attachment.sheetOne then 1 else 0

/-- Every nonterminal even-face edge carries the same sheet label as its odd-model counterpart. -/
theorem evenFaceSheet_castSucc {genus : Nat} (face : Attachment.Face)
    (index : Fin (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.EdgeCount genus)) :
    Purelib.Curves.Hyperelliptic.Topology.Cells.evenFaceSheet face index.castSucc =
      Purelib.Curves.Hyperelliptic.Topology.Cells.oddFaceSheet face index := by
  cases face with
  | mk hemisphere lift =>
      cases hemisphere with
      | upper => rfl
      | lower =>
          unfold Cells.evenFaceSheet Cells.oddFaceSheet Cells.evenLowerSheet Cells.oddLowerSheet
          have below : index.castSucc.val + 1 < Cells.evenBaseCount genus := by
            change index.val + 1 < Cells.evenBaseCount genus
            have bound := index.isLt
            unfold OddCellularHomology.EdgeCount at bound
            unfold Cells.evenBaseCount Cells.branchCount
            omega0
          rw [dif_pos below]
          rfl

/-- The terminal even-face sheet label equals the original odd-face label at edge zero. -/
theorem evenFaceSheet_last {genus : Nat} (face : Attachment.Face) :
    Purelib.Curves.Hyperelliptic.Topology.Cells.evenFaceSheet face (Fin.last (2 * genus + 2)) =
      Purelib.Curves.Hyperelliptic.Topology.Cells.oddFaceSheet face
        (0 : Fin (OddCellularHomology.EdgeCount genus)) := by
  cases face with
  | mk hemisphere lift =>
      cases hemisphere with
      | upper => rfl
      | lower =>
          unfold Cells.evenFaceSheet Cells.oddFaceSheet Cells.evenLowerSheet Cells.oddLowerSheet
          have terminal : ¬((Fin.last (2 * genus + 2)).val + 1 <
              Cells.evenBaseCount genus) := by
            rw [Fin.val_last]
            unfold Cells.evenBaseCount Cells.branchCount
            omega0
          rw [dif_neg terminal]
          rfl

/-- The actual even face word is obtained by extending the corresponding odd word across the unramified infinity edge.
-/
theorem faceChain_eq_extend_oddFaceChain (genus : Nat) (face : Attachment.Face) :
    Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain (genus := genus) face =
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
        (Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology.faceChain (genus := genus) face) := by
  apply Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain.ext <;> intro position
  · rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain OddCellularHomology.faceChain
      rw [Data.Vector.Basic.vectorOfFn_apply, Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_last,
        Data.Vector.Basic.vectorOfFn_apply,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.evenFaceSheet_last]
    · subst position
      unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain OddCellularHomology.faceChain
      rw [Data.Vector.Basic.vectorOfFn_apply,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetZero_castSucc,
        Data.Vector.Basic.vectorOfFn_apply,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.evenFaceSheet_castSucc]
  · rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain OddCellularHomology.faceChain
      rw [Data.Vector.Basic.vectorOfFn_apply, Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_last,
        Data.Vector.Basic.vectorOfFn_apply,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.evenFaceSheet_last]
    · subst position
      unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain OddCellularHomology.faceChain
      rw [Data.Vector.Basic.vectorOfFn_apply,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_sheetOne_castSucc, Data.Vector.Basic.vectorOfFn_apply,
        Curves.Hyperelliptic.Topology.EvenCellularHomology.evenFaceSheet_castSucc]

/-- The oriented boundary of all four even-model faces also cancels exactly. The terminal edge at the two points over
infinity is included by the explicit `extend` construction. -/
theorem upperFaceChains_eq_lowerFaceChains (genus : Nat) :
    (Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain (genus := genus)
      OddCellularHomology.upperZeroFace).add
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain (genus := genus) OddCellularHomology.upperOneFace)
          =
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain (genus := genus)
        OddCellularHomology.lowerZeroFace).add
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain (genus := genus) OddCellularHomology.lowerOneFace)
          := by
  rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain_eq_extend_oddFaceChain,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain_eq_extend_oddFaceChain,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain_eq_extend_oddFaceChain,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.faceChain_eq_extend_oddFaceChain,
    ← Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_add, ←
      Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_add,
    OddCellularHomology.upperFaceChains_eq_lowerFaceChains]

/-- Even boundaries are exactly extensions of the already reduced span of the corresponding concrete face words. -/
@[expose] def IsBoundary {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus) :
  Prop :=
  exists oddBoundary : OddCellularHomology.EdgeChain genus,
    OddCellularHomology.IsFaceBoundary oddBoundary /\
      chain = Curves.Hyperelliptic.Topology.EvenCellularHomology.extend oddBoundary

/-! ## Transported symplectic basis -/

/-- The two standard genus-sized integral coordinate blocks of the even-model homology. -/
abbrev StandardHomology (genus : Nat) :=
  OddSymplecticHomology.StandardHomology genus

/-- Delete the terminal edge and read the corresponding odd-model symplectic coordinates. -/
@[expose] def homologyCoordinates {genus : Nat} (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.StandardHomology genus :=
  OddSymplecticHomology.homologyCoordinates (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain)

/-- Realize the standard homology coordinates as an odd-model chain and restore its terminal sheet coefficients. -/
@[expose] def realize {genus : Nat} (coordinate : Curves.Hyperelliptic.Topology.EvenCellularHomology.StandardHomology
  genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus :=
  Curves.Hyperelliptic.Topology.EvenCellularHomology.extend (OddSymplecticHomology.realize coordinate)

/-- The restored edge representative of standard homology coordinates is an even-model cycle. -/
@[expose] def realize_cycle {genus : Nat} (coordinate :
  Curves.Hyperelliptic.Topology.EvenCellularHomology.StandardHomology genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle (Curves.Hyperelliptic.Topology.EvenCellularHomology.realize
      coordinate) :=
  Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_cycle (OddSymplecticHomology.realize_cycle coordinate)

/-- Reading the coordinates of the restored representative returns the original standard vector. -/
@[simp] theorem homologyCoordinates_realize {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.EvenCellularHomology.StandardHomology genus) :
    Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.realize coordinate) = coordinate := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates
    Curves.Hyperelliptic.Topology.EvenCellularHomology.realize
  rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_extend,
    OddSymplecticHomology.homologyCoordinates_realize]

/-- The actual even-model edge representative of the indexed standard a-class. -/
@[expose] def aCycle {genus : Nat} (index : Fin genus) : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus :=
  Curves.Hyperelliptic.Topology.EvenCellularHomology.realize (CellularHomology.aCycle index)

/-- The actual even-model edge representative of the indexed standard b-class. -/
@[expose] def bCycle {genus : Nat} (index : Fin genus) : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus :=
  Curves.Hyperelliptic.Topology.EvenCellularHomology.realize (CellularHomology.bCycle index)

/-- The actual even-model a-representative is a cellular cycle. -/
@[expose] def aCycle_isCycle {genus : Nat} (index : Fin genus) :
  Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle (Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle
  index) :=
  Curves.Hyperelliptic.Topology.EvenCellularHomology.realize_cycle _

/-- The actual even-model b-representative is a cellular cycle. -/
@[expose] def bCycle_isCycle {genus : Nat} (index : Fin genus) :
  Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle (Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle
  index) :=
  Curves.Hyperelliptic.Topology.EvenCellularHomology.realize_cycle _

/-- The integral intersection pairing on the original even-model chains read through their standard coordinates. -/
@[expose] def intersection {genus : Nat} (left right : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain
  genus) : Int :=
  CellularHomology.intersection
    (Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates left)
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates right)

/-- Any two even-model a-cycles have zero intersection. -/
theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle left)
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle right) = 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
    Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle
  rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates_realize,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates_realize]
  exact CellularHomology.intersection_a_a left right

/-- Any two even-model b-cycles have zero intersection. -/
theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle left)
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle right) = 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
    Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle
  rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates_realize,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates_realize]
  exact CellularHomology.intersection_b_b left right

/-- The even-model a/b intersection is the Kronecker delta. -/
theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle left)
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle right) =
      if left = right then 1 else 0 := by
  unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
    Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle
  rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates_realize,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates_realize]
  exact CellularHomology.intersection_a_b left right

/-- Every even-model cycle is its realized symplectic coordinate plus an extension of an explicit concrete face-boundary
combination. -/
theorem cycle_symplectic_decomposition {genus : Nat}
    (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus) (cycle :
      Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle chain) :
    exists boundary : OddCellularHomology.EdgeChain genus,
      OddCellularHomology.IsFaceBoundary boundary /\
      chain = (Curves.Hyperelliptic.Topology.EvenCellularHomology.realize
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates chain)).add
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend boundary) := by
  let reduced := Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain
  have reducedCycle : OddCellularHomology.Cycle reduced :=
    Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_cycle cycle
  let evenWeight := reduced.sheetZero 0
  let oddWeight := reduced.sheetZero 1
  let totalWeight := reduced.sheetZero 0 + reduced.sheetOne 0 -
    evenWeight - oddWeight
  let boundary := OddCellularHomology.boundaryCombination genus
    evenWeight oddWeight totalWeight
  refine ⟨boundary, ?_, ?_⟩
  · exact (OddCellularHomology.isBoundary_iff_isFaceBoundary boundary).mp
      ⟨evenWeight, oddWeight, totalWeight, rfl⟩
  · have reducedDecomposition :=
      OddSymplecticHomology.cycle_symplectic_decomposition
        reduced reducedCycle
    dsimp only at reducedDecomposition
    have restored := Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_restrict_of_cycle chain cycle
    dsimp [reduced, evenWeight, oddWeight, totalWeight, boundary] at reducedDecomposition
    dsimp [reduced, evenWeight, oddWeight, totalWeight, boundary]
    calc
      chain = Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain) := restored.symm
      _ = Curves.Hyperelliptic.Topology.EvenCellularHomology.extend
          ((OddSymplecticHomology.realize
              (OddSymplecticHomology.homologyCoordinates (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict
                chain))).add
            (OddCellularHomology.boundaryCombination genus
              ((Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 0)
                ((Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 1)
              ((Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 0 +
                (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetOne 0 -
                (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 0 -
                (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 1))) := by
            exact congrArg Curves.Hyperelliptic.Topology.EvenCellularHomology.extend reducedDecomposition
      _ = (Curves.Hyperelliptic.Topology.EvenCellularHomology.realize
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates chain)).add
          (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend (OddCellularHomology.boundaryCombination genus
            ((Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 0)
              ((Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 1)
            ((Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 0 +
              (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetOne 0 -
              (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 0 -
              (Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict chain).sheetZero 1))) := by
            rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.extend_add]
            rfl

/-- A restored standard coordinate represents a face boundary exactly when the original coordinate vector vanishes. -/
theorem realize_boundary_iff_zero {genus : Nat}
    (coordinate : Curves.Hyperelliptic.Topology.EvenCellularHomology.StandardHomology genus) :
    Curves.Hyperelliptic.Topology.EvenCellularHomology.IsBoundary
      (Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology.realize coordinate) <->
      coordinate = CellularHomology.zeroOneChain genus := by
  constructor
  · rintro ⟨oddBoundary, faceBoundary, equal⟩
    have restricted := congrArg Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict equal
    unfold Curves.Hyperelliptic.Topology.EvenCellularHomology.realize at restricted
    rw [Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_extend,
      Curves.Hyperelliptic.Topology.EvenCellularHomology.restrict_extend] at restricted
    have oddBoundaryProperty : OddCellularHomology.IsBoundary
        (OddSymplecticHomology.realize coordinate) := by
      apply (OddCellularHomology.isBoundary_iff_isFaceBoundary _).mpr
      rw [restricted]
      exact faceBoundary
    exact (OddSymplecticHomology.realize_boundary_iff_zero coordinate).mp
      oddBoundaryProperty
  · intro zero
    have oddBoundary :=
      (OddSymplecticHomology.realize_boundary_iff_zero coordinate).mpr zero
    exact ⟨OddSymplecticHomology.realize coordinate,
      (OddCellularHomology.isBoundary_iff_isFaceBoundary _).mp oddBoundary, rfl⟩

set_option genInjectivity false in
/-- A finite symplectic basis certificate for the even-degree cellular quotient.

It retains the actual cycle equations, explicit face-boundary decomposition, uniqueness of standard coordinates and the
three symplectic intersection blocks. -/
structure Certificate (genus : Nat) : Type where
  /-- Each original a-representative satisfies the even-model cycle equations. -/ a_cycle : forall index : Fin genus,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle (Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle
    index)
  /-- Each original b-representative satisfies the even-model cycle equations. -/ b_cycle : forall index : Fin genus,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle (Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle
    index)
  /-- Every original cycle is its standard-coordinate representative plus an explicitly extended face boundary. -/
    decompose : forall (chain : Curves.Hyperelliptic.Topology.EvenCellularHomology.EdgeChain genus),
    Curves.Hyperelliptic.Topology.EvenCellularHomology.Cycle chain ->
    exists boundary : OddCellularHomology.EdgeChain genus,
      OddCellularHomology.IsFaceBoundary boundary /\
      chain = (Curves.Hyperelliptic.Topology.EvenCellularHomology.realize
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.homologyCoordinates chain)).add
        (Curves.Hyperelliptic.Topology.EvenCellularHomology.extend boundary)
  /-- The realized standard coordinate is a face boundary exactly when that coordinate vector is zero. -/ unique :
    forall coordinate : Curves.Hyperelliptic.Topology.EvenCellularHomology.StandardHomology genus,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.IsBoundary
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.realize coordinate) <->
      coordinate = CellularHomology.zeroOneChain genus
  /-- The original a-cycle block has zero pairwise intersection. -/ a_a : forall left right : Fin genus,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle left)
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle right) = 0
  /-- The original b-cycle block has zero pairwise intersection. -/ b_b : forall left right : Fin genus,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle left)
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle right) = 0
  /-- The mixed original a/b intersection block is the identity matrix. -/ a_b : forall left right : Fin genus,
    Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle left)
      (Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle right) =
      if left = right then 1 else 0

constructive_injectivity Certificate

/-- Construct the even-model symplectic basis certificate from the explicit restriction and extension proofs. -/
@[expose] def certificate (genus : Nat) : Curves.Hyperelliptic.Topology.EvenCellularHomology.Certificate genus where
  a_cycle := Curves.Hyperelliptic.Topology.EvenCellularHomology.aCycle_isCycle
  b_cycle := Curves.Hyperelliptic.Topology.EvenCellularHomology.bCycle_isCycle
  decompose := Curves.Hyperelliptic.Topology.EvenCellularHomology.cycle_symplectic_decomposition
  unique := Curves.Hyperelliptic.Topology.EvenCellularHomology.realize_boundary_iff_zero
  a_a := Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection_a_a
  b_b := Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection_b_b
  a_b := Curves.Hyperelliptic.Topology.EvenCellularHomology.intersection_a_b

end Purelib.Curves.Hyperelliptic.Topology.EvenCellularHomology

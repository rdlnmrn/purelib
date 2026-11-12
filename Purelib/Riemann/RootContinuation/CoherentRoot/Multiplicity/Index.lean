module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Indices of original multiplicity root caches

The structural index retains the original factor preparation and its bounded
root index. Its finite enumeration follows that same preparation spine and
reads the already stored coherent programs.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Count the actual root entries of the original retained factor-preparation spine. -/
@[expose] def size : {entries : List PositiveEntry} → Residual.Multiplicity.Family entries → Nat
  | [], .nil => 0
  | _ :: _, .cons head tail => count head + size tail

set_option genInjectivity false in
/-- A bounded root occurrence belonging to an original retained factor preparation.

The head case keeps its original factor-root index. The tail case keeps the
original remaining preparation, without replacing either factor owner.
-/
inductive Index : {entries : List PositiveEntry} → Residual.Multiplicity.Family entries → Type where
  /-- Select a root of the original head factor at its original bounded index. -/
  | head {entry : PositiveEntry} {entries : List PositiveEntry}
      {factor : Residual.Multiplicity.Factor entry} {remaining : Residual.Multiplicity.Family entries}
      (rootIndex : Fin (count factor)) : Index (.cons factor remaining)
  /-- Select an unchanged occurrence in the original retained tail. -/
  | tail {entry : PositiveEntry} {entries : List PositiveEntry}
      {factor : Residual.Multiplicity.Factor entry} {remaining : Residual.Multiplicity.Family entries}
      (index : Index remaining) : Index (.cons factor remaining)

constructive_injectivity Index

namespace Index

/-- Enumerate a structural occurrence in the original factor order and original root order. -/
@[expose] def toFin : {entries : List PositiveEntry} → {preparation : Residual.Multiplicity.Family entries} →
    Index preparation → Fin (size preparation)
  | _ :: _, .cons _ _, .head rootIndex =>
      ⟨rootIndex.val, Nat.lt_of_lt_of_le rootIndex.isLt (Nat.le_add_right _ _)⟩
  | _ :: _, .cons factor _, .tail index =>
      let tailIndex := index.toFin
      ⟨count factor + tailIndex.val, Nat.add_lt_add_left tailIndex.isLt (count factor)⟩

/-- Recover the original factor-root occurrence from its bounded enumeration index. -/
@[expose] def ofFin : {entries : List PositiveEntry} → (preparation : Residual.Multiplicity.Family entries) →
    Fin (size preparation) → Index preparation
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons factor remaining, index =>
      if bound : index.val < count factor then
        .head ⟨index.val, bound⟩
      else
        .tail (ofFin remaining ⟨index.val - count factor, by
          have original := index.isLt
          change index.val < count factor + size remaining at original
          omega0⟩)

/-- Head enumeration preserves the original bounded factor-root value. -/
theorem toFin_head {entry : PositiveEntry} {entries : List PositiveEntry}
    {factor : Residual.Multiplicity.Factor entry} {remaining : Residual.Multiplicity.Family entries}
    (index : Fin (count factor)) :
    (Index.head (remaining := remaining) index).toFin =
      ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩ := rfl

/-- Tail enumeration adds the original head count to the unchanged original tail position. -/
theorem toFin_tail {entry : PositiveEntry} {entries : List PositiveEntry}
    {factor : Residual.Multiplicity.Factor entry} {remaining : Residual.Multiplicity.Family entries}
    (index : Index remaining) :
    (Index.tail (factor := factor) index).toFin =
      ⟨count factor + index.toFin.val, Nat.add_lt_add_left index.toFin.isLt (count factor)⟩ := rfl

/-- Enumeration inversion follows the original head-count test and retained tail. -/
theorem ofFin_cons {entry : PositiveEntry} {entries : List PositiveEntry}
    (factor : Residual.Multiplicity.Factor entry) (remaining : Residual.Multiplicity.Family entries)
    (index : Fin (size (.cons factor remaining))) :
    ofFin (.cons factor remaining) index =
      if bound : index.val < count factor then .head ⟨index.val, bound⟩
      else .tail (ofFin remaining ⟨index.val - count factor, by
        have original := index.isLt
        change index.val < count factor + size remaining at original
        omega0⟩) := rfl

/-- The finite enumeration recovers every original bounded enumeration position. -/
theorem toFin_ofFin : {entries : List PositiveEntry} → (preparation : Residual.Multiplicity.Family entries) →
    (index : Fin (size preparation)) → (ofFin preparation index).toFin = index
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons factor remaining, index => by
      rewrite [ofFin_cons]
      split
      · rfl
      · rename_i outside
        change (⟨count factor + (ofFin remaining _).toFin.val, _⟩ : Fin _) = index
        have tailEqual := toFin_ofFin remaining ⟨index.val - count factor, by
          have original := index.isLt
          change index.val < count factor + size remaining at original
          omega0⟩
        apply Fin.ext
        change count factor + (ofFin remaining _).toFin.val = index.val
        rewrite [tailEqual]
        change count factor + (index.val - count factor) = index.val
        omega0

/-- Recovering a finite position preserves its original structural factor-root occurrence. -/
theorem ofFin_toFin : {entries : List PositiveEntry} → {preparation : Residual.Multiplicity.Family entries} →
    (index : Index preparation) → ofFin preparation index.toFin = index
  | _ :: _, .cons factor remaining, .head rootIndex => by
      rewrite [toFin_head, ofFin_cons, dif_pos rootIndex.isLt]
      rfl
  | _ :: _, .cons factor remaining, .tail index => by
      rewrite [toFin_tail, ofFin_cons]
      have outside : ¬ count factor + index.toFin.val < count factor := by omega0
      rewrite [dif_neg outside]
      have position : (⟨count factor + index.toFin.val - count factor, by
        have original := index.toFin.isLt
        omega0⟩ : Fin (size remaining)) = index.toFin := by
        apply Fin.ext
        change count factor + index.toFin.val - count factor = index.toFin.val
        omega0
      change Index.tail (factor := factor) (ofFin remaining
        ⟨count factor + index.toFin.val - count factor, _⟩) = Index.tail index
      rewrite [position, ofFin_toFin index]
      rfl

/-- Locate a root using its original bounded factor index and unchanged original root index. -/
@[expose] def fromFactor : {entries : List PositiveEntry} → (preparation : Residual.Multiplicity.Family entries) →
    (factorIndex : Fin entries.length) → Fin (count (preparation.get factorIndex)) → Index preparation
  | [], .nil, factorIndex, _ => Fin.elim0 factorIndex
  | _ :: _, .cons _ _, ⟨0, _⟩, rootIndex => .head rootIndex
  | _ :: _, .cons _ remaining, ⟨index + 1, bound⟩, rootIndex =>
      .tail (fromFactor remaining ⟨index, Nat.lt_of_succ_lt_succ bound⟩ rootIndex)

/-- Read the unchanged original bounded factor-list position of a root occurrence. -/
@[expose] def factorIndex : {entries : List PositiveEntry} →
    {preparation : Residual.Multiplicity.Family entries} → Index preparation → Fin entries.length
  | _ :: _, .cons _ _, .head _ => ⟨0, Nat.zero_lt_succ _⟩
  | _ :: _, .cons _ _, .tail index => index.factorIndex.succ

/-- Read the unchanged bounded root index of the occurrence's original factor preparation. -/
@[expose] def rootIndex : {entries : List PositiveEntry} →
    {preparation : Residual.Multiplicity.Family entries} → (index : Index preparation) →
    Fin (count (preparation.get index.factorIndex))
  | _ :: _, .cons _ _, .head index => index
  | _ :: _, .cons _ _, .tail index => index.rootIndex

/-- The structural occurrence is recovered from its same original factor and root projections. -/
theorem fromFactor_projections : {entries : List PositiveEntry} →
    {preparation : Residual.Multiplicity.Family entries} → (index : Index preparation) →
    fromFactor preparation index.factorIndex index.rootIndex = index
  | _ :: _, .cons _ _, .head _ => rfl
  | _ :: _, .cons _ _, .tail index => congrArg Index.tail (fromFactor_projections index)

end Index

namespace Family

/-- Read the same stored original approximation at a structural factor-root occurrence. -/
@[expose] def approximation : {entries : List PositiveEntry} → {preparation : Residual.Multiplicity.Family entries} →
    Family preparation → Index preparation → Sequence.ApproximationData
  | _ :: _, .cons _ _, .cons roots _, .head index => roots.approximation index
  | _ :: _, .cons _ _, .cons _ remaining, .tail index => remaining.approximation index

/-- Read the same stored original coherent channel at a structural factor-root occurrence. -/
@[expose] def channel : {entries : List PositiveEntry} → {preparation : Residual.Multiplicity.Family entries} →
    Family preparation → Index preparation → CoherentNamed
  | _ :: _, .cons _ _, .cons roots _, .head index => roots.channel index
  | _ :: _, .cons _ _, .cons _ remaining, .tail index => remaining.channel index

/-- Enumerate the existing original approximation caches without rebuilding their realizations. -/
@[expose] def candidates {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (index : Fin (size preparation)) : Sequence.ApproximationData :=
  roots.approximation (Index.ofFin preparation index)

/-- Structural lookup agrees with the original dependent factor-cache lookup. -/
theorem approximation_fromFactor : {entries : List PositiveEntry} →
    {preparation : Residual.Multiplicity.Family entries} →
    (roots : Family preparation) → (factorIndex : Fin entries.length) →
    (rootIndex : Fin (count (preparation.get factorIndex))) →
    roots.approximation (Index.fromFactor preparation factorIndex rootIndex) =
      (roots.get factorIndex).approximation rootIndex
  | [], .nil, .nil, factorIndex, _ => Fin.elim0 factorIndex
  | _ :: _, .cons _ _, .cons _ _, ⟨0, _⟩, _ => rfl
  | _ :: _, .cons _ _, .cons _ remaining, ⟨index + 1, bound⟩, rootIndex =>
      approximation_fromFactor remaining ⟨index, Nat.lt_of_succ_lt_succ bound⟩ rootIndex

/-- Structural channel lookup agrees with the original dependent factor-cache lookup. -/
theorem channel_fromFactor : {entries : List PositiveEntry} →
    {preparation : Residual.Multiplicity.Family entries} →
    (roots : Family preparation) → (factorIndex : Fin entries.length) →
    (rootIndex : Fin (count (preparation.get factorIndex))) →
    roots.channel (Index.fromFactor preparation factorIndex rootIndex) =
      (roots.get factorIndex).channel rootIndex
  | [], .nil, .nil, factorIndex, _ => Fin.elim0 factorIndex
  | _ :: _, .cons _ _, .cons _ _, ⟨0, _⟩, _ => rfl
  | _ :: _, .cons _ _, .cons _ remaining, ⟨index + 1, bound⟩, rootIndex =>
      channel_fromFactor remaining ⟨index, Nat.lt_of_succ_lt_succ bound⟩ rootIndex

/-- Finite enumeration reads the unchanged original structural occurrence's cache. -/
theorem candidates_toFin {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (index : Index preparation) :
    roots.candidates index.toFin = roots.approximation index := by
  unfold candidates
  rewrite [Index.ofFin_toFin]
  rfl

/-- Finite lookup retains the selected original factor index, root index and stored approximation. -/
theorem candidates_fromFactor {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation)
    (factorIndex : Fin entries.length) (rootIndex : Fin (count (preparation.get factorIndex))) :
    roots.candidates (Index.fromFactor preparation factorIndex rootIndex).toFin =
      (roots.get factorIndex).approximation rootIndex :=
  (roots.candidates_toFin _).trans (roots.approximation_fromFactor factorIndex rootIndex)

/-- Structural lookup reads the original dependent factor cache at both original occurrence indices. -/
theorem approximation_projections {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation) (index : Index preparation) :
    roots.approximation index = (roots.get index.factorIndex).approximation index.rootIndex := by
  have original := roots.approximation_fromFactor index.factorIndex index.rootIndex
  rewrite [Index.fromFactor_projections] at original
  exact original

/-- Structural channel lookup reads both original occurrence indices of the same retained factor cache. -/
theorem channel_projections {entries : List PositiveEntry}
    {preparation : Residual.Multiplicity.Family entries} (roots : Family preparation) (index : Index preparation) :
    roots.channel index = (roots.get index.factorIndex).channel index.rootIndex := by
  have original := roots.channel_fromFactor index.factorIndex index.rootIndex
  rewrite [Index.fromFactor_projections] at original
  exact original

end Family

end Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

end

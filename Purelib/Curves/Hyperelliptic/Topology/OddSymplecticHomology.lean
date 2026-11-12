module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Vector.Basic

public import Purelib.Topology.Surface.CellularHomology
public import Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Topology

open Purelib.Topology.Surface

public section

/-!
# Symplectic coordinates for the odd-degree attaching model

The explicit edge-cycle quotient has `2g` tail coordinates.  This module
identifies those structural coordinates with the standard two blocks of `g`
integral coefficients, transports the finite intersection pairing, and
exhibits actual edge chains representing the `a`- and `b`-cycles.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology

open Purelib.Curves.Hyperelliptic.Topology.OddCellularHomology

/-- The standard integral homology coordinates arranged in two blocks of the retained genus. -/
abbrev StandardHomology (genus : Nat) :=
  CellularHomology.FirstHomology genus

/-- Reindex the `2g` tail coordinates as the standard pair of `g` blocks. -/
@[expose] def toStandard {genus : Nat} (coordinate : TailVector genus) :
    StandardHomology genus :=
  Data.Vector.Basic.vectorOfFn fun index => coordinate ⟨index.val, by
    have bound := index.isLt
    unfold TailRank
    omega0⟩

/-- Reindex the standard pair of blocks back to the actual edge tail. -/
@[expose] def fromStandard {genus : Nat} (coordinate :
  StandardHomology genus) :
    TailVector genus :=
  Data.Vector.Basic.vectorOfFn fun index => coordinate ⟨index.val, by
    have bound := index.isLt
    unfold TailRank at bound
    omega0⟩

/-- Reindexing standard coordinates to the original tail and back returns the same vector. -/
@[simp] theorem toStandard_fromStandard {genus : Nat}
    (coordinate : StandardHomology genus) :
    toStandard
      (fromStandard coordinate) = coordinate := by
  apply Data.Vector.Basic.vector_ext
  intro index
  unfold toStandard
    fromStandard
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]

/-- Reindexing the original tail to standard coordinates and back returns the same vector. -/
@[simp] theorem fromStandard_toStandard {genus : Nat}
    (coordinate : TailVector genus) :
    fromStandard
      (toStandard coordinate) = coordinate := by
  apply Data.Vector.Basic.vector_ext
  intro index
  unfold toStandard
    fromStandard
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]

/-- The zero tail vector maps to the zero standard homology chain. -/
theorem toStandard_zero (genus : Nat) :
    toStandard (Data.Vector.Basic.vectorOfFn (fun _ : Fin
      (TailRank genus) => 0)) =
      CellularHomology.zeroOneChain genus := by
  apply Data.Vector.Basic.vector_ext
  intro index
  unfold toStandard CellularHomology.zeroOneChain
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- The zero standard homology chain maps to the zero tail vector. -/
theorem fromStandard_zero (genus : Nat) :
    fromStandard
      (CellularHomology.zeroOneChain genus) =
      Data.Vector.Basic.vectorOfFn (fun _ : Fin (TailRank genus) => 0) := by
  apply Data.Vector.Basic.vector_ext
  intro index
  unfold fromStandard CellularHomology.zeroOneChain
  rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  rw [Data.Vector.Basic.vectorOfFn_apply]

/-- Standard homology coordinates of an actual edge chain. -/
@[expose] def homologyCoordinates {genus : Nat} (chain : EdgeChain genus) :
    StandardHomology genus :=
  toStandard (coordinates chain)

/-- An actual odd-model edge chain representing a standard homology vector. -/
@[expose] def realize {genus : Nat} (coordinate : StandardHomology
  genus) :
    EdgeChain genus :=
  representative (fromStandard coordinate)

/-- The edge chain realizing a standard homology coordinate is a cellular cycle. -/
@[expose] def realize_cycle {genus : Nat} (coordinate :
  StandardHomology genus) :
    Cycle (realize coordinate) :=
  representative_cycle (fromStandard coordinate)

/-- Reading the homology coordinates of their realized edge chain returns the original vector. -/
@[simp] theorem homologyCoordinates_realize {genus : Nat}
    (coordinate : StandardHomology genus) :
    homologyCoordinates
      (realize coordinate) = coordinate := by
  unfold homologyCoordinates
    realize
  rw [coordinates_representative,
    toStandard_fromStandard]

/-- The actual edge representative of the standard `a_i` class. -/
@[expose] def aCycle {genus : Nat} (index : Fin genus) : EdgeChain genus :=
  realize (CellularHomology.aCycle index)

/-- The actual edge representative of the standard `b_i` class. -/
@[expose] def bCycle {genus : Nat} (index : Fin genus) : EdgeChain genus :=
  realize (CellularHomology.bCycle index)

/-- The retained actual edge representative of each standard a-class is a cycle. -/
@[expose] def aCycle_isCycle {genus : Nat} (index : Fin genus) :
    Cycle (aCycle index) :=
  realize_cycle _

/-- The retained actual edge representative of each standard b-class is a cycle. -/
@[expose] def bCycle_isCycle {genus : Nat} (index : Fin genus) :
    Cycle (bCycle index) :=
  realize_cycle _

/-- The actual a-cycle has the corresponding standard a-coordinate vector. -/
@[simp] theorem homologyCoordinates_aCycle {genus : Nat}
    (index : Fin genus) :
    homologyCoordinates
      (aCycle index) =
      CellularHomology.aCycle index := by
  exact homologyCoordinates_realize _

/-- The actual b-cycle has the corresponding standard b-coordinate vector. -/
@[simp] theorem homologyCoordinates_bCycle {genus : Nat}
    (index : Fin genus) :
    homologyCoordinates
      (bCycle index) =
      CellularHomology.bCycle index := by
  exact homologyCoordinates_realize _

/-- The intersection pairing on actual odd-model chains, defined on their boundary-invariant quotient coordinates. -/
@[expose] def intersection {genus : Nat} (left right : EdgeChain genus) : Int :=
  CellularHomology.intersection
    (homologyCoordinates left)
      (homologyCoordinates right)

/-- Any two actual a-cycles have zero intersection. -/
theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    intersection
      (aCycle left)
      (aCycle right) = 0 := by
  unfold intersection
  rw [homologyCoordinates_aCycle,
    homologyCoordinates_aCycle]
  exact CellularHomology.intersection_a_a left right

/-- Any two actual b-cycles have zero intersection. -/
theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    intersection
      (bCycle left)
      (bCycle right) = 0 := by
  unfold intersection
  rw [homologyCoordinates_bCycle,
    homologyCoordinates_bCycle]
  exact CellularHomology.intersection_b_b left right

/-- The actual a-cycle and b-cycle intersect by the Kronecker delta of their indices. -/
theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    intersection
      (aCycle left)
      (bCycle right) =
      if left = right then 1 else 0 := by
  unfold intersection
  rw [homologyCoordinates_aCycle,
    homologyCoordinates_bCycle]
  exact CellularHomology.intersection_a_b left right

/-- The actual b-cycle and a-cycle intersect by minus the Kronecker delta of their indices. -/
theorem intersection_b_a {genus : Nat} (left right : Fin genus) :
    intersection
      (bCycle left)
      (aCycle right) =
      -(if left = right then 1 else 0) := by
  unfold intersection
  rw [homologyCoordinates_bCycle,
    homologyCoordinates_aCycle]
  exact CellularHomology.intersection_b_a left right

/-- Every actual cellular cycle is its symplectic-coordinate representative plus an explicit combination of the three
concrete independent face words. -/
theorem cycle_symplectic_decomposition {genus : Nat}
    (chain : EdgeChain genus) (cycle : Cycle chain) :
    let evenWeight := chain.sheetZero 0
    let oddWeight := chain.sheetZero 1
    let totalWeight := chain.sheetZero 0 + chain.sheetOne 0 -
      evenWeight - oddWeight
    chain = (realize
      (homologyCoordinates chain)).add
      (boundaryCombination genus evenWeight oddWeight totalWeight) := by
  dsimp only
  have realized : realize
    (homologyCoordinates chain) =
      representative (coordinates chain) := by
    unfold realize
      homologyCoordinates
    rw [fromStandard_toStandard]
  rw [realized]
  exact cycle_decomposition chain cycle

/-- The realized standard coordinate is a face boundary exactly when all its displayed integral coordinates vanish. -/
theorem realize_boundary_iff_zero {genus : Nat}
    (coordinate : StandardHomology genus) :
    IsBoundary (realize coordinate) <->
      coordinate = CellularHomology.zeroOneChain genus := by
  rw [show realize coordinate = representative
    (fromStandard coordinate) by
    rfl]
  constructor
  · intro boundary
    have zero := (representative_boundary_iff_coordinates_zero _).mp boundary
    have mapped := congrArg toStandard zero
    rw [toStandard_fromStandard,
      toStandard_zero] at mapped
    exact mapped
  · intro zero
    apply (representative_boundary_iff_coordinates_zero _).mpr
    subst coordinate
    exact fromStandard_zero genus

set_option genInjectivity false in
/-- Finite certificate that the displayed actual edge cycles form a symplectic basis for the odd-degree cellular
quotient. -/
structure Certificate (genus : Nat) : Type where
  /-- Each retained actual a-cycle has zero cellular boundary. -/ a_cycle : forall index : Fin genus,
    Cycle (aCycle index)
  /-- Each retained actual b-cycle has zero cellular boundary. -/ b_cycle : forall index : Fin genus,
    Cycle (bCycle index)
  /-- Every actual cycle equals its standard-coordinate representative plus the displayed original face-boundary
    combination. -/ decompose : forall (chain : EdgeChain genus), Cycle chain ->
    let evenWeight := chain.sheetZero 0
    let oddWeight := chain.sheetZero 1
    let totalWeight := chain.sheetZero 0 + chain.sheetOne 0 -
      evenWeight - oddWeight
    chain = (realize
      (homologyCoordinates chain)).add
      (boundaryCombination genus evenWeight oddWeight totalWeight)
  /-- A realized standard coordinate is a face boundary exactly when that coordinate vector is zero. -/ unique : forall
    coordinate : StandardHomology genus,
    IsBoundary (realize coordinate) <->
      coordinate = CellularHomology.zeroOneChain genus
  /-- The a-cycle block has zero pairwise intersection. -/ a_a : forall left right : Fin genus,
    intersection
      (aCycle left)
      (aCycle right) = 0
  /-- The b-cycle block has zero pairwise intersection. -/ b_b : forall left right : Fin genus,
    intersection
      (bCycle left)
      (bCycle right) = 0
  /-- The mixed a/b intersection block is the identity matrix. -/ a_b : forall left right : Fin genus,
    intersection
      (aCycle left)
      (bCycle right) =
    if left = right then 1 else 0

set_option cleanup.letToHave false in
constructive_injectivity Certificate

/-- Construct the finite symplectic basis certificate from the explicit edge cycles and boundary decomposition. -/
@[expose] def certificate (genus : Nat) : Certificate genus where
  a_cycle := aCycle_isCycle
  b_cycle := bCycle_isCycle
  decompose := cycle_symplectic_decomposition
  unique := realize_boundary_iff_zero
  a_a := intersection_a_a
  b_b := intersection_b_b
  a_b := intersection_a_b

end Purelib.Curves.Hyperelliptic.Topology.OddSymplecticHomology

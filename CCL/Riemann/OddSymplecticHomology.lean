import CCL.Riemann.OddCellularHomology

/-!
# Symplectic coordinates for the odd-degree attaching model

The explicit edge-cycle quotient has `2g` tail coordinates.  This module
identifies those structural coordinates with the standard two blocks of `g`
integral coefficients, transports the finite intersection pairing, and
exhibits actual edge chains representing the `a`- and `b`-cycles.
-/

namespace CCL.Riemann.OddSymplecticHomology

open RFAP.ConstructiveFiniteMatrix
open CCL.Riemann.OddCellularHomology

abbrev StandardHomology (genus : Nat) :=
  CCL.Riemann.CellularHomology.FirstHomology genus

/-- Reindex the `2g` tail coordinates as the standard pair of `g` blocks. -/
def toStandard {genus : Nat} (coordinate : TailVector genus) :
    StandardHomology genus :=
  vectorOfFn fun index => coordinate ⟨index.val, by
    have bound := index.isLt
    unfold TailRank
    omega0⟩

/-- Reindex the standard pair of blocks back to the actual edge tail. -/
def fromStandard {genus : Nat} (coordinate : StandardHomology genus) :
    TailVector genus :=
  vectorOfFn fun index => coordinate ⟨index.val, by
    have bound := index.isLt
    unfold TailRank at bound
    omega0⟩

@[simp] theorem toStandard_fromStandard {genus : Nat}
    (coordinate : StandardHomology genus) :
    toStandard (fromStandard coordinate) = coordinate := by
  apply vector_ext
  intro index
  unfold toStandard fromStandard
  rw [vectorOfFn_apply, vectorOfFn_apply]

@[simp] theorem fromStandard_toStandard {genus : Nat}
    (coordinate : TailVector genus) :
    fromStandard (toStandard coordinate) = coordinate := by
  apply vector_ext
  intro index
  unfold toStandard fromStandard
  rw [vectorOfFn_apply, vectorOfFn_apply]

theorem toStandard_zero (genus : Nat) :
    toStandard (vectorOfFn (fun _ : Fin (TailRank genus) => 0)) =
      CCL.Riemann.CellularHomology.zeroOneChain genus := by
  apply vector_ext
  intro index
  unfold toStandard CCL.Riemann.CellularHomology.zeroOneChain
  rw [vectorOfFn_apply, vectorOfFn_apply]
  rw [vectorOfFn_apply]

theorem fromStandard_zero (genus : Nat) :
    fromStandard (CCL.Riemann.CellularHomology.zeroOneChain genus) =
      vectorOfFn (fun _ : Fin (TailRank genus) => 0) := by
  apply vector_ext
  intro index
  unfold fromStandard CCL.Riemann.CellularHomology.zeroOneChain
  rw [vectorOfFn_apply, vectorOfFn_apply]
  rw [vectorOfFn_apply]

/-- Standard homology coordinates of an actual edge chain. -/
def homologyCoordinates {genus : Nat} (chain : EdgeChain genus) :
    StandardHomology genus :=
  toStandard (coordinates chain)

/-- An actual odd-model edge chain representing a standard homology vector. -/
def realize {genus : Nat} (coordinate : StandardHomology genus) :
    EdgeChain genus :=
  representative (fromStandard coordinate)

def realize_cycle {genus : Nat} (coordinate : StandardHomology genus) :
    Cycle (realize coordinate) :=
  representative_cycle (fromStandard coordinate)

@[simp] theorem homologyCoordinates_realize {genus : Nat}
    (coordinate : StandardHomology genus) :
    homologyCoordinates (realize coordinate) = coordinate := by
  unfold homologyCoordinates realize
  rw [coordinates_representative, toStandard_fromStandard]

/-- The actual edge representative of the standard `a_i` class. -/
def aCycle {genus : Nat} (index : Fin genus) : EdgeChain genus :=
  realize (CCL.Riemann.CellularHomology.aCycle index)

/-- The actual edge representative of the standard `b_i` class. -/
def bCycle {genus : Nat} (index : Fin genus) : EdgeChain genus :=
  realize (CCL.Riemann.CellularHomology.bCycle index)

def aCycle_isCycle {genus : Nat} (index : Fin genus) :
    Cycle (aCycle index) :=
  realize_cycle _

def bCycle_isCycle {genus : Nat} (index : Fin genus) :
    Cycle (bCycle index) :=
  realize_cycle _

@[simp] theorem homologyCoordinates_aCycle {genus : Nat}
    (index : Fin genus) :
    homologyCoordinates (aCycle index) =
      CCL.Riemann.CellularHomology.aCycle index := by
  exact homologyCoordinates_realize _

@[simp] theorem homologyCoordinates_bCycle {genus : Nat}
    (index : Fin genus) :
    homologyCoordinates (bCycle index) =
      CCL.Riemann.CellularHomology.bCycle index := by
  exact homologyCoordinates_realize _

/-- The intersection pairing on actual odd-model chains, defined on their
boundary-invariant quotient coordinates. -/
def intersection {genus : Nat} (left right : EdgeChain genus) : Int :=
  CCL.Riemann.CellularHomology.intersection
    (homologyCoordinates left) (homologyCoordinates right)

theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (aCycle right) = 0 := by
  unfold intersection
  rw [homologyCoordinates_aCycle, homologyCoordinates_aCycle]
  exact CCL.Riemann.CellularHomology.intersection_a_a left right

theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (bCycle right) = 0 := by
  unfold intersection
  rw [homologyCoordinates_bCycle, homologyCoordinates_bCycle]
  exact CCL.Riemann.CellularHomology.intersection_b_b left right

theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (bCycle right) =
      if left = right then 1 else 0 := by
  unfold intersection
  rw [homologyCoordinates_aCycle, homologyCoordinates_bCycle]
  exact CCL.Riemann.CellularHomology.intersection_a_b left right

theorem intersection_b_a {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (aCycle right) =
      -(if left = right then 1 else 0) := by
  unfold intersection
  rw [homologyCoordinates_bCycle, homologyCoordinates_aCycle]
  exact CCL.Riemann.CellularHomology.intersection_b_a left right

/-- Every actual cellular cycle is its symplectic-coordinate representative
plus an explicit combination of the three concrete independent face words. -/
theorem cycle_symplectic_decomposition {genus : Nat}
    (chain : EdgeChain genus) (cycle : Cycle chain) :
    let evenWeight := chain.sheetZero 0
    let oddWeight := chain.sheetZero 1
    let totalWeight := chain.sheetZero 0 + chain.sheetOne 0 -
      evenWeight - oddWeight
    chain = (realize (homologyCoordinates chain)).add
      (boundaryCombination genus evenWeight oddWeight totalWeight) := by
  dsimp only
  have realized : realize (homologyCoordinates chain) =
      representative (coordinates chain) := by
    unfold realize homologyCoordinates
    rw [fromStandard_toStandard]
  rw [realized]
  exact cycle_decomposition chain cycle

/-- The realized standard coordinate is a face boundary exactly when all
its displayed integral coordinates vanish. -/
theorem realize_boundary_iff_zero {genus : Nat}
    (coordinate : StandardHomology genus) :
    IsBoundary (realize coordinate) <->
      coordinate = CCL.Riemann.CellularHomology.zeroOneChain genus := by
  rw [show realize coordinate = representative (fromStandard coordinate) by
    rfl]
  rw [representative_boundary_iff_coordinates_zero]
  constructor
  · intro zero
    have mapped := congrArg toStandard zero
    rw [toStandard_fromStandard, toStandard_zero] at mapped
    exact mapped
  · intro zero
    subst coordinate
    exact fromStandard_zero genus

/-- Finite certificate that the displayed actual edge cycles form a
symplectic basis for the odd-degree cellular quotient. -/
structure Certificate (genus : Nat) : Type where
  a_cycle : forall index : Fin genus, Cycle (aCycle index)
  b_cycle : forall index : Fin genus, Cycle (bCycle index)
  decompose : forall (chain : EdgeChain genus), Cycle chain ->
    let evenWeight := chain.sheetZero 0
    let oddWeight := chain.sheetZero 1
    let totalWeight := chain.sheetZero 0 + chain.sheetOne 0 -
      evenWeight - oddWeight
    chain = (realize (homologyCoordinates chain)).add
      (boundaryCombination genus evenWeight oddWeight totalWeight)
  unique : forall coordinate : StandardHomology genus,
    IsBoundary (realize coordinate) <->
      coordinate = CCL.Riemann.CellularHomology.zeroOneChain genus
  a_a : forall left right : Fin genus,
    intersection (aCycle left) (aCycle right) = 0
  b_b : forall left right : Fin genus,
    intersection (bCycle left) (bCycle right) = 0
  a_b : forall left right : Fin genus,
    intersection (aCycle left) (bCycle right) =
    if left = right then 1 else 0

def certificate (genus : Nat) : Certificate genus where
  a_cycle := aCycle_isCycle
  b_cycle := bCycle_isCycle
  decompose := cycle_symplectic_decomposition
  unique := realize_boundary_iff_zero
  a_a := intersection_a_a
  b_b := intersection_b_b
  a_b := intersection_a_b

end CCL.Riemann.OddSymplecticHomology

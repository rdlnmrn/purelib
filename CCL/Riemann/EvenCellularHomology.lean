import CCL.Riemann.OddSymplecticHomology
import mathlib.Data.ConstructiveFin

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

namespace CCL.Riemann.EvenCellularHomology

open RFAP.ConstructiveFiniteMatrix
open CCL.Riemann.HyperellipticCells

open CCL.Riemann

abbrev EdgeCount (genus : Nat) := 2 * genus + 3
abbrev EdgeVector (genus : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector Int (EdgeCount genus)

/-- Integral coefficients on all lifted even-model edges. -/
structure EdgeChain (genus : Nat) where
  sheetZero : EdgeVector genus
  sheetOne : EdgeVector genus

namespace EdgeChain

theorem ext {genus : Nat} {left right : EdgeChain genus}
    (zeroEqual : forall index, left.sheetZero index = right.sheetZero index)
    (oneEqual : forall index, left.sheetOne index = right.sheetOne index) :
    left = right := by
  cases left with
  | mk leftZero leftOne =>
      cases right with
      | mk rightZero rightOne =>
          have zeroVector : leftZero = rightZero := vector_ext zeroEqual
          have oneVector : leftOne = rightOne := vector_ext oneEqual
          cases zeroVector
          cases oneVector
          rfl

def add {genus : Nat} (left right : EdgeChain genus) : EdgeChain genus where
  sheetZero := vectorOfFn fun index =>
    left.sheetZero index + right.sheetZero index
  sheetOne := vectorOfFn fun index =>
    left.sheetOne index + right.sheetOne index

def scale {genus : Nat} (chain : EdgeChain genus) (scalar : Int) :
    EdgeChain genus where
  sheetZero := vectorOfFn fun index => scalar * chain.sheetZero index
  sheetOne := vectorOfFn fun index => scalar * chain.sheetOne index

@[simp] theorem add_sheetZero {genus : Nat} (left right : EdgeChain genus)
    (index : Fin (EdgeCount genus)) :
    (left.add right).sheetZero index =
      left.sheetZero index + right.sheetZero index := by
  unfold add
  rw [vectorOfFn_apply]

@[simp] theorem add_sheetOne {genus : Nat} (left right : EdgeChain genus)
    (index : Fin (EdgeCount genus)) :
    (left.add right).sheetOne index =
      left.sheetOne index + right.sheetOne index := by
  unfold add
  rw [vectorOfFn_apply]

end EdgeChain

/-- Exact vertex-boundary equations: totals agree at every ramified vertex,
and the two sheet coefficients close separately at unramified infinity. -/
structure Cycle {genus : Nat} (chain : EdgeChain genus) : Type where
  total_eq : forall index : Fin (EdgeCount genus),
    chain.sheetZero index + chain.sheetOne index =
      chain.sheetZero 0 + chain.sheetOne 0
  closesZero : chain.sheetZero (Fin.last (2 * genus + 2)) =
    chain.sheetZero 0
  closesOne : chain.sheetOne (Fin.last (2 * genus + 2)) =
    chain.sheetOne 0

/-- Delete the terminal edge at infinity. -/
def restrict {genus : Nat} (chain : EdgeChain genus) :
    OddCellularHomology.EdgeChain genus where
  sheetZero := vectorOfFn fun index => chain.sheetZero index.castSucc
  sheetOne := vectorOfFn fun index => chain.sheetOne index.castSucc

/-- Restore the terminal edge by copying the edge-zero coefficient on each
sheet. -/
def extend {genus : Nat} (chain : OddCellularHomology.EdgeChain genus) :
    EdgeChain genus where
  sheetZero := vectorOfFn fun position =>
    QuotientFreeFin.lastCases (chain.sheetZero 0)
      (fun index => chain.sheetZero index)
      position
  sheetOne := vectorOfFn fun position =>
    QuotientFreeFin.lastCases (chain.sheetOne 0)
      (fun index => chain.sheetOne index)
      position

@[simp] theorem restrict_sheetZero {genus : Nat} (chain : EdgeChain genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (restrict chain).sheetZero index = chain.sheetZero index.castSucc := by
  unfold restrict
  rw [vectorOfFn_apply]

@[simp] theorem restrict_sheetOne {genus : Nat} (chain : EdgeChain genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (restrict chain).sheetOne index = chain.sheetOne index.castSucc := by
  unfold restrict
  rw [vectorOfFn_apply]

@[simp] theorem extend_sheetZero_castSucc {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (extend chain).sheetZero index.castSucc = chain.sheetZero index := by
  unfold extend
  rw [vectorOfFn_apply, QuotientFreeFin.lastCases_castSucc]

@[simp] theorem extend_sheetOne_castSucc {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    (extend chain).sheetOne index.castSucc = chain.sheetOne index := by
  unfold extend
  rw [vectorOfFn_apply, QuotientFreeFin.lastCases_castSucc]

@[simp] theorem extend_sheetZero_last {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (extend chain).sheetZero (Fin.last (2 * genus + 2)) =
      chain.sheetZero 0 := by
  unfold extend
  rw [vectorOfFn_apply, QuotientFreeFin.lastCases_last]

@[simp] theorem extend_sheetOne_last {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (extend chain).sheetOne (Fin.last (2 * genus + 2)) =
      chain.sheetOne 0 := by
  unfold extend
  rw [vectorOfFn_apply, QuotientFreeFin.lastCases_last]

@[simp] theorem extend_sheetZero_zero {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (extend chain).sheetZero 0 = chain.sheetZero 0 := by
  unfold extend
  rw [vectorOfFn_apply]
  change QuotientFreeFin.lastCases (chain.sheetZero 0)
    (fun index => chain.sheetZero index)
    (Fin.castSucc (0 : Fin (2 * genus + 2))) = chain.sheetZero 0
  rw [QuotientFreeFin.lastCases_castSucc]

@[simp] theorem extend_sheetOne_zero {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    (extend chain).sheetOne 0 = chain.sheetOne 0 := by
  unfold extend
  rw [vectorOfFn_apply]
  change QuotientFreeFin.lastCases (chain.sheetOne 0)
    (fun index => chain.sheetOne index)
    (Fin.castSucc (0 : Fin (2 * genus + 2))) = chain.sheetOne 0
  rw [QuotientFreeFin.lastCases_castSucc]

@[simp] theorem restrict_extend {genus : Nat}
    (chain : OddCellularHomology.EdgeChain genus) :
    restrict (extend chain) = chain := by
  apply OddCellularHomology.EdgeChain.ext <;> intro index
  · rw [restrict_sheetZero, extend_sheetZero_castSucc]
  · rw [restrict_sheetOne, extend_sheetOne_castSucc]

theorem extend_restrict_of_cycle {genus : Nat} (chain : EdgeChain genus)
    (cycle : Cycle chain) : extend (restrict chain) = chain := by
  apply EdgeChain.ext <;> intro position
  · rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      rw [extend_sheetZero_last, restrict_sheetZero]
      change chain.sheetZero 0 =
        chain.sheetZero (Fin.last (2 * genus + 2))
      exact cycle.closesZero.symm
    · subst position
      rw [extend_sheetZero_castSucc, restrict_sheetZero]
  · rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      rw [extend_sheetOne_last, restrict_sheetOne]
      change chain.sheetOne 0 =
        chain.sheetOne (Fin.last (2 * genus + 2))
      exact cycle.closesOne.symm
    · subst position
      rw [extend_sheetOne_castSucc, restrict_sheetOne]

def restrict_cycle {genus : Nat} {chain : EdgeChain genus}
    (cycle : Cycle chain) :
    OddCellularHomology.Cycle (restrict chain) where
  total_eq := by
    intro index
    rw [restrict_sheetZero, restrict_sheetOne,
      restrict_sheetZero, restrict_sheetOne]
    exact cycle.total_eq index.castSucc

def extend_cycle {genus : Nat}
    {chain : OddCellularHomology.EdgeChain genus}
    (cycle : OddCellularHomology.Cycle chain) : Cycle (extend chain) where
  total_eq := by
    intro position
    rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      rw [extend_sheetZero_last, extend_sheetOne_last,
        extend_sheetZero_zero, extend_sheetOne_zero]
    · subst position
      rw [extend_sheetZero_castSucc, extend_sheetOne_castSucc,
        extend_sheetZero_zero, extend_sheetOne_zero]
      exact cycle.total_eq index
  closesZero := by
    rw [extend_sheetZero_last, extend_sheetZero_zero]
  closesOne := by
    rw [extend_sheetOne_last, extend_sheetOne_zero]

theorem extend_add {genus : Nat}
    (left right : OddCellularHomology.EdgeChain genus) :
    extend (left.add right) = (extend left).add (extend right) := by
  apply EdgeChain.ext <;> intro position
  · rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      simp only [extend_sheetZero_last,
        OddCellularHomology.EdgeChain.add_sheetZero,
        EdgeChain.add_sheetZero]
    · subst position
      simp only [extend_sheetZero_castSucc,
        OddCellularHomology.EdgeChain.add_sheetZero,
        EdgeChain.add_sheetZero]
  · rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      simp only [extend_sheetOne_last,
        OddCellularHomology.EdgeChain.add_sheetOne,
        EdgeChain.add_sheetOne]
    · subst position
      simp only [extend_sheetOne_castSucc,
        OddCellularHomology.EdgeChain.add_sheetOne,
        EdgeChain.add_sheetOne]

/-! ## Agreement with the actual even attaching words -/

def faceChain {genus : Nat} (face : Face) : EdgeChain genus where
  sheetZero := vectorOfFn fun index =>
    if evenFaceSheet face index = sheetZero then 1 else 0
  sheetOne := vectorOfFn fun index =>
    if evenFaceSheet face index = sheetOne then 1 else 0

theorem evenFaceSheet_castSucc {genus : Nat} (face : Face)
    (index : Fin (OddCellularHomology.EdgeCount genus)) :
    evenFaceSheet face index.castSucc = oddFaceSheet face index := by
  cases face with
  | mk hemisphere lift =>
      cases hemisphere with
      | upper => rfl
      | lower =>
          unfold evenFaceSheet oddFaceSheet evenLowerSheet oddLowerSheet
          have below : index.castSucc.val + 1 < evenBaseCount genus := by
            change index.val + 1 < evenBaseCount genus
            have bound := index.isLt
            unfold OddCellularHomology.EdgeCount at bound
            unfold evenBaseCount finiteBranchCount
            omega0
          rw [dif_pos below]
          rfl

theorem evenFaceSheet_last {genus : Nat} (face : Face) :
    evenFaceSheet face (Fin.last (2 * genus + 2)) =
      oddFaceSheet face
        (0 : Fin (OddCellularHomology.EdgeCount genus)) := by
  cases face with
  | mk hemisphere lift =>
      cases hemisphere with
      | upper => rfl
      | lower =>
          unfold evenFaceSheet oddFaceSheet evenLowerSheet oddLowerSheet
          have terminal : ¬((Fin.last (2 * genus + 2)).val + 1 <
              evenBaseCount genus) := by
            rw [Fin.val_last]
            unfold evenBaseCount finiteBranchCount
            omega0
          rw [dif_neg terminal]
          rfl

/-- The actual even face word is obtained by extending the corresponding odd
word across the unramified infinity edge. -/
theorem faceChain_eq_extend_oddFaceChain (genus : Nat) (face : Face) :
    faceChain (genus := genus) face =
      extend (OddCellularHomology.faceChain (genus := genus) face) := by
  apply EdgeChain.ext <;> intro position
  · rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      unfold faceChain OddCellularHomology.faceChain
      rw [vectorOfFn_apply, extend_sheetZero_last, vectorOfFn_apply,
        evenFaceSheet_last]
    · subst position
      unfold faceChain OddCellularHomology.faceChain
      rw [vectorOfFn_apply, extend_sheetZero_castSucc, vectorOfFn_apply,
        evenFaceSheet_castSucc]
  · rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
    · subst position
      unfold faceChain OddCellularHomology.faceChain
      rw [vectorOfFn_apply, extend_sheetOne_last, vectorOfFn_apply,
        evenFaceSheet_last]
    · subst position
      unfold faceChain OddCellularHomology.faceChain
      rw [vectorOfFn_apply, extend_sheetOne_castSucc, vectorOfFn_apply,
        evenFaceSheet_castSucc]

/-- The oriented boundary of all four even-model faces also cancels exactly.
The terminal edge at the two points over infinity is included by the explicit
`extend` construction. -/
theorem upperFaceChains_eq_lowerFaceChains (genus : Nat) :
    (faceChain (genus := genus) OddCellularHomology.upperZeroFace).add
        (faceChain (genus := genus) OddCellularHomology.upperOneFace) =
      (faceChain (genus := genus) OddCellularHomology.lowerZeroFace).add
        (faceChain (genus := genus) OddCellularHomology.lowerOneFace) := by
  rw [faceChain_eq_extend_oddFaceChain,
    faceChain_eq_extend_oddFaceChain,
    faceChain_eq_extend_oddFaceChain,
    faceChain_eq_extend_oddFaceChain,
    ← extend_add, ← extend_add,
    OddCellularHomology.upperFaceChains_eq_lowerFaceChains]

/-- Even boundaries are exactly extensions of the already reduced span of
the corresponding concrete face words. -/
def IsBoundary {genus : Nat} (chain : EdgeChain genus) : Prop :=
  exists oddBoundary : OddCellularHomology.EdgeChain genus,
    OddCellularHomology.IsFaceBoundary oddBoundary /\
      chain = extend oddBoundary

/-! ## Transported symplectic basis -/

abbrev StandardHomology (genus : Nat) :=
  OddSymplecticHomology.StandardHomology genus

def homologyCoordinates {genus : Nat} (chain : EdgeChain genus) :
    StandardHomology genus :=
  OddSymplecticHomology.homologyCoordinates (restrict chain)

def realize {genus : Nat} (coordinate : StandardHomology genus) :
    EdgeChain genus :=
  extend (OddSymplecticHomology.realize coordinate)

def realize_cycle {genus : Nat} (coordinate : StandardHomology genus) :
    Cycle (realize coordinate) :=
  extend_cycle (OddSymplecticHomology.realize_cycle coordinate)

@[simp] theorem homologyCoordinates_realize {genus : Nat}
    (coordinate : StandardHomology genus) :
    homologyCoordinates (realize coordinate) = coordinate := by
  unfold homologyCoordinates realize
  rw [restrict_extend,
    OddSymplecticHomology.homologyCoordinates_realize]

def aCycle {genus : Nat} (index : Fin genus) : EdgeChain genus :=
  realize (CCL.Riemann.CellularHomology.aCycle index)

def bCycle {genus : Nat} (index : Fin genus) : EdgeChain genus :=
  realize (CCL.Riemann.CellularHomology.bCycle index)

def aCycle_isCycle {genus : Nat} (index : Fin genus) : Cycle (aCycle index) :=
  realize_cycle _

def bCycle_isCycle {genus : Nat} (index : Fin genus) : Cycle (bCycle index) :=
  realize_cycle _

def intersection {genus : Nat} (left right : EdgeChain genus) : Int :=
  CCL.Riemann.CellularHomology.intersection
    (homologyCoordinates left) (homologyCoordinates right)

theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (aCycle right) = 0 := by
  unfold intersection aCycle
  rw [homologyCoordinates_realize, homologyCoordinates_realize]
  exact CCL.Riemann.CellularHomology.intersection_a_a left right

theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    intersection (bCycle left) (bCycle right) = 0 := by
  unfold intersection bCycle
  rw [homologyCoordinates_realize, homologyCoordinates_realize]
  exact CCL.Riemann.CellularHomology.intersection_b_b left right

theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    intersection (aCycle left) (bCycle right) =
      if left = right then 1 else 0 := by
  unfold intersection aCycle bCycle
  rw [homologyCoordinates_realize, homologyCoordinates_realize]
  exact CCL.Riemann.CellularHomology.intersection_a_b left right

/-- Every even-model cycle is its realized symplectic coordinate plus an
extension of an explicit concrete face-boundary combination. -/
theorem cycle_symplectic_decomposition {genus : Nat}
    (chain : EdgeChain genus) (cycle : Cycle chain) :
    exists boundary : OddCellularHomology.EdgeChain genus,
      OddCellularHomology.IsFaceBoundary boundary /\
      chain = (realize (homologyCoordinates chain)).add (extend boundary) := by
  let reduced := restrict chain
  have reducedCycle : OddCellularHomology.Cycle reduced :=
    restrict_cycle cycle
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
    have restored := extend_restrict_of_cycle chain cycle
    dsimp [reduced, evenWeight, oddWeight, totalWeight, boundary] at reducedDecomposition
    dsimp [reduced, evenWeight, oddWeight, totalWeight, boundary]
    calc
      chain = extend (restrict chain) := restored.symm
      _ = extend
          ((OddSymplecticHomology.realize
              (OddSymplecticHomology.homologyCoordinates (restrict chain))).add
            (OddCellularHomology.boundaryCombination genus
              ((restrict chain).sheetZero 0) ((restrict chain).sheetZero 1)
              ((restrict chain).sheetZero 0 + (restrict chain).sheetOne 0 -
                (restrict chain).sheetZero 0 -
                (restrict chain).sheetZero 1))) := by
            exact congrArg extend reducedDecomposition
      _ = (realize (homologyCoordinates chain)).add
          (extend (OddCellularHomology.boundaryCombination genus
            ((restrict chain).sheetZero 0) ((restrict chain).sheetZero 1)
            ((restrict chain).sheetZero 0 + (restrict chain).sheetOne 0 -
              (restrict chain).sheetZero 0 -
              (restrict chain).sheetZero 1))) := by
            rw [extend_add]
            rfl

theorem realize_boundary_iff_zero {genus : Nat}
    (coordinate : StandardHomology genus) :
    IsBoundary (realize coordinate) <->
      coordinate = CCL.Riemann.CellularHomology.zeroOneChain genus := by
  constructor
  · rintro ⟨oddBoundary, faceBoundary, equal⟩
    have restricted := congrArg restrict equal
    unfold realize at restricted
    rw [restrict_extend, restrict_extend] at restricted
    have oddBoundaryProperty : OddCellularHomology.IsBoundary
        (OddSymplecticHomology.realize coordinate) := by
      rw [OddCellularHomology.isBoundary_iff_isFaceBoundary]
      rw [restricted]
      exact faceBoundary
    exact (OddSymplecticHomology.realize_boundary_iff_zero coordinate).mp
      oddBoundaryProperty
  · intro zero
    have oddBoundary :=
      (OddSymplecticHomology.realize_boundary_iff_zero coordinate).mpr zero
    rw [OddCellularHomology.isBoundary_iff_isFaceBoundary] at oddBoundary
    exact ⟨OddSymplecticHomology.realize coordinate, oddBoundary, rfl⟩

structure Certificate (genus : Nat) : Type where
  a_cycle : forall index : Fin genus, Cycle (aCycle index)
  b_cycle : forall index : Fin genus, Cycle (bCycle index)
  decompose : forall (chain : EdgeChain genus), Cycle chain ->
    exists boundary : OddCellularHomology.EdgeChain genus,
      OddCellularHomology.IsFaceBoundary boundary /\
      chain = (realize (homologyCoordinates chain)).add (extend boundary)
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

end CCL.Riemann.EvenCellularHomology

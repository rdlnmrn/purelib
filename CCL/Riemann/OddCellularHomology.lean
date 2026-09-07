import CCL.Riemann.CellularBoundary
import CCL.Riemann.CellularHomology

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

namespace CCL.Riemann.OddCellularHomology

open CCL.Riemann.HyperellipticCells
open RFAP.ConstructiveFiniteMatrix

abbrev EdgeCount (genus : Nat) := 2 * genus + 2
abbrev TailRank (genus : Nat) := 2 * genus
abbrev EdgeVector (genus : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector Int (EdgeCount genus)

abbrev TailVector (genus : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector Int (TailRank genus)

/-- Integral coefficients on the two lifted copies of every base edge. -/
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

def zero (genus : Nat) : EdgeChain genus where
  sheetZero := vectorOfFn fun _ => 0
  sheetOne := vectorOfFn fun _ => 0

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

@[simp] theorem scale_sheetZero {genus : Nat} (scalar : Int)
    (chain : EdgeChain genus) (index : Fin (EdgeCount genus)) :
    (chain.scale scalar).sheetZero index = scalar * chain.sheetZero index := by
  unfold scale
  rw [vectorOfFn_apply]

@[simp] theorem scale_sheetOne {genus : Nat} (scalar : Int)
    (chain : EdgeChain genus) (index : Fin (EdgeCount genus)) :
    (chain.scale scalar).sheetOne index = scalar * chain.sheetOne index := by
  unfold scale
  rw [vectorOfFn_apply]

end EdgeChain

/-- The cellular vertex-cycle condition for the connected ramified polygon. -/
structure Cycle {genus : Nat} (chain : EdgeChain genus) : Type where
  total_eq : forall index : Fin (EdgeCount genus),
    chain.sheetZero index + chain.sheetOne index =
      chain.sheetZero 0 + chain.sheetOne 0

/-- Edge chain of one explicitly attached face. -/
def faceChain {genus : Nat} (face : Face) : EdgeChain genus where
  sheetZero := vectorOfFn fun index =>
    if oddFaceSheet face index = sheetZero then 1 else 0
  sheetOne := vectorOfFn fun index =>
    if oddFaceSheet face index = sheetOne then 1 else 0

theorem faceChain_total (face : Face) {genus : Nat}
    (index : Fin (EdgeCount genus)) :
    (faceChain face).sheetZero index + (faceChain face).sheetOne index = 1 := by
  unfold faceChain
  rw [vectorOfFn_apply, vectorOfFn_apply]
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
    have different : sheetOne ≠ sheetZero := by
      intro impossible
      have values := congrArg Fin.val impossible
      change (1 : Nat) = 0 at values
      omega0
    rw [if_neg different]
    omega0

def faceCycle {genus : Nat} (face : Face) :
    Cycle (faceChain (genus := genus) face) where
  total_eq := by
    intro index
    rw [faceChain_total, faceChain_total]

def upperZeroFace : Face := ⟨.upper, sheetZero⟩
def upperOneFace : Face := ⟨.upper, sheetOne⟩
def lowerZeroFace : Face := ⟨.lower, sheetZero⟩
def lowerOneFace : Face := ⟨.lower, sheetOne⟩

theorem sheetZero_ne_sheetOne : sheetZero ≠ sheetOne := by
  intro equal
  have valueEqual := congrArg Fin.val equal
  change (0 : Nat) = 1 at valueEqual
  omega0

theorem sheetOne_ne_sheetZero : sheetOne ≠ sheetZero := by
  intro equal
  exact sheetZero_ne_sheetOne equal.symm

/-- The span of three independent attached faces.  The fourth face is their
negative sum after orienting the two hemispheres oppositely. -/
def boundaryCombination (genus : Nat) (evenWeight oddWeight totalWeight : Int) :
    EdgeChain genus where
  sheetZero := vectorOfFn fun index =>
    if index.val % 2 = 0 then evenWeight else oddWeight
  sheetOne := vectorOfFn fun index =>
    if index.val % 2 = 0 then oddWeight + totalWeight
    else evenWeight + totalWeight

/-- The upper zero-sheet attaching word is the displayed combination of the
three independent boundary generators. -/
theorem faceChain_upperZero (genus : Nat) :
    faceChain (genus := genus) upperZeroFace =
      boundaryCombination genus 1 1 (-1) := by
  apply EdgeChain.ext <;> intro index
  · unfold faceChain upperZeroFace oddFaceSheet boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply, if_pos rfl]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
    · rw [if_neg even]
  · unfold faceChain upperZeroFace oddFaceSheet boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply,
      if_neg sheetZero_ne_sheetOne]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
      decide
    · rw [if_neg even]
      decide

/-- The upper one-sheet attaching word is the total boundary generator. -/
theorem faceChain_upperOne (genus : Nat) :
    faceChain (genus := genus) upperOneFace =
      boundaryCombination genus 0 0 1 := by
  apply EdgeChain.ext <;> intro index
  · unfold faceChain upperOneFace oddFaceSheet boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply,
      if_neg sheetOne_ne_sheetZero]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
    · rw [if_neg even]
  · unfold faceChain upperOneFace oddFaceSheet boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply, if_pos rfl]
    by_cases even : index.val % 2 = 0
    · rw [if_pos even]
      ring1
    · rw [if_neg even]
      ring1

private theorem lowerZeroFace_sheet {genus : Nat}
    (index : Fin (EdgeCount genus)) :
    oddFaceSheet lowerZeroFace index = oddLowerSheet index := by
  rfl

private theorem lowerOneFace_sheet {genus : Nat}
    (index : Fin (EdgeCount genus)) :
    oddFaceSheet lowerOneFace index = toggleSheet (oddLowerSheet index) := by
  rfl

/-- The alternating lower zero-sheet word is the even-parity generator. -/
theorem faceChain_lowerZero (genus : Nat) :
    faceChain (genus := genus) lowerZeroFace =
      boundaryCombination genus 1 0 0 := by
  apply EdgeChain.ext <;> intro index
  · unfold faceChain boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [lowerZeroFace_sheet, oddLowerSheet, if_pos even,
        if_pos rfl]
      rw [if_pos even]
    · rw [lowerZeroFace_sheet, oddLowerSheet, if_neg even,
        if_neg sheetOne_ne_sheetZero]
      rw [if_neg even]
  · unfold faceChain boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [lowerZeroFace_sheet, oddLowerSheet, if_pos even,
        if_neg sheetZero_ne_sheetOne]
      rw [if_pos even]
      ring1
    · rw [lowerZeroFace_sheet, oddLowerSheet, if_neg even,
        if_pos rfl]
      rw [if_neg even]
      ring1

/-- The alternating lower one-sheet word is the odd-parity generator. -/
theorem faceChain_lowerOne (genus : Nat) :
    faceChain (genus := genus) lowerOneFace =
      boundaryCombination genus 0 1 0 := by
  apply EdgeChain.ext <;> intro index
  · unfold faceChain boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [lowerOneFace_sheet, oddLowerSheet, if_pos even,
        toggleSheet_zero, if_neg sheetOne_ne_sheetZero]
      rw [if_pos even]
    · rw [lowerOneFace_sheet, oddLowerSheet, if_neg even,
        toggleSheet_one, if_pos rfl]
      rw [if_neg even]
  · unfold faceChain boundaryCombination
    rw [vectorOfFn_apply, vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · rw [lowerOneFace_sheet, oddLowerSheet, if_pos even,
        toggleSheet_zero, if_pos rfl]
      rw [if_pos even]
      ring1
    · rw [lowerOneFace_sheet, oddLowerSheet, if_neg even,
        toggleSheet_one, if_neg sheetZero_ne_sheetOne]
      rw [if_neg even]
      ring1

/-- With the two hemispheres oppositely oriented, the complete boundary of
the four actual attached faces cancels edge by edge.  This is the signed
cellular surface identity behind the finite Stokes pairing. -/
theorem upperFaceChains_eq_lowerFaceChains (genus : Nat) :
    (faceChain (genus := genus) upperZeroFace).add
        (faceChain (genus := genus) upperOneFace) =
      (faceChain (genus := genus) lowerZeroFace).add
        (faceChain (genus := genus) lowerOneFace) := by
  rw [faceChain_upperZero, faceChain_upperOne,
    faceChain_lowerZero, faceChain_lowerOne]
  apply EdgeChain.ext <;> intro index
  · simp only [EdgeChain.add_sheetZero]
    unfold boundaryCombination
    simp only [vectorOfFn_apply]
    by_cases even : index.val % 2 = 0 <;> simp [even]
  · simp only [EdgeChain.add_sheetOne]
    unfold boundaryCombination
    simp only [vectorOfFn_apply]
    by_cases even : index.val % 2 = 0 <;> simp [even]

/-- Every displayed boundary combination is literally an integral linear
combination of three of the four attached face words. -/
theorem boundaryCombination_eq_faceCombination (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    boundaryCombination genus evenWeight oddWeight totalWeight =
      ((faceChain (genus := genus) lowerZeroFace).scale evenWeight).add
        (((faceChain (genus := genus) lowerOneFace).scale oddWeight).add
          ((faceChain (genus := genus) upperOneFace).scale totalWeight)) := by
  rw [faceChain_lowerZero, faceChain_lowerOne, faceChain_upperOne]
  apply EdgeChain.ext <;> intro index
  · rw [EdgeChain.add_sheetZero, EdgeChain.scale_sheetZero,
      EdgeChain.add_sheetZero, EdgeChain.scale_sheetZero,
      EdgeChain.scale_sheetZero]
    unfold boundaryCombination
    repeat' rw [vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · repeat' rw [if_pos even]
      ring1
    · repeat' rw [if_neg even]
      ring1
  · rw [EdgeChain.add_sheetOne, EdgeChain.scale_sheetOne,
      EdgeChain.add_sheetOne, EdgeChain.scale_sheetOne,
      EdgeChain.scale_sheetOne]
    unfold boundaryCombination
    repeat' rw [vectorOfFn_apply]
    by_cases even : index.val % 2 = 0
    · repeat' rw [if_pos even]
      ring1
    · repeat' rw [if_neg even]
      ring1
@[simp] theorem boundaryCombination_sheetZero_zero (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    (boundaryCombination genus evenWeight oddWeight totalWeight).sheetZero 0 =
      evenWeight := by
  unfold boundaryCombination
  rw [vectorOfFn_apply]
  rfl

@[simp] theorem boundaryCombination_sheetZero_one (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    (boundaryCombination genus evenWeight oddWeight totalWeight).sheetZero 1 =
      oddWeight := by
  unfold boundaryCombination
  rw [vectorOfFn_apply]
  rfl

def IsBoundary {genus : Nat} (chain : EdgeChain genus) : Prop :=
  exists evenWeight oddWeight totalWeight : Int,
    chain = boundaryCombination genus evenWeight oddWeight totalWeight

/-- Boundary membership stated directly as the span of concrete attached
face words. -/
def IsFaceBoundary {genus : Nat} (chain : EdgeChain genus) : Prop :=
  exists evenWeight oddWeight totalWeight : Int,
    chain =
      ((faceChain (genus := genus) lowerZeroFace).scale evenWeight).add
        (((faceChain (genus := genus) lowerOneFace).scale oddWeight).add
          ((faceChain (genus := genus) upperOneFace).scale totalWeight))

theorem isBoundary_iff_isFaceBoundary {genus : Nat}
    (chain : EdgeChain genus) :
    IsBoundary chain <-> IsFaceBoundary chain := by
  constructor
  · rintro ⟨evenWeight, oddWeight, totalWeight, equal⟩
    exact ⟨evenWeight, oddWeight, totalWeight,
      equal.trans (boundaryCombination_eq_faceCombination genus _ _ _)⟩
  · rintro ⟨evenWeight, oddWeight, totalWeight, equal⟩
    exact ⟨evenWeight, oddWeight, totalWeight,
      equal.trans (boundaryCombination_eq_faceCombination genus _ _ _).symm⟩

@[simp] theorem boundaryCombination_total (genus : Nat)
    (evenWeight oddWeight totalWeight : Int)
    (index : Fin (EdgeCount genus)) :
    (boundaryCombination genus evenWeight oddWeight totalWeight).sheetZero index +
        (boundaryCombination genus evenWeight oddWeight totalWeight).sheetOne index =
      evenWeight + oddWeight + totalWeight := by
  unfold boundaryCombination
  rw [vectorOfFn_apply, vectorOfFn_apply]
  by_cases even : index.val % 2 = 0
  · rw [if_pos even, if_pos even]
    ring1
  · rw [if_neg even, if_neg even]
    ring1

def boundaryCombination_cycle (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    Cycle (boundaryCombination genus evenWeight oddWeight totalWeight) where
  total_eq := by
    intro index
    rw [boundaryCombination_total, boundaryCombination_total]

/-- The first two edge positions are parity references; the remaining `2g`
positions are the free homology coordinates. -/
def coordinates {genus : Nat} (chain : EdgeChain genus) : TailVector genus :=
  vectorOfFn fun index =>
    chain.sheetZero index.succ.succ -
      if index.val % 2 = 0 then chain.sheetZero 0 else chain.sheetZero 1

/-- Canonical total-zero cycle with zero reference coefficients. -/
def representative {genus : Nat} (coordinate : TailVector genus) :
    EdgeChain genus :=
  let zeroCoefficients : EdgeVector genus :=
    vectorOfFn fun position =>
      Fin.cases 0
        (fun afterZero => Fin.cases 0 (fun index => coordinate index) afterZero)
        position
  { sheetZero := zeroCoefficients
    sheetOne := vectorOfFn fun position => -zeroCoefficients position }

@[simp] theorem representative_sheetZero_zero {genus : Nat}
    (coordinate : TailVector genus) :
    (representative coordinate).sheetZero 0 = 0 := by
  unfold representative
  rw [vectorOfFn_apply]
  rfl

@[simp] theorem representative_sheetZero_one {genus : Nat}
    (coordinate : TailVector genus) :
    (representative coordinate).sheetZero 1 = 0 := by
  unfold representative
  rw [vectorOfFn_apply]
  rfl

@[simp] theorem representative_sheetZero_tail {genus : Nat}
    (coordinate : TailVector genus) (index : Fin (TailRank genus)) :
    (representative coordinate).sheetZero index.succ.succ = coordinate index := by
  unfold representative
  rw [vectorOfFn_apply]
  rfl

@[simp] theorem representative_sheetOne {genus : Nat}
    (coordinate : TailVector genus) (index : Fin (EdgeCount genus)) :
    (representative coordinate).sheetOne index =
      -(representative coordinate).sheetZero index := by
  unfold representative
  rw [vectorOfFn_apply]

def representative_cycle {genus : Nat} (coordinate : TailVector genus) :
    Cycle (representative coordinate) where
  total_eq := by
    intro index
    rw [representative_sheetOne, representative_sheetOne]
    ring1

theorem coordinates_representative {genus : Nat}
    (coordinate : TailVector genus) :
    coordinates (representative coordinate) = coordinate := by
  apply vector_ext
  intro index
  unfold coordinates
  rw [vectorOfFn_apply, representative_sheetZero_tail]
  by_cases even : index.val % 2 = 0
  · rw [if_pos even, representative_sheetZero_zero]
    ring1
  · rw [if_neg even, representative_sheetZero_one]
    ring1

theorem coordinates_boundaryCombination (genus : Nat)
    (evenWeight oddWeight totalWeight : Int) :
    coordinates (boundaryCombination genus evenWeight oddWeight totalWeight) =
      vectorOfFn fun _ : Fin (TailRank genus) => 0 := by
  apply vector_ext
  intro index
  unfold coordinates
  rw [vectorOfFn_apply]
  rw [boundaryCombination_sheetZero_zero,
    boundaryCombination_sheetZero_one]
  unfold boundaryCombination
  rw [vectorOfFn_apply, vectorOfFn_apply]
  have parity : (index.val + 2) % 2 = index.val % 2 := by omega0
  change (if (index.val + 2) % 2 = 0 then evenWeight else oddWeight) -
      (if index.val % 2 = 0 then evenWeight else oddWeight) = 0
  rw [parity]
  ring1

/-- Every cellular cycle is its canonical free representative plus an
explicit combination of the three independent face boundaries. -/
theorem cycle_decomposition {genus : Nat} (chain : EdgeChain genus)
    (cycle : Cycle chain) :
    let coordinate := coordinates chain
    let evenWeight := chain.sheetZero 0
    let oddWeight := chain.sheetZero 1
    let totalWeight := chain.sheetZero 0 + chain.sheetOne 0 -
      evenWeight - oddWeight
    chain = (representative coordinate).add
      (boundaryCombination genus evenWeight oddWeight totalWeight) := by
  dsimp only
  apply EdgeChain.ext
  · intro position
    refine Fin.cases ?_ (fun afterZero =>
      Fin.cases ?_ (fun index => ?_) afterZero) position
    · rw [EdgeChain.add_sheetZero, representative_sheetZero_zero,
        boundaryCombination_sheetZero_zero]
      ring1
    · rw [Fin.succ_zero_eq_one, EdgeChain.add_sheetZero,
        representative_sheetZero_one,
        boundaryCombination_sheetZero_one]
      ring1
    · rw [EdgeChain.add_sheetZero, representative_sheetZero_tail]
      unfold coordinates boundaryCombination
      rw [vectorOfFn_apply, vectorOfFn_apply]
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
    rw [EdgeChain.add_sheetOne, representative_sheetOne]
    have totalAt := cycle.total_eq position
    have boundaryTotal := boundaryCombination_total genus
      (chain.sheetZero 0) (chain.sheetZero 1)
      (chain.sheetZero 0 + chain.sheetOne 0 -
        chain.sheetZero 0 - chain.sheetZero 1) position
    have zeroCoordinateEqual :
        chain.sheetZero position =
          (representative (coordinates chain)).sheetZero position +
            (boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position := by
      refine Fin.cases ?_ (fun afterZero =>
        Fin.cases ?_ (fun index => ?_) afterZero) position
      · rw [representative_sheetZero_zero,
          boundaryCombination_sheetZero_zero]
        ring1
      · rw [Fin.succ_zero_eq_one, representative_sheetZero_one,
          boundaryCombination_sheetZero_one]
        ring1
      · rw [representative_sheetZero_tail]
        unfold coordinates boundaryCombination
        rw [vectorOfFn_apply, vectorOfFn_apply]
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
        (boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
            (chain.sheetZero 0 + chain.sheetOne 0 -
              chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position +
          (boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
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
      _ = ((boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position +
            (boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetOne position) -
          ((representative (coordinates chain)).sheetZero position +
            (boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
              (chain.sheetZero 0 + chain.sheetOne 0 -
                chain.sheetZero 0 - chain.sheetZero 1)).sheetZero position) := by
              rw [boundaryTotalSimplified, zeroCoordinateEqual]
      _ = -(representative (coordinates chain)).sheetZero position +
          (boundaryCombination genus (chain.sheetZero 0) (chain.sheetZero 1)
            (chain.sheetZero 0 + chain.sheetOne 0 -
              chain.sheetZero 0 - chain.sheetZero 1)).sheetOne position := by
              ring1

/-- A canonical representative is a face boundary only when every free
coordinate vanishes. -/
theorem representative_boundary_iff_coordinates_zero {genus : Nat}
    (coordinate : TailVector genus) :
    IsBoundary (representative coordinate) <->
      coordinate = vectorOfFn (fun _ : Fin (TailRank genus) => 0) := by
  constructor
  · intro boundary
    rcases boundary with ⟨evenWeight, oddWeight, totalWeight, equal⟩
    have coordinateEqual := congrArg coordinates equal
    rw [coordinates_representative,
      coordinates_boundaryCombination] at coordinateEqual
    exact coordinateEqual
  · intro coordinateZero
    subst coordinate
    have zeroSheet : forall index : Fin (EdgeCount genus),
        (representative (vectorOfFn
          (fun _ : Fin (TailRank genus) => 0))).sheetZero index = 0 := by
      intro index
      refine Fin.cases ?_ (fun afterZero =>
        Fin.cases ?_ (fun tail => ?_) afterZero) index
      · rw [representative_sheetZero_zero]
      · rw [Fin.succ_zero_eq_one, representative_sheetZero_one]
      · rw [representative_sheetZero_tail, vectorOfFn_apply]
    exact ⟨0, 0, 0, by
      apply EdgeChain.ext
      · intro index
        rw [zeroSheet]
        unfold boundaryCombination
        rw [vectorOfFn_apply]
        split <;> rfl
      · intro index
        rw [representative_sheetOne, zeroSheet]
        unfold boundaryCombination
        rw [vectorOfFn_apply]
        split <;> rfl⟩

end CCL.Riemann.OddCellularHomology

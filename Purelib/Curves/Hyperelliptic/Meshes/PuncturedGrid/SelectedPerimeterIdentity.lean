module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces

public section

/-! Exact selected-face boundary accounting. Matching regular sides split
into pairs wholly inside the selection and oriented sides crossing its
boundary. Original hole and exterior sides remain explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

attribute [local congr] FiniteSum.Fin.sumFin_congr

namespace SelectedSides

/-- Retain a selected side area and return zero for an unselected side. -/
@[expose] def value (keep : Bool) (area : Gaussian.Basic.Canonical) : Gaussian := if keep then area else 0

/-- Boolean side selection distributes over subtraction. -/
theorem value_sub (keep : Bool) (first last : Gaussian.Basic.Canonical) :
  SelectedSides.value keep (first - last) =
  SelectedSides.value keep first -
  SelectedSides.value keep last := by
  cases keep with
  | false => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | true => rfl

/-- Boolean side selection distributes over the finite indexed area sum. -/
theorem value_sum {count : Nat} (keep : Bool) (values : Fin count → Gaussian.Basic.Canonical) :
    SelectedSides.value keep (FiniteSum.Fin.sumFin values)
      = FiniteSum.Fin.sumFin (fun index =>
      SelectedSides.value keep (values index)) := by
  cases keep with
  | false => exact FiniteSum.Fin.sumFin_zero.symm
  | true => rfl

/-- Selecting a zero side value returns zero. -/
theorem value_zero (keep : Bool) : SelectedSides.value keep
  0 = 0 := by cases keep <;> rfl

/-- The signed outgoing or incoming contribution across a selected-to-unselected face interface. -/
@[expose] def transition (first last : Bool) (outgoing incoming : Gaussian.Basic.Canonical) : Gaussian :=
  SelectedSides.value (first && !last) outgoing -
    SelectedSides.value (!first && last) incoming

/-- A selected side difference splits into the both-selected pair difference and the oriented selection transition. -/
theorem split (first last : Bool) (outgoing incoming : Gaussian.Basic.Canonical) :
    SelectedSides.value first outgoing -
      SelectedSides.value last incoming =
      SelectedSides.value (first && last) (outgoing -
        incoming) + SelectedSides.transition first last
        outgoing incoming := by
  cases first <;> cases last <;> simp only [-eq_self, -iff_self,
    SelectedSides.value,
    SelectedSides.transition, Bool.and, Bool.not, if_neg
    (show (false : Bool) ≠ true by decide), if_pos (Eq.refl true)] <;> ring1

end SelectedSides

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {request : TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    target}
  {i j : Fin genus} {stage : Nat} {cache : RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}

namespace FacePerimeters
open SelectedSides (value transition)

/-- The oriented sum of retained hole and outer-frame sides on the selected original faces. -/
@[expose] def selectedPhysical (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (keep : Fin faces.regulars.length → Bool)
      : Gaussian :=
  FiniteSum.Fin.sumFin (fun p =>
    SideNeighbor.physicalValue
    (neighbors.entries.get p).right (value (keep p)
    (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right p))) -
  FiniteSum.Fin.sumFin (fun p =>
    SideNeighbor.physicalValue
    (neighbors.entries.get p).left (value (keep p)
    (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .left p))) -
  (FiniteSum.Fin.sumFin (fun p =>
    SideNeighbor.physicalValue
    (neighbors.entries.get p).top (value (keep p)
    (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top p))) -
    FiniteSum.Fin.sumFin (fun p =>
      SideNeighbor.physicalValue
      (neighbors.entries.get p).bottom (value (keep p)
      (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom p))))

/-- Sum the retained matching-side contributions crossing the face selection boundary in the specified direction. -/
@[expose] def selectedTransition (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (keep : Fin faces.regulars.length → Bool) (side : Meshes.GridLiftedDualSteps.GridSide) : Gaussian :=
  FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
    if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box then
      transition (keep first) (keep last)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side first)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side.opposite
        last) else 0))

/-- Selected physical sides and oriented interfaces to unselected regular faces. -/
@[expose] def selectedBoundary (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (keep : Fin faces.regulars.length → Bool)
      : Gaussian :=
  FacePerimeters.selectedPhysical perimeters neighbors keep
    + FacePerimeters.selectedTransition perimeters keep
    .right - FacePerimeters.selectedTransition perimeters
    keep .top

/-- Sum the original matched-side differences whose two endpoint faces are selected. -/
private def selectedPair (perimeters : Matched.FacePerimeters (request
  := request) cache i j)
    (keep : Fin faces.regulars.length → Bool) (side : Meshes.GridLiftedDualSteps.GridSide) : Gaussian :=
  FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
    if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box then
      value (keep first && keep last) (GlobalPerimeterIdentity.FacePerimeters.sideSum
        perimeters side first - GlobalPerimeterIdentity.FacePerimeters.sideSum
        perimeters side.opposite last) else 0))

/-- The selected matching-side sum splits into internal selected pairs and oriented selection transitions. -/
private theorem selected_pair_split (perimeters :
  Matched.FacePerimeters (request := request) cache i j)
    (keep : Fin faces.regulars.length → Bool) (side : Meshes.GridLiftedDualSteps.GridSide) :
    FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun last =>
      if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box then
        value (keep first) (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
          side first) - value (keep last)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side.opposite
          last) else 0)) =
      FacePerimeters.selectedPair perimeters keep side +
        FacePerimeters.selectedTransition perimeters keep
        side := by
  have pointwise (first last : Fin faces.regulars.length) :
      (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box
        then
        value (keep first) (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
          side first) - value (keep last)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side.opposite
          last) else 0) =
      (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box
        then
        value (keep first && keep last)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side first -
          GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side.opposite
          last) else 0) +
      (if side.Matches (faces.regulars[first.val]'first.isLt).cell.box (faces.regulars[last.val]'last.isLt).cell.box
        then
        transition (keep first) (keep last)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side first)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side.opposite
          last) else 0) := by
    split
    · exact SelectedSides.split ..
    · exact (zero_add _).symm
  rw [FiniteSum.Fin.sumFin_congr (fun first => FiniteSum.Fin.sumFin_congr (pointwise first))]
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_add,
    FacePerimeters.selectedPair,
    FacePerimeters.selectedTransition]
  rfl

/-- The selected original perimeter sum equals the oriented right, left, top and bottom side sums. -/
private theorem selected_side_sum (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (keep : Fin faces.regulars.length → Bool) :
    perimeters.selectedPerimeterSum keep =
      FiniteSum.Fin.sumFin (fun p => value (keep p)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right p)) -
      FiniteSum.Fin.sumFin (fun p => value (keep p)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .left p)) -
      (FiniteSum.Fin.sumFin (fun p => value (keep p)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top p)) -
        FiniteSum.Fin.sumFin (fun p => value (keep p)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom p))) :=
          by
  have pointwise (p : Fin faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun sheet => if keep p then
        let sides := (perimeters.perimeters.get p).get sheet
        sides.bottom + sides.right - sides.top - sides.left else 0) =
      value (keep p) (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
        .right p) - value (keep p) (GlobalPerimeterIdentity.FacePerimeters.sideSum
        perimeters .left p) -
        (value (keep p) (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters
          .top p) - value (keep p) (GlobalPerimeterIdentity.FacePerimeters.sideSum
          perimeters .bottom p)) := by
    cases keep p <;> simp only [-eq_self, -iff_self, value, if_neg (show (false : Bool) ≠ true by decide), if_pos
      (Eq.refl true), FiniteSum.Fin.sumFin_zero,
      GlobalPerimeterIdentity.FacePerimeters.sideSum, FiniteSum.Fin.sumFin_add,
      FiniteSum.Fin.sumFin_sub] <;> ring1
  unfold Matched.FacePerimeters.selectedPerimeterSum
  rw [FiniteSum.Fin.sumFin_congr pointwise]
  simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_sub]
  rfl

/-- The selected original perimeter sum decomposes into its internal pair sums and complete selected boundary. -/
private theorem selected_split (perimeters : Matched.FacePerimeters
  (request := request) cache i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (keep : Fin faces.regulars.length → Bool)
      :
    perimeters.selectedPerimeterSum keep =
      FacePerimeters.selectedPair perimeters keep .right -
        FacePerimeters.selectedPair perimeters keep .top +
        FacePerimeters.selectedBoundary perimeters
        neighbors keep := by
  have split (side : Meshes.GridLiftedDualSteps.GridSide) : FiniteSum.Fin.sumFin (fun p => value (keep p)
    (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p)) =
      FiniteSum.Fin.sumFin (fun p =>
        SideNeighbor.regularValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) (value (keep p)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p))) +
      FiniteSum.Fin.sumFin (fun p =>
        SideNeighbor.physicalValue
        (FaceNeighbors.at
        (neighbors.entries.get p) side) (value (keep p)
        (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p))) := by
    rw [FiniteSum.Fin.sumFin_congr (fun p =>
      SideNeighbor.value_split
      (FaceNeighbors.at
      (neighbors.entries.get p) side) (value (keep p)
      (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p))),
      FiniteSum.Fin.sumFin_add]
  have pairs (side : Meshes.GridLiftedDualSteps.GridSide) :=
    (FacePerimeters.selected_pair_split perimeters keep
    side).symm.trans
    (NeighborBank.pair_sum
      neighbors side (fun p => value (keep p)
      (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters side p))
      (fun p => value (keep p) (GlobalPerimeterIdentity.FacePerimeters.sideSum
        perimeters side.opposite p)))
  have vertical := pairs .right
  have horizontal := pairs .top
  rw [FacePerimeters.selected_side_sum perimeters keep,
    split .right, split .left, split .top, split .bottom]
  dsimp only [-eq_self, -iff_self,
    FaceNeighbors.at,
    Meshes.GridLiftedDualSteps.GridSide.opposite] at vertical horizontal ⊢
  dsimp only [-eq_self, -iff_self,
    FacePerimeters.selectedBoundary,
    FacePerimeters.selectedPhysical]
  have combine {a b c d r l t bot v x vt xt : Gaussian.Basic.Canonical}
      (vEq : v + vt = a - b) (xEq : x + xt = c - d) :
      (a + r) - (b + l) - ((c + t) - (d + bot)) =
        v - x + ((r - l - (t - bot)) + vt - xt) := by
    calc
      _ = (a - b) - (c - d) + (r - l - (t - bot)) := by ring1
      _ = _ := by rw [← vEq, ← xEq]; ring1
  exact combine vertical horizontal

end FacePerimeters

namespace CrossingRequests

/-- The retained crossing-bank perimeter difference restricted to crossings whose two original endpoint faces are
selected. -/
@[expose] def selectedPairedPerimeter (retained : Matched.CrossingBank
  request mesh) (perimeters : Matched.FacePerimeters (request :=
  request) cache i j)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    SelectedSides.value (keep a && keep c)
    (Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
      (((retained.vertical.get a).get b).get c))))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    SelectedSides.value (keep a && keep c)
    (Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
      (((retained.horizontal.get a).get b).get c)))))

end CrossingRequests

/-- Pair only interfaces with both endpoint faces selected. The same sheet
permutation as the original crossing bank is retained. -/
theorem CrossingBank.selected_exterior_eq (retained :
  Matched.CrossingBank request mesh)
    (perimeters : Matched.FacePerimeters (request := request) cache i
      j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (keep : Fin faces.regulars.length → Bool)
      :
    perimeters.selectedPerimeterSum keep =
      CrossingRequests.selectedPairedPerimeter retained
      perimeters keep +
      FacePerimeters.selectedBoundary perimeters neighbors
        keep := by
  have horizontal (a : Fin faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
        SelectedSides.value (keep a && keep c)
        (Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
          (((retained.horizontal.get a).get b).get c)))) =
      FiniteSum.Fin.sumFin (fun c => if Meshes.GridLiftedDualSteps.GridSide.Matches .top
        (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a && keep c)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .top a -
          GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .bottom c) else
          0) := by
    rw [FiniteSum.Fin.sumFin_swap]
    apply FiniteSum.Fin.sumFin_congr
    intro c
    rw [← SelectedSides.value_sum,
      CrossingPairSums.CrossingBank.horizontal_pair_sum retained perimeters a c]
    split
    · rfl
    · exact SelectedSides.value_zero _
  have vertical (a : Fin faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
        SelectedSides.value (keep a && keep c)
        (Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
          (((retained.vertical.get a).get b).get c)))) =
      FiniteSum.Fin.sumFin (fun c => if Meshes.GridLiftedDualSteps.GridSide.Matches .right
        (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a && keep c)
          (GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .right a -
          GlobalPerimeterIdentity.FacePerimeters.sideSum perimeters .left c) else 0)
          := by
    rw [FiniteSum.Fin.sumFin_swap]
    apply FiniteSum.Fin.sumFin_congr
    intro c
    rw [← SelectedSides.value_sum,
      CrossingPairSums.CrossingBank.vertical_pair_sum retained perimeters a c]
    split
    · rfl
    · exact SelectedSides.value_zero _
  rw [FacePerimeters.selected_split perimeters neighbors
    keep]
  unfold CrossingRequests.selectedPairedPerimeter
  rw [FiniteSum.Fin.sumFin_congr vertical, FiniteSum.Fin.sumFin_congr horizontal]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

end

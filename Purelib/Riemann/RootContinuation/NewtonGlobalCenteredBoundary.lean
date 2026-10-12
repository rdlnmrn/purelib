module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Tactic.Ring

public section

/-! Separate the centered discrepancies controlled by contact requests from
the retained endpoint terms of the global period comparison. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterSamples (sideSum paired
  exterior physical)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Purelib.Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

section
open Purelib.Algebra
/-- Sum the retained centered area of one actual face side over both sheets. -/
@[expose] def centeredSideSum (side : GridSide) (position : Fin grid.faces.regulars.length) : Gaussian :=
  FiniteSum.Fin.sumFin fun sheet : Fin 2 => match side with
    | .bottom => ((samples.get sheet).get position).bottom.centeredArea
    | .right => ((samples.get sheet).get position).right.centeredArea
    | .top => ((samples.get sheet).get position).top.centeredArea
    | .left => ((samples.get sheet).get position).left.centeredArea

/-- Sum the retained endpoint term of one actual face side over both sheets. -/
@[expose] def endpointSideSum (side : GridSide) (position : Fin grid.faces.regulars.length) : Gaussian :=
  FiniteSum.Fin.sumFin fun sheet : Fin 2 => match side with
    | .bottom => ((samples.get sheet).get position).bottom.endpoint
    | .right => ((samples.get sheet).get position).right.endpoint
    | .top => ((samples.get sheet).get position).top.endpoint
    | .left => ((samples.get sheet).get position).left.endpoint

/-- The actual two-sheet side reading splits into centered area and endpoint terms. -/
theorem side_decomposition (side : GridSide) (position : Fin grid.faces.regulars.length) :
    samples.sideSum side position = centeredSideSum samples side position + endpointSideSum samples side position := by
  unfold sideSum centeredSideSum endpointSideSum
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  cases side
  · exact ((samples.get sheet).get position).bottom.decomposition
  · exact ((samples.get sheet).get position).right.decomposition
  · exact ((samples.get sheet).get position).top.decomposition
  · exact ((samples.get sheet).get position).left.decomposition

end

section
open Purelib.Algebra
open Purelib.Data
/-- Sum the signed outgoing-minus-incoming readings over actual matching ordered face pairs. -/
private def pairSum (side : GridSide) (outgoing incoming : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical) :
  Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun last =>
    if side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box then outgoing first - incoming last else 0

/-- Sum the signed outgoing-minus-incoming readings over actual matching ordered face pairs. -/
@[expose] def pairSum_for_boundary (side : GridSide) (outgoing incoming : Fin grid.faces.regulars.length →
  Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun last =>
    if side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box then outgoing first - incoming last else 0

/-- Pointwise centered and endpoint decompositions split the complete matching-pair sum. -/
private theorem pairSum_split (side : GridSide)
    (first last firstCentered lastCentered firstEndpoint lastEndpoint : Fin grid.faces.regulars.length →
      Gaussian.Basic.Canonical)
    (firstEq : ∀ position, first position = firstCentered position + firstEndpoint position)
    (lastEq : ∀ position, last position = lastCentered position + lastEndpoint position) :
    pairSum side first last = pairSum side firstCentered lastCentered + pairSum side firstEndpoint lastEndpoint := by
  unfold pairSum
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro a
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro b
  by_cases matching : side.Matches (grid.faces.regulars[a.val]'a.isLt).cell.box
    (grid.faces.regulars[b.val]'b.isLt).cell.box
  · rw [if_pos matching, if_pos matching, if_pos matching, firstEq a, lastEq b]
    ring1
  · rw [if_neg matching, if_neg matching, if_neg matching, add_zero]

/-- Pointwise centered and endpoint decompositions split the complete matching-pair sum. -/
theorem pairSum_split_for_boundary (side : GridSide)
    (first last firstCentered lastCentered firstEndpoint lastEndpoint : Fin grid.faces.regulars.length →
      Gaussian.Basic.Canonical)
    (firstEq : ∀ position, first position = firstCentered position + firstEndpoint position)
    (lastEq : ∀ position, last position = lastCentered position + lastEndpoint position) :
    pairSum_for_boundary side first last = pairSum_for_boundary side firstCentered lastCentered + pairSum_for_boundary
      side firstEndpoint lastEndpoint := by
  unfold pairSum_for_boundary
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro a
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro b
  by_cases matching : side.Matches (grid.faces.regulars[a.val]'a.isLt).cell.box
    (grid.faces.regulars[b.val]'b.isLt).cell.box
  · rw [if_pos matching, if_pos matching, if_pos matching, firstEq a, lastEq b]
    ring1
  · rw [if_neg matching, if_neg matching, if_neg matching, add_zero]

end

/-- The oriented difference of vertical and horizontal centered matching-pair sums. -/
@[expose] def pairedCentered : Gaussian :=
  pairSum_for_boundary .right (centeredSideSum samples .right) (centeredSideSum samples .left) -
    pairSum_for_boundary .top (centeredSideSum samples .top) (centeredSideSum samples .bottom)

/-- The oriented difference of vertical and horizontal endpoint matching-pair sums. -/
@[expose] def pairedEndpoints : Gaussian :=
  pairSum_for_boundary .right (endpointSideSum samples .right) (endpointSideSum samples .left) -
    pairSum_for_boundary .top (endpointSideSum samples .top) (endpointSideSum samples .bottom)

/-- The actual paired boundary reading splits into centered and endpoint contributions. -/
theorem paired_decomposition : samples.paired = pairedCentered samples + pairedEndpoints samples := by
  change pairSum_for_boundary .right (samples.sideSum .right) (samples.sideSum .left) -
    pairSum_for_boundary .top (samples.sideSum .top) (samples.sideSum .bottom) = _
  rw [pairSum_split_for_boundary .right _ _ _ _ _ _ (side_decomposition samples .right) (side_decomposition samples
    .left),
    pairSum_split_for_boundary .top _ _ _ _ _ _ (side_decomposition samples .top) (side_decomposition samples .bottom)]
  unfold pairedCentered pairedEndpoints
  ring1

section
open Purelib.Data
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Gaussian.Norm.Sum
/-- Bound a complete matching-pair sum by the fourth power of the regular face count.

Each actual matching difference has squared norm at most the same nonnegative allowance; unmatched pairs contribute
zero. -/
private theorem pairSum_bound (side : GridSide)
    (outgoing incoming : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical) {allowance : Rat.Fraction.Rational}
    (nonnegative : 0 ≤ allowance)
    (bounded : ∀ first last, side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (outgoing first - incoming last) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (pairSum side outgoing incoming) ≤
      (grid.faces.regulars.length : Rat.Fraction.Rational)^4 * allowance := by
  have pointwise (first last : Fin grid.faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq
        (if side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
          (grid.faces.regulars[last.val]'last.isLt).cell.box then outgoing first - incoming last else 0) ≤ allowance :=
            by
    by_cases matching : side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box
    · rw [if_pos matching]
      exact bounded first last matching
    · rw [if_neg matching]
      exact nonnegative
  have rows (first : Fin grid.faces.regulars.length) :=
    Indexed.normSq_sumFin_le _ allowance (pointwise first)
  have total := Indexed.normSq_sumFin_le _
    ((grid.faces.regulars.length : Rat.Fraction.Rational)^2 * allowance) rows
  exact total.trans_eq (by ring1)

/-- Bound a complete matching-pair sum by the fourth power of the regular face count.

Each actual matching difference has squared norm at most the same nonnegative allowance; unmatched pairs contribute
zero. -/
theorem pairSum_bound_for_boundary (side : GridSide)
    (outgoing incoming : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical) {allowance : Rat.Fraction.Rational}
    (nonnegative : 0 ≤ allowance)
    (bounded : ∀ first last, side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq (outgoing first - incoming last) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (pairSum_for_boundary side outgoing incoming) ≤
      (grid.faces.regulars.length : Rat.Fraction.Rational)^4 * allowance := by
  have pointwise (first last : Fin grid.faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq
        (if side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
          (grid.faces.regulars[last.val]'last.isLt).cell.box then outgoing first - incoming last else 0) ≤ allowance :=
            by
    by_cases matching : side.Matches (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box
    · rw [if_pos matching]
      exact bounded first last matching
    · rw [if_neg matching]
      exact nonnegative
  have rows (first : Fin grid.faces.regulars.length) :=
    Indexed.normSq_sumFin_le _ allowance (pointwise first)
  have total := Indexed.normSq_sumFin_le _
    ((grid.faces.regulars.length : Rat.Fraction.Rational)^2 * allowance) rows
  exact total.trans_eq (by ring1)

end

open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
/-- Bound the paired boundary error after retaining its exact endpoint contribution.

Horizontal and vertical contact estimates with one nonnegative allowance give four times the fourth power of the regular
face count. -/
theorem paired_error_bound {allowance : Rat.Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq
        (centeredSideSum samples .top first - centeredSideSum samples .bottom last) ≤ allowance)
    (vertical : ∀ first last, GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      Data.Gaussian.Norm.Basic.normSq
        (centeredSideSum samples .right first - centeredSideSum samples .left last) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (samples.paired - pairedEndpoints samples) ≤
      4 * (grid.faces.regulars.length : Rat.Fraction.Rational)^4 * allowance := by
  have equal : samples.paired - pairedEndpoints samples = pairedCentered samples := by
    rw [paired_decomposition samples]
    ring1
  rw [equal]
  unfold pairedCentered
  have right := pairSum_bound_for_boundary .right _ _ nonnegative vertical
  have top := pairSum_bound_for_boundary .top _ _ nonnegative horizontal
  exact (Bounds.normSq_sub_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct right top) (by decide : (0 : Rat.Fraction.Rational) ≤ 2)).trans_eq (by ring1))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces in
open Purelib.Data in
/-- The retained physical-neighbor readback preserves addition of side contributions. -/
private theorem physicalValue_add {face : RegularFace grid.shrunk.prepared.toBranchCellBank} {side : GridSide}
    (neighbor : PuncturedFaces.SideNeighbor grid.faces face side) (first last : Gaussian.Basic.Canonical) :
    SideNeighbor.physicalValue neighbor (first + last) = SideNeighbor.physicalValue neighbor first +
      SideNeighbor.physicalValue neighbor last := by
  cases neighbor with
  | neighbor cell member matching location =>
      cases location <;> simp only [-eq_self, -iff_self, SideNeighbor.physicalValue, add_zero] <;> rfl
  | exterior equal => rfl

section
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces
/-- The oriented physical boundary sum of the actual centered side readings.

The original neighbor bank selects the physical contributions, preserving each face, side and sheet. -/
@[expose] def physicalCentered (neighbors : PuncturedFaces.NeighborBank grid.faces) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).right) (centeredSideSum samples
    .right p)) -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).left) (centeredSideSum samples
      .left p)) -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).top) (centeredSideSum samples
      .top p)) -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).bottom) (centeredSideSum
        samples .bottom p)))

/-- The oriented physical boundary sum of the actual retained endpoint terms.

The original neighbor bank selects the same physical occurrences used by the complete perimeter reading. -/
@[expose] def physicalEndpoints (neighbors : PuncturedFaces.NeighborBank grid.faces) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).right) (endpointSideSum samples
    .right p)) -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).left) (endpointSideSum samples
      .left p)) -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).top) (endpointSideSum samples
      .top p)) -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue ((neighbors.entries.get p).bottom) (endpointSideSum
        samples .bottom p)))

/-- The actual physical perimeter reading splits into its centered and endpoint sums. -/
theorem physical_decomposition (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    samples.physical neighbors = physicalCentered samples neighbors + physicalEndpoints samples neighbors := by
  have split (side : GridSide) :
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (FaceNeighbors.at (neighbors.entries.get p) side)
        (samples.sideSum side p)) =
        FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (FaceNeighbors.at (neighbors.entries.get p) side)
          (centeredSideSum samples side p)) +
          FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (FaceNeighbors.at (neighbors.entries.get p) side)
            (endpointSideSum samples side p)) := by
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro p
    rw [side_decomposition samples side p, physicalValue_add]
  have bottom := split .bottom
  have right := split .right
  have top := split .top
  have left := split .left
  dsimp only [FaceNeighbors.at] at bottom right top left
  unfold physical physicalCentered physicalEndpoints
  rw [bottom, right, top, left]
  ring1

end

/-- Split the complete exterior reading into centered and endpoint contributions.

Both parts retain the actual paired contacts and physical-neighbor occurrences of the original perimeter samples. -/
theorem exterior_decomposition (neighbors : PuncturedFaces.NeighborBank grid.faces) :
    samples.exterior = (pairedCentered samples + physicalCentered samples neighbors) +
      (pairedEndpoints samples + physicalEndpoints samples neighbors) := by
  rw [samples.exterior_eq_paired_add_physical neighbors, paired_decomposition samples, physical_decomposition samples
    neighbors]
  ring1

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary

module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterBounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.Ring

public section

/-! The existing crossing requests pay selected internal interfaces.
The endpoint jumps retain their actual samples; physical and selection
boundary sides are separated by the exact selected-perimeter identity. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction.Compatibility

attribute [local congr] FiniteSum.Fin.sumFin_congr

/-- Boolean selection preserves the same nonnegative Gaussian magnitude bound. -/
private theorem SelectedCrossingBounds.selected_bound (keep : Bool) {value : Gaussian.Basic.Canonical} {bound :
  Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
      Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value keep value) ≤ bound := by
  cases keep with
  | false =>
      change Data.Gaussian.Norm.Basic.normSq 0 ≤ bound
      rewrite [Gaussian.Norm.Basic.normSq_zero]
      exact nonnegative
  | true => exact bounded

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    target}
  {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {retained : Matched.CrossingBank request mesh}
  {allocated : Matched.CrossingRequests
    (Periods.PeriodMatrix.standardDifferential i) (Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained} {cache :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

namespace Matched

/-- Read only the interfaces with both adjacent faces selected, on the
original matched sheet continuations and shared numerical cache. -/
@[expose] def
  CrossingSamples.CrossingRequests.Samples.selectedJump
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples allocated cache)
      (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value (keep a && keep c)
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump (prepared :=
      (((allocated.vertical.get a).get b).get c)) (cache := cache)
      (((samples.vertical.get a).get b).get c))))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value (keep a && keep c)
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump (prepared :=
      (((allocated.horizontal.get a).get b).get c)) (cache := cache)
      (((samples.horizontal.get a).get b).get c)))))

/-- The retained normalized samples bound the selected vertical-minus-horizontal jump by the original fourth-power
face-count allowance. -/
theorem
  CrossingSamples.CrossingRequests.Samples.selected_jump_bound
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples allocated
      cache.normalize)
    (perimeters : FacePerimeters (request := request)
      cache.normalize i j) (keep : Fin faces.regulars.length → Bool)
    (positive : 0 < tolerance) (later : allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.CrossingRequests.selectedPairedPerimeter retained
      perimeters keep - samples.selectedJump keep) ≤
      64 * (faces.regulars.length : Fraction.Rational)^4 * tolerance := by
  let horizontal := fun a b c => Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value (keep
    a && keep c)
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.areaDifference (prepared :=
      (((allocated.horizontal.get a).get b).get c))
      (cache := cache.normalize) (((samples.horizontal.get a).get b).get c) -
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump (prepared :=
      (((allocated.horizontal.get a).get b).get c))
      (cache := cache.normalize) (((samples.horizontal.get a).get b).get c))
  let vertical := fun a b c => Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value (keep a
    && keep c)
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.areaDifference (prepared :=
      (((allocated.vertical.get a).get b).get c))
      (cache := cache.normalize) (((samples.vertical.get a).get b).get c) -
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump (prepared :=
      (((allocated.vertical.get a).get b).get c))
      (cache := cache.normalize) (((samples.vertical.get a).get b).get c))
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) positive.le
  have horizontalBound := Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.triple_bound horizontal (4 *
    tolerance) (fun a b c =>
    Hyperelliptic.Meshes.PuncturedGrid.SelectedCrossingBounds.selected_bound (keep a && keep c) nonnegative
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.normalized_jump_bound
        (((samples.horizontal.get a).get b).get c) positive
        ((allocated.horizontal_le a b c).trans later)))
  have verticalBound := Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.triple_bound vertical (4 * tolerance)
    (fun a b c =>
    Hyperelliptic.Meshes.PuncturedGrid.SelectedCrossingBounds.selected_bound (keep a && keep c) nonnegative
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.normalized_jump_bound
        (((samples.vertical.get a).get b).get c) positive
        ((allocated.vertical_le a b c).trans later)))
  have equal : Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.CrossingRequests.selectedPairedPerimeter
    retained perimeters keep - samples.selectedJump keep =
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (vertical a b))) -
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (horizontal a b))) := by
    dsimp only [horizontal, vertical, -eq_self, -iff_self]
    simp only [Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.CrossingRequests.selectedPairedPerimeter,
      Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.selectedJump,
      Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value_sub,
      Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalPrepared.Sample.areaDifference_eq_cache
        perimeters,
        Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalPrepared.Sample.areaDifference_eq_cache
        perimeters,
      FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
    ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      verticalBound horizontalBound) (by decide)).trans_eq (by ring1))

/-- The paid total crossing request bounds the selected original jump by its quarter-target allocation. -/
theorem
  CrossingTotal.CrossingRequests.TotalRequest.selected_jump_bound
  {error : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (error / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (perimeters : FacePerimeters (request := request)
      cache.normalize i j)
    (keep : Fin faces.regulars.length → Bool) (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.CrossingRequests.selectedPairedPerimeter retained
      perimeters keep - samples.selectedJump keep) ≤ error := by
  have estimate := samples.selected_jump_bound perimeters keep total.positive later
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct total.paid (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have equal : 4 * (16 * (faces.regulars.length : Fraction.Rational)^4 * total.perEntry) =
      64 * (faces.regulars.length : Fraction.Rational)^4 * total.perEntry := by ring1
  rw [equal, Fraction.Field.mul_comm 4 (error / 4), Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)] at paid
  exact estimate.trans paid

/-- Remove the selected internal interfaces with their paid endpoint jump
correction. No crossing to an unselected face is removed. -/
theorem
  CrossingTotal.CrossingRequests.TotalRequest.selected_boundary_bound
  {error : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent (error / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (perimeters : FacePerimeters (request := request)
      cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces) (keep : Fin faces.regulars.length → Bool)
    (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (perimeters.selectedPerimeterSum keep -
      Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.FacePerimeters.selectedBoundary perimeters neighbors
      keep - samples.selectedJump keep) ≤ error := by
  have equal : perimeters.selectedPerimeterSum keep -
    Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.FacePerimeters.selectedBoundary perimeters neighbors
    keep =
      Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.CrossingRequests.selectedPairedPerimeter retained
        perimeters keep := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.CrossingBank.selected_exterior_eq retained
      perimeters neighbors keep]
    ring1
  rw [equal]
  exact total.selected_jump_bound samples perimeters keep later

end Matched
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

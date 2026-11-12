module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCrossingBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.Ring

public section

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation

/-! Replace selected internal crossing jumps by the actual cached source
triangle areas. The existing corner request pays every retained occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction.Compatibility

attribute [local congr] FiniteSum.Fin.sumFin_congr

/-- Boolean selection preserves the supplied nonnegative bound on an original Gaussian value. -/
private theorem selected_bound (keep : Bool) {value : Gaussian.Basic.Canonical} {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : Gaussian.Norm.Basic.normSq value ≤ bound) :
      Gaussian.Norm.Basic.normSq
      (SelectedPerimeterIdentity.SelectedSides.value keep value) ≤ bound := by
  cases keep with
  | false =>
    simpa only [SelectedPerimeterIdentity.SelectedSides.value, if_neg (by decide : ¬
      false = true), if_pos (Eq.refl true), Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self] using nonnegative
  | true => exact bounded

/-- Boolean selection commutes with negation of the original side value. -/
private theorem value_neg (keep : Bool) (value : Gaussian.Basic.Canonical) :
  SelectedPerimeterIdentity.SelectedSides.value keep (-value) =
  -(SelectedPerimeterIdentity.SelectedSides.value keep value) := by
  cases keep with
  | false => exact (neg_zero).symm
  | true => rfl

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
  {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {retained : Matched.CrossingBank request mesh}
  {allocated : Matched.CrossingRequests
    (Periods.PeriodMatrix.standardDifferential i) (Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained} {cache :
      RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- Sum the actual crossing triangles whose two original incident faces are selected, retaining both horizontal and
vertical outcomes. -/
@[expose] def CrossingBank.selectedTriangleArea (retained :
  Matched.CrossingBank request mesh)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    SelectedPerimeterIdentity.SelectedSides.value (keep a && keep c)
    (CrossingTriangleAreas.VerticalOutcome.triangleArea
      (((retained.vertical.get a).get b).get c) left right)))) +
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    SelectedPerimeterIdentity.SelectedSides.value (keep a && keep c)
    (CrossingTriangleAreas.HorizontalOutcome.triangleArea
      (((retained.horizontal.get a).get b).get c) left right))))

/-- The original normalized vertical-minus-horizontal corner jump restricted to crossings with both faces selected. -/
private def selectedCorner (retained : Matched.CrossingBank request
  mesh) (cache : RegularDomainMeshes.RegularMeshes.Numerics domains stage) (i j : Fin
  genus)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    SelectedPerimeterIdentity.SelectedSides.value (keep a && keep c)
    ((((retained.vertical.get a).get b).get c).cornerJump cache i j)))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    SelectedPerimeterIdentity.SelectedSides.value (keep a && keep c)
    ((((retained.horizontal.get a).get b).get c).cornerJump cache i j))))

/-- The normalized selected corner jump equals the original selected crossing-triangle area. -/
private theorem selectedCorner_eq (retained : Matched.CrossingBank
  request mesh)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) :
    SelectedCornerBounds.selectedCorner retained cache.normalize i j keep =
      CrossingBank.selectedTriangleArea retained left right keep
      := by
  simp only [SelectedCornerBounds.selectedCorner,
    CrossingBank.selectedTriangleArea,
    CrossingTriangleAreas.HorizontalOutcome.cornerJump_eq_triangleArea (left := left)
      (right := right),
    CrossingTriangleAreas.VerticalOutcome.cornerJump_eq_triangleArea (left := left)
      (right := right),
    SelectedCornerBounds.value_neg, FiniteSum.Fin.sumFin_neg, -eq_self, -iff_self]
  ring1

/-- The original paid corner request bounds the selected sampled jump minus its actual retained crossing triangles.

The same original magnitude banks, corner grids and per-occurrence allocation control every selected crossing. -/
theorem CornerRequest.selected_triangle_bound {cornerTarget : Fraction.Rational}
    (corner : CrossingCornerBudget.CornerRequest fixed i j cornerTarget) (later :
      corner.index ≤ stage)
    (samples : Matched.CrossingSamples.CrossingRequests.Samples allocated
      cache.normalize)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) :
    Gaussian.Norm.Basic.normSq
      (Matched.CrossingSamples.CrossingRequests.Samples.selectedJump samples keep -
      CrossingBank.selectedTriangleArea retained left right
        keep) ≤ cornerTarget := by
  let perEntry := 512 * (4 * (corner.firstMagnitude.bound + corner.secondMagnitude.bound) + 1) * corner.tolerance
  have nonnegative : 0 ≤ perEntry := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg corner.firstMagnitude.nonnegative
        corner.secondMagnitude.nonnegative)) (by decide)))
    corner.positive.le
  let horizontal := fun a b c => SelectedPerimeterIdentity.SelectedSides.value (keep
    a && keep c)
    (Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump (prepared :=
      (((allocated.horizontal.get a).get b).get c))
      (cache := cache.normalize) (((samples.horizontal.get a).get b).get c) -
      (((retained.horizontal.get a).get b).get c).cornerJump cache.normalize i j)
  let vertical := fun a b c => SelectedPerimeterIdentity.SelectedSides.value (keep a
    && keep c)
    (Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump (prepared :=
      (((allocated.vertical.get a).get b).get c))
      (cache := cache.normalize) (((samples.vertical.get a).get b).get c) -
      (((retained.vertical.get a).get b).get c).cornerJump cache.normalize i j)
  have horizontalBound := Matched.CrossingTotal.triple_bound horizontal perEntry (fun
    a b c => SelectedCornerBounds.selected_bound (keep a && keep c) nonnegative
    (CrossingCornerRequests.HorizontalPrepared.Sample.corner_jump_bound
      (((samples.horizontal.get a).get b).get c)
      corner.firstMagnitude corner.secondMagnitude (corner.first_le.trans later) (corner.second_le.trans later)
      corner.grids (corner.grids_le.trans later) corner.positive corner.small))
  have verticalBound := Matched.CrossingTotal.triple_bound vertical perEntry (fun a b
    c => SelectedCornerBounds.selected_bound (keep a && keep c) nonnegative
    (CrossingCornerRequests.VerticalPrepared.Sample.corner_jump_bound
      (((samples.vertical.get a).get b).get c)
      corner.firstMagnitude corner.secondMagnitude (corner.first_le.trans later) (corner.second_le.trans later)
      corner.grids (corner.grids_le.trans later) corner.positive corner.small))
  have equal : Matched.CrossingSamples.CrossingRequests.Samples.selectedJump samples
    keep -
      SelectedCornerBounds.selectedCorner retained cache.normalize i j keep =
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (vertical a b))) -
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (horizontal a b))) := by
    dsimp only [horizontal, vertical]
    simp only [Matched.CrossingSamples.CrossingRequests.Samples.selectedJump,
      SelectedCornerBounds.selectedCorner,
        SelectedPerimeterIdentity.SelectedSides.value_sub, FiniteSum.Fin.sumFin_sub,
        -eq_self, -iff_self]
    ring1
  rw [← SelectedCornerBounds.selectedCorner_eq retained left right keep, equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      verticalBound horizontalBound) (by decide)).trans
      ((show 2 * (4 * (faces.regulars.length : Fraction.Rational)^4 * perEntry +
        4 * (faces.regulars.length : Fraction.Rational)^4 * perEntry) =
        8192 * (faces.regulars.length : Fraction.Rational)^4 *
          (4 * (corner.firstMagnitude.bound + corner.secondMagnitude.bound) + 1) * corner.tolerance by
        dsimp only [perEntry]; ring1).trans_le corner.paid))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds

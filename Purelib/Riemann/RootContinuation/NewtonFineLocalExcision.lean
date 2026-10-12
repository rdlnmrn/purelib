module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalSewnFormula
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound
import Purelib.Tactic.Ring

open Purelib.Data

public section

/-! The existing fine local perimeter/crossing request is consumed on the
actual Newton excision. Physical and annular corrections are both retained. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison (Sample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (SewnSample)
open
  _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining.NewtonPreparation.FamilyAreaRequest
open PairedComparison.SewnSample (Excision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest (ExteriorBoundaryRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests (TotalRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests (Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget (CornerRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}

namespace NewtonPreparation.FamilyAreaRequest

variable {request :
  FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison

variable {stage : Nat}
  {cache : Numerics domains stage}
  {left : TriangleReadings (cache.get first)
    lifted.mesh} {right : TriangleReadings
    (cache.get second) lifted.mesh}
  {firstSurface : CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : CachedSample lifted.cutPolygon.patch
    right.values}

open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision} {comparison :
  PairedComparison
  prepared first second domains}
  {source :
    PairedComparison.Sample
    comparison left right}

namespace SewnSample.Excision

open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {sample :
  PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}

variable {cuts : CommonCuts domains}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
  Preflights domains sheet}
  {localTarget : Rational} {firstParent secondParent : Fin 2} {floor : Nat}

open Purelib.Curves
open Purelib.Topology
open Purelib.Data
/-- Transfer the fine local sewn-boundary estimate to the retained Newton excision.

At a stage beyond every sewing, crossing, corner and annular request, the local perimeter differs from remaining area
plus physical and annular corrections by quadrance below twice four local targets plus the annular target. -/
theorem
  fine_local_accurate
  (cached :
  PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample)
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth)
      fixed ((localTarget / 4) / 4))
    {retained : PuncturedGrid.Matched.CrossingBank exterior.prepared.energy
      lifted.mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained first
      second firstParent secondParent
      (((localTarget / 4) / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed first second (localTarget /
      4))
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache first second)
    (normalized : PuncturedGrid.Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize first second)
    {global : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first
      second}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global localTarget
      floor)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    (neighbors : PuncturedFaces.NeighborBank request.single.grid.faces) (positive : 0 < localTarget)
    (sewingLater : sewing.index ≤ stage) (later : total.allocated.index ≤ stage)
    (cornerLater : corner.index ≤ stage) (annularLater : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (perimeters.localTotalSum - cached.remainingArea -
      ((Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        - Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right) +
        sample.correction)) <
      2 * (4 * localTarget + target) := by
  have localBound := total.local_sewn_boundary_bound exterior corner left right samples perimeters normalized
    sewing bilinear sewingLater neighbors positive later cornerLater
  exact
    PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision.local_boundary_transfer
    cached bilinear perimeters.localTotalSum
    (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors -
      Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right) localBound
      annularLater

/-- Bound the retained excision's remaining area together with its physical and annular corrections.

The local perimeter bound and fine local comparison apply at a common stage beyond all request and ownership floors; the
estimate retains the displayed exterior and annular budgets. -/
theorem
  corrected_remaining_small
  (cached :
  PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample)
    (exterior : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth)
      fixed ((localTarget / 4) / 4))
    {retained : PuncturedGrid.Matched.CrossingBank exterior.prepared.energy
      lifted.mesh}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained first
      second firstParent secondParent
      (((localTarget / 4) / 4) / 4) floor)
    (corner : Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed first second (localTarget /
      4))
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache first second)
    (normalized : PuncturedGrid.Matched.FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize first second)
    {global : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first
      second}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global localTarget
      floor)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    (neighbors : PuncturedFaces.NeighborBank request.single.grid.faces) (positive : 0 < localTarget)
    (sewingLater : sewing.index ≤ stage) (later : total.allocated.index ≤ stage)
    (cornerLater : corner.index ≤ stage) (annularLater : comparison.index ≤ stage)
    (ownershipLater : exterior.prepared.ownership.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.remainingArea +
      ((Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter normalized neighbors
        - Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right) +
        sample.correction)) <
      2 * (exterior.localTarget + 2 * (4 * localTarget + target)) := by
  have localBound := Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.FacePerimeters.local_bound exterior.prepared
    perimeters ownershipLater
  have difference := cached.fine_local_accurate exterior total corner samples perimeters normalized sewing bilinear
    neighbors positive sewingLater later cornerLater annularLater
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      ((Rat.Fraction.Order.Arithmetic.add_le_add_right_direct localBound _).trans_lt
        (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct difference _)))
  have equal : ∀ a b c : Gaussian.Basic.Canonical, a - (a - b - c) = b + c := by intros; ring1
  rwa [equal] at estimate

end SewnSample.Excision
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining

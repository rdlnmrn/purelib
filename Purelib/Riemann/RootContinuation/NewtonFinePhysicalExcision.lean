module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Riemann.RootContinuation.NewtonFineLocalExcision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalComparison
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

public section

/-! Fine retained-surface bound after simultaneous physical source-chord cancellation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining

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

open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PhysicalSides)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open PhysicalComparison.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.PhysicalSides

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
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
  PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision} {comparison :
  PairedComparison
  prepared first second domains}
  {source :
    Sample
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

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Bound the retained remaining area after simultaneous physical source-chord cancellation.

The stage satisfies all sewing, crossing, corner, annular and ownership requests. The bound retains the exterior local
error, original annular target, squared physical hole count and actual sewing weight/error. -/
theorem
  physical_remaining_small
  (cached :
  Excision
  sample) (physical :
  PhysicalSides
  sample)
    (exterior : ExteriorBoundaryRequest (fun sheet =>
      RegularMeshes.build domains cuts sheet coarseDepth)
      fixed ((localTarget / 4) / 4))
    {retained : CrossingBank exterior.prepared.energy
      lifted.mesh}
    (total : TotalRequest retained first
      second firstParent secondParent
      (((localTarget / 4) / 4) / 4) floor)
    (corner : CornerRequest fixed first second (localTarget /
      4))
    (samples : Samples total.allocated
      cache.normalize)
    (perimeters : FacePerimeters (request :=
      exterior.prepared.energy) cache first second)
    (normalized : FacePerimeters (request :=
      exterior.prepared.energy) cache.normalize first second)
    {global : BilinearPreparation lifted.cutPolygon domains first
      second}
    (sewing : BilinearPreparation.Request global localTarget
      floor)
    (bilinear : Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    (neighbors : PuncturedFaces.NeighborBank request.single.grid.faces) (positive : 0 < localTarget)
    (sewingLater : sewing.index ≤ stage) (later : total.allocated.index ≤ stage)
    (cornerLater : corner.index ≤ stage) (annularLater : comparison.index ≤ stage)
    (ownershipLater : exterior.prepared.ownership.index ≤ stage) :
    normSq (cached.remainingArea +
      (physicalComponentCorrection normalized neighbors
        left right .exterior +
        gaussianSum (physical.entries.map (fun entry =>
          remainingCorrection
          entry normalized)))) <
      2 * (2 * (exterior.localTarget + 2 * (4 * localTarget + target)) +
        (request.single.grid.faces.holes.length : Rational) *
          ((request.single.grid.faces.holes.length : Rational) * (8 * (8 * (sewing.budget.weight *
            sewing.budget.error))))) := by
  have original := cached.corrected_remaining_small exterior total corner samples perimeters normalized sewing bilinear
    neighbors positive sewingLater later cornerLater annularLater ownershipLater
  have correction :=
    global_correction_accurate
    physical normalized neighbors sewing sewingLater bilinear
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
      ((Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct original _).trans_le
        (Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) correction)))
  have equal : ∀ r a b c d : Gaussian.Basic.Canonical, (r + (a + b)) - (b + a - (c + d)) = r + (c + d) := by
    intros; ring1
  rwa [equal] at estimate

end SewnSample.Excision
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining

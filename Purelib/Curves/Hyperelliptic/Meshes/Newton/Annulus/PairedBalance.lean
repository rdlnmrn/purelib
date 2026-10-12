module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation.ProjectedEdgePairing

open Purelib.Topology.Surface.Cut.PrimitiveJumps

@[expose] public section

/-! The retained projected cancellation applies to arbitrary paired
primitive values on the original selected cut triangles. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedBalance

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea edgeArea
  edgeArea_reverse edgeListArea_append)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus (CutBalance)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing (PrimitiveSample)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {lifted : LiftedPuncturedGrid grid.punctured}

namespace AllHoleExcision.SewnAnnulus.CutBalance

variable {localValues : Fin lifted.mesh.triangles.length →
  PrimitiveValues 3}
  {surface : CachedSample lifted.cutPolygon.patch localValues}
  {annulus : SewnAnnulus surface} {prepared :
    OuterPreparation
    annulus.source.region}
  {outer : CutSourceWord
    lifted.cutPolygon.patch.cut prepared.sources}

/-- Every selected triangle, inner boundary, jump and defect is retained. -/
theorem paired_area_balance (balance : CutBalance annulus prepared
  outer)
    (primitive : Fin lifted.cutPolygon.patch.cut.count → Stokes.PrimitivePoint)
    (sample : ProjectedEdgePairing.PrimitiveSample balance.complete.pairing primitive) :
    Stokes.edgeListArea primitive (annulus.selected.triangles.flatMap OrientedTriangle.boundary) =
      Stokes.edgeListArea primitive outer.edges + Stokes.edgeListArea primitive balance.inner.word.edges +
        sample.jumpSum + sample.defectSum := by
  have equal := (congrArg (Stokes.edgeListArea primitive) balance.edges_eq).symm.trans
    (Complete.area_eq_jumps_defects balance.complete primitive sample)
  rw [Stokes.edgeListArea_append, WitnessReadbacks.reverse_area, Stokes.edgeListArea_append] at equal
  calc
    _ = (Stokes.edgeListArea primitive (annulus.selected.triangles.flatMap OrientedTriangle.boundary) +
      -(Stokes.edgeListArea primitive outer.edges + Stokes.edgeListArea primitive balance.inner.word.edges)) +
      (Stokes.edgeListArea primitive outer.edges + Stokes.edgeListArea primitive balance.inner.word.edges) := by ring1
    _ = _ := by rw [equal]; ring1

end AllHoleExcision.SewnAnnulus.CutBalance
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedBalance

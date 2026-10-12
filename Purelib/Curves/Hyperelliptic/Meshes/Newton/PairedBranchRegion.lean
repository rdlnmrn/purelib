module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! The original branch region compared with the ordered based excursion
for two actual differentials. Inner boundaries and cut corrections remain. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A paid paired comparison between an original branch region and its retained based excursion.

It keeps the original outer annular faces, stem and hole requests, sewing geometry and two differential magnitude banks.
-/
structure PairedBranchRequest (bank :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (entry :
  Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) (sheet : Fin 2)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
    (error : Rational) (floor : Nat) where
  /-- The original annular face region for the retained branch hole. -/ outer :
    RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid entry.hole.index
  /-- The paired original stem request at its allocated error. -/ stems :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests.BilinearStemRequest bank grid.shrunk.included
    leftFixed rightFixed entry.hole.index sheet (error / 4 / 10)
  /-- The paired original doubled-hole request at its allocated error. -/ holes :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest bank grid.shrunk.included
    leftFixed rightFixed entry.hole.index (error / 4 / 10)
  /-- The actual retained included-hole sewing geometry. -/ geometry :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing.IncludedHoleSewing bank grid.shrunk.included
    entry.hole.index domains leftDifferential
  /-- The paired sewing request on that same original geometry. -/ sewing :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing.PairedRequest geometry leftFixed rightFixed (error /
    4) floor

constructive_injectivity PairedBranchRequest

namespace PairedBranchRequest

variable {entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current} {sheet : Fin 2}
  {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
    {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}

/-- Prepare the original annular region, paired stem and hole allowances and sewing comparison for the supplied positive
target. -/
@[expose] def build (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) (sheet : Fin 2)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
    (error : Rational) (positive : 0 < error) (floor : Nat) :
      Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed rightFixed error
      floor :=
  have quarter := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Rational) < 4)
  have inner := Fraction.Order.Field.div_pos_direct quarter (by decide : (0 : Rational) < 10)
  let geometry := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing.IncludedHoleSewing.build bank
    grid.shrunk.included entry.hole.index domains leftDifferential
  ⟨OriginalAnnularFaces.build grid entry.hole.index,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests.BilinearStemRequest.build bank
      grid.shrunk.included leftFixed rightFixed entry.hole.index sheet _ inner,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest.build bank
      grid.shrunk.included leftFixed rightFixed entry.hole.index _ inner,
    geometry, Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing.PairedRequest.build geometry leftFixed
      rightFixed _ quarter floor⟩

/-- The maximum sufficient stage of the retained stem, hole and sewing requests. -/
@[expose] def index (request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
  leftFixed rightFixed error floor) : Nat :=
  max (max request.stems.index request.holes.index) request.sewing.index

/-- The common sufficient stage respects the original supplied floor. -/
theorem floor_le (request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
  leftFixed rightFixed error floor) : floor ≤ request.index :=
  request.sewing.floor_le.trans (Data.Nat.Order.le_max_right _ _)

set_option genInjectivity false in
/-- The actual paired cut balance and cached based-excursion polygon on the retained shared surface readings. -/
structure Sample (request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
  leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      rightReadings.values) where
  /-- The actual cut balance on the retained original annular region and left surface. -/ balance :
    OriginalCutBalance request.outer entry.region request.geometry
    leftSurface
  /-- The paired sample of that same original cut balance and right surface. -/ cut :
    Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.PairedSample balance rightSurface
  /-- The cached actual based-excursion paired polygon. -/ polygon : Gaussian.Basic.Canonical
  /-- The polygon is exactly the paired canonical value on the retained resplit reference walk and sheet. -/ polygon_eq
    : polygon = Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices
    (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet).map (fun
      edge =>
      (⟨edgeValuation current.mesh leftReadings.values edge,
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint)))

constructive_injectivity Sample

namespace Sample

variable {request : Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
  leftFixed rightFixed error floor}
  {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
    stage domains}
  {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
  {leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh}
    {rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
    current.mesh}
  {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values}
  {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
    rightReadings.values}

/-- Cache the actual original paired cut sample and based-excursion polygon from the supplied surface readings. -/
@[expose] def build (request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
  leftFixed rightFixed error floor)
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      rightReadings.values) :
    request.Sample leftReadings rightReadings leftSurface rightSurface :=
  let balance := OriginalCutBalance.build request.outer entry.region
    request.geometry leftSurface
  ⟨balance, Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.PairedSample.build balance rightSurface,
    Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet).map (fun
        edge =>
        (⟨edgeValuation current.mesh leftReadings.values edge,
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))), rfl⟩

/-- The original corrected region area minus twice the retained based-excursion polygon. -/
@[expose] def residual (sample : request.Sample leftReadings rightReadings leftSurface rightSurface) : Gaussian :=
  sample.cut.area - sample.cut.correction - (sample.polygon + sample.polygon)

/-- Sewing, both stem defects, both sheet areas and the lap-total cross term
are paid on one later sample, with the original region's corrections retained. -/
theorem accurate (sample : request.Sample leftReadings rightReadings leftSurface rightSurface)
    (later : request.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq sample.residual ≤ error := open
      Purelib.RootIsolation in by
  let value := fun edge => (⟨edgeValuation current.mesh leftReadings.values edge,
    Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
      Topology.Polygon.Stokes.PrimitivePoint)
  let walk := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests.BilinearHoleRequest.boundary (next :=
    grid.punctured) bank grid.shrunk.included entry.hole.index
  let arrival := SquareRoot.Grid.EdgeBank.RootEdgeBank.target current.edges
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests.BilinearStemRequest.stem (next := grid.punctured)
    bank grid.shrunk.included entry.hole.index) sheet
  let lap := Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices walk arrival).map value)
  let double := Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map
    value)
  have stemBound := request.stems.accurate leftReadings rightReadings
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans later))
  have stem : Data.Gaussian.Norm.Basic.normSq (sample.polygon - lap) ≤ error / 4 / 10 := by
    rw [sample.polygon_eq]
    exact stemBound
  have hole : Data.Gaussian.Norm.Basic.normSq (lap + lap - double) ≤ error / 4 / 10 := request.holes.accurate
    leftReadings rightReadings
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans later)) arrival
  have twice : Data.Gaussian.Norm.Basic.normSq ((sample.polygon - lap) + (sample.polygon - lap)) ≤ 4 * (error / 4 /
    10) :=
    ((Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct stem
        stem) (by decide))).trans_eq (by ring1)
  have branch := (Gaussian.Norm.Bounds.normSq_add_le_two ((sample.polygon - lap) + (sample.polygon - lap)) (lap + lap -
    double)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct twice hole)
      (by decide))
  rw [show (sample.polygon - lap) + (sample.polygon - lap) + (lap + lap - double) =
    sample.polygon + sample.polygon - double by ring1] at branch
  have branchBound : Data.Gaussian.Norm.Basic.normSq (sample.polygon + sample.polygon - double) ≤ error / 4 :=
    branch.trans_eq ((by ring1 : 2 * (4 * (error / 4 / 10) + error / 4 / 10) = error / 4 / 10 * 10).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))
  have sewn := sample.cut.canonical_accurate request.sewing leftReadings rightReadings leftSurface rightSurface
    ((Data.Nat.Order.le_max_right _ _).trans later)
  have reversed : Data.Gaussian.Norm.Basic.normSq (double - (sample.polygon + sample.polygon)) ≤ error / 4 := by
    rw [show double - (sample.polygon + sample.polygon) = -(sample.polygon + sample.polygon - double) by ring1,
      Gaussian.Norm.Basic.normSq_neg]
    exact branchBound
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_via (sample.cut.area - sample.cut.correction) double
    (sample.polygon + sample.polygon)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sewn
      reversed) (by decide))
  exact estimate.trans_eq ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Sample
end PairedBranchRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion

module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearHoleRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemRequests
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateStemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
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

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

open Purelib

public section

/-! The conjugate original branch region compares to the actual based
excursion on the compiler sheet, retaining all inner and cut corrections. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion

open Purelib.Data.Rat.Fraction (Rational)

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

namespace PairedBranchRequest

variable {entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current} {sheet : Fin 2}
  {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
    {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}
set_option genInjectivity false in
/-- The original paired branch-region sample evaluated through its retained conjugate surface pairing.

It retains the original cut balance and conjugate occurrence correction, together with the cached conjugate
based-excursion polygon. -/
structure ConjugateSample (request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
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
      rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) where
  /-- The original cut balance on the retained left surface and annular region. -/ balance :
    OriginalCutBalance request.outer entry.region request.geometry
    leftSurface
  /-- The conjugate sample of that same original cut balance and right surface. -/ cut :
    Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance.ConjugateSample balance rightSurface pair
  /-- The cached actual conjugate based-excursion polygon. -/ polygon : Gaussian.Basic.Canonical
  /-- The polygon equals the conjugate canonical value on the retained reference walk and original sheet. -/ polygon_eq
    : polygon = Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices
    (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet).map (fun
      edge =>
      (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint)))

constructive_injectivity ConjugateSample

namespace ConjugateSample

variable {request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed
  rightFixed error floor}
  {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
    stage domains}
  {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
  {leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh}
    {rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
    current.mesh}
  {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values}
  {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
    rightReadings.values}
  {pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface}

/-- Cache the original conjugate cut sample and based-excursion polygon from the supplied shared surface readings. -/
@[expose] def build (request : Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry sheet
  leftFixed rightFixed error floor)
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) :
    Hyperelliptic.Meshes.Newton.ConjugateBranchRegion.PairedBranchRequest.ConjugateSample request leftReadings
      rightReadings leftSurface rightSurface pair :=
  let balance := OriginalCutBalance.build request.outer entry.region
    request.geometry leftSurface
  ⟨balance, Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance.ConjugateSample.build balance rightSurface pair,
    Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet).map (fun
        edge =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))), rfl⟩

/-- The corrected original conjugate region area minus twice the retained conjugate based-excursion polygon. -/
@[expose] def residual (sample : Hyperelliptic.Meshes.Newton.ConjugateBranchRegion.PairedBranchRequest.ConjugateSample
  request leftReadings rightReadings leftSurface rightSurface pair) : Gaussian :=
  sample.cut.area - sample.cut.correction - (sample.polygon + sample.polygon)

/-- Sewing, both stem defects, both sheet areas and the lap-total cross term
are paid on one later sample, with the original region's corrections retained. -/
theorem accurate (sample : Hyperelliptic.Meshes.Newton.ConjugateBranchRegion.PairedBranchRequest.ConjugateSample request
  leftReadings rightReadings leftSurface rightSurface pair)
    (later : request.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq sample.residual ≤ error := open
      Purelib.Data.Rat in open Purelib.RootIsolation in by
  let value := fun edge => (⟨Data.Gaussian.Basic.conj
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge),
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
  have stemBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateStemRequests.BilinearStemRequest.conjugate_accurate
    request.stems leftReadings rightReadings
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans later))
  have stem : Data.Gaussian.Norm.Basic.normSq (sample.polygon - lap) ≤ error / 4 / 10 := by
    rw [sample.polygon_eq]
    exact stemBound
  have hole : Data.Gaussian.Norm.Basic.normSq (lap + lap - double) ≤ error / 4 / 10 :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleRequests.BilinearHoleRequest.conjugate_accurate
    request.holes leftReadings rightReadings
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
  have sewn := Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance.ConjugateSample.canonical_accurate request.sewing
    leftReadings rightReadings leftSurface rightSurface pair sample.cut
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

end ConjugateSample
end PairedBranchRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion

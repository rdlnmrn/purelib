module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Topology.NewtonSewnExcision

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnConjugateRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

public section

/-! The exact regular and branch region receipts compare with the selected
source triangles on their shared conjugate pair and original source masks. -/
namespace Purelib.Riemann.Topology.NewtonSelectedConjugateSewing.NewtonGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance (BoundaryWords)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion (ConjugateRegionSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton (OriginalCutBalance)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance (ConjugateSample)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Numerics
    domains stage}

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Curves in
/-- Read any original position mask as the same complete two-sheet conjugate triangle sum.

The retained source-position map covers regular and enclosing branch regions without replacing their actual selected
triangles. -/
theorem selected_conjugate_source_sum (left :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
    (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
      (keep : Fin grid.faces.regulars.length → Bool) :
    FiniteSum.Fin.sumFin (fun source => if keep (Topology.NewtonSewnExcision.AllHoleExcision.sourcePosition current
      source) then Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left
      right source else 0) =
      Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right keep := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum current.mesh]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  rw [Topology.NewtonSewnExcision.AllHoleExcision.sourcePosition_triangleIndex current position sheet false,
    Topology.NewtonSewnExcision.AllHoleExcision.sourcePosition_triangleIndex current position sheet true]
  rfl

namespace OriginalRegularFaces.ConjugateRegionSample

variable {face : RegularFace original} {region : OriginalRegularFaces grid face} {words :
  BoundaryWords face current}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- The original regular-region conjugate receipt approximates its exact selected source triangles.

Both retained sewn surfaces and their conjugate pair use the same original region mask and permitted numerical stage. -/
theorem selected_accurate (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  (cache.get i) current.mesh)
    (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    {leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {pair : Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface}
    (sample : Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion.ConjugateRegionSample region words leftSurface
      rightSurface pair)
    {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i
      j} {error : Rational} {floor : Nat}
    (request : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request prepared error floor)
      (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.area -
      Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
      position =>
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines face.cell.box))) < error := by
  have estimated := request.selected_conjugate_accurate later left right pair sample.balance.selected
  rw [← sample.area_eq] at estimated
  have read := Topology.NewtonSelectedConjugateSewing.NewtonGrid.selected_conjugate_source_sum
    left right (fun position =>
    decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines face.cell.box))
  exact (congrArg (fun triangles => Data.Gaussian.Norm.Basic.normSq (sample.area - triangles)) read).symm.trans_lt
    estimated

end OriginalRegularFaces.ConjugateRegionSample
end Purelib.Riemann.Topology.NewtonSelectedConjugateSewing.NewtonGrid

namespace Purelib.Riemann.Topology.NewtonSelectedConjugateSewing.ConjugateSample

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance (BoundaryWords)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion (ConjugateRegionSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton (OriginalCutBalance)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance (ConjugateSample)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {index :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Numerics
    domains stage}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- The original enclosing branch-region conjugate receipt approximates its exact selected source triangles.

The original cut balance and conjugate pair retain the selected annulus, including its physical inner boundary. -/
theorem selected_accurate
    {outer : OriginalAnnularFaces grid index} {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid
      index}
    {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus current}
    {geometry : IncludedHoleSewing bank grid.shrunk.included index domains (standardDifferential i)}
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    {leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {pair : Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface}
    {balance : Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance outer region geometry leftSurface}
    (sample : Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance.ConjugateSample balance rightSurface pair)
    {prepared : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i
      j} {error : Rational} {floor : Nat}
    (request : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request prepared error floor)
      (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.area -
      Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
      position =>
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell index).box))) < error
        := by
  have estimated := request.selected_conjugate_accurate later left right pair balance.selected
  rw [← sample.area_eq] at estimated
  have read := Topology.NewtonSelectedConjugateSewing.NewtonGrid.selected_conjugate_source_sum
    left right (fun position =>
    decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell index).box))
  exact (congrArg (fun triangles => Data.Gaussian.Norm.Basic.normSq (sample.area - triangles)) read).symm.trans_lt
    estimated

end Purelib.Riemann.Topology.NewtonSelectedConjugateSewing.ConjugateSample

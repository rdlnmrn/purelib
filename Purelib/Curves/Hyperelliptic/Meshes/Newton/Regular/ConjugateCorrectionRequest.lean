module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing
public import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.Topology.NewtonSelectedConjugateSewing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateWindowSelectedRequest
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data.Rat

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology.NewtonSelectedConjugateSewing.NewtonGrid.OriginalRegularFaces

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

open Purelib.Topology.Surface.Sewing

public section

/-! Requested decay of the actual regular-region cut correction, obtained
by comparing its sewn area and both corrected polygons to the same triangles. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateCorrectionRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance (BoundaryWords)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion (ConjugateRegionSample conjugatePolygon)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedSewing (PairedSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {face : RegularFace original}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}

/-- The request controls the cached correction on any two sewn samples at a common later stage; no vanishing correction
is assumed. -/
@[expose] def conjugateCorrectionRequest (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (words :
  CutBalance.BoundaryWords face current)
    (prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j)
    (error : Rational) (positive : 0 < error) (floor : Nat) :
    { threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
        (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
        (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
        (sample : ConjugateRegion.ConjugateRegionSample region words leftSurface rightSurface pair),
        threshold ≤ stage → Data.Gaussian.Norm.Basic.normSq sample.correction ≤ error } := by
  let part := error / 16
  have partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Rational) < 16)
  have sheetPositive : 0 < part / 4 := Fraction.Order.Field.div_pos_direct partPositive (by decide : (0 : Rational) < 4)
  let geometry := ConjugateWindowSelectedRequest.selectedConjugateTriangleRequest region prepared.leftMagnitude
    prepared.rightMagnitude part partPositive floor
  let sewing := BilinearPreparation.Request.build prepared part partPositive floor
  let zeroRequest := PairedSheetRequest.build words 0 words.zero prepared.leftMagnitude prepared.rightMagnitude
    (part / 4) sheetPositive floor
  let oneRequest := PairedSheetRequest.build words 1 words.one prepared.leftMagnitude prepared.rightMagnitude
    (part / 4) sheetPositive floor
  let threshold := max (max geometry.val sewing.index) (max zeroRequest.index oneRequest.index)
  refine ⟨threshold, geometry.property.1.trans ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)), ?_⟩
  intro stage cache left right leftSurface rightSurface pair sample later
  have geometryLater := (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have sewingLater := (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have zeroLater := (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans later)
  have oneLater := (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans later)
  let triangles := ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun position =>
    decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines face.cell.box))
  let polygon := ConjugateRegion.conjugatePolygon face current left.values right.values
  let boundary := fun sheet => BilinearPolarization.extract (fun coefficient => current.edges.chainArea current.vertices
    (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
      current.mesh left.values edge))
      (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
    (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)
  have polygonEq (sheet : Fin 2) : boundary sheet = polygon sheet :=
    BilinearPolarization.extract_wordArea_mix _ _ _
  have geometryBound := geometry.property.2 stage cache left right geometryLater
  change Data.Gaussian.Norm.Basic.normSq (boundary 0 + boundary 1 - triangles) < part at geometryBound
  rw [polygonEq 0, polygonEq 1] at geometryBound
  have areaBound := ConjugateRegionSample.selected_accurate left right sample sewing sewingLater
  change Data.Gaussian.Norm.Basic.normSq (sample.area - triangles) < part at areaBound
  have zero := PairedSheetRequest.conjugate_corrected_accurate zeroRequest left right leftSurface rightSurface zeroLater
    pair sample.zero
  have one := PairedSheetRequest.conjugate_corrected_accurate oneRequest left right leftSurface rightSurface oneLater
    pair sample.one
  change Data.Gaussian.Norm.Basic.normSq ((sample.zero.raw - sample.zero.correction) - polygon 0) ≤ part / 4 at zero
  change Data.Gaussian.Norm.Basic.normSq ((sample.one.raw - sample.one.correction) - polygon 1) ≤ part / 4 at one
  have corrected : Data.Gaussian.Norm.Basic.normSq (sample.area - sample.correction - (polygon 0 + polygon 1))
    ≤ part := by
    have equal : sample.area - sample.correction - (polygon 0 + polygon 1) =
        ((sample.zero.raw - sample.zero.correction) - polygon 0) +
        ((sample.one.raw - sample.one.correction) - polygon 1) := by
      rw [ConjugateRegionSample.corrected_area sample]
      ring1
    rw [equal]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct zero
        one) (by decide)).trans_eq
        ((by ring1 : 2 * (part / 4 + part / 4) = part / 4 * 4).trans
          (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  have towardTriangles : Data.Gaussian.Norm.Basic.normSq (sample.area - sample.correction - triangles) ≤ 2 *
    (part + part) := by
    have equal : sample.area - sample.correction - triangles =
        (sample.area - sample.correction - (polygon 0 + polygon 1)) + (polygon 0 + polygon 1 - triangles) := by ring1
    rw [equal]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct corrected
        geometryBound.le) (by decide))
  have equal : sample.correction = (sample.area - triangles) - (sample.area - sample.correction - triangles) := by ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      areaBound.le towardTriangles) (by decide)).trans
      (calc
        2 * (part + 2 * (part + part)) = 10 * part := by ring1
        _ ≤ 16 * part := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) partPositive.le
        _ = error := (Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateCorrectionRequest

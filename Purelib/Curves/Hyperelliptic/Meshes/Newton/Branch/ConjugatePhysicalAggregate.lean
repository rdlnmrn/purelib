module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugatePhysicalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Surface.Sewing

public section

/-! Sum the original branch corrections together with the physical-hole
polygons on their actual excision entries, paying every occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugatePhysicalAggregate

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion (PairedBranchRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.NewtonGrid (originalCellMask)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr sumValues_zero sumValues_swap)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion (pairedValues)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate (PairedBranchRequests)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate.PairedBranchRequests (ConjugateSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {sheet : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {leftFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)}
  {rightFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)}
  {error : Rational} {floor : Nat}
  {entries : List (AnnularEntry grid current)}

/-- The original branch corrections paired with their actual conjugate physical-hole areas in excision order. -/
@[expose] def physicalCorrectionTerms {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    {left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh} {right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh}
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface} :
    {entries : List (Excision.AnnularEntry grid current)} →
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries} →
    PairedBranchRequests.ConjugateSamples left right leftSurface rightSurface pair requests → List
      Data.Gaussian.Basic.Canonical
  | _, _, .nil => []
  | entry :: _, _, .cons first last => (first.cut.correction + entry.conjugatePhysicalHoleArea left right) ::
    physicalCorrectionTerms last

/-- The sum of the retained correction terms equals the original branch correction plus the actual conjugate
physical-hole sum. -/
theorem physicalCorrectionTerms_sum {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    {left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh} {right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh}
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface}
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries}
    (samples : PairedBranchRequests.ConjugateSamples left right leftSurface rightSurface pair requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (physicalCorrectionTerms samples) =
      samples.corrections +
      CellBoundary.sumValues (fun entry => entry.conjugatePhysicalHoleArea left right) entries := by
  induction samples with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 + 0; ring1
  | cons first last ih =>
      change (first.cut.correction + _) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (physicalCorrectionTerms last) =
        (first.cut.correction + last.corrections) + (_ + _)
      rw [ih]
      ring1

/-- There is exactly one retained physical correction term per original excision entry. -/
theorem physicalCorrectionTerms_length {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    {left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh} {right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh}
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface}
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries}
    (samples : PairedBranchRequests.ConjugateSamples left right leftSurface rightSurface pair requests) :
    (physicalCorrectionTerms samples).length =
      entries.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every actual conjugate physical correction term satisfies the given squared-norm bound at every later sample stage.
-/
@[expose] def CorrectionsSmallAt (requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
  error floor entries)
    (bound : Fraction.Rational) (threshold : Nat) : Prop :=
  ∀ stage (cache : RegularMeshes.Numerics domains stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
    (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (samples : PairedBranchRequests.ConjugateSamples left right leftSurface rightSurface pair requests), threshold ≤
      stage →
    ∀ term ∈ physicalCorrectionTerms samples,
      Data.Gaussian.Norm.Basic.normSq term ≤ bound

/-- Prepare a common stage bounding every original branch correction together with its actual conjugate physical-hole
area.

The dependent recursion retains each excision entry and its original request, combining their paid thresholds with the
requested floor. -/
@[expose] def physicalCorrectionRequests (prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains
  i j)
    (bound : Fraction.Rational) (positive : 0 < bound) (minimum : Nat) :
    {entries : List (Excision.AnnularEntry grid current)} →
    (requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries) →
    {threshold : Nat // minimum ≤ threshold ∧
      CorrectionsSmallAt requests bound threshold}
  | _, .nil => ⟨minimum, le_rfl, by
      intro stage cache left right leftSurface rightSurface pair samples later term member
      cases samples
      exact (by nomatch member)⟩
  | _, .cons head tail =>
      let first := head.conjugatePhysicalCorrectionRequest prepared bound positive minimum
      let rest :=
        physicalCorrectionRequests prepared
        bound positive minimum tail
      ⟨max first.val rest.val, first.property.1.trans (Nat.Order.le_max_left _ _), by
        intro stage cache left right leftSurface rightSurface pair samples later term member
        cases samples with
        | cons headSample tailSamples =>
            rcases Data.List.Membership.mem_cons.mp member with same | member
            · cases same
              have estimate := first.property.2 stage cache left right leftSurface rightSurface pair headSample
                ((Nat.Order.le_max_left _ _).trans later)
              rw [head.conjugatePhysicalHoleArea_eq left right] at estimate
              exact estimate
            · exact rest.property.2 stage cache left right leftSurface rightSurface pair tailSamples
                ((Nat.Order.le_max_right _ _).trans later) term member⟩

/-- One threshold bounds all branch corrections plus their actual physical hole polygons, with both factors of the
occurrence count paid. -/
@[expose] def conjugatePhysicalCorrectionRequest (prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon
  domains i j)
    (requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries)
    (bound : Fraction.Rational) (positive : 0 < bound) (minimum : Nat) :
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
        (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
    (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
        (samples : PairedBranchRequests.ConjugateSamples left right leftSurface rightSurface pair requests), threshold ≤
          stage →
        Data.Gaussian.Norm.Basic.normSq (samples.corrections + CellBoundary.sumValues (fun entry =>
          entry.conjugatePhysicalHoleArea left right) entries) < bound} := by
  let acquired := physicalCorrectionRequests
    prepared (Aggregate.perTerm bound entries.length)
    (Aggregate.perTerm_positive positive _) minimum requests
  refine ⟨acquired.val, acquired.property.1, ?_⟩
  intro stage cache left right leftSurface rightSurface pair samples later
  rw [← physicalCorrectionTerms_sum samples]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro term member
  rw [physicalCorrectionTerms_length samples]
  exact acquired.property.2 stage cache left right leftSurface rightSurface pair samples later term member

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugatePhysicalAggregate

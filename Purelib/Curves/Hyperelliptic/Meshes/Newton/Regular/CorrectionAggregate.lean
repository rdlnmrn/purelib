module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CorrectionRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Data

/-! Requested decay of the complete regular correction retained by the
original ordered compiler. The finite occurrence multiplicity is paid. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CorrectionAggregate

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (ResplitRegularOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate (PairedRegularRequests)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests (Samples)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
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
  {occurrences : List
    (PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
    (faces := base.faces) grid.shrunk.included current.edges current.vertices)}

/-- The actual paired cut corrections in the original regular-occurrence order. -/
@[expose] def correctionTerms {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    {left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh} {right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh}
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values} :
    {occurrences : List (CircuitPartition.ResplitRegularOccurrence (faces := base.faces) grid.shrunk.included
      current.edges current.vertices)} →
    {requests : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor occurrences} →
    PairedRegularRequests.Samples left right leftSurface rightSurface requests → List Data.Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.cut.correction ::
    correctionTerms last

/-- Summing the retained correction list gives the original paired aggregate. -/
theorem correctionTerms_sum {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    {left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh} {right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh}
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {requests : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor occurrences}
    (samples : PairedRegularRequests.Samples left right leftSurface rightSurface requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (correctionTerms samples) = samples.corrections :=
      by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg (first.cut.correction + ·) ih

/-- The retained correction list has one term per original regular occurrence. -/
theorem correctionTerms_length {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    {left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh} {right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh}
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {requests : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor occurrences}
    (samples : PairedRegularRequests.Samples left right leftSurface rightSurface requests) :
    (correctionTerms samples).length = occurrences.length
      := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every actual retained correction term meets the supplied bound at every later shared numerical stage. -/
@[expose] def CorrectionsSmallAt (requests : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
  floor occurrences)
    (bound : Rational) (threshold : Nat) : Prop :=
  ∀ stage (cache : RegularMeshes.Numerics domains stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
    (samples : PairedRegularRequests.Samples left right leftSurface rightSurface requests), threshold ≤ stage →
    ∀ term ∈ correctionTerms samples,
      Data.Gaussian.Norm.Basic.normSq term ≤ bound

/-- Prepare one common threshold for the original regular-occurrence corrections.

Every term keeps its original region, boundary words and sewn samples; the recursion pays both the requested floor and
all entry thresholds. -/
@[expose] def correctionRequests (prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j)
    (bound : Rational) (positive : 0 < bound) (minimum : Nat) :
    {occurrences : List (CircuitPartition.ResplitRegularOccurrence (faces := base.faces) grid.shrunk.included
      current.edges current.vertices)} →
    (requests : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor occurrences) →
    {threshold : Nat // minimum ≤ threshold ∧
      CorrectionsSmallAt requests bound threshold}
  | _, .nil => ⟨minimum, le_rfl, by
      intro stage cache left right leftSurface rightSurface samples later term member
      cases samples
      exact (List.not_mem_nil member).elim⟩
  | _, .cons head tail =>
      let first := CorrectionRequest.correctionRequest head.region head.words prepared bound positive minimum
      let rest := correctionRequests prepared
        bound positive minimum tail
      ⟨max first.val rest.val, first.property.1.trans (Nat.Order.le_max_left _ _), by
        intro stage cache left right leftSurface rightSurface samples later term member
        cases samples with
        | cons headSample tailSamples =>
            rcases List.Membership.mem_cons.mp member with same | member
            · cases same
              exact first.property.2 stage cache left right leftSurface rightSurface headSample.cut
                ((Nat.Order.le_max_left _ _).trans later)
            · exact rest.property.2 stage cache left right leftSurface rightSurface tailSamples
                ((Nat.Order.le_max_right _ _).trans later) term member⟩

/-- One threshold bounds the exact aggregate used by the original paired boundary comparison, with both factors of the
occurrence count paid. -/
@[expose] def correctionRequest (prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j)
    (requests : PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor occurrences)
    (bound : Rational) (positive : 0 < bound) (minimum : Nat) :
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
        (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
        (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
        (samples : PairedRegularRequests.Samples left right leftSurface rightSurface requests), threshold ≤ stage →
        Data.Gaussian.Norm.Basic.normSq samples.corrections < bound} := by
  let acquired := correctionRequests prepared
    (Aggregate.perTerm bound occurrences.length)
    (Aggregate.perTerm_positive positive _) minimum requests
  refine ⟨acquired.val, acquired.property.1, ?_⟩
  intro stage cache left right leftSurface rightSurface samples later
  rw [← correctionTerms_sum samples]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro term member
  rw [correctionTerms_length samples]
  exact acquired.property.2 stage cache left right leftSurface rightSurface samples later term member

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CorrectionAggregate

module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison
public import Purelib.Polynomial.Geometry.Grid.Boundary.Segments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

public section

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

/-!
# Newton bounds on the complete original shared-source path

The same-side certificates are consumed along the retained preparation and
its actual face assignments. One cached index controls every occurrence.
The resulting estimates concern the literal triangle-source word, including
reversals and repetitions, not independently prepared endpoint chords.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison (NewtonReference)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
    {ambient : Rational.Box}
  {differential : Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {fixed : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile differential.exponent}
  {target tolerance : Fraction.Rational}

/-- The original Newton-controlled reference for each retained segment occurrence and comparison owner. -/
@[expose] def NewtonReferences (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
  (tolerance : Fraction.Rational) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
        AssignedSegments.Comparisons differential
        parentSheet assigned → Type 2
  | _, _, _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, _, _, .cons _ remaining, compared =>
      NewtonReference compared.1 band tolerance ×
        NewtonReferences band tolerance remaining
        compared.2

namespace NewtonReferences

variable {band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target}

/-- Prepare the original references recursively from the retained same-side boundary geometry. -/
@[expose] def build (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target) (positive : 0 <
  tolerance) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        AssignedSegments.Comparisons differential
        parentSheet assigned),
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary band.sample.output.box path →
        NewtonReferences band tolerance assigned compared
  | _, _, _, _, _, _, .nil _ _, _, _ => ⟨⟩
  | _, _, _, _, _, _, .cons _ remaining, compared, geometry =>
      ⟨NewtonReference.build compared.1 band positive geometry.1 geometry.2.1 geometry.2.2.1,
        NewtonReferences.build band positive
          remaining compared.2 geometry.2.2.2⟩

/-- Take the common sufficient stage of all original retained segment-reference budgets. -/
@[expose] def index : ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial
  ambient start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
      AssignedSegments.Comparisons differential
      parentSheet assigned),
    NewtonReferences band tolerance assigned compared → Nat
  | _, _, _, _, _, _, .nil _ _, _, _ => 0
  | _, _, _, _, _, _, .cons _ remaining, compared, references =>
      max references.1.reference.budget.grid.index
        (NewtonReferences.index remaining
        compared.2 references.2)

/-- Every original corner increment satisfies the retained three-tolerance plus four-target Newton bound. -/
theorem corner_bound {domains : Face.DomainBanks.FaceDomainBank frames
  faces.regulars} {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        AssignedSegments.Comparisons differential
        parentSheet assigned)
      (_aligned :
        AssignedSegments.Comparisons.UsesDomains
        domains differential parentSheet assigned compared)
      (references : NewtonReferences band tolerance assigned
        compared),
      NewtonReferences.index assigned compared references ≤
        stage →
      ∀ value ∈ Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned,
        Gaussian.Norm.Basic.normSq value ≤ 3 * tolerance + 4 * target
  | _, _, _, _, _, _, .nil _ _, _, _, _, _, _, member => (List.not_mem_nil member).elim
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, references, later, value, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · exact references.1.corner_bound aligned.1 ((Nat.Order.le_max_left _ _).trans later) shared
      · exact NewtonReferences.corner_bound
          shared remaining compared.2 aligned.2 references.2 ((Nat.Order.le_max_right _ _).trans later) value
          member

end NewtonReferences

set_option genInjectivity false in
/-- Cache the finite common stage once. The reference bank itself retains
the original parent polynomials and their Newton-controlled resamplings. -/
structure NewtonReferenceBank (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
  (tolerance : Fraction.Rational)
    {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
      AssignedSegments.Comparisons differential
      parentSheet assigned) where
  /-- The original reference-comparison tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The original segment references aligned with the exact retained path and comparison spine. -/ references :
    NewtonReferences band tolerance assigned compared
  /-- The cached sufficient numerical stage for all original segment references. -/ index : Nat
  /-- The cached stage equals the exact original reference-bank maximum. -/ index_eq : index =
    NewtonReferences.index assigned compared references

constructive_injectivity NewtonReferenceBank

namespace NewtonReferenceBank

variable {band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target}
  {start finish : Gaussian.Basic.Canonical} {path : Geometry.ClearPath curve.polynomial ambient start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
    Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
    PreparedPath.CoveredSegments prepared}
  {assigned : PreparedFaceSegments.AssignedSegments mesh pieces} {compared :
    AssignedSegments.Comparisons differential
    parentSheet assigned}

/-- Cache the complete original Newton reference bank and its exact maximum comparison stage. -/
@[expose] def build (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target) (positive : 0 <
  tolerance)
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
      AssignedSegments.Comparisons differential
      parentSheet assigned)
    (geometry : Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary band.sample.output.box path) :
      NewtonReferenceBank band tolerance assigned compared :=
  let references := NewtonReferences.build band positive
    assigned compared geometry
  ⟨positive, references, NewtonReferences.index assigned
    compared references, rfl⟩

/-- The original common Newton increment allowance is nonnegative. -/
theorem bound_nonnegative (reference : NewtonReferenceBank band
  tolerance assigned compared) :
    0 ≤ 3 * tolerance + 4 * target := by
  have paid : 0 ≤ target := (Arithmetic.mul_nonneg_direct
    (add_nonneg (Arithmetic.mul_nonneg_direct (by decide) fixed.rate_nonnegative)
      (by decide +kernel)) band.sample.output.radiusPositive.le).trans band.paid
  exact add_nonneg (Arithmetic.mul_nonneg_direct (by decide) reference.positive.le)
    (Arithmetic.mul_nonneg_direct (by decide) paid)

/-- Every actual retained triangle-source increment satisfies the original common Newton bound. -/
theorem source_bound (reference : NewtonReferenceBank band
  tolerance assigned compared)
    {domains : Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      AssignedSegments.Comparisons.UsesDomains domains
      differential parentSheet assigned compared)
    {stage : Nat} (later : reference.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    ∀ value ∈ (AssignedSegments.sourceEdges assigned).map (fun
      source => source.increment readings.values),
      Gaussian.Norm.Basic.normSq value ≤ 3 * tolerance + 4 * target := by
  rw [AssignedSegments.sourceEdges_increments readings
    assigned]
  exact NewtonReferences.corner_bound shared assigned compared
    aligned reference.references (reference.index_eq ▸ later)

/-- The retained source-increment list has exactly the original assigned indexed word length. -/
theorem source_count {domains : Face.DomainBanks.FaceDomainBank frames
  faces.regulars} {stage : Nat}
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains}
      (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    ((AssignedSegments.sourceEdges assigned).map (fun source
      => source.increment readings.values)).length = assigned.indexed.length := by
  have count := congrArg List.length
    (AssignedSegments.sourceEdges_project assigned)
  rw [List.Map.length_map] at count ⊢
  exact count

/-- All coarse grid occurrences are paid, but later face refinement counts
do not enter the bound. This is the full cumulative polygon, not its total. -/
theorem source_area_bound (reference : NewtonReferenceBank band
  tolerance assigned compared)
    {domains : Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      AssignedSegments.Comparisons.UsesDomains domains
      differential parentSheet assigned compared)
    {stage : Nat} (later : reference.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea
      ((AssignedSegments.sourceEdges assigned).map (fun source
      => source.increment readings.values))) ≤
      4 * ((assigned.indexed.length : Fraction.Rational) ^ 2 * (3 * tolerance + 4 * target)) ^ 2 := by
  have bounded := Path.IncrementArea.pathArea_bound _ reference.bound_nonnegative (reference.source_bound aligned later
    readings)
  rw [NewtonReferenceBank.source_count readings] at bounded
  exact bounded

/-- Coordinate/root closure of the projected word does not erase this
anchor term: source increments on distinct faces need not telescope. -/
theorem source_trace_bound (reference : NewtonReferenceBank band
  tolerance assigned compared) (anchor : Gaussian.Basic.Canonical)
    {domains : Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      AssignedSegments.Comparisons.UsesDomains domains
      differential parentSheet assigned compared)
    {stage : Nat} (later : reference.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea anchor
      ((AssignedSegments.sourceEdges assigned).map (fun source
      => source.increment readings.values))) ≤
      8 * ((assigned.indexed.length : Fraction.Rational) ^ 2 * (3 * tolerance + 4 * target)) ^ 2 +
        8 * Gaussian.Norm.Basic.normSq anchor * ((assigned.indexed.length : Fraction.Rational) ^ 2 * (3 *
          tolerance + 4 * target)) := by
  let values := (AssignedSegments.sourceEdges assigned).map
    (fun source => source.increment readings.values)
  have total := Path.IncrementArea.sum_bound_of_length reference.bound_nonnegative
    (reference.source_bound aligned later readings) (count := assigned.indexed.length)
      (NewtonReferenceBank.source_count readings).le
  have endpoint := (Path.BoundaryRibbon.area_bound anchor (Gaussian.Norm.Sum.Basic.gaussianSum values)).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct total
      (Arithmetic.mul_nonneg_direct (by decide) (Gaussian.Norm.Basic.normSq_nonneg anchor)))
  rw [Path.IncrementArea.traceArea_eq]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (reference.source_area_bound aligned later readings) endpoint) (by decide)).trans_eq (by ring1))

end NewtonReferenceBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPathComparison

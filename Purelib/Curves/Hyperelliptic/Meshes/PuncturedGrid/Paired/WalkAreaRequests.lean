module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-!
# Requested opposite-sheet area cancellation on a shared numerical tail

The existing fixed face references discharge the increment magnitudes before
the paired edge tolerances are chosen. The same references and paired walk
can be reused at every accuracy and every later shared face bank.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests

open Purelib.Data
open Purelib.Data.Rat

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk (Requests)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct add_le_add_direct)
open Purelib.Integration.Path.IncrementArea (pathArea)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
    base.bank.grid start finish}

set_option genInjectivity false in
/-- A paid opposite-sheet area comparison on the original paired walk.

The actual magnitude reference, edge allowance, comparison requests and common stage are retained for the same source
polygons. -/
structure AreaRequest (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (paired :
  WalkOccurrences.PairedWalk mesh walk)
    (target : Fraction.Rational) where
  /-- The original requested area tolerance is strictly positive. -/ positive : 0 < target
  /-- The cached full walk-length and fixed-magnitude comparison weight. -/ weight : Fraction.Rational
  /-- The weight retains the exact fourth-power edge-count factor and original magnitude reference. -/ weight_eq :
    weight = 64 * (walk.edgeCount : Fraction.Rational) ^ 4 * fixed.bound
  /-- The cached positive tolerance allocated to each original paired edge. -/ perEdge : Fraction.Rational
  /-- The edge tolerance is exactly the weighted allowance of the original target and cached weight. -/ perEdge_eq :
    perEdge = Weighted.allowance target weight
  /-- The original opposite-sheet comparison requests at the cached per-edge tolerance. -/ requests :
    PairedWalk.Requests domains differential perEdge paired
  /-- The cached common stage paying the magnitude reference and every original edge request. -/ index : Nat
  /-- The common stage is exactly the maximum of those original reference and request stages. -/ index_eq : index = max
    fixed.index requests.index

constructive_injectivity AreaRequest

namespace AreaRequest

variable {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk}
  {target : Purelib.Data.Rat.Fraction.Rational}

/-- The original fourth-power walk-count and magnitude comparison weight is nonnegative. -/
theorem weight_nonnegative (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (walk : Walks.Walk
  base.bank.grid start finish) :
    0 ≤ 64 * (walk.edgeCount : Fraction.Rational) ^ 4 * fixed.bound :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
      fixed.nonnegative

/-- Cache the original complete walk weight and paid edge allowance, then retain the paired requests and their common
magnitude stage. -/
@[expose] def build (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (paired : WalkOccurrences.PairedWalk
  mesh walk)
    (target : Fraction.Rational) (positive : 0 < target) : AreaRequest fixed paired target :=
  let weight := 64 * (walk.edgeCount : Fraction.Rational) ^ 4 * fixed.bound
  let perEdge := Weighted.allowance target weight
  let requests := Requests.build domains differential perEdge
    (Weighted.allowance_positive positive (weight_nonnegative fixed walk)) paired
  ⟨positive, weight, rfl, perEdge, rfl, requests, max fixed.index requests.index, rfl⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
  (ownerFromMesh SingleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaCancellation
  (ReadingComparison realizeComparison)

/-- The single original source reading sample on the retained mesh owner. -/
@[reducible, expose] def Sample :=
  SingleReadings (owner := ownerFromMesh mesh) domains differential

/-- The original triangle reading bank at its actual retained numerical stage. -/
@[reducible, expose] def ReadingParent {index : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :=
  TrianglePrimitiveReadings.TriangleReadings numerics mesh

/-- The original opposite-sheet source comparison with the retained per-edge tolerance and fixed magnitude bound. -/
@[reducible, expose] def ComparisonData (request : AreaRequest fixed paired target)
    {index : Nat} {numerics : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : ReadingParent (mesh := mesh) numerics) (left right : Fin 2) :=
  ReadingComparison readings paired left right request.perEdge (4 * fixed.bound)

set_option genInjectivity false in
/-- The actual single request, original reading parents and the shared opposite observations at the original sample
stage. No mixed differential is constructed. -/
structure Realization (request : AreaRequest fixed paired target)
    {index : Nat} {numerics : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : ReadingParent (mesh := mesh) numerics)
    (later : request.index ≤ index) (left right : Fin 2) (different : left ≠ right) where
  /-- The actual retained original area request. -/ selection : AreaRequest fixed paired target
  /-- The retained selection is exactly the supplied original request. -/ selection_eq : selection = request
  /-- The actual original triangle reading parent consumed by the comparison. -/ readingParent : ReadingParent (mesh :=
    mesh) numerics
  /-- The retained reading parent is exactly the supplied original reading bank. -/ readingParent_eq : readingParent =
    readings
  /-- The cached source reading sample built from that same retained parent. -/ sample : Sample (mesh := mesh) (domains
    := domains) (differential := differential)
  /-- The sample is exactly the original parent's source reading view. -/ sample_eq : sample = SingleReadings.ofReadings
    (owner := ownerFromMesh mesh) readings
  /-- The retained sample stage pays the original fixed magnitude reference. -/ referenceLater : fixed.index ≤ index
  /-- The retained sample stage pays every original paired edge request. -/ requestLater : request.requests.index ≤
    index
  /-- The actual cached opposite-sheet comparison on the original readings and paired walk. -/ comparison :
    ComparisonData request readings left right
  /-- The retained comparison bound is paid by the original requested area tolerance. -/ budget : comparison.areaBound ≤
    target

constructive_injectivity Realization

namespace Realization

variable {request : AreaRequest fixed paired target}
  {index : Nat} {numerics : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    differential index domains}
  {readings : ReadingParent (mesh := mesh) numerics}
  {later : request.index ≤ index} {left right : Fin 2} {different : left ≠ right}

/-- The cached original source polygon for the retained left sheet. -/
@[expose] def leftSources (result : Realization request readings later left right different) :=
  result.comparison.leftSources

/-- The cached original source polygon for the retained right sheet. -/
@[expose] def rightSources (result : Realization request readings later left right different) :=
  result.comparison.rightSources

/-- The retained difference of the actual original opposite-sheet source polygon areas. -/
@[expose] def residual (result : Realization request readings later left right different) : Gaussian :=
  result.comparison.residual

/-- The cached quantitative bound of the original opposite-sheet area comparison. -/
@[expose] def areaBound (result : Realization request readings later left right different) : Fraction.Rational :=
  result.comparison.areaBound

/-- The retained residual equals the difference of the two actual cached source summary areas. -/
theorem residual_eq (result : Realization request readings later left right different) :
    result.residual = result.leftSources.summary.area - result.rightSources.summary.area :=
  result.comparison.residual_eq

/-- The retained residual reads the full original source polygons in their certified sheet occurrence orders. -/
theorem area_readback (result : Realization request readings later left right different) :
    result.residual =
      IncrementArea.pathArea ((paired.sources left).map (fun source => source.increment readings.values)) -
      IncrementArea.pathArea ((paired.sources right).map (fun source => source.increment readings.values)) :=
  result.comparison.area_readback

/-- The squared norm of the actual retained area residual is bounded by its original computed comparison bound. -/
theorem bounded (result : Realization request readings later left right different) :
    normSq result.residual ≤ result.areaBound := result.comparison.numeric.bounded

/-- The original requested tolerance pays the squared norm of the actual retained area residual. -/
theorem pay (result : Realization request readings later left right different) :
    normSq result.residual ≤ target := result.bounded.trans result.budget

end Realization

/-- Acquire the same original reading's source pairs once, retaining their summaries for both single source/chart
clients and paying the original budget. -/
@[expose] def realize (request : AreaRequest fixed paired target) {index : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank differential index domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings numerics mesh)
    (later : request.index ≤ index) (left right : Fin 2) (different : left ≠ right) :
    Realization request readings later left right different :=
  have referenceLater := (Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have requestLater := (Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have nonnegative : 0 ≤ request.weight := request.weight_eq ▸ weight_nonnegative fixed walk
  have perEdgePositive : 0 < request.perEdge := by
    rw [request.perEdge_eq]
    exact Weighted.allowance_positive request.positive nonnegative
  let magnitude := Readings.EdgeMagnitude.ofBank
    (owner := ownerFromMesh mesh) fixed referenceLater readings
  have magnitudeBound : magnitude.bound = fixed.bound := rfl
  let comparison := realizeComparison readings paired request.requests left right different requestLater
    perEdgePositive.le (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)
    (fun source _ => by
      have h := magnitude.source_bounded source
      rw [magnitudeBound] at h
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact h)
    (fun source _ => by
      have h := magnitude.source_bounded source
      rw [magnitudeBound] at h
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact h)
  have paid : comparison.areaBound ≤ target := by
    calc
      comparison.areaBound = 16 * (walk.edgeCount : Fraction.Rational) ^ 4 * request.perEdge * (4 * fixed.bound) :=
        comparison.areaBound_eq
      _ = request.weight * request.perEdge := by rw [request.weight_eq]; ring1
      _ ≤ target := by
        rw [request.perEdge_eq]
        exact Weighted.mul_allowance_le request.positive.le nonnegative
  { selection := request
    selection_eq := rfl
    readingParent := readings
    readingParent_eq := rfl
    sample := SingleReadings.ofReadings (owner := ownerFromMesh mesh) readings
    sample_eq := rfl
    referenceLater := referenceLater
    requestLater := requestLater
    comparison := comparison
    budget := paid }

/-- No caller-supplied numerical magnitude or sheet-transport equality is needed. The cached request controls the full
two source polygons at every later shared index, including a walk of length zero. -/
theorem accurate (request : AreaRequest fixed paired target) {index : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank differential index domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings numerics mesh)
    (later : request.index ≤ index) (left right : Fin 2) (different : left ≠ right) :
    normSq (IncrementArea.pathArea ((paired.sources left).map (fun source => source.increment readings.values)) -
      IncrementArea.pathArea ((paired.sources right).map (fun source => source.increment readings.values))) ≤ target :=
        by
  let result := realize request readings later left right different
  rw [← result.area_readback]
  exact result.pay

end AreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests

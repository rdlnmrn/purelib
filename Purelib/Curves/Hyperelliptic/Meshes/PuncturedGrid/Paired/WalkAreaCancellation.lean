module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.AreaComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Opposite-sheet control of the full transported stem area

The paired edge requests control a list of increment pairs in the original
walk order, not merely their sum. Each tail follows its actual cached sheet
permutation. The resulting estimate pays the fourth power of the original
walk length and retains an explicit increment magnitude bound.
-/

section

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Surface.Sewing

open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk (Requests)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaCancellation

/-- The two distinct original sheet readings sum to the actual zero-sheet and one-sheet source increments. -/
private theorem source_sum {start finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge base.bank.grid start
  finish}
    (head : EdgeOccurrences mesh edge) (values : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (left right : Fin 2) (different : left ≠ right) :
    (head.source left).increment values + (head.source right).increment values =
      head.zeroSource.increment values + head.oneSource.increment values := by
  have distinct : left.val ≠ right.val := fun equal => different (Fin.ext equal)
  have leftBound := left.isLt
  have rightBound := right.isLt
  by_cases zero : left.val = 0
  · have first : left = (⟨0, by decide⟩ : Fin 2) := Fin.ext zero
    have last : right = (⟨1, by decide⟩ : Fin 2) := Fin.ext (by change right.val = 1; omega0)
    rw [first, last]
    rfl
  · have first : left = (⟨1, by decide⟩ : Fin 2) := Fin.ext (by change left.val = 1; omega0)
    have last : right = (⟨0, by decide⟩ : Fin 2) := Fin.ext (by change right.val = 0; omega0)
    rw [first, last]
    exact Data.Gaussian.Basic.Canonical.add_comm _ _

/-- Every actual opposite-sheet increment pair satisfies the original single-differential request bound at the paid
common stage. -/
private theorem pair_errors {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus} {target : Fraction.Rational} {sampleIndex : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank differential sampleIndex domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings numerics mesh) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk mesh walk) (requests : PairedWalk.Requests domains differential target
        paired)
      (left right : Fin 2), left ≠ right → requests.index ≤ sampleIndex →
      ∀ pair ∈ ValuePairedEdgeRequests.incrementPairs (owner := SourceChartComparison.ownerFromMesh mesh)
        readings.values paired left right, normSq (pair.1 - pair.2) ≤ target
  | _, _, _, .nil _, .nil _, _, _, _, _, _, member => (List.not_mem_nil member).elim
  | _, _, _, .cons (edge := edge) head tail, .cons request remaining, left, right, different, later, pair, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · change normSq ((head.source left).increment readings.values - -(head.source right).increment readings.values) ≤
          target
        rw [show (head.source left).increment readings.values - -(head.source right).increment readings.values =
          (head.source left).increment readings.values + (head.source right).increment readings.values by ring1,
          source_sum head readings.values left right different]
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
          (head.accurate readings readings request
            ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans later)).le
      · have injective := ((edges.edge edge).bijection
          (BranchCellBank.referenceAt base.bank.toBranchCellBank _ edge.vertices.1).toLoop (BranchCellBank.referenceAt
            base.bank.toBranchCellBank _ edge.vertices.2).toLoop).forward_injective
        exact pair_errors readings tail remaining _ _ (fun equal => different (injective equal))
          ((Data.Nat.Order.le_max_right _ _).trans later) pair member

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
  (ownerFromMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests
  (OppositeComparison incrementPairs)

/-- The exact generic opposite cache for the original single reading. -/
@[reducible, expose] def ReadingComparison
    {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus} {sampleIndex : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank differential sampleIndex domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings numerics mesh)
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk mesh walk) (left right : Fin 2) (error bound : Fraction.Rational) :=
  OppositeComparison (owner := ownerFromMesh mesh) readings.values paired left right error bound

/-- Use the original nominal single edge requests to certify the shared value-parameterized pair observations. No second
reading or coefficient exists. -/
@[expose] def realizeComparison {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus} {error bound : Fraction.Rational} {sampleIndex : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank differential sampleIndex domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings numerics mesh)
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk mesh walk) (requests : PairedWalk.Requests domains differential error paired)
    (left right : Fin 2) (different : left ≠ right) (later : requests.index ≤ sampleIndex)
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (leftBound : ∀ source ∈ paired.sources left, normSq (source.increment readings.values) ≤ bound)
    (rightBound : ∀ source ∈ paired.sources right, normSq (source.increment readings.values) ≤ bound) :
    ReadingComparison readings paired left right error bound :=
  OppositeComparison.realize (owner := ownerFromMesh mesh) readings.values paired left right error bound
    errorNonnegative boundNonnegative
    (by exact pair_errors readings paired requests left right different later) leftBound rightBound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaCancellation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk

/-- Full source-path area control from the actual paired edge requests. The magnitude hypotheses concern only the two
retained forward source lists, and the count does not grow with later numerical refinement. -/
theorem area_difference_bound
  {domains : DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus} {target bound : Fraction.Rational} {sampleIndex : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank differential sampleIndex domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings numerics mesh)
    {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk mesh walk) (requests : PairedWalk.Requests domains differential target paired)
    (left right : Fin 2) (different : left ≠ right) (later : requests.index ≤ sampleIndex)
    (targetNonnegative : 0 ≤ target) (boundNonnegative : 0 ≤ bound)
    (leftBound : ∀ source ∈ paired.sources left, normSq (source.increment readings.values) ≤ bound)
    (rightBound : ∀ source ∈ paired.sources right, normSq (source.increment readings.values) ≤ bound) :
    normSq (IncrementArea.pathArea ((paired.sources left).map (fun source => source.increment readings.values)) -
      IncrementArea.pathArea ((paired.sources right).map (fun source => source.increment readings.values))) ≤
        16 * (walk.edgeCount : Fraction.Rational) ^ 4 * target * bound := by
  let comparison := Paired.WalkAreaCancellation.realizeComparison readings paired requests left right different later
    targetNonnegative boundNonnegative leftBound rightBound
  have estimate := comparison.numeric.bounded
  change normSq comparison.residual ≤ comparison.areaBound at estimate
  rw [comparison.area_readback, comparison.areaBound_eq] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk

end

module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Gaussian.Norm

public section

/-! Opposite-sheet cancellation for the canonical edge valuation. The
existing paired source request pays transport; signed chart requests pay
the two changes to the valuation used by the corrected period identity. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Topology.Surface.Sewing

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk (Requests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (SourceChartRequests)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    LiftedMesh vertices edges base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars} {differential : Differential genus}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)

variable {start finish : Data.Gaussian.Basic.Canonical} {walk : Polynomial.Geometry.Grid.Walks.Walk
  base.bank.grid start finish}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

set_option genInjectivity false in
/-- The three retained request families paying opposite-sheet cancellation in the original canonical edge valuation.

The shared stage pays paired source transport and both sheet-specific source/chart comparisons. -/
structure IncrementRequest (paired : WalkOccurrences.PairedWalk mesh walk) (domains : FaceDomainBank frames
  base.faces.regulars)
    (differential : Differential genus) (sheet : Fin 2) (target : Fraction.Rational)
    (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- The original complete cancellation target is strictly positive. -/ positive : 0 < target
  /-- The cached common target allocated to each original comparison family. -/ partTarget : Fraction.Rational
  /-- Each comparison family receives exactly one tenth of the complete cancellation target. -/ partTarget_eq :
    partTarget = target / 10
  /-- The actual opposite-sheet source transport requests on the original paired walk. -/ opposite : Requests
    domains differential (Aggregate.perTerm partTarget walk.edgeCount) paired
      (PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)
  /-- The retained signed source/chart requests on the originally selected sheet. -/ outward :
    SourceChartRequests differential domains
    (Aggregate.perTerm partTarget (paired.sources sheet).length) (paired.sources sheet) polynomial
  /-- The retained signed source/chart requests on the actual opposite sheet. -/ other :
    SourceChartRequests differential domains
    (Aggregate.perTerm partTarget (paired.sources (BranchCutLifts.otherSheet sheet)).length)
    (paired.sources (BranchCutLifts.otherSheet sheet)) polynomial
  /-- The cached common stage paying all three original request families. -/ index : Nat
  /-- The common stage is exactly the maximum of the original transport and both source/chart stages. -/ index_eq :
    index = max opposite.index (max outward.index other.index)

constructive_injectivity IncrementRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

variable {paired : PairedWalk mesh walk} {sheet
  : Fin 2} {target : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
namespace IncrementRequest

/-- Prepare all three original request families with the paid aggregate allowances and cache their common stage. -/
@[expose] def build (paired : WalkOccurrences.PairedWalk mesh walk) (domains : FaceDomainBank frames
  base.faces.regulars)
    (differential : Differential genus) (sheet : Fin 2) (target : Fraction.Rational) (positive : 0 <
      target) (polynomial : Option (Ordinary curve.polynomial) := none) :

      IncrementRequest
      paired domains differential sheet target polynomial :=
  let partTarget := target / 10
  have partPositive : 0 < partTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let opposite := Requests.build domains differential (Aggregate.perTerm partTarget walk.edgeCount)
    (Aggregate.perTerm_positive partPositive _) paired
    (PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)
  let outward := SourceChartRequests.build differential domains
    (Aggregate.perTerm partTarget (paired.sources sheet).length)
    (Aggregate.perTerm_positive partPositive _) (paired.sources sheet) (SignedSourceChartRequests.paired_sources_nonloop
      paired sheet) polynomial
  let other := SourceChartRequests.build differential domains
    (Aggregate.perTerm partTarget (paired.sources (BranchCutLifts.otherSheet sheet)).length)
    (Aggregate.perTerm_positive partPositive _) (paired.sources (BranchCutLifts.otherSheet sheet))
    (SignedSourceChartRequests.paired_sources_nonloop paired _) polynomial
  ⟨positive, partTarget, rfl, opposite, outward, other, max opposite.index (max outward.index other.index), rfl⟩

/-- The two actual sheet-specific source increment totals sum to the retained paired-walk source total. -/
private theorem sheet_sum (paired : WalkOccurrences.PairedWalk mesh walk) (values : Fin mesh.triangles.length →
  PrimitiveValues 3) (sheet : Fin 2) :
    Sum.Basic.gaussianSum ((paired.sources sheet).map (fun source => source.increment values)) +
      Sum.Basic.gaussianSum ((paired.sources (BranchCutLifts.otherSheet sheet)).map (fun source
        => source.increment values)) =
        Sum.Basic.gaussianSum (paired.sums values) := by
  have cases : sheet = 0 ∨ sheet = 1 := by
    have bound := sheet.isLt
    by_cases zero : sheet.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by change sheet.val = 1; omega))
  rcases cases with rfl | rfl
  · exact paired.sums_eq values
  · rw [BranchCutLifts.otherSheet_one, _root_.add_comm]
    exact paired.sums_eq values

/-- Original finite cancellation payment from the actual source transport and two paid chart discrepancies. -/
private theorem cancel_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : IncrementRequest paired domains differential sheet target polynomial)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared mesh) (later : request.index ≤ stage)
    (outward : Basic.normSq (Sum.Basic.gaussianSum ((paired.sources sheet).map (fun source =>
        source.increment readings.values)) - SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values) (edges.indexedEdges vertices walk sheet)) ≤
        request.partTarget)
    (other : Basic.normSq (Sum.Basic.gaussianSum ((paired.sources (BranchCutLifts.otherSheet sheet)).map (fun source =>
        source.increment readings.values)) - SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (edges.indexedEdges vertices walk (BranchCutLifts.otherSheet sheet))) ≤ request.partTarget) :
    Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (edges.indexedEdges vertices walk sheet) + SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (edges.indexedEdges vertices walk (BranchCutLifts.otherSheet sheet))) ≤ target := by
  have partPositive : 0 < request.partTarget := by
    rw [request.partTarget_eq]
    exact Fraction.Order.Field.div_pos_direct request.positive (by decide)
  have oppositeLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  let first := Sum.Basic.gaussianSum ((paired.sources sheet).map (fun source => source.increment
    readings.values))
  let last := Sum.Basic.gaussianSum ((paired.sources (BranchCutLifts.otherSheet sheet)).map (fun
    source => source.increment readings.values))
  let left := SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh readings.values) (edges.indexedEdges
    vertices walk sheet)
  let right := SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh readings.values) (edges.indexedEdges
    vertices walk (BranchCutLifts.otherSheet sheet))
  have opposite : Basic.normSq (first + last) ≤ request.partTarget := by
    rw
      [sheet_sum]
    apply (Gaussian.Budget.Aggregate.normSq_sum_lt _ partPositive ?_).le
    intro value member
    rw [paired.sums_length]
    exact (request.opposite.term_bound readings paired oppositeLater value member).le
  have middle : Basic.normSq (first + right) ≤ 2 * (request.partTarget + request.partTarget)
    := by
    have estimate := (Bounds.normSq_sub_le_two (first + last) (last - right)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct opposite other) (by decide))
    rw [show first + last - (last - right) = first + right by ring1] at estimate
    exact estimate
  have estimate := (Bounds.normSq_sub_le_two (first + right) (first - left)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct middle outward) (by decide))
  rw [show first + right - (first - left) = left + right by ring1] at estimate
  apply estimate.trans_eq
  rw [request.partTarget_eq]
  exact (by ring1 : 2 * (2 * (target / 10 + target / 10) + target / 10) = target / 10 * 10).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

/-- At the paid common stage the two original opposite-sheet canonical word valuations cancel within the complete
requested squared-norm bound. -/
theorem accurate (request :
  IncrementRequest
  paired domains differential sheet target)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains} (readings :
      TriangleReadings shared mesh)
    (later : request.index ≤ stage) :
    Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh
      readings.values) (edges.indexedEdges vertices walk sheet) +
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh readings.values) (edges.indexedEdges vertices
        walk (BranchCutLifts.otherSheet sheet))) ≤ target := by
  have partPositive : 0 < request.partTarget := by
    rw [request.partTarget_eq]
    exact Fraction.Order.Field.div_pos_direct request.positive (by decide)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have outward :=
    (PuncturedGrid.SourceChartRequests.total_accurate
    partPositive request.outward readings ((Data.Nat.Order.le_max_left _ _).trans chartLater)).le
  have other :=
    (PuncturedGrid.SourceChartRequests.total_accurate
    partPositive request.other readings ((Data.Nat.Order.le_max_right _ _).trans chartLater)).le
  rw [paired.sources_project] at outward other
  exact cancel_accurate request readings later outward other

/-- The two actual signed chart-comparison products for the original selected and opposite sheets. -/
@[expose] def Comparison {polynomial : Option (Ordinary curve.polynomial)}
    (request : IncrementRequest paired domains differential sheet target polynomial) {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  request.outward.Comparisons shared × request.other.Comparisons shared

/-- Execute both original signed chart-comparison products once, sharing the GIVEN polynomial primitive bank. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : IncrementRequest paired domains differential sheet target polynomial) {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    request.Comparison shared :=
  let outward := request.outward.compare shared
  let other := request.other.compare shared
  ⟨outward, other⟩

/-- Actual retained polynomial chart comparisons and true P opposite-sheet requests pay the complete canonical sum. -/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : IncrementRequest paired domains differential sheet target polynomial)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared mesh) (compared : request.Comparison shared)
    (later : request.index ≤ stage) :
    Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (edges.indexedEdges vertices walk sheet) + SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values)
      (edges.indexedEdges vertices walk (BranchCutLifts.otherSheet sheet))) ≤ target := by
  have partPositive : 0 < request.partTarget := by
    rw [request.partTarget_eq]
    exact Fraction.Order.Field.div_pos_direct request.positive (by decide)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have outward := (PuncturedGrid.SourceChartRequests.comparison_total_accurate
    partPositive request.outward readings compared.1 ((Data.Nat.Order.le_max_left _ _).trans chartLater)).le
  have other := (PuncturedGrid.SourceChartRequests.comparison_total_accurate
    partPositive request.other readings compared.2 ((Data.Nat.Order.le_max_right _ _).trans chartLater)).le
  rewrite [paired.sources_project] at outward other
  exact cancel_accurate request readings later outward other

end IncrementRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

end

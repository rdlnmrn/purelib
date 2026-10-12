module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Riemann.Paths.UniformPreparedBoundarySegments

public section

/-! The complete common dyadic mesh supplies every adjacent endpoint equality. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Topology.Chain
open Purelib.Data.List
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint ParameterEdge dyadicEdges)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)

/-- Concatenate the original endpoint-certified parameter paths through their retained common endpoint. -/
private theorem path_append {first last : List Subdivision.ParameterEdge} {start middle finish :
  InverseRootPolynomial.Coordinate}
    (before : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) first
      start middle)
    (after : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) last middle
      finish) :
    PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) (first ++ last)
      start finish := by
  induction before with
  | nil => exact after
  | cons tail ih => exact .cons (ih after)

/-- The original complete dyadic edge spine has the exact supplied first and last parameters. -/
private theorem dyadic_path (depth : Nat) (first last : Subdivision.Endpoint) :
    PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (Subdivision.dyadicEdges depth first last) first.parameter last.parameter := by
  induction depth generalizing first last with
  | zero => exact .cons (.nil _)
  | succ depth ih =>
    exact Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.path_append (ih _ _) (ih _ _)

/-- Every dyadic interval subdivision contains an edge.

The unsplit interval supplies the base edge, and concatenating the two
retained subinterval spines preserves a strictly positive length. -/
private theorem dyadic_nonempty (depth : Nat) (first last : Subdivision.Endpoint) :
    0 < (Subdivision.dyadicEdges depth first last).length := by
  induction depth generalizing first last with
  | zero => exact Nat.zero_lt_succ _
  | succ depth ih =>
      rw [Subdivision.dyadicEdges, Append.length_append]
      exact Nat.lt_of_lt_of_le (ih _ _) (Nat.le_add_right _ _)

/-- The first retained edge of a nonempty original parameter path begins at its exact initial parameter. -/
private theorem path_first {edges : List Subdivision.ParameterEdge} {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) edges start
      finish)
    (nonempty : 0 < edges.length) : (edges[0]'nonempty).left.parameter = start := by
  cases path with
  | nil => exact Fin.elim0 ⟨0, nonempty⟩
  | cons tail => rfl

/-- The last retained edge of a nonempty original parameter path ends at its exact final parameter. -/
private theorem path_last {edges : List Subdivision.ParameterEdge} {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) edges start
      finish)
    (nonempty : 0 < edges.length) : (edges[edges.length - 1]'(by omega0)).right.parameter = finish := by
  induction path with
  | nil => exact Fin.elim0 ⟨0, nonempty⟩
  | @cons edge remaining finish tail ih =>
      cases remaining with
      | nil => cases tail; rfl
      | cons next rest => exact ih (Nat.zero_lt_succ _)

/-- The original nonempty parameter path begins at its retained head edge's left parameter. -/
private theorem path_start {edge : Subdivision.ParameterEdge} {tail : List Subdivision.ParameterEdge} {start finish :
  InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) (edge ::
      tail) start finish) :
    start = edge.left.parameter := by
  cases path
  rfl

/-- Consecutive retained original parameter edges have exactly equal joining parameters. -/
private theorem path_adjacent {edges : List Subdivision.ParameterEdge} {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) edges start
      finish)
    (i : Nat) (bound : i + 1 < edges.length) :
    (edges[i]'(by omega0)).right.parameter = (edges[i + 1]'bound).left.parameter := by
  induction path generalizing i with
  | nil => simp only [List.length_nil] at bound; exact False.elim (Nat.not_lt_zero _ bound)
  | @cons edge remaining finish tail ih =>
      cases i with
      | zero =>
          cases remaining with
          | nil => exact False.elim (Nat.lt_irrefl 1 bound)
          | cons next rest => exact Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.path_start tail
      | succ i => exact ih i (Nat.lt_of_succ_lt_succ bound)

variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}

/-- The complete common dyadic cover has at least one interval.

Its cached interval edges equal the nonempty dyadic subdivision, so the
map length identifies the same positive interval count. -/
theorem CommonCover.nonempty (common : UniformReciprocalCommonCover.CommonCover cover otherCover) : 0 <
  common.intervals.length := by
  have same := congrArg List.length common.edges_eq
  rw [Map.length_map] at same
  exact same.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_nonempty common.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint

/-- The exact bounded index of the first original common-cover interval. -/
@[expose] def CommonCover.firstIndex (common : UniformReciprocalCommonCover.CommonCover cover otherCover) : Fin
  common.intervals.length := ⟨0, common.nonempty⟩
/-- The exact bounded index of the last original common-cover interval. -/
@[expose] def CommonCover.lastIndex (common : UniformReciprocalCommonCover.CommonCover cover otherCover) : Fin
  common.intervals.length :=
  ⟨common.intervals.length - 1, by have positive := common.nonempty; omega0⟩

/-- The first common-cover interval begins at parameter zero.

The explicit first-index bound reads the cached interval and its mapped
edge, whose supplied path relation certifies that initial parameter. -/
theorem CommonCover.first_parameter (common : UniformReciprocalCommonCover.CommonCover cover otherCover) :
    (common.intervals[0]'common.nonempty).edge.left.parameter = 0 := by
  have path := common.edges_eq.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_path
    common.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  have positive : 0 < (common.intervals.map CommonInterval.edge).length := by
    rw [Map.length_map]; exact common.nonempty
  exact (show (common.intervals[0]'common.nonempty).edge.left.parameter =
      ((common.intervals.map CommonInterval.edge)[0]'positive).left.parameter by
          rw [Map.getElem_map CommonInterval.edge common.intervals 0 common.nonempty positive]).trans
    (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.path_first path positive)

/-- The last common-cover interval ends at parameter one.

The cached last-index bound is transported through the edge-map length
before reading that same interval's certified final path parameter. -/
theorem CommonCover.last_parameter (common : UniformReciprocalCommonCover.CommonCover cover otherCover) :
    (common.intervals[common.lastIndex.val]'common.lastIndex.isLt).edge.right.parameter = 1 := by
  have path := common.edges_eq.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_path
    common.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  have positive : 0 < (common.intervals.map CommonInterval.edge).length := by
    rw [Map.length_map]; exact common.nonempty
  have last := Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.path_last path positive
  have mapLength := Map.length_map CommonInterval.edge common.intervals
  have retainedBound : common.intervals.length - 1 < common.intervals.length :=
    common.lastIndex.isLt
  have mappedBound : common.intervals.length - 1 <
      (common.intervals.map CommonInterval.edge).length := mapLength.symm ▸ retainedBound
  have readback := Map.getElem_map CommonInterval.edge common.intervals
    (common.intervals.length - 1) retainedBound mappedBound
  have originalBound : (common.intervals.map CommonInterval.edge).length - 1 <
      (common.intervals.map CommonInterval.edge).length := by omega0
  have indices :
      (⟨(common.intervals.map CommonInterval.edge).length - 1, originalBound⟩ :
        Fin (common.intervals.map CommonInterval.edge).length) =
      ⟨common.intervals.length - 1, mappedBound⟩ :=
    Fin.ext (congrArg (fun size : Nat => size - 1) mapLength)
  have same := congrArg (fun position : Fin (common.intervals.map CommonInterval.edge).length =>
    ((common.intervals.map CommonInterval.edge)[position.val]'position.isLt).right.parameter) indices
  have final := same.symm.trans last
  rw [readback] at final
  exact final

/-- Consecutive common-cover intervals have equal joining parameters.

Both explicit interval bounds read their mapped edges; the retained path
relation certifies the right-to-left junction of those same occurrences. -/
theorem CommonCover.adjacent (common : UniformReciprocalCommonCover.CommonCover cover otherCover)
    (i : Nat) (bound : i + 1 < common.intervals.length) :
    (common.intervals[i]'(by omega0)).edge.right.parameter =
      (common.intervals[i + 1]'bound).edge.left.parameter := by
  have path := common.edges_eq.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_path
    common.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  have bound' : i + 1 < (common.intervals.map CommonInterval.edge).length := by
    simpa only [Map.length_map] using bound
  have joined := Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.path_adjacent path i bound'
  have originalBound : i < common.intervals.length := Nat.lt_trans
    (Nat.lt_succ_self i) bound
  have mappedBound : i < (common.intervals.map CommonInterval.edge).length :=
    (Map.length_map CommonInterval.edge common.intervals).symm ▸ originalBound
  rw [Map.getElem_map CommonInterval.edge common.intervals i originalBound mappedBound,
    Map.getElem_map CommonInterval.edge common.intervals (i + 1) bound bound'] at joined
  exact joined

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Riemann.Branches
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Topology.Chain

/-! The ordered common mesh propagates the retained sheet bit between
adjacent cells. Both complete source/cap comparisons use one signed pair. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (Entry Evaluation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint ParameterEdge dyadicEdges)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)

/-- Concatenate two actual parameter-edge paths at their retained common endpoint. -/
private theorem path_append {first last : List ClearSheetContinuation.Subdivision.ParameterEdge} {start middle finish :
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

/-- A nonempty retained parameter path starts at its actual first edge's left parameter. -/
private theorem path_start {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {tail : List
  ClearSheetContinuation.Subdivision.ParameterEdge} {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter) (edge ::
      tail) start finish) :
    start = edge.left.parameter := by
  cases path
  rfl

/-- The actual dyadic edge list forms a parameter path between the original retained endpoints. -/
private theorem dyadic_path (depth : Nat) (first last : ClearSheetContinuation.Subdivision.Endpoint) :
    PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (ClearSheetContinuation.Subdivision.dyadicEdges depth first last) first.parameter last.parameter := by
  induction depth generalizing first last with
  | zero => exact .cons (.nil _)
  | succ depth ih =>
    exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.path_append (ih _ _) (ih _
      _)

variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {secondCover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage depth : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data stage}
    {otherSource : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive otherData
    stage}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common
    target minimum}

/-- Adjacent retained common intervals have the same actual left flip bit at every stage at least two. -/
theorem Entry.adjacent_sign (first last : CommonRibbonRequest.Entry request sample otherSample source otherSource depth)
    (joined : first.plan.interval.edge.right.parameter = last.plan.interval.edge.left.parameter) (later : 2 ≤ stage) :
    first.left.first.flip = last.left.first.flip := by
  apply first.left.same_parent last.left first.plan.interval.edge.right.parameter
    ⟨first.plan.interval.first.lower.trans first.plan.interval.ordered, first.plan.interval.first.upper⟩ _ later
  rw [joined]
  exact ⟨last.plan.interval.first.lower, last.plan.interval.ordered.trans last.plan.interval.first.upper⟩

/-- Read the actual first retained entry's left flip bit, using false for an empty bank. -/
@[expose] def firstFlip : List (CommonRibbonRequest.Entry request sample otherSample source otherSource depth) → Bool
  | [] => false
  | head :: _ => head.left.first.flip

/-- Every entry of a connected retained parameter path has its actual left flip equal to the first entry's bit. -/
private theorem path_signs (entries : List (CommonRibbonRequest.Entry request sample otherSample source otherSource
  depth))
    {start finish : InverseRootPolynomial.Coordinate}
    (path : PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (entries.map (fun entry => entry.plan.interval.edge)) start finish) (later : 2 ≤ stage) :
    ∀ entry ∈ entries, entry.left.first.flip =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.firstFlip entries := by
  induction entries generalizing start with
  | nil => intro entry member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      cases path with
      | cons tailPath =>
          intro entry member
          rcases Data.List.Membership.mem_cons.mp member with same | member
          · subst entry; rfl
          · cases tail with
            | nil => exact False.elim (List.not_mem_nil member)
            | cons next rest =>
                have joined : head.plan.interval.edge.right.parameter = next.plan.interval.edge.left.parameter :=
                  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.path_start tailPath
                exact (ih tailPath entry member).trans (head.adjacent_sign next joined later).symm

/-- The actual retained common-chart entries form the complete parameter path from zero to one. -/
theorem Evaluation.parameterPath (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source
  otherSource depth) :
    PathBoundary.PathEndpoints (fun edge => edge.left.parameter) (fun edge => edge.right.parameter)
      (evaluated.entries.map (fun entry => entry.plan.interval.edge)) 0 1 := by
  have plans := congrArg (List.map (fun plan => plan.interval.edge)) evaluated.plans_eq
  have intervals := congrArg (List.map CommonInterval.edge) request.intervals_eq
  rw [Data.List.Map.map_map] at plans intervals
  have edges : evaluated.entries.map (fun entry => entry.plan.interval.edge) =
      ClearSheetContinuation.Subdivision.dyadicEdges common.depth UniformPrimitiveMesh.firstEndpoint lastEndpoint :=
    (plans.trans intervals).trans common.edges_eq
  exact edges.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.dyadic_path
    common.depth _ _

/-- The common bit is computed from the first retained entry. Every later entry consumes actual interval adjacency and
the recast-root sign proof. -/
theorem Evaluation.shared_signs (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source
  otherSource depth)
    (later : 2 ≤ stage) (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth) (member
      : entry ∈ evaluated.entries) :
    entry.left.first.flip = Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.firstFlip
      evaluated.entries ∧ entry.right.first.flip =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.firstFlip evaluated.entries :=
      by
  have left := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.path_signs
    evaluated.entries evaluated.parameterPath later entry member
  exact ⟨left, (entry.same_sign later).symm.trans left⟩

namespace Evaluation

set_option genInjectivity false in
/-- One common retained sign choice and its exact two signed polynomial primitives.

The bit is read from the first actual entry; every retained interval uses these same polynomial owners. -/
structure SharedPair (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource depth)
  where
  /-- The cached common flip bit of the actual retained entries. -/ flip : Bool
  /-- The cached bit is exactly the original first retained entry's bit. -/ flip_eq : flip =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.firstFlip evaluated.entries
  /-- The cached first signed polynomial primitive. -/ first : InverseRootPolynomial.Polynomial
  /-- The first cache is exactly the original first primitive, negated precisely when the retained bit is true. -/
    first_eq : first = if flip then -sample.primitive.value else sample.primitive.value
  /-- The cached second signed polynomial primitive. -/ second : InverseRootPolynomial.Polynomial
  /-- The second cache uses the same actual retained bit on the original second primitive. -/ second_eq : second = if
    flip then -otherSample.primitive.value else otherSample.primitive.value
  /-- Every actual retained entry uses this exact first signed polynomial primitive. -/ first_owner : ∀ entry ∈
    evaluated.entries, entry.left.primitive = first
  /-- Every actual retained entry uses this exact second signed polynomial primitive. -/ second_owner : ∀ entry ∈
    evaluated.entries, entry.right.primitive = second

constructive_injectivity SharedPair

/-- Cache the common actual flip bit and both signed primitives, retaining their equality with every original entry
owner. -/
@[expose] def sharedPair (evaluated : CommonRibbonRequest.Evaluation request sample otherSample source otherSource
  depth) (later : 2 ≤ stage) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair evaluated :=
  by
  let flip := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.firstFlip
    evaluated.entries
  refine ⟨flip, rfl, if flip then -sample.primitive.value else sample.primitive.value, rfl,
    if flip then -otherSample.primitive.value else otherSample.primitive.value, rfl, ?_, ?_⟩
  · intro entry member
    rw [entry.left.primitive_eq, (evaluated.shared_signs later entry member).1]
  · intro entry member
    rw [entry.right.primitive_eq, (evaluated.shared_signs later entry member).2]

/-- Subtracting two increments at a fixed original origin cancels that origin exactly. -/
private theorem unanchor (a b c d origin otherOrigin : InverseRootPolynomial.Gaussian) :
    ((b - origin) - (d - otherOrigin)) - ((a - origin) - (c - otherOrigin)) = (b - a) - (d - c) := by ring1

/-- The local estimate now compares increments of the same two polynomials on every common interval; no local primitive
origins occur in the result. -/
theorem SharedPair.increment_errors {evaluated : CommonRibbonRequest.Evaluation request sample otherSample source
  otherSource depth}
    (shared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.SharedPair
      evaluated) (entry : CommonRibbonRequest.Entry request sample otherSample source otherSource depth)
    (member : entry ∈ evaluated.entries) {first last : InverseRootPolynomial.Coordinate}
    (firstInside : entry.plan.interval.edge.left.parameter ≤ first ∧ first ≤ entry.plan.interval.edge.right.parameter)
    (lastInside : entry.plan.interval.edge.left.parameter ≤ last ∧ last ≤ entry.plan.interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      ((source.primitive.value.eval (parent.edge.point last) - source.primitive.value.eval (parent.edge.point first)) -
        (shared.first.eval (parent.edge.point last)⁻¹ - shared.first.eval (parent.edge.point first)⁻¹)) ≤
      Geometric.Basic.quarterRadius
        (RegularComparison.Data.regularScale entry.plan.first) stage * (last - first)^2 ∧
    Data.Gaussian.Norm.Basic.normSq
      ((otherSource.primitive.value.eval (parent.edge.point last) - otherSource.primitive.value.eval (parent.edge.point
        first)) -
        (shared.second.eval (parent.edge.point last)⁻¹ - shared.second.eval (parent.edge.point first)⁻¹)) ≤
      Geometric.Basic.quarterRadius
        (RegularComparison.Data.regularScale entry.plan.second) stage * (last - first)^2 := by
  have left := RegularAlignment.drift_bound source entry.left
    ⟨entry.plan.interval.first.lower.trans firstInside.1, firstInside.2.trans entry.plan.interval.first.upper⟩
    ⟨entry.plan.interval.first.lower.trans lastInside.1, lastInside.2.trans entry.plan.interval.first.upper⟩
  have right := RegularAlignment.drift_bound otherSource entry.right
    ⟨entry.plan.interval.second.lower.trans firstInside.1, firstInside.2.trans entry.plan.interval.second.upper⟩
    ⟨entry.plan.interval.second.lower.trans lastInside.1, lastInside.2.trans entry.plan.interval.second.upper⟩
  dsimp only [CellPrimitive.sourceValue,
    RegularAlignment.capValue] at left right
  rw [shared.first_owner entry member,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.unanchor] at left
  rw [shared.second_owner entry member,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation.unanchor] at right
  exact ⟨left, right⟩

end Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest

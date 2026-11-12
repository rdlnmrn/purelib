module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore.Intervals
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! # The retained whole shifted parent's exact parameter partition

The complete original paid subdivision supplies its zero-to-one endpoint
chain and original weak step ordering. Its same retained centers and parent
list determine the indexed child intervals, including repeated endpoints.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Data.List

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)

/-- The original retained local child at its unchanged ordered bounded occurrence. -/
@[expose] def childAt (index : Fin retained.parents.covered.parents.length) :=
  retained.parents.covered.parents[index.val]'index.isLt

/-- Read the original child's parameter interval without selecting a new partition. -/
@[expose] def intervalAt (index : Fin retained.parents.covered.parents.length) :=
  (retained.childAt index).parameterInterval

/-- The actual complete subdivision's SAME centered children chain the original parameter zero to one. -/
theorem interval_chain : Partition.Interval.Chain 0 1 (List.ofFn retained.intervalAt) := by
  have actual := Riemann.Integration.PreparedSubdivisionModelCore.centeredEdges_chain
    (Fibre.frameCurve target) basis parent.edge.sheet
    retained.acquired.traced.prepared.subdivision retained.parents.centers
  rewrite [retained.acquired.traced.prepared.endpoint_eq] at actual
  have table : List.ofFn retained.intervalAt =
      retained.parents.covered.parents.map
        Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge.parameterInterval :=
    OfFn.Basic.ofFn_map_cast retained.parents.covered.parents rfl _
  rewrite [table, retained.parents.parents_eq]
  exact actual

/-- Each actual local child keeps its original nonnegative accepted parameter width. -/
theorem interval_nonnegative (index : Fin retained.parents.covered.parents.length) :
    0 ≤ (retained.intervalAt index).finish - (retained.intervalAt index).start := by
  have bounded : index.val <
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers).length :=
    Eq.mp (congrArg (fun length => index.val < length)
      (congrArg List.length retained.parents.parents_eq)) index.isLt
  have selected : retained.childAt index =
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers)[index.val]'bounded :=
    getElem_congr retained.parents.parents_eq rfl index.isLt
  have member : retained.childAt index ∈ centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
      retained.acquired.traced.prepared.subdivision retained.parents.centers :=
    selected.symm ▸ List.getElem_mem bounded
  exact Riemann.Integration.PreparedSubdivisionModelCore.centeredEdges_ordered
    (Fibre.frameCurve target) basis parent.edge.sheet retained.acquired.traced.prepared.subdivision
    retained.parents.centers (retained.childAt index) member

/-- The same complete parent's original oriented child widths sum to one, independently of its adaptive child count. -/
theorem sum_widths : Algebra.FiniteSum.Fin.sumFin (fun index =>
    (retained.intervalAt index).finish - (retained.intervalAt index).start) = 1 := by
  exact (Partition.Interval.Chain.sum_widths retained.intervalAt retained.interval_chain).trans (by ring1)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end

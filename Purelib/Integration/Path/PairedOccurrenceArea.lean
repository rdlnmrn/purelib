module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Tactic.Ring

@[expose] public section

/-! Raw paired edge areas retain every displacement from the running
increment origin. The correction is cached with its exact finite readback. -/

namespace Purelib.Integration.Path

namespace PairedOccurrenceArea

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- Compute the ordered signed area offsets of original edge occurrences against an evolving anchor.

Every occurrence keeps its original endpoints; the next anchor advances by that occurrence's exact primitive
displacement. -/
def pairedOffsetTerms {count : Nat} (values : Fin count → Stokes.PrimitivePoint) (anchor : Stokes.PrimitivePoint) :
    List (Stokes.OrientedEdge count) → List Basic.Canonical
  | [] => []
  | edge :: tail =>
      let increment := (Stokes.PrimitivePoint.sub (values edge.finish)) (values edge.start)
      Stokes.edgeArea ((Stokes.PrimitivePoint.sub (values edge.start)) anchor) increment ::
        Purelib.Integration.Path.PairedOccurrenceArea.pairedOffsetTerms values (anchor.add increment) tail

end PairedOccurrenceArea

namespace PairedOccurrenceArea

open Purelib.Topology.Polygon in
/-- Split an original edge area into its displaced anchor edge and the exact signed offset term. -/
private theorem paired_displaced_edge (first last anchor : Stokes.PrimitivePoint) :
    Stokes.edgeArea first last = Stokes.edgeArea anchor (anchor.add ((Stokes.PrimitivePoint.sub last) first)) +
      Stokes.edgeArea ((Stokes.PrimitivePoint.sub first) anchor) ((Stokes.PrimitivePoint.sub last) first) := by
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.add, Stokes.PrimitivePoint.sub]
  ring1

end PairedOccurrenceArea

namespace PairedOccurrenceArea

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The original occurrence area equals the displaced increment-trace area plus the ordered offset sum.

The recursive trace follows the same original edge occurrences and evolving anchor, preserving all signs and repeated
edges. -/
theorem paired_occurrence_area {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    (anchor : Stokes.PrimitivePoint) (edges : List (Stokes.OrientedEdge count)) :
    Stokes.edgeListArea values edges =
      PairedIncrementArea.traceArea anchor
        (edges.map (fun edge => (Stokes.PrimitivePoint.sub (values edge.finish)) (values edge.start))) +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (PairedOccurrenceArea.pairedOffsetTerms values anchor edges) := by
  induction edges generalizing anchor with
  | nil => exact (add_zero 0).symm
  | cons edge tail ih =>
    change Stokes.edgeArea (values edge.start) (values edge.finish) + _ =
      (Stokes.edgeArea anchor (anchor.add ((Stokes.PrimitivePoint.sub (values edge.finish)) (values edge.start))) + _) +
      (Stokes.edgeArea ((Stokes.PrimitivePoint.sub (values edge.start)) anchor) ((Stokes.PrimitivePoint.sub (values
        edge.finish)) (values edge.start)) + _)
    rw [PairedOccurrenceArea.paired_displaced_edge (values edge.start) (values edge.finish) anchor, ih]
    ring1

end PairedOccurrenceArea

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
set_option genInjectivity false in
/-- Cached offsets, correction and raw area for the exact original primitive values and edge occurrences.

The specification equalities retain the zero-anchor offset list and its sum separately from the original raw edge area.
-/
structure PairedOccurrenceArea {count : Nat} (values : Fin count → Stokes.PrimitivePoint)
    (edges : List (Stokes.OrientedEdge count)) where
  /-- The retained ordered signed offset terms. -/ offsets : List Basic.Canonical
  /-- The retained offsets equal the original zero-anchor occurrence offsets. -/ offsets_eq : offsets =
    PairedOccurrenceArea.pairedOffsetTerms values Stokes.PrimitivePoint.zero edges
  /-- The cached sum of the retained offset terms. -/ correction : Basic.Canonical
  /-- The retained correction is exactly the retained offset sum. -/ correction_eq : correction =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum offsets
  /-- The cached raw area of the original edge occurrences. -/ raw : Basic.Canonical
  /-- The retained raw value equals the original occurrence-area sum. -/ raw_eq : raw = Stokes.edgeListArea values edges

constructive_injectivity PairedOccurrenceArea

namespace PairedOccurrenceArea
variable {count : Nat} {values : Fin count → Purelib.Topology.Polygon.Stokes.PrimitivePoint} {edges : List
  (Purelib.Topology.Polygon.Stokes.OrientedEdge count)}

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Compute and retain the exact offset list, correction sum and raw area of the original edge occurrences. -/
def build (values : Fin count → Stokes.PrimitivePoint) (edges : List (Stokes.OrientedEdge count)) :
    PairedOccurrenceArea values edges :=
  let offsets := PairedOccurrenceArea.pairedOffsetTerms values Stokes.PrimitivePoint.zero edges
  ⟨offsets, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum offsets, rfl, Stokes.edgeListArea values edges, rfl⟩

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The cached raw area minus cached correction is the paired area of the exact original occurrence increments. -/
theorem corrected (sample : PairedOccurrenceArea values edges) :
    sample.raw - sample.correction = PairedIncrementArea.area
      (edges.map (fun edge => (Stokes.PrimitivePoint.sub (values edge.finish)) (values edge.start))) := by
  rw [sample.raw_eq, PairedOccurrenceArea.paired_occurrence_area values Stokes.PrimitivePoint.zero,
    sample.correction_eq,
    sample.offsets_eq, add_sub_cancel_right, ← PairedIncrementArea.area_eq_trace]

end PairedOccurrenceArea
end Purelib.Integration.Path

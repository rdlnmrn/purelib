module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Centered area under concatenation retains the polygon of piece endpoints.
The joining edges between distinct owners occur in that polygon unchanged. -/
namespace Purelib.Integration.Path.JoinedCenteredArea

open Purelib.Data.Rat in
/-- The rational carrier for centered-area comparison bounds. -/
private abbrev Coordinate := Fraction.Rational

variable {Vertex : Type} {count : Nat}

section
open Purelib.Integration.Path
/-- Keep the original trace's endpoints as a single-edge vertex trace. -/
def chord (trace : JoinedTrace.VertexTrace Vertex) : JoinedTrace.VertexTrace Vertex := ⟨trace.first, [trace.last]⟩

/-- Concatenate the exact endpoint chords of the original nonempty indexed trace family. -/
def endpointPolygon (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) : JoinedTrace.VertexTrace Vertex :=
  JoinedTrace.VertexTrace.concatenate (fun index => JoinedCenteredArea.chord (traces index))

end

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The endpoint chord's area is the original trace endpoints' cross area. -/
private theorem chord_area (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    (JoinedCenteredArea.chord trace).area values = Stokes.edgeArea (values trace.first) (values trace.last) := by
  change Stokes.edgeArea (values trace.first) (values trace.last) + 0 = _
  rw [add_zero]

open Purelib.Integration.Path in
/-- The concatenated nonempty trace family starts at the first original trace's initial vertex. -/
private theorem first_concatenate (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) :
    (JoinedTrace.VertexTrace.concatenate traces).first = (traces 0).first := JoinedTrace.VertexTrace.glue_first _ _

open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- A retained indexed sample's original area equals the area of its original vertex trace. -/
theorem sample_area (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint)
    (sample : CenteredBilinearPath.Sample (fun vertex => values (trace.indexed vertex))) : sample.originalArea =
      trace.area values :=
  sample.originalArea_eq.trans (trace.indexed_area values)

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The retained sample endpoint correction is the cross area of the original trace endpoints. -/
theorem sample_endpoint (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint)
    (sample : CenteredBilinearPath.Sample (fun vertex => values (trace.indexed vertex))) :
    sample.endpoint = Stokes.edgeArea (values trace.first) (values trace.last) := by
  rw [sample.endpoint_eq]
  change Stokes.edgeArea (values trace.first) ((Stokes.PrimitivePoint.sub (values (DyadicTrace.indexed trace.first
    trace.rest (Fin.last trace.rest.length))))
    (values trace.first)) = _
  rw [DyadicTrace.indexed_last]
  change Stokes.edgeArea (values trace.first) ((Stokes.PrimitivePoint.sub (values trace.last)) (values trace.first)) = _
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
  ring1

open Purelib.Algebra in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The endpoint polygon area is the sum of original chord areas and intervening joining cross areas. -/
theorem endpointPolygon_area (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) (values : Vertex →
  Stokes.PrimitivePoint) :
    (JoinedCenteredArea.endpointPolygon traces).area values =
      FiniteSum.Fin.sumFin (fun index => Stokes.edgeArea (values (traces index).first) (values (traces index).last)) +
        FiniteSum.Fin.sumFin (fun index : Fin count => Stokes.edgeArea (values (traces index.castSucc).last) (values
          (traces index.succ).first)) := by
  rw [JoinedCenteredArea.endpointPolygon, JoinedTrace.VertexTrace.concatenate_area,
    JoinedTrace.VertexTrace.joiningArea_ofFn (fun index => JoinedCenteredArea.chord (traces index)) values,
    FiniteSum.Fin.sumFin_congr (fun index => JoinedCenteredArea.chord_area (traces index) values)]
  rfl

open Purelib.Algebra in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The concatenated centered area is the sum of original piece centered areas and the endpoint polygon's centered area.

The exact trace concatenation equality and all original sample owners are retained; their endpoint corrections cancel
using the common first and last vertices. -/
theorem centered_concatenate (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) (values : Vertex →
  Stokes.PrimitivePoint)
    {combinedTrace : JoinedTrace.VertexTrace Vertex} (equal : combinedTrace = JoinedTrace.VertexTrace.concatenate
      traces)
    (pieces : (index : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => values ((traces index).indexed
      vertex)))
    (combined : CenteredBilinearPath.Sample (fun vertex => values (combinedTrace.indexed vertex)))
    (polygon : CenteredBilinearPath.Sample (fun vertex => values ((JoinedCenteredArea.endpointPolygon traces).indexed
      vertex))) :
    combined.centeredArea = FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) + polygon.centeredArea := by
  cases equal
  have full := JoinedCenteredArea.sample_area (JoinedTrace.VertexTrace.concatenate traces) values combined
  rw [JoinedTrace.VertexTrace.concatenate_area, JoinedTrace.VertexTrace.joiningArea_ofFn] at full
  have pieceAreas := FiniteSum.Fin.sumFin_congr fun index => (JoinedCenteredArea.sample_area (traces index) values
    (pieces index)).symm
  rw [pieceAreas] at full
  have parts : FiniteSum.Fin.sumFin (fun index => (pieces index).originalArea) =
      FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) +
        FiniteSum.Fin.sumFin (fun index => Stokes.edgeArea (values (traces index).first) (values (traces index).last))
          := by
    rw [← FiniteSum.Fin.sumFin_add]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [(pieces index).decomposition, JoinedCenteredArea.sample_endpoint]
  rw [parts] at full
  have coarse := JoinedCenteredArea.sample_area (JoinedCenteredArea.endpointPolygon traces) values polygon
  rw [JoinedCenteredArea.endpointPolygon_area] at coarse
  have endpoint : combined.endpoint = polygon.endpoint := by
    rw [JoinedCenteredArea.sample_endpoint, JoinedCenteredArea.sample_endpoint]
    unfold JoinedCenteredArea.endpointPolygon
    rw [JoinedCenteredArea.first_concatenate, JoinedCenteredArea.first_concatenate,
      JoinedTrace.VertexTrace.concatenate_last, JoinedTrace.VertexTrace.concatenate_last]
    rfl
  have assembled : combined.originalArea = FiniteSum.Fin.sumFin (fun index => (pieces index).centeredArea) +
    polygon.originalArea :=
    full.trans (by rw [coarse]; ring1)
  rw [combined.decomposition, polygon.decomposition, endpoint] at assembled
  exact add_right_cancel (assembled.trans (by ring1))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Bound two concatenated centered areas from the original piece and endpoint-polygon comparisons.

The two vertex carriers and both trace families remain distinct; the estimate is twice squared piece count times the
common piece allowance plus polygon allowance. -/
theorem centered_comparison_bound {Other : Type}
    (first : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) (last : Fin (count + 1) → JoinedTrace.VertexTrace Other)
    (firstValues : Vertex → Stokes.PrimitivePoint) (lastValues : Other → Stokes.PrimitivePoint)
    {firstTrace : JoinedTrace.VertexTrace Vertex} {lastTrace : JoinedTrace.VertexTrace Other}
    (firstEq : firstTrace = JoinedTrace.VertexTrace.concatenate first) (lastEq : lastTrace =
      JoinedTrace.VertexTrace.concatenate last)
    (firstPieces : (index : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => firstValues ((first
      index).indexed vertex)))
    (lastPieces : (index : Fin (count + 1)) → CenteredBilinearPath.Sample (fun vertex => lastValues ((last
      index).indexed vertex)))
    (firstSample : CenteredBilinearPath.Sample (fun vertex => firstValues (firstTrace.indexed vertex)))
    (lastSample : CenteredBilinearPath.Sample (fun vertex => lastValues (lastTrace.indexed vertex)))
    (firstPolygon : CenteredBilinearPath.Sample (fun vertex => firstValues ((JoinedCenteredArea.endpointPolygon
      first).indexed vertex)))
    (lastPolygon : CenteredBilinearPath.Sample (fun vertex => lastValues ((JoinedCenteredArea.endpointPolygon
      last).indexed vertex)))
    {pieceAllowance polygonAllowance : Fraction.Rational}
    (piecesBound : ∀ index, Data.Gaussian.Norm.Basic.normSq
      ((firstPieces index).centeredArea - (lastPieces index).centeredArea) ≤ pieceAllowance)
    (polygonBound : Data.Gaussian.Norm.Basic.normSq
      (firstPolygon.centeredArea - lastPolygon.centeredArea) ≤ polygonAllowance) :
    Data.Gaussian.Norm.Basic.normSq (firstSample.centeredArea - lastSample.centeredArea) ≤
      2 * (((count + 1 : Nat) : Fraction.Rational)^2 * pieceAllowance + polygonAllowance) := by
  have firstArea := JoinedCenteredArea.centered_concatenate first firstValues firstEq firstPieces firstSample
    firstPolygon
  have lastArea := JoinedCenteredArea.centered_concatenate last lastValues lastEq lastPieces lastSample lastPolygon
  have equal : firstSample.centeredArea - lastSample.centeredArea =
      FiniteSum.Fin.sumFin (fun index => (firstPieces index).centeredArea - (lastPieces index).centeredArea) +
        (firstPolygon.centeredArea - lastPolygon.centeredArea) := by
    rw [firstArea, lastArea, FiniteSum.Fin.sumFin_sub]
    ring1
  rw [equal]
  have pieces := Norm.Sum.Indexed.normSq_sumFin_le _ pieceAllowance piecesBound
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct pieces polygonBound) (by decide : (0 : Fraction.Rational) ≤ 2))

end Purelib.Integration.Path.JoinedCenteredArea

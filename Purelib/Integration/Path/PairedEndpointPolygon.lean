module
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Path.JoinedCenteredArea
public import Purelib.Integration.Path.JoinedTraceProperties
import Purelib.Data.Gaussian.Basic

public section

/-! One paired endpoint polygon retains both owner sequences. Its two area
projections are exactly the original endpoint polygons; no trace-length
identification or equality of primitive readings is assumed. -/
namespace Purelib.Integration.Path.PairedEndpointPolygon

open Purelib.Data.List

open Purelib.Integration.Path.JoinedTrace.VertexTrace
  (concatenate concatenate_area concatenate_last joiningArea_ofFn glue_first)

open Purelib.Integration.Path.JoinedCenteredArea
  (chord endpointPolygon endpointPolygon_area sample_area sample_endpoint)

variable {Left Right : Type} {count : Nat}

section
open Purelib.Integration.Path.JoinedTrace.VertexTrace
open Purelib.Integration.Path
/-- Pair the two original traces' initial and terminal vertices into one endpoint chord. -/
@[expose] def pairedChord (first : JoinedTrace.VertexTrace Left) (last : JoinedTrace.VertexTrace Right) :
  JoinedTrace.VertexTrace (Left × Right) :=
  ⟨(first.first, last.first), [(first.last, last.last)]⟩

/-- Concatenate paired endpoint chords from the two original nonempty indexed trace families.

Each paired vertex retains its separate left and right owners at the same original trace index. -/
@[expose] def pairedEndpointPolygon (first : Fin (count + 1) → JoinedTrace.VertexTrace Left)
    (last : Fin (count + 1) → JoinedTrace.VertexTrace Right) : JoinedTrace.VertexTrace (Left × Right) :=
  JoinedTrace.VertexTrace.concatenate (fun index => PairedEndpointPolygon.pairedChord (first index) (last index))

end

open Purelib.Integration.Path.JoinedTrace.VertexTrace in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Read the paired chord area from the exact original initial and terminal vertex pairs. -/
private theorem pairedChord_area (first : JoinedTrace.VertexTrace Left) (last : JoinedTrace.VertexTrace Right)
    (values : Left × Right → Stokes.PrimitivePoint) :
    (PairedEndpointPolygon.pairedChord first last).area values = Stokes.edgeArea (values (first.first, last.first))
      (values (first.last, last.last)) := by
  change Stokes.edgeArea _ _ + 0 = _
  rw [add_zero]
  rfl

section
open Purelib.Integration.Path.JoinedTrace.VertexTrace
open Purelib.Algebra
open Purelib.Integration.Path
open Purelib.Topology.Polygon
/-- Reading the left coordinate of the paired endpoint polygon gives the original left endpoint-polygon area. -/
theorem pairedEndpointPolygon_left_area (first : Fin (count + 1) → JoinedTrace.VertexTrace Left)
    (last : Fin (count + 1) → JoinedTrace.VertexTrace Right) (values : Left → Stokes.PrimitivePoint) :
    (PairedEndpointPolygon.pairedEndpointPolygon first last).area (fun pair => values pair.1) =
      (JoinedCenteredArea.endpointPolygon first).area values := by
  rw [PairedEndpointPolygon.pairedEndpointPolygon, JoinedTrace.VertexTrace.concatenate_area,
    JoinedTrace.VertexTrace.joiningArea_ofFn (fun index => PairedEndpointPolygon.pairedChord (first index) (last
      index)), JoinedCenteredArea.endpointPolygon_area,
    FiniteSum.Fin.sumFin_congr (fun index => PairedEndpointPolygon.pairedChord_area (first index) (last index) (fun pair
      => values pair.1))]
  rfl

/-- Reading the right coordinate of the paired endpoint polygon gives the original right endpoint-polygon area. -/
theorem pairedEndpointPolygon_right_area (first : Fin (count + 1) → JoinedTrace.VertexTrace Left)
    (last : Fin (count + 1) → JoinedTrace.VertexTrace Right) (values : Right → Stokes.PrimitivePoint) :
    (PairedEndpointPolygon.pairedEndpointPolygon first last).area (fun pair => values pair.2) =
      (JoinedCenteredArea.endpointPolygon last).area values := by
  rw [PairedEndpointPolygon.pairedEndpointPolygon, JoinedTrace.VertexTrace.concatenate_area,
    JoinedTrace.VertexTrace.joiningArea_ofFn (fun index => PairedEndpointPolygon.pairedChord (first index) (last
      index)), JoinedCenteredArea.endpointPolygon_area,
    FiniteSum.Fin.sumFin_congr (fun index => PairedEndpointPolygon.pairedChord_area (first index) (last index) (fun pair
      => values pair.2))]
  rfl

end

open Purelib.Integration.Path.JoinedTrace.VertexTrace in
open Purelib.Integration.Path in
/-- A predicate valid on both endpoint pairs holds throughout their paired polygon.

Each retained chord has its original initial pair and one terminal pair.
The indexed concatenation uses the supplied predicate evidence at both. -/
theorem pairedEndpointPolygon_all (first : Fin (count + 1) → JoinedTrace.VertexTrace Left)
    (last : Fin (count + 1) → JoinedTrace.VertexTrace Right) (predicate : Left × Right → Prop)
    (starts : ∀ index, predicate ((first index).first, (last index).first))
    (ends : ∀ index, predicate ((first index).last, (last index).last)) :
    JoinedTraceProperties.All (PairedEndpointPolygon.pairedEndpointPolygon first last) predicate := by
  apply JoinedTraceProperties.concatenate_all
  intro index
  refine ⟨starts index, ?_⟩
  intro vertex member
  have equal : vertex = ((first index).last, (last index).last) := Membership.mem_singleton.mp member
  exact equal.symm ▸ ends index

open Purelib.Integration.Path.JoinedTrace.VertexTrace
open Purelib.Integration.Path
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
/-- The paired polygon's retained left sample has the same centered area as the original left endpoint polygon.

The exact area and endpoint readbacks preserve both sample owners and cancel their matching endpoint corrections. -/
theorem pairedEndpointPolygon_left_centered (first : Fin (count + 1) → JoinedTrace.VertexTrace Left)
    (last : Fin (count + 1) → JoinedTrace.VertexTrace Right) (values : Left → Stokes.PrimitivePoint)
    (paired : CenteredBilinearPath.Sample (fun vertex => values ((PairedEndpointPolygon.pairedEndpointPolygon first
      last).indexed vertex).1))
    (original : CenteredBilinearPath.Sample (fun vertex => values ((JoinedCenteredArea.endpointPolygon first).indexed
      vertex))) :
    paired.centeredArea = original.centeredArea := by
  have area : paired.originalArea = original.originalArea :=
    (JoinedCenteredArea.sample_area _ _ paired).trans ((PairedEndpointPolygon.pairedEndpointPolygon_left_area first last
      values).trans
      (JoinedCenteredArea.sample_area _ _ original).symm)
  have endpoint : paired.endpoint = original.endpoint := by
    rw [JoinedCenteredArea.sample_endpoint (PairedEndpointPolygon.pairedEndpointPolygon first last) (fun pair => values
      pair.1) paired, JoinedCenteredArea.sample_endpoint _ values original]
    unfold PairedEndpointPolygon.pairedEndpointPolygon JoinedCenteredArea.endpointPolygon
    rw [JoinedTrace.VertexTrace.concatenate_last, JoinedTrace.VertexTrace.concatenate_last]
    rw [show (JoinedTrace.VertexTrace.concatenate (fun index => PairedEndpointPolygon.pairedChord (first index) (last
      index))).first =
      ((first 0).first, (last 0).first) from JoinedTrace.VertexTrace.glue_first _ _]
    rw [show (JoinedTrace.VertexTrace.concatenate (fun index => JoinedCenteredArea.chord (first index))).first = (first
      0).first from JoinedTrace.VertexTrace.glue_first _ _]
    rfl
  rw [paired.decomposition, original.decomposition, endpoint] at area
  exact add_right_cancel area

/-- The paired polygon's retained right sample has the same centered area as the original right endpoint polygon.

The exact area and endpoint readbacks preserve both sample owners and cancel their matching endpoint corrections. -/
theorem pairedEndpointPolygon_right_centered (first : Fin (count + 1) → JoinedTrace.VertexTrace Left)
    (last : Fin (count + 1) → JoinedTrace.VertexTrace Right) (values : Right → Stokes.PrimitivePoint)
    (paired : CenteredBilinearPath.Sample (fun vertex => values ((PairedEndpointPolygon.pairedEndpointPolygon first
      last).indexed vertex).2))
    (original : CenteredBilinearPath.Sample (fun vertex => values ((JoinedCenteredArea.endpointPolygon last).indexed
      vertex))) :
    paired.centeredArea = original.centeredArea := by
  have area : paired.originalArea = original.originalArea :=
    (JoinedCenteredArea.sample_area _ _ paired).trans ((PairedEndpointPolygon.pairedEndpointPolygon_right_area first
      last values).trans
      (JoinedCenteredArea.sample_area _ _ original).symm)
  have endpoint : paired.endpoint = original.endpoint := by
    rw [JoinedCenteredArea.sample_endpoint (PairedEndpointPolygon.pairedEndpointPolygon first last) (fun pair => values
      pair.2) paired, JoinedCenteredArea.sample_endpoint _ values original]
    unfold PairedEndpointPolygon.pairedEndpointPolygon JoinedCenteredArea.endpointPolygon
    rw [JoinedTrace.VertexTrace.concatenate_last, JoinedTrace.VertexTrace.concatenate_last]
    rw [show (JoinedTrace.VertexTrace.concatenate (fun index => PairedEndpointPolygon.pairedChord (first index) (last
      index))).first =
      ((first 0).first, (last 0).first) from JoinedTrace.VertexTrace.glue_first _ _]
    rw [show (JoinedTrace.VertexTrace.concatenate (fun index => JoinedCenteredArea.chord (last index))).first = (last
      0).first from JoinedTrace.VertexTrace.glue_first _ _]
    rfl
  rw [paired.decomposition, original.decomposition, endpoint] at area
  exact add_right_cancel area

end Purelib.Integration.Path.PairedEndpointPolygon

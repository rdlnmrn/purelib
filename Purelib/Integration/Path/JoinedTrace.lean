module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Tactic.Ring

public section

/-! Concatenation retains the joining edge between distinct owner readings,
even when the two readings have the same physical coordinate. -/
namespace Purelib.Integration.Path.JoinedTrace
open Purelib.Algebra
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Data.Gaussian
open Purelib.Integration.Path

open Purelib.Data.List

set_option genInjectivity false in
/-- A nonempty ordered vertex trace represented by its original first vertex and tail list.

The retained head supplies the initial occurrence even for an empty tail. Every
tail occurrence keeps its original order, including repeated vertex labels. -/
structure VertexTrace (Vertex : Type) where
  /-- The original initial vertex of this nonempty trace. -/ first : Vertex
  /-- The ordered original vertices following the initial vertex. -/ rest : List Vertex

constructive_injectivity VertexTrace

namespace VertexTrace

variable {Vertex : Type}

/-- Read the retained trace's terminal vertex, using its first vertex when the tail is empty. -/
@[expose] def last (trace : JoinedTrace.VertexTrace Vertex) : Vertex := Dyadic.DyadicTrace.terminal trace.first
  trace.rest

/-- Sum the original trace's consecutive primitive-point edge areas. -/
@[expose] def area (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) : Basic.Canonical
  :=
  Dyadic.DyadicTrace.areaFrom values trace.first trace.rest

/-- Read an original trace vertex at its retained finite index. -/
@[expose] def indexed (trace : JoinedTrace.VertexTrace Vertex) (vertex : Fin (trace.rest.length + 1)) : Vertex :=
  Dyadic.DyadicTrace.indexed trace.first trace.rest vertex

/-- The indexed vertex path has the same area as the original ordered trace. -/
theorem indexed_area (trace : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    CenteredBilinearPath.area (fun vertex => values (trace.indexed vertex)) = trace.area values :=
  Dyadic.DyadicTrace.indexed_area values trace.first trace.rest

/-- Retain a nonempty indexed vertex family as its first vertex and ordered successor list. -/
@[expose] def ofIndexed {count : Nat} (vertices : Fin (count + 1) → Vertex) : JoinedTrace.VertexTrace Vertex :=
  ⟨vertices 0, List.ofFn (fun index : Fin count => vertices index.succ)⟩

/-- Converting an indexed vertex family to a trace preserves its exact path area. -/
theorem ofIndexed_area {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    (JoinedTrace.VertexTrace.ofIndexed vertices).area values = CenteredBilinearPath.area (fun vertex => values (vertices
      vertex)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      dsimp only [JoinedTrace.VertexTrace.ofIndexed, JoinedTrace.VertexTrace.area]
      rw [OfFn.Basic.ofFn_succ, Dyadic.DyadicTrace.areaFrom, CenteredBilinearPath.area,
        FiniteSum.Fin.sumFin_succ]
      exact congrArg (Stokes.edgeArea (values (vertices 0)) (values (vertices (0 : Fin (count + 1)).succ)) + ·)
        (ih (fun vertex => vertices vertex.succ))

/-- The converted trace's terminal vertex is the original family's last vertex. -/
theorem ofIndexed_last {count : Nat} (vertices : Fin (count + 1) → Vertex) :
    (JoinedTrace.VertexTrace.ofIndexed vertices).last = vertices (Fin.last count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      dsimp only [JoinedTrace.VertexTrace.ofIndexed, last]
      rw [OfFn.Basic.ofFn_succ]
      exact ih (fun vertex => vertices vertex.succ)

/-- Join two original traces, retaining both boundary vertices and the explicit edge between them.

The first trace tail is followed by the second trace first vertex and tail, even when the two boundary vertices have
equal readings. -/
@[expose] def join (first last : JoinedTrace.VertexTrace Vertex) : JoinedTrace.VertexTrace Vertex :=
  ⟨first.first, first.rest ++ last.first :: last.rest⟩

/-- The joined trace ends at the original second trace's terminal vertex. -/
theorem join_last (first last : JoinedTrace.VertexTrace Vertex) : (first.join last).last = last.last := by
  dsimp only [JoinedTrace.VertexTrace.join, JoinedTrace.VertexTrace.last]
  rw [Dyadic.DyadicTrace.terminal_append]
  rfl

/-- Joining traces adds their areas and the joining edge area between their original boundary vertices. -/
theorem join_area (first last : JoinedTrace.VertexTrace Vertex) (values : Vertex → Stokes.PrimitivePoint) :
    (first.join last).area values = first.area values + Stokes.edgeArea (values first.last) (values last.first) +
      last.area values := by
  dsimp only [JoinedTrace.VertexTrace.join, JoinedTrace.VertexTrace.area, JoinedTrace.VertexTrace.last]
  rw [Dyadic.DyadicTrace.areaFrom_append]
  simp only [Dyadic.DyadicTrace.areaFrom]
  ring1

/-- Join a retained first trace with an ordered list of further traces, keeping every joining edge. -/
@[expose] def glue (first : JoinedTrace.VertexTrace Vertex) : List (JoinedTrace.VertexTrace Vertex) →
  JoinedTrace.VertexTrace Vertex
  | [] => first
  | next :: rest => first.join (Purelib.Integration.Path.JoinedTrace.VertexTrace.glue next rest)

/-- Gluing traces preserves the original first vertex. -/
theorem glue_first (first : JoinedTrace.VertexTrace Vertex) (rest : List (JoinedTrace.VertexTrace Vertex)) :
    (first.glue rest).first = first.first := by
  cases rest <;> rfl

/-- Sum the areas of the explicit edges joining successive original traces. -/
@[expose] def joiningArea (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace Vertex) : List
  (JoinedTrace.VertexTrace Vertex) → Basic.Canonical
  | [] => 0
  | next :: rest => Stokes.edgeArea (values first.last) (values next.first) +
    Purelib.Integration.Path.JoinedTrace.VertexTrace.joiningArea values next rest

/-- The glued trace area is the sum of original trace areas plus the exact joining-edge area.

The original component traces remain in order. Their internal areas and the areas of the explicit edges between
components are separate terms. -/
theorem glue_area (values : Vertex → Stokes.PrimitivePoint) (first : JoinedTrace.VertexTrace Vertex) (rest : List
  (JoinedTrace.VertexTrace Vertex)) :
    (first.glue rest).area values = Data.Gaussian.Norm.Sum.Basic.gaussianSum ((first :: rest).map (fun trace =>
      trace.area
      values)) + JoinedTrace.VertexTrace.joiningArea values first rest := by
  induction rest generalizing first with
  | nil => change first.area values = first.area values + 0 + 0; ring1
  | cons next rest ih =>
      rw [JoinedTrace.VertexTrace.glue, JoinedTrace.VertexTrace.join_area, JoinedTrace.VertexTrace.glue_first, ih]
      change first.area values + Stokes.edgeArea (values first.last) (values next.first) +
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum ((next :: rest).map (fun trace => trace.area values)) +
            JoinedTrace.VertexTrace.joiningArea values next rest) =
        first.area values + Data.Gaussian.Norm.Sum.Basic.gaussianSum ((next :: rest).map (fun trace => trace.area
          values)) +
          (Stokes.edgeArea (values first.last) (values next.first) + JoinedTrace.VertexTrace.joiningArea values next
            rest)
      ring1

/-- Summing a Gaussian list built from a finite family agrees with the original finite sum. -/
private theorem sum_ofFn {count : Nat} (values : Fin count → Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn values) = FiniteSum.Fin.sumFin values := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      exact congrArg (values 0 + ·) (ih (fun index => values index.succ))

/-- Join a nonempty indexed family of traces in its original finite order. -/
@[expose] def concatenate {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) :
  JoinedTrace.VertexTrace Vertex :=
  (traces 0).glue (List.ofFn (fun index : Fin count => traces index.succ))

/-- The concatenated trace ends at the last original trace's terminal vertex. -/
theorem concatenate_last {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) :
    (JoinedTrace.VertexTrace.concatenate traces).last = (traces (Fin.last count)).last := by
  induction count with
  | zero => rfl
  | succ count ih =>
      unfold JoinedTrace.VertexTrace.concatenate
      rw [OfFn.Basic.ofFn_succ, JoinedTrace.VertexTrace.glue, JoinedTrace.VertexTrace.join_last]
      exact ih (fun index => traces index.succ)

/-- The concatenated trace area equals the finite sum of component areas plus the retained joining-edge sum. -/
theorem concatenate_area {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) (values : Vertex →
  Stokes.PrimitivePoint) :
    (JoinedTrace.VertexTrace.concatenate traces).area values = FiniteSum.Fin.sumFin (fun index => (traces index).area
      values) +
      JoinedTrace.VertexTrace.joiningArea values (traces 0) (List.ofFn (fun index : Fin count => traces index.succ)) :=
        by
  rw [JoinedTrace.VertexTrace.concatenate, JoinedTrace.VertexTrace.glue_area, List.map_cons, OfFn.Basic.map_ofFn,
    FiniteSum.Fin.sumFin_succ]
  change (traces 0).area values + Data.Gaussian.Norm.Sum.Basic.gaussianSum _ + _ = _
  rw [JoinedTrace.VertexTrace.sum_ofFn]
  rfl

/-- The ordered joining-edge sum equals the finite sum of areas between adjacent original traces. -/
theorem joiningArea_ofFn {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) (values : Vertex →
  Stokes.PrimitivePoint) :
    JoinedTrace.VertexTrace.joiningArea values (traces 0) (List.ofFn (fun index : Fin count => traces index.succ)) =
      FiniteSum.Fin.sumFin (fun index : Fin count =>
        Stokes.edgeArea (values (traces index.castSucc).last) (values (traces index.succ).first)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, JoinedTrace.VertexTrace.joiningArea, FiniteSum.Fin.sumFin_succ]
      exact congrArg (Stokes.edgeArea (values (traces 0).last) (values (traces (0 : Fin (count + 1)).succ).first) + ·)
        (ih (fun index => traces index.succ))

end VertexTrace
end Purelib.Integration.Path.JoinedTrace

end

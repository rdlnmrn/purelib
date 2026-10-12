module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.Dyadic.DyadicTrace
public import Purelib.Integration.Path.JoinedTrace
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Purelib.Tactic.Ring

public section

/-! Monotone finite trace concatenation retains coincident junction vertices.
Its signed coordinate increments are nonnegative and telescope exactly. -/
namespace Purelib.Integration.Path.TraceLengths
open Purelib.Data
open Purelib.Algebra
open Purelib.Integration.Path.Dyadic.DyadicTrace
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path
open Purelib.Data.Rat

open Purelib.Data.List

open scoped Purelib.Data.Nat

/-- The rational carrier for original trace coordinates and lengths. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Integration.Path.JoinedTrace (VertexTrace)

open Purelib.Integration.Path.Dyadic.DyadicTrace (terminal indexed tail tail_terminal)

namespace Dyadic

/-- The original coordinate never decreases along the retained ordered vertex list. -/
@[expose] def Forward {Vertex : Type} (coordinate : Vertex → Fraction.Rational) : Vertex → List Vertex → Prop
  | _, [] => True
  | first, next :: rest => coordinate first ≤ coordinate next ∧ Purelib.Integration.Path.TraceLengths.Dyadic.Forward
    coordinate next rest

/-- Concatenating original coordinate-monotone lists preserves monotonicity at their shared terminal. -/
theorem forward_append {Vertex : Type} (coordinate : Vertex → Fraction.Rational)
    (first : Vertex) (left right : List Vertex)
    (hl : TraceLengths.Dyadic.Forward coordinate first left) (hr : TraceLengths.Dyadic.Forward coordinate
      (DyadicTrace.terminal first left) right) :
    TraceLengths.Dyadic.Forward coordinate first (left ++ right) := by
  induction left generalizing first with
  | nil => exact hr
  | cons next rest ih => exact ⟨hl.1, ih next hl.2 hr⟩

/-- A retained forward list has nondecreasing coordinates on every exact indexed edge.

The original finite coordinate is split into its first edge or retained successor edge. The supplied forward certificate
is consumed along that same ordered list spine. -/
theorem forward_indexed {Vertex : Type} (coordinate : Vertex → Fraction.Rational)
    (first : Vertex) (rest : List Vertex) (forward : TraceLengths.Dyadic.Forward coordinate first rest)
    (edge : Fin rest.length) :
    coordinate (DyadicTrace.indexed first rest edge.castSucc) ≤ coordinate (DyadicTrace.indexed first rest edge.succ) :=
      by
  induction rest generalizing first with
  | nil => exact Fin.elim0 edge
  | cons next rest ih =>
    refine Purelib.Data.Fin.cases_induction (motive := fun edge => coordinate (DyadicTrace.indexed first (next :: rest)
      edge.castSucc) ≤ coordinate (DyadicTrace.indexed first (next :: rest) edge.succ)) forward.1 (fun index => ?_) edge
    exact ih next forward.2 index

open Purelib.Geometry.Rectangle.Partition in
/-- Dyadic targets between ordered original endpoints form a forward coordinate list. -/
theorem tail_forward (depth : Nat) {first last : Fraction.Rational} (ordered : first ≤ last) :
    TraceLengths.Dyadic.Forward id first (tail depth first last) := by
  induction depth generalizing first last with
  | zero => exact ⟨ordered, trivial⟩
  | succ depth ih =>
    have between := PreparedBoxPartitions.midpoint_between ordered
    apply TraceLengths.Dyadic.forward_append id first _ _ (ih between.1)
    rw [DyadicTrace.tail_terminal]
    exact ih between.2

end Dyadic

namespace VertexTrace
variable {Vertex : Type}

/-- The original vertex trace has nondecreasing coordinates in its retained vertex order. -/
@[expose] def Ordered (trace : JoinedTrace.VertexTrace Vertex) (coordinate : Vertex → Fraction.Rational) : Prop :=
  TraceLengths.Dyadic.Forward coordinate trace.first trace.rest

/-- Joining the original ordered traces preserves coordinate order when the exact join endpoints are ordered. -/
theorem ordered_join (first last : JoinedTrace.VertexTrace Vertex) (coordinate : Vertex → Fraction.Rational)
    (hf : TraceLengths.VertexTrace.Ordered first coordinate) (hl : TraceLengths.VertexTrace.Ordered last coordinate)
    (joined : coordinate first.last ≤ coordinate last.first) :
    TraceLengths.VertexTrace.Ordered (first.join last) coordinate :=
  TraceLengths.Dyadic.forward_append coordinate first.first first.rest (last.first :: last.rest) hf ⟨joined, hl⟩

/-- Pointwise coordinate order on the original indexed edges gives an ordered retained trace. -/
theorem ordered_ofIndexed {count : Nat} (vertices : Fin (count + 1) → Vertex)
    (coordinate : Vertex → Fraction.Rational)
    (ordered : ∀ edge : Fin count, coordinate (vertices edge.castSucc) ≤ coordinate (vertices edge.succ)) :
    TraceLengths.VertexTrace.Ordered (JoinedTrace.VertexTrace.ofIndexed vertices) coordinate := by
  induction count with
  | zero => trivial
  | succ count ih =>
    change TraceLengths.Dyadic.Forward coordinate (vertices 0) (List.ofFn (fun index : Fin (count + 1) => vertices
      index.succ))
    rw [OfFn.Basic.ofFn_succ]
    exact ⟨ordered 0, ih (fun vertex => vertices vertex.succ) (fun edge => ordered edge.succ)⟩

/-- Concatenating original ordered traces preserves order under their retained join-endpoint inequalities. -/
theorem ordered_concatenate {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (coordinate : Vertex → Fraction.Rational) (ordered : ∀ index, TraceLengths.VertexTrace.Ordered (traces index)
      coordinate)
    (joined : ∀ edge : Fin count, coordinate (traces edge.castSucc).last ≤ coordinate (traces edge.succ).first) :
    TraceLengths.VertexTrace.Ordered (JoinedTrace.VertexTrace.concatenate traces) coordinate := by
  induction count with
  | zero => exact ordered 0
  | succ count ih =>
    unfold JoinedTrace.VertexTrace.concatenate
    rw [OfFn.Basic.ofFn_succ, JoinedTrace.VertexTrace.glue]
    apply TraceLengths.VertexTrace.ordered_join _ _ coordinate (ordered 0)
    · exact ih (fun index => traces index.succ) (fun index => ordered index.succ) (fun edge => joined edge.succ)
    · rw [JoinedTrace.VertexTrace.glue_first]
      exact joined 0

/-- A retained ordered trace has nondecreasing coordinates at each exact indexed edge. -/
theorem ordered_indexed (trace : JoinedTrace.VertexTrace Vertex) (coordinate : Vertex → Fraction.Rational)
    (ordered : TraceLengths.VertexTrace.Ordered trace coordinate) (edge : Fin trace.rest.length) :
    coordinate (trace.indexed edge.castSucc) ≤ coordinate (trace.indexed edge.succ) :=
  TraceLengths.Dyadic.forward_indexed coordinate trace.first trace.rest ordered edge

set_option genInjectivity false in
/-- Cached nonnegative coordinate lengths and total for the exact original ordered trace.

The original edge indices determine each coordinate difference, and the total equals both the retained finite sum and
original endpoint difference. -/
structure Lengths (trace : JoinedTrace.VertexTrace Vertex) (coordinate : Vertex → Fraction.Rational) where
  /-- The cached rational lengths indexed by the exact original trace edges. -/ values : Data.Vector
    Fraction.Rational trace.rest.length
  /-- Each cached length is the original successor-minus-predecessor coordinate difference. -/ values_eq : ∀ edge,
    values edge = coordinate (trace.indexed edge.succ) - coordinate (trace.indexed edge.castSucc)
  /-- Every retained edge length is nonnegative. -/ nonnegative : ∀ edge, 0 ≤ values edge
  /-- The cached total coordinate length. -/ total : Fraction.Rational
  /-- The cached total equals the finite sum of the retained lengths. -/ total_eq : total = FiniteSum.Fin.sumFin values
  /-- The cached total equals the original terminal-minus-initial coordinate difference. -/ endpoints : total =
    coordinate trace.last - coordinate trace.first

constructive_injectivity Lengths

/-- The finite sum of the original indexed coordinate increments equals the endpoint difference.

Each successor step cancels the shared coordinate between its first increment and retained tail sum. The count, finite
edge indices and outer endpoint values stay unchanged. -/
theorem scalar_telescope {count : Nat} (values : Fin (count + 1) → Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun edge : Fin count => values edge.succ - values edge.castSucc) = values (Fin.last count) -
      values 0 := by
  induction count with
  | zero => change 0 = values 0 - values 0; ring1
  | succ count ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    have tail := ih (fun vertex => values vertex.succ)
    change values (Fin.succ (0 : Fin (count + 1))) - values 0 +
      FiniteSum.Fin.sumFin (fun edge : Fin count => values edge.succ.succ - values edge.castSucc.succ) = _
    rw [tail]
    change values (Fin.succ (0 : Fin (count + 1))) - values 0 +
      (values (Fin.last (count + 1)) - values (Fin.succ (0 : Fin (count + 1)))) = _
    ring1

namespace Lengths
variable {trace : Purelib.Integration.Path.JoinedTrace.VertexTrace Vertex} {coordinate : Vertex →
  Purelib.Data.Rat.Fraction.Rational}

/-- Cache the coordinate lengths of the original ordered trace and their exact telescoped total.

The retained vector uses the original edge indices; order proves each entry nonnegative and the total keeps the original
endpoints. -/
@[expose] def build (trace : JoinedTrace.VertexTrace Vertex) (coordinate : Vertex → Fraction.Rational) (ordered :
  TraceLengths.VertexTrace.Ordered trace coordinate) :
    TraceLengths.VertexTrace.Lengths trace coordinate := by
  let values := Vector.Basic.vectorOfFn fun edge : Fin trace.rest.length =>
    coordinate (trace.indexed edge.succ) - coordinate (trace.indexed edge.castSucc)
  refine ⟨values, Vector.Basic.vectorOfFn_apply _, ?_, coordinate trace.last - coordinate trace.first, ?_, rfl⟩
  · intro edge
    rw [Vector.Basic.vectorOfFn_apply]
    exact Fraction.Order.Arithmetic.sub_nonneg_direct (TraceLengths.VertexTrace.ordered_indexed trace coordinate ordered
      edge)
  · have readback := FiniteSum.Fin.sumFin_congr (fun edge : Fin trace.rest.length =>
      Vector.Basic.vectorOfFn_apply (fun edge : Fin trace.rest.length =>
        coordinate (trace.indexed edge.succ) - coordinate (trace.indexed edge.castSucc)) edge)
    change coordinate trace.last - coordinate trace.first = FiniteSum.Fin.sumFin values
    rw [readback, TraceLengths.VertexTrace.scalar_telescope (fun vertex => coordinate (trace.indexed vertex))]
    rw [show trace.indexed (Fin.last trace.rest.length) = trace.last from DyadicTrace.indexed_last trace.first
      trace.rest]
    rfl

end Lengths
end VertexTrace
end Purelib.Integration.Path.TraceLengths

end

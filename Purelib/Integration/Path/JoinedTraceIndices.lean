module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.List.Append
public import Purelib.Data.List.OfFn.Basic

import Purelib.Integration.Path.Dyadic.DyadicTrace
public import Purelib.Integration.Path.JoinedTrace

public section

/-! Positional inclusions into a joined trace. Equal vertex labels are not
searched or deduplicated: the two junction occurrences remain distinct. -/
namespace Purelib.Integration.Path.JoinedTraceIndices

open Purelib.Data
open Purelib.Data.List
open Purelib.Integration.Path
open scoped Purelib.Data.Nat

variable {Vertex : Type}

/-- Equal lists have equal bounded readings at the same natural index, regardless of the supplied bound proofs. -/
theorem readAt_eq_of_list_eq {Item : Type} {left right : List Item} (equal : left = right)
    (index : Nat) (leftBound : index < left.length) (rightBound : index < right.length) :
    left[index]'leftBound = right[index]'rightBound := by
  cases equal
  rfl

set_option genInjectivity false in
/-- An index map from the exact part trace to the exact whole trace preserving every original vertex reading.

Both the part and whole are the original trace owners. The certificate specifies the exact mapped indices and pointwise
readback; it imposes no separate injectivity condition. -/
structure Embedding (part whole : JoinedTrace.VertexTrace Vertex) where
  /-- The retained map from original part indices to original whole indices. -/ index : Fin (part.rest.length + 1) → Fin
    (whole.rest.length + 1)
  /-- Each mapped whole index reads exactly the original part vertex. -/ indexed_eq : ∀ vertex, whole.indexed (index
    vertex) = part.indexed vertex

constructive_injectivity Embedding

/-- The joined trace's vertex count is the sum of the two original vertex counts.

The concatenation retains both original heads and both ordered tails. In particular, the two junction occurrences
contribute separately to the total vertex count. -/
private theorem join_length (first last : JoinedTrace.VertexTrace Vertex) :
    (first.join last).rest.length + 1 = (first.rest.length + 1) + (last.rest.length + 1) := by
  simp only [JoinedTrace.VertexTrace.join, Append.length_append, List.length_cons]
  exact Nat.add_right_comm _ _ _

/-- Embed every original left trace vertex into the joined trace at the unchanged finite index.

The exact left vertex count bounds each original coordinate inside the joined trace. Bounded readback into the unchanged
left prefix certifies that same occurrence. -/
def leftEmbedding (first last : JoinedTrace.VertexTrace Vertex) : JoinedTraceIndices.Embedding first (first.join last)
  where
  index vertex := ⟨vertex.val, by
    rw [JoinedTraceIndices.join_length]
    exact Nat.lt_of_lt_of_le vertex.isLt (Nat.le_add_right _ _)⟩
  indexed_eq vertex := by
    change ((first.first :: first.rest) ++ (last.first :: last.rest))[vertex.val]'_ =
      (first.first :: first.rest)[vertex.val]'vertex.isLt
    exact Append.getElem_append_left (first.first :: first.rest) (last.first :: last.rest) vertex.val vertex.isLt _

/-- Embed every original right trace vertex into the joined trace at its exact left-vertex-count offset.

The complete left vertex count supplies the retained offset. Bounded readback into the unchanged right list certifies
the original right occurrence. -/
def rightEmbedding (first last : JoinedTrace.VertexTrace Vertex) : JoinedTraceIndices.Embedding last (first.join last)
  where
  index vertex := ⟨first.rest.length + 1 + vertex.val, by
    rw [JoinedTraceIndices.join_length]
    exact Nat.add_lt_add_left vertex.isLt _⟩
  indexed_eq vertex := by
    change ((first.first :: first.rest) ++ (last.first :: last.rest))[first.rest.length + 1 + vertex.val]'_ =
      (last.first :: last.rest)[vertex.val]'vertex.isLt
    exact Append.getElem_append_right (first.first :: first.rest) (last.first :: last.rest) vertex.val vertex.isLt _

/-- Compose retained trace embeddings through their original intermediate owner.

The retained index maps compose through the exact middle trace. Their two readback certificates identify the same
original vertex after both mapped positions. -/
def Embedding.trans {first middle last : JoinedTrace.VertexTrace Vertex}
    (left : JoinedTraceIndices.Embedding first middle) (right : JoinedTraceIndices.Embedding middle last) :
      JoinedTraceIndices.Embedding first last :=
  ⟨fun vertex => right.index (left.index vertex),
    fun vertex => (right.indexed_eq (left.index vertex)).trans (left.indexed_eq vertex)⟩

/-- Transport an embedding along equality of its exact whole trace owner. -/
def Embedding.castWhole {part first last : JoinedTrace.VertexTrace Vertex} (embedding : JoinedTraceIndices.Embedding
  part first)
    (equal : first = last) : JoinedTraceIndices.Embedding part last := equal ▸ embedding

/-- Embed the original first trace into its glued trace without changing its vertex indices.

An empty tail preserves the original identity index map. A nonempty tail reuses the exact joining embedding into its
cached glued trace. -/
def glueHead (first : JoinedTrace.VertexTrace Vertex) (rest : List (JoinedTrace.VertexTrace Vertex)) :
  JoinedTraceIndices.Embedding first (first.glue rest) :=
  match rest with
  | [] => ⟨fun vertex => vertex, fun _ => rfl⟩
  | next :: rest => JoinedTraceIndices.leftEmbedding first (next.glue rest)

/-- Embed a retained trace occurrence, selected by its original list index, into the exact glued trace.

The recursion preserves the selected occurrence and composes the actual joining embeddings through the original trace
owners. -/
def glueEntry (first : JoinedTrace.VertexTrace Vertex) (rest : List (JoinedTrace.VertexTrace Vertex)) :
    (position : Fin (rest.length + 1)) → JoinedTraceIndices.Embedding ((first :: rest)[position.val]'position.isLt)
      (first.glue rest) :=
  match rest with
  | [] => fun position => Fin.casesDependent
      (motive := fun position : Fin 1 => JoinedTraceIndices.Embedding
        ((first :: [])[position.val]'position.isLt) (first.glue []))
      ⟨fun vertex => vertex, fun _ => rfl⟩ (fun impossible => Fin.elim0 impossible) position
  | next :: rest => fun position => Fin.casesDependent
      (motive := fun position : Fin ((next :: rest).length + 1) => JoinedTraceIndices.Embedding
        ((first :: next :: rest)[position.val]'position.isLt) (first.glue (next :: rest)))
      (JoinedTraceIndices.glueHead first (next :: rest))
      (fun tail => (Purelib.Integration.Path.JoinedTraceIndices.glueEntry next rest tail).trans
        (JoinedTraceIndices.rightEmbedding first (next.glue rest))) position

/-- Reading the retained trace built from an indexed family recovers the original family at the same bounded index.

The retained function table has exactly the original finite domain size. Its head-and-tail materialization equation
transports the supplied bounded coordinate without replacing the indexed family. -/
theorem ofIndexed_indexed {count : Nat} (vertices : Fin (count + 1) → Vertex)
    (vertex : Fin ((JoinedTrace.VertexTrace.ofIndexed vertices).rest.length + 1)) :
    (JoinedTrace.VertexTrace.ofIndexed vertices).indexed vertex = vertices ⟨vertex.val, by
      have bound := vertex.isLt
      simpa only [JoinedTrace.VertexTrace.ofIndexed, OfFn.Basic.length_ofFn] using bound⟩ := by
  change (vertices 0 :: List.ofFn (fun entry : Fin count => vertices entry.succ))[vertex.val]'_ = _
  have bound : vertex.val < count + 1 := by simpa only [JoinedTrace.VertexTrace.ofIndexed, OfFn.Basic.length_ofFn] using
    vertex.isLt
  exact (JoinedTraceIndices.readAt_eq_of_list_eq (OfFn.Basic.ofFn_succ (function := vertices)).symm vertex.val _
    (by rw [OfFn.Basic.length_ofFn]; exact bound)).trans (OfFn.Basic.getElem_ofFn _ ⟨_, bound⟩ _)

/-- Embed a selected original indexed trace into the exact concatenated trace.

The selected original trace occurrence is retained through its finite list position. The embedding uses the
concatenation construction and transports the exact occurrence equality. -/
def concatenateEntry {count : Nat} (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex)
    (position : Fin (count + 1)) : JoinedTraceIndices.Embedding (traces position) (JoinedTrace.VertexTrace.concatenate
      traces) := by
  let rest := List.ofFn (fun index : Fin count => traces index.succ)
  have lengthEq : rest.length + 1 = count + 1 := by
    dsimp only [rest]
    rewrite [OfFn.Basic.length_ofFn]
    exact Eq.refl _
  let index := Fin.cast lengthEq.symm position
  have entryEq : (traces 0 :: rest)[index.val]'index.isLt = traces position := by
    change (traces 0 :: List.ofFn (fun entry : Fin count => traces entry.succ))[position.val]'_ = _
    exact (JoinedTraceIndices.readAt_eq_of_list_eq (OfFn.Basic.ofFn_succ (function := traces)).symm position.val _
      (by rw [OfFn.Basic.length_ofFn]; exact position.isLt)).trans (OfFn.Basic.getElem_ofFn _ position _)
  exact Eq.mp (congrArg (fun part => JoinedTraceIndices.Embedding part (JoinedTrace.VertexTrace.concatenate traces))
    entryEq)
    (JoinedTraceIndices.glueEntry (traces 0) rest index)

/-- Map an original finite-family vertex through its retained trace embedding into the whole trace.

The materialized table length supplies the bound for the same original natural coordinate. The existing embedding maps
this retained coordinate into its exact whole trace. -/
def Embedding.indexOfIndexed {count : Nat} {vertices : Fin (count + 1) → Vertex} {whole : JoinedTrace.VertexTrace
  Vertex}
    (embedding : JoinedTraceIndices.Embedding (JoinedTrace.VertexTrace.ofIndexed vertices) whole) (vertex : Fin (count +
      1)) : Fin (whole.rest.length + 1) :=
  embedding.index ⟨vertex.val, by simpa only [JoinedTrace.VertexTrace.ofIndexed, OfFn.Basic.length_ofFn] using
    vertex.isLt⟩

/-- The mapped whole-trace index reads the exact original finite-family vertex. -/
theorem Embedding.indexOfIndexed_eq {count : Nat} {vertices : Fin (count + 1) → Vertex} {whole : JoinedTrace.VertexTrace
  Vertex}
    (embedding : JoinedTraceIndices.Embedding (JoinedTrace.VertexTrace.ofIndexed vertices) whole) (vertex : Fin (count +
      1)) :
    whole.indexed (embedding.indexOfIndexed vertex) = vertices vertex :=
  (embedding.indexed_eq _).trans (JoinedTraceIndices.ofIndexed_indexed vertices _)

/-- Embed the two original junction endpoints into the whole trace using the retained left and right embeddings.

The zero coordinate selects the retained left endpoint occurrence and the other coordinate selects the retained right
occurrence. Equal vertex labels never merge their original index positions. -/
def junctionEmbedding {first last whole : JoinedTrace.VertexTrace Vertex}
    (left : JoinedTraceIndices.Embedding first whole) (right : JoinedTraceIndices.Embedding last whole) :
    JoinedTraceIndices.Embedding (JoinedTrace.VertexTrace.ofIndexed (fun vertex : Fin 2 => if vertex.val = 0 then
      first.last else last.first)) whole where
  index vertex := if vertex.val = 0 then left.index (Fin.last first.rest.length) else right.index 0
  indexed_eq vertex := by
    rw [JoinedTraceIndices.ofIndexed_indexed]
    by_cases zero : vertex.val = 0
    · rewrite [if_pos zero, if_pos zero]
      exact (left.indexed_eq (Fin.last first.rest.length)).trans (Dyadic.DyadicTrace.indexed_last first.first
        first.rest)
    · rewrite [if_neg zero, if_neg zero]
      exact right.indexed_eq 0

end Purelib.Integration.Path.JoinedTraceIndices

end

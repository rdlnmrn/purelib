module
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.VertexRotation
import Purelib.Topology.Surface.Word.Vertices
public import Purelib.Topology.Surface.Word.VertexSurgery
public import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Word.Selection

open Purelib.LinearAlgebra.Alternating

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.VertexRotation

open Purelib.Topology.Surface.Word.VertexSurgery

@[expose] public section

/-!
# Vertex identifications along the retained word-surgery trace

Reconstruct the original finite vertex presentation from a presentation of
the terminal word. Every step uses its stored literal rotation and handle
split. Universal factorization and coverage are preserved, so no vertex
vertex classes cannot disappear or be invented along the trace.
-/

namespace Purelib.Topology.Surface.Chord.WordVertexTrace

open Purelib.Topology.Surface.Word.Surgery (IntegralWordSignature)
open Purelib.Topology.Surface.Word.NormalForm (WordSurgeryTrace)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Vertices (WordVertexModel)

variable {count size : Nat}

/-- Reconstruct the original word's finite vertex model along its retained surgery trace.

Each handle step uses the stored cut, occurrence counts, and reverse rotation while preserving the terminal carrier
size. -/
def restoreVertices : {word : List (SignedWord.SignedGenerator count)} → {integral : Surgery.IntegralWordSignature word}
  →
    {pivots : List (Handle.Basic.PivotIndices count)} →
    (trace : NormalForm.WordSurgeryTrace word integral pivots) → Vertices.WordVertexModel trace.terminalWord size →
      Vertices.WordVertexModel word size
  | _, _, _, .zero .., terminal => terminal
  | _, _, _, .handle selected unique _ _ tail, terminal =>
      WordVertexModel.rotate
        (InterlacedWord.restoreVertexModel selected.cut (Purelib.Topology.Surface.Chord.WordVertexTrace.restoreVertices
          tail terminal) (selected.counts unique))
        (WordRotation.symm selected.rotation)

open Purelib.Topology.Surface.Chord in
/-- Original and terminal vertex models along the same word-surgery trace have equal carrier sizes. -/
theorem vertex_count_eq {word : List (SignedWord.SignedGenerator count)} {integral : Surgery.IntegralWordSignature word}
    {pivots : List (Handle.Basic.PivotIndices count)} (trace : NormalForm.WordSurgeryTrace word integral pivots)
    (original : Vertices.WordVertexModel word size) {terminalSize : Nat} (terminal : Vertices.WordVertexModel
      trace.terminalWord terminalSize) :
    size = terminalSize := original.size_eq (WordVertexTrace.restoreVertices trace terminal)

end Purelib.Topology.Surface.Chord.WordVertexTrace

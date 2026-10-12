module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Ring.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
public import Purelib.Integration.Energy.Polygon

import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Cut.CoordinatePairing
public import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Cut.WordArea

public section

/-! Exact matrix readback of the complete projected cut increment sequence. -/
namespace Purelib.Topology.Surface.Cut.ValuationMatrix

open Purelib.Data.List
open Purelib.Algebra.Ring
open Purelib.Data.Gaussian

open Purelib

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open Purelib.Data.Gaussian.Basic (conj_add)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates (combine)
open Purelib.Topology.Surface.Word.Pairing (Coefficients traceArea Signature contract linear)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Surface.Cut.CoordinatePairing (linear_energyPrimitivePoint edgeArea_energyPrimitivePoint)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry CutBoundaryWord)

namespace Word

/-- The primitive-point trace of Gaussian energy coordinates equals the Gaussian increment trace area.

Each original coefficient row supplies the same Gaussian increment. Structural word induction transports the unchanged
remaining rows and their retained starting point. -/
theorem traceArea_energy {count : Nat} (values : Fin count → Data.Gaussian.Basic.Canonical)
    (word : List (Topology.Surface.Word.Pairing.Coefficients count)) (start : Data.Gaussian.Basic.Canonical) :
    Topology.Surface.Word.Pairing.traceArea (fun index => Integration.Energy.Polygon.energyPrimitivePoint (values
      index)) (Integration.Energy.Polygon.energyPrimitivePoint start) word =
      Integration.Path.IncrementArea.traceArea start (word.map (fun letter =>
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (fun index => letter index) values)) := by
  induction word generalizing start with
  | nil => rfl
  | cons letter rest ih =>
      rw [Topology.Surface.Word.Pairing.traceArea, Topology.Surface.Cut.CoordinatePairing.linear_energyPrimitivePoint]
      have added : (Integration.Energy.Polygon.energyPrimitivePoint start).add
        (Integration.Energy.Polygon.energyPrimitivePoint
        (Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine letter values)) =
          Integration.Energy.Polygon.energyPrimitivePoint (start +
            Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine letter values) :=
        congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (Data.Gaussian.Basic.conj_add _ _).symm rfl
      rw [added, ih, Topology.Surface.Cut.CoordinatePairing.edgeArea_energyPrimitivePoint]
      rfl

open Purelib in
/-- Starting the entire increment trace at zero reads precisely the cached matrix.

The signature retains the original total row and matrix. The zero primitive point contributes no initial edge area, so
the complete ordered trace reads that same matrix contraction. -/
theorem Signature.contract_energy {count : Nat} {word : List (Topology.Surface.Word.Pairing.Coefficients count)}
    (signature : Topology.Surface.Word.Pairing.Signature word) (values : Fin count → Data.Gaussian.Basic.Canonical) :
    Topology.Surface.Word.Pairing.contract (fun row column => signature.matrix row column) (fun index =>
      Integration.Energy.Polygon.energyPrimitivePoint (values index)) =
      Integration.Path.IncrementArea.pathArea (word.map (fun letter =>
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (fun index => letter index) values)) := by
  have trace := signature.traceArea_eq (fun index => Integration.Energy.Polygon.energyPrimitivePoint (values index))
    Topology.Polygon.Stokes.PrimitivePoint.zero
  have initial : Topology.Polygon.Stokes.edgeArea Topology.Polygon.Stokes.PrimitivePoint.zero
      (Topology.Surface.Word.Pairing.linear signature.total (fun index =>
        Integration.Energy.Polygon.energyPrimitivePoint (values index))) = 0 := by
    dsimp only [Topology.Polygon.Stokes.edgeArea, Topology.Polygon.Stokes.PrimitivePoint.zero]
    rw [Basic.zero_mul, Basic.mul_zero]
    rfl
  rw [initial, zero_add] at trace
  exact trace.symm.trans (Topology.Surface.Cut.ValuationMatrix.Word.traceArea_energy values word 0)

end Word

/-- Evaluating one signed-generator coefficient row gives its generator value with the retained orientation sign.

The bounded generator index selects its original coefficient slot. The retained Boolean orientation chooses its sign,
while every other finite slot contributes zero. -/
theorem SignedGenerator.combine_value {count : Nat} (letter : Topology.Surface.Word.SignedWord.SignedGenerator count)
    (values : Fin count → Data.Gaussian.Basic.Canonical) :
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine letter.coefficients values = if
      letter.reversed then -values letter.index else values letter.index := by
  have expanded : Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine letter.coefficients values =
      Algebra.FiniteSum.Fin.sumFin (fun index => if index = letter.index then
        (if letter.reversed then -values index else values index) else 0) := by
    apply Algebra.FiniteSum.Fin.sumFin_congr
    intro index
    rw [Topology.Surface.Word.SignedWord.SignedGenerator.coefficients, Data.Vector.Basic.vectorOfFn_apply]
    by_cases same : index = letter.index
    · rw [if_pos same, if_pos same]
      cases direction : letter.reversed with
      | false =>
          rw [if_neg (by intro impossible; nomatch impossible),
            if_neg (by intro impossible; nomatch impossible), Int.cast_one, Basic.one_mul]
      | true =>
          rw [if_pos (Eq.refl true), if_pos (Eq.refl true)]
          change ((Int.negSucc 0 : Int) : Data.Gaussian.Basic.Canonical) * values index = -values index
          rw [IntCast.cast_negSucc]
          change -(1 : Data.Gaussian.Basic.Canonical) * values index = -values index
          rw [Multiplication.neg_mul, Basic.one_mul]
    · rw [if_neg same, if_neg same, IntCast.cast_zero, Basic.zero_mul]
  exact expanded.trans (Algebra.FiniteSum.Fin.sumFin_ite_eq letter.index _)

variable {source target count : Nat} {labels : Fin source → Fin target}
  {generators : Data.Vector (Topology.Polygon.Stokes.OrientedEdge source) count}

open Purelib in
/-- An antisymmetric projected edge reading agrees with its retained signed-generator combination.

The original cut entry supplies its projected-edge equation. The supplied reversal law transports its retained sign
without replacing the generator values. -/
theorem CutWordEntry.value_eq_combine (entry : Topology.Surface.Cut.BoundaryWord.CutWordEntry labels generators)
    (value : Topology.Polygon.Stokes.OrientedEdge target → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels entry.edge) =
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine entry.letter.coefficients (fun index =>
        value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels (generators index))) := by
  rw [entry.projected_eq, Topology.Surface.Cut.ValuationMatrix.SignedGenerator.combine_value entry.letter]
  cases direction : entry.letter.reversed with
  | false =>
      rw [if_neg (by intro impossible; nomatch impossible),
        if_neg (by intro impossible; nomatch impossible)]
  | true =>
      rw [if_pos (Eq.refl true), if_pos (Eq.refl true)]
      exact anti _

namespace CutBoundaryWord
variable {edges : List (Topology.Polygon.Stokes.OrientedEdge source)} (word :
  Topology.Surface.Cut.BoundaryWord.CutBoundaryWord labels edges)

open Purelib
/-- Every increment, including repeated and reversed occurrences, is retained in order.

The original alphabet equations identify the edge and coefficient lists. Mapping their displayed entries preserves every
occurrence and evaluates its same retained signed coefficient row. -/
theorem projected_values_eq (value : Topology.Polygon.Stokes.OrientedEdge target → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    (edges.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)).map value =
      word.coefficients.map (fun letter => Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (fun
        index => letter index)
        (fun index => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels (word.alphabet.generators
          index)))) := by
  apply Eq.trans (congrArg (fun items => (items.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)).map
    value) word.alphabet.edges_eq.symm)
  rw [word.coefficients_eq, word.letters_eq]
  rw [Map.map_map, Map.map_map, Map.map_map, Map.map_map]
  dsimp only [Function.comp_def]
  exact Data.List.Map.map_congr_left (fun entry _ => Topology.Surface.Cut.ValuationMatrix.CutWordEntry.value_eq_combine
    entry value anti)

/-- The complete projected boundary word area is the cached signature-matrix contraction on generator readings.

The supplied antisymmetry certificate identifies each original projected increment. Their complete ordered list is
evaluated using the same retained signature and Gaussian generator readings. -/
theorem wordArea_eq_contract (value : Topology.Polygon.Stokes.OrientedEdge target → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Topology.Mesh.RetracingWords.wordArea value (edges.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      labels)) =
      Topology.Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column)
        (fun index => Integration.Energy.Polygon.energyPrimitivePoint (value
          (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels (word.alphabet.generators index)))) := by
  unfold Topology.Mesh.RetracingWords.wordArea
  rw [Topology.Surface.Cut.ValuationMatrix.CutBoundaryWord.projected_values_eq word value anti]
  exact (Topology.Surface.Cut.ValuationMatrix.Word.Signature.contract_energy word.signature _).symm

end CutBoundaryWord
end Purelib.Topology.Surface.Cut.ValuationMatrix

end

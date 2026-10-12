module
public import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Mesh.CornerWalks
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Cut.PairingKernel
public import Purelib.Topology.Surface.Word.GeneratorValuations
import Purelib.LinearAlgebra.Vector.Weighted
import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
public import Purelib.LinearAlgebra.Alternating.NormalForm.Spanning
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.LinearAlgebra.Matrix.Integral.RowSpan
import Mathlib.Data.Int.Cast.Defs

/-!
# Constructive integral spanning of actual closed surface words

The finite kernel tests of the retained unit normal form are realized as
actual antisymmetric edge valuations. Cut-surface completeness discharges
them, producing integer row coefficients with an explicit physical part.
No search success, abstract homology basis, or analytic vanishing premise
is supplied by the caller.
-/

public section
open Purelib.Algebra.Ring

section

open Purelib
open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra.Vector
open Purelib.Topology.Chain
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryPairs
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Cut.PairingKernel.SewingForest
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewingConnected
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.GeneratorValuations

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Mesh.CornerWalks (VertexConnection)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.LinearAlgebra
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open Purelib.LinearAlgebra.Vector.Weighted (weighted)

namespace Purelib.Topology.Surface.Cut.Spanning

/-- Casting a finite integer sum into Gaussian coordinates commutes with the sum. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((FiniteSum.Fin.sumFin values : Int) : Gaussian.Basic.Canonical) = FiniteSum.Fin.sumFin (fun index => (values index
      : Gaussian.Basic.Canonical)) := by
  induction count with
  | zero => exact IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, IntCast.add, ih]

end Purelib.Topology.Surface.Cut.Spanning

namespace Purelib.Topology.Surface.Cut.Spanning

open Purelib.Topology.Surface.Cut in
/-- Gaussian evaluation of integer weights agrees with the cast of the corresponding integer combination. -/
private theorem cast_weighted {count : Nat} (weights : Fin count → Int)
    (values : Data.Vector Int count) :
    ((Weighted.weighted weights values : Int) : Gaussian.Basic.Canonical) = WordCoordinates.combine weights (fun index
      => (values index : Gaussian.Basic.Canonical)) := by
  rw [Weighted.weighted, cast_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  exact Ring.IntCast.intCast_mul _ _

/-- The real coordinate of a Gaussian integer cast is its rational cast. -/
private theorem gaussian_int_re (value : Int) :
    (value : Gaussian.Basic.Canonical).re = (value : Fraction.Rational) := by
  cases value with
  | ofNat value =>
      change (((value : Nat) : Int) : Gaussian.Basic.Canonical).re = (((value : Nat) : Int) : Fraction.Rational)
      rw [Int.cast_natCast, Cast.natCast_re, Int.cast_natCast]
  | negSucc value => rw [IntCast.cast_negSucc, Gaussian.Basic.neg_re,
      Cast.natCast_re, IntCast.cast_negSucc]

end Purelib.Topology.Surface.Cut.Spanning

namespace Purelib.Topology.Surface.Cut.Spanning

open Purelib.Topology.Surface.Cut in
/-- A zero Gaussian integer cast has zero original integer value. -/
private theorem gaussian_int_zero {value : Int} (zero : (value : Gaussian.Basic.Canonical) = 0) : value = 0 := by
  apply Fraction.Cast.Compatibility.intCast_injective_direct
  have realPart := congrArg (fun z : Gaussian.Basic.Canonical => z.re) zero
  rw [gaussian_int_re] at realPart
  exact realPart

end Purelib.Topology.Surface.Cut.Spanning

section

variable {source target : Nat} {labels : Fin source → Fin target} {boundary : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels boundary}

namespace Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing

set_option genInjectivity false in
/-- Exact coordinates in the paired rows, retaining every physical term. Both vectors are cached executable integers,
not a mere span proposition. -/
structure SpanningCoordinates (integral : IntegralPairing word)
    (row : Data.Vector Int word.alphabet.count) where
  /-- Retained integer coefficients for the original paired matrix rows. -/ coefficients : Data.Vector Int
    word.alphabet.count
  /-- Retained part of the original row supported on one-sided generators. -/ physical : Data.Vector Int
    word.alphabet.count
  /-- Physical coordinates equal the original row; paired coordinates are zero. -/ physical_eq : ∀ column, physical
    column = if word.alphabet.oneSided column then row column else 0
  /-- The original row is exactly the paired-row combination plus the retained physical remainder. -/ equation : ∀
    column, row column =
    FiniteSum.Fin.sumFin (fun index => coefficients index * integral.paired index column) + physical column

constructive_injectivity SpanningCoordinates

end Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing

namespace Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates

/-- Evaluate the retained row decomposition as paired-row and physical Gaussian contributions. -/
theorem value_eq {integral : IntegralPairing word}
    {row : Data.Vector Int word.alphabet.count}
    (span : SpanningCoordinates integral row) (values : Fin word.alphabet.count →
      Gaussian.Basic.Canonical) :
    WordCoordinates.combine row values =
      WordCoordinates.combine span.coefficients (fun index => WordCoordinates.combine (integral.paired index) values) +
        WordCoordinates.combine span.physical values := by
  calc
    _ = FiniteSum.Fin.sumFin (fun column =>
        FiniteSum.Fin.sumFin (fun index => (span.coefficients index : Gaussian.Basic.Canonical) * (integral.paired index
          column : Gaussian.Basic.Canonical) * values column) +
          (span.physical column : Gaussian.Basic.Canonical) * values column) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [span.equation, IntCast.add, add_mul, cast_sum, ← FiniteSum.Fin.sumFin_mul_right]
      apply congrArg (· + (span.physical column : Gaussian.Basic.Canonical) * values column)
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [Ring.IntCast.intCast_mul]
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_swap]
      apply congrArg (· + WordCoordinates.combine span.physical values)
      apply FiniteSum.Fin.sumFin_congr
      intro index
      exact (FiniteSum.Fin.sumFin_congr (fun column => _root_.mul_assoc _ _ _)).trans (FiniteSum.Fin.sumFin_mul_left _
        _)

end Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates

namespace Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing

/-- The paired matrix block vanishes in every one-sided generator column. -/
private theorem physical_column (integral : IntegralPairing word) (row column : Fin word.alphabet.count)
    (side : word.alphabet.oneSided column = true) : integral.paired row column = 0 := by
  rw [integral.paired_eq, side, Bool.or_true]
  rfl

end Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing

namespace Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord in
/-- Construct finite row-span coordinates from an annihilation certificate. The surface constructor below supplies that
certificate from closed words. -/
@[expose] def spanningOfAnnihilation (integral : IntegralPairing word)
    {raw : List (Handle.Basic.PivotIndices word.alphabet.count)} (normal : LinearAlgebra.Alternating.NormalForm
      integral.paired
      raw)
    (row : Data.Vector Int word.alphabet.count)
    (annihilates : ∀ values : Fin word.alphabet.count → Gaussian.Basic.Canonical,
      (∀ index, word.alphabet.oneSided index = true → values index = 0) →
      (∀ index, word.alphabet.oneSided index = false → WordCoordinates.combine (integral.paired index) values = 0) →
      WordCoordinates.combine row values = 0) : SpanningCoordinates integral row := by
  have castSum {count : Nat} (entries : Fin count → Int) :
      ((FiniteSum.Fin.sumFin entries : Int) : Gaussian.Basic.Canonical) =
        FiniteSum.Fin.sumFin (fun index => (entries index : Gaussian.Basic.Canonical)) := by
    induction count with
    | zero => exact IntCast.cast_zero
    | succ count ih => rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, IntCast.add, ih]
  have castWeighted {count : Nat} (weights : Fin count → Int)
      (entries : Data.Vector Int count) :
      ((Weighted.weighted weights entries : Int) : Gaussian.Basic.Canonical) =
        WordCoordinates.combine
          weights (fun index => (entries index : Gaussian.Basic.Canonical)) := by
    rw [Weighted.weighted, castSum]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    exact Ring.IntCast.intCast_mul _ _
  have gaussianIntRe (value : Int) :
      (value : Gaussian.Basic.Canonical).re =
        (value : Fraction.Rational) := by
    cases value with
    | ofNat value =>
        change (((value : Nat) : Int) : Gaussian.Basic.Canonical).re =
          (((value : Nat) : Int) : Fraction.Rational)
        rw [Int.cast_natCast, Cast.natCast_re, Int.cast_natCast]
    | negSucc value => rw [IntCast.cast_negSucc, Gaussian.Basic.neg_re,
        Cast.natCast_re, IntCast.cast_negSucc]
  have gaussianIntZero {value : Int} (zero : (value : Gaussian.Basic.Canonical) = 0) :
      value = 0 := by
    apply Fraction.Cast.Compatibility.intCast_injective_direct
    have realPart := congrArg (fun z : Gaussian.Basic.Canonical => z.re) zero
    rw [gaussianIntRe] at realPart
    exact realPart
  let restricted := Data.Vector.Basic.vectorOfFn fun index => if word.alphabet.oneSided index then (0 : Int) else row
    index
  have tests : ∀ index, index ∉ Handle.Basic.handleIndices raw →
      Weighted.weighted restricted (normal.reduction.cycleRows index) = 0 := by
    intro index unused
    let test := normal.reduction.cycleRows index
    let values := fun column => if word.alphabet.oneSided column then (0 : Gaussian.Basic.Canonical) else (test column :
      Gaussian.Basic.Canonical)
    have physical (column : Fin word.alphabet.count) (side : word.alphabet.oneSided column = true) : values column = 0
      := by
      dsimp only [values]
      rw [side]
      rfl
    have kernel (row : Fin word.alphabet.count) : WordCoordinates.combine (integral.paired row) values = 0 := by
      calc
        _ = WordCoordinates.combine (integral.paired row) (fun column => (test column : Gaussian.Basic.Canonical)) := by
          apply FiniteSum.Fin.sumFin_congr
          intro column
          cases side : word.alphabet.oneSided column
          · change _ * (if word.alphabet.oneSided column then 0 else (test column : Gaussian.Basic.Canonical)) = _
            rw [side]
            rfl
          · rw [physical_column integral row column side, IntCast.cast_zero, zero_mul, zero_mul]
        _ = ((Weighted.weighted (integral.paired row) test : Int) : Gaussian.Basic.Canonical) := (castWeighted _
          test).symm
        _ = 0 := by rw [normal.unused_kernel index unused row, IntCast.cast_zero]
    have evaluated : WordCoordinates.combine row values = ((Weighted.weighted restricted test : Int) :
      Gaussian.Basic.Canonical) := by
      rw [castWeighted]
      apply FiniteSum.Fin.sumFin_congr
      intro column
      change (row column : Gaussian.Basic.Canonical) * (if word.alphabet.oneSided column then 0 else (test column :
        Gaussian.Basic.Canonical)) = _
      rw [Data.Vector.Basic.vectorOfFn_apply]
      cases word.alphabet.oneSided column
      · rfl
      · change (row column : Gaussian.Basic.Canonical) * 0 = ((0 : Int) : Gaussian.Basic.Canonical) * (test column :
          Gaussian.Basic.Canonical)
        rw [mul_zero, IntCast.cast_zero, zero_mul]
    exact gaussianIntZero (evaluated.symm.trans (annihilates values physical (fun row _ => kernel row)))
  let span := normal.rowSpan restricted tests
  let physical := Data.Vector.Basic.vectorOfFn fun column => if word.alphabet.oneSided column then row column else (0 :
    Int)
  refine ⟨span.coefficients, physical, fun column => Data.Vector.Basic.vectorOfFn_apply _ column, fun column => ?_⟩
  rw [← span.equation, Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  cases word.alphabet.oneSided column
  · exact (add_zero _).symm
  · exact (zero_add _).symm

end Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing

end

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {forest : Topology.Surface.Sewing.SewingForest faces}

namespace Purelib.Topology.Surface.Cut.Spanning.SewingForest.SinglePolygon

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord in
/-- Construct actual integral row coordinates for any retained closed word. The only topology input is the vertex-star
connection already supplied by the root-backed grid; no guessed cycle basis is assumed. -/
@[expose] def closed_spanning (polygon : SewingForest.SinglePolygon forest)
    (unique : (Stokes.triangleEdgeOccurrences faces).Nodup)
    (nonloop : ∀ edge ∈ Stokes.triangleEdgeOccurrences faces, edge.start ≠ edge.finish)
    (connected : CornerWalks.VertexConnection faces)
    (pairing : ProjectedEdgePairs.ProjectedEdgePairing polygon.patch.cut.vertexLabels polygon.patch.cut.boundary)
    (integral : IntegralPairing (ProjectedEdgePairing.boundaryWord pairing))
    {raw : List (Handle.Basic.PivotIndices (ProjectedEdgePairing.boundaryWord pairing).alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm integral.paired raw)
    {edges : List (Stokes.OrientedEdge vertexCount)} {anchor : Fin vertexCount}
    (coordinates : BoundaryCoordinates.WordCoordinates (ProjectedEdgePairing.boundaryWord pairing).alphabet edges)
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (supported : CutPath.Supported polygon.patch.boundary edges) :
    IntegralPairing.SpanningCoordinates integral coordinates.totals := by
  apply IntegralPairing.spanningOfAnnihilation integral normal coordinates.totals
  intro values physical kernel
  have cutUnique : (polygon.patch.cut.boundary.map (OrientedEdge.map polygon.patch.cut.vertexLabels)).Nodup := by
    rw [polygon.patch.cut.boundary_eq]
    exact SewnPatch.boundary_unique polygon.patch (SinglePolygon.originalEdges_unique polygon unique)
  let value := ProjectedEdgePairing.generatorValue pairing values
  have zero := SinglePolygon.closed_value_zero_of_kernel polygon unique nonloop connected pairing integral value
    (ProjectedEdgePairing.generatorValue_reverse pairing values) (ProjectedEdgePairing.generatorValue_physical pairing
      cutUnique values physical)
    (fun index paired => (FiniteSum.Fin.sumFin_congr (fun column => by
      dsimp only [value]
      rw [ProjectedEdgePairing.generatorValue_generator pairing cutUnique])).trans (kernel index paired)) closed
        supported
  calc
    _ = WordCoordinates.combine coordinates.totals
        (fun column => value (OrientedEdge.map polygon.patch.cut.vertexLabels ((ProjectedEdgePairing.boundaryWord
          pairing).alphabet.generators column))) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      dsimp only [value]
      rw [ProjectedEdgePairing.generatorValue_generator pairing cutUnique]
    _ = SewingRetraction.wordValue value edges := (WordCoordinates.value_eq coordinates value
      (ProjectedEdgePairing.generatorValue_reverse pairing values)).symm
    _ = 0 := zero

end Purelib.Topology.Surface.Cut.Spanning.SewingForest.SinglePolygon

end

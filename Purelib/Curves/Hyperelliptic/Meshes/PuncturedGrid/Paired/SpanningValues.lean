module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
open Purelib.Algebra.Ring

open Purelib

open Purelib.Algebra

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-! Actual word reconstruction from cached A/B coefficients, with all correction values retained. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows (BasisCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates (combine)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue FaceTerm)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_swap sumFin_mul_left sumFin_mul_right
  sumFin_zero)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues

/-- Casting an integer finite sum into the Gaussian field commutes with the original finite sum. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((sumFin values : Int) : Data.Gaussian.Basic.Canonical) = sumFin (fun index => (values index :
      Data.Gaussian.Basic.Canonical)) := by
  induction count with
  | zero => exact IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ, IntCast.add, ih]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  {cut : CutBank prepared} {word : List
    (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
  {row : ClosedCoordinates word cut.integral}
    (coordinates : BasisCoordinates cut row)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

/-- The retained closed-row coordinates split its actual combined value into the original A and B basis contributions
and physical remainder. -/
theorem combine_eq (values
  : Fin lifted.cutBoundaryWord.alphabet.count → Data.Gaussian.Basic.Canonical) :
    WordCoordinates.combine row.coordinates.totals values = sumFin (fun index : Fin genus =>
      ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine
        (cut.rows.get
        index).a.coordinates.totals values +
      ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine
        (cut.rows.get
        index).b.coordinates.totals values) +
      WordCoordinates.combine coordinates.physical values := by
  calc
    _ = sumFin (fun column => sumFin (fun index : Fin genus =>
        (((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * ((cut.rows.get
          index).a.coordinates.totals
          column : Data.Gaussian.Basic.Canonical) +
          ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * ((cut.rows.get
            index).b.coordinates.totals column : Data.Gaussian.Basic.Canonical)) * values column) +
        ((Data.Vector.get coordinates.physical column : Int) : Data.Gaussian.Basic.Canonical) * values column) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [coordinates.equation column, IntCast.add, add_mul,
        Paired.SpanningValues.cast_sum, ← FiniteSum.Fin.sumFin_mul_right]
      apply congrArg (· + ((Data.Vector.get coordinates.physical column : Int) : Data.Gaussian.Basic.Canonical) * values
        column)
      exact FiniteSum.Fin.sumFin_congr (fun index => by
          rw [IntCast.add, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_mul])
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_swap]
      apply congrArg (· + WordCoordinates.combine coordinates.physical values)
      apply FiniteSum.Fin.sumFin_congr
      intro index
      calc
        _ = sumFin (fun column =>
            ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * (((cut.rows.get
              index).a.coordinates.totals column : Data.Gaussian.Basic.Canonical) * values column) +
            ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * (((cut.rows.get
              index).b.coordinates.totals column : Data.Gaussian.Basic.Canonical) * values column)) :=
          FiniteSum.Fin.sumFin_congr (fun column => by ring1)
        _ = _ := by rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_mul_left]; rfl

/-- The original A and B period values weighted by the retained closed-row coordinates. -/
def periodValue (value :
  Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) : Gaussian :=
  sumFin (fun index : Fin genus => ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) *
    SewingRetraction.wordValue value (prepared.aWord index) +
    ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
      (prepared.bWord index))

/-- The actual value of the retained physical remainder on the original cut-alphabet generator readings. -/
def physicalValue (value :
  Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) : Gaussian :=
  WordCoordinates.combine coordinates.physical (fun column =>
    value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators
      column)))

/-- The original face correction minus the two coefficient-weighted basis face corrections. -/
def faceResidual (value :
  Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) : Gaussian :=
  SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.route.correction - sumFin (fun index : Fin genus
    =>
    ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.faceValue
      lifted.mesh.triangulation.faces value (cut.rows.get index).a.route.correction +
    ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.faceValue
      lifted.mesh.triangulation.faces value (cut.rows.get index).b.route.correction)

/-- An antisymmetric cochain reads the original word as its retained period contribution, physical remainder and face
residual. -/
theorem word_value_eq
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value word = coordinates.periodValue value + coordinates.physicalValue value +
      coordinates.faceResidual value := by
  let values := fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutBoundaryWord.alphabet.generators column))
  have original := row.value_eq value anti
  have combined := coordinates.combine_eq values
  have periods : coordinates.periodValue value = sumFin (fun index : Fin genus =>
      ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine
        (cut.rows.get
        index).a.coordinates.totals values +
      ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine
        (cut.rows.get
        index).b.coordinates.totals values) +
      sumFin (fun index : Fin genus =>
        ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.faceValue
          lifted.mesh.triangulation.faces value (cut.rows.get index).a.route.correction +
        ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.faceValue
          lifted.mesh.triangulation.faces value (cut.rows.get index).b.route.correction) := by
    apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) (FiniteSum.Fin.sumFin_add _ _)
    rw [(cut.rows.get index).a.value_eq value anti, (cut.rows.get index).b.value_eq value anti]
    ring1
  apply original.trans
  rw [combined, periods]
  unfold physicalValue
    faceResidual
  change _ = _ + WordCoordinates.combine coordinates.physical values + _
  ring1

/-- The physical remainder has zero value when the cochain vanishes on every original one-sided physical generator. -/
theorem physicalValue_zero
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (physical : ∀ column, lifted.cutBoundaryWord.alphabet.oneSided column = true →
      value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators
        column)) = 0) :
    coordinates.physicalValue value = 0 := by
  apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun column => ?_)) FiniteSum.Fin.sumFin_zero
  dsimp only
  cases side : lifted.cutBoundaryWord.alphabet.oneSided column
  · rw [coordinates.physical_paired_zero column side, IntCast.cast_zero, zero_mul]
  · rw [physical column side, mul_zero]

/-- The retained face residual vanishes when the cochain is closed on every original triangle boundary. -/
theorem faceResidual_zero
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (closed : ∀ index, SewingRetraction.wordValue value (lifted.mesh.triangulation.faces index).boundary = 0) :
    coordinates.faceResidual value = 0 := by
  have zero (terms : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length)) :
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value terms = 0 := by
    induction terms with
    | nil => rfl
    | cons term rest ih =>
        change (term.1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
          (lifted.mesh.triangulation.faces term.2).boundary + _ = 0
        rw [closed term.2, mul_zero, ih, zero_add]
  unfold faceResidual
  rw [zero]
  have correction : sumFin (fun index : Fin genus =>
      ((Data.Vector.get coordinates.a index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.faceValue
        lifted.mesh.triangulation.faces value (cut.rows.get index).a.route.correction +
      ((Data.Vector.get coordinates.b index : Int) : Data.Gaussian.Basic.Canonical) * SewingRetraction.faceValue
        lifted.mesh.triangulation.faces value (cut.rows.get index).b.route.correction) = 0 := by
    apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) FiniteSum.Fin.sumFin_zero
    rw [zero, zero, mul_zero, mul_zero, zero_add]
  rw [correction, sub_self]

/-- An antisymmetric cochain closed on the original faces and zero on physical generators reads the word as its retained
period combination. -/
theorem
  word_value_of_closed
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    (closed : ∀ index, SewingRetraction.wordValue value (lifted.mesh.triangulation.faces index).boundary = 0)
    (physical : ∀ column, lifted.cutBoundaryWord.alphabet.oneSided column = true →
      value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators
        column)) = 0) :
    SewingRetraction.wordValue value word = coordinates.periodValue value := by
  rw [coordinates.word_value_eq value anti, coordinates.physicalValue_zero value physical,
    coordinates.faceResidual_zero value closed, add_zero, add_zero]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

end

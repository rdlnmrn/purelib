module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Unit
import Purelib.LinearAlgebra.Vector.Weighted

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Cut.PairedRowReadback
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StandardIntersections
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution

open Purelib

open Purelib.Algebra

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Vector

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

public section

/-! Explicit integral A/B spanning coordinates with the full physical row retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra.Vector.Weighted (weighted)
open Purelib.LinearAlgebra.Bilinear.Matrix.Basic (bilinear)
open Purelib.LinearAlgebra.Vector.Unit (unitVector weighted_right_unit)
local notation "vget" => Data.Vector.get

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  (cut : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) {word : List
    (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
  (row : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word cut.integral)

/-- Every original paired column is reconstructed from its retained integral A/B intersection coordinates. -/
theorem paired_spanning (column : Fin lifted.cutBoundaryWord.alphabet.count) :
    (PairedRowReadback.pairedReadback row.span) column = FiniteSum.Fin.sumFin (fun index : Fin genus =>
      -((SpanningCoordinates.intersection (cut.rows.get index).b.span) row.span) * (PairedRowReadback.pairedReadback
        (cut.rows.get index).a.span) column +
      (SpanningCoordinates.intersection (cut.rows.get index).a.span) row.span * (PairedRowReadback.pairedReadback
        (cut.rows.get index).b.span) column) := by
  have initial : (PairedRowReadback.pairedReadback row.span) column =
      Bilinear.Matrix.Basic.bilinear (fun first last => cut.integral.paired first last) row.span.coefficients
        (Unit.unitVector column) := by
    apply (Unit.weighted_right_unit (PairedRowReadback.pairedReadback row.span) column).symm.trans
    apply (PairedRowReadback.weighted_pairedReadback row.span (Unit.unitVector column)).trans
    exact Bilinear.Matrix.Basic.bilinear_congr (fun _ _ => Int.cast_id) _ _
  apply initial.trans ((cut.bilinear_reconstruction row.span.coefficients (Unit.unitVector column)).trans ?_)
  apply FiniteSum.Fin.sumFin_congr
  intro index
  have aRead := (SpanningCoordinates.intersection_left_readback (cut.rows.get index).a.span) row.span
  have bRead := (SpanningCoordinates.intersection_left_readback (cut.rows.get index).b.span) row.span
  change (SpanningCoordinates.intersection (cut.rows.get index).a.span) row.span = Weighted.weighted
    (PairedRowReadback.pairedReadback (cut.rows.get index).a.span) row.span.coefficients at aRead
  change (SpanningCoordinates.intersection (cut.rows.get index).b.span) row.span = Weighted.weighted
    (PairedRowReadback.pairedReadback (cut.rows.get index).b.span) row.span.coefficients at bRead
  rw [Unit.weighted_right_unit, Unit.weighted_right_unit, ← aRead, ← bRead]
  ring1

/-- The original closed row equals its finite retained A/B combination plus the full physical remainder, column by
column. -/
@[expose] def BasisEquation (a b : Data.Vector Int genus)
    (physical : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) : Prop :=
  ∀ column, row.coordinates.totals column = FiniteSum.Fin.sumFin (fun index : Fin genus =>
    vget a index * (cut.rows.get index).a.coordinates.totals column +
    vget b index * (cut.rows.get index).b.coordinates.totals column) + vget physical column

/-- The physical remainder is the original physical row minus the physical parts of its retained A/B combination. -/
@[expose] def BasisPhysicalEquation (a b : Data.Vector Int genus)
    (physical : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) : Prop :=
  ∀ column, vget physical column = row.span.physical column - FiniteSum.Fin.sumFin (fun index : Fin genus =>
    vget a index * (cut.rows.get index).a.span.physical column + vget b index * (cut.rows.get index).b.span.physical
      column)

set_option genInjectivity false in
/-- Coefficients and physical remainder are computed once and tied to the original closed word. -/
structure BasisCoordinates where
  /-- The cached integral coefficients of the original A rows. -/ a : Data.Vector Int genus
  /-- The cached integral coefficients of the original B rows. -/ b : Data.Vector Int genus
  /-- Each A coefficient is the negative original intersection against the corresponding B row. -/ a_eq : ∀ index, vget
    a index = -(SpanningCoordinates.intersection (cut.rows.get index).b.span) row.span
  /-- Each B coefficient is the original intersection against the corresponding A row. -/ b_eq : ∀ index, vget b index =
    (SpanningCoordinates.intersection (cut.rows.get index).a.span) row.span
  /-- The cached full physical remainder on the original cut alphabet. -/ physical : Data.Vector Int
    lifted.cutBoundaryWord.alphabet.count
  /-- The physical cache has the exact retained original row subtraction equation. -/ physical_eq :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisPhysicalEquation cut row a b physical
  /-- The cached coefficients and physical remainder reconstruct the entire original closed row. -/ equation :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisEquation cut row a b physical

constructive_injectivity BasisCoordinates

namespace BasisCoordinates

/-- The original paired spanning identity and retained physical subtraction imply the full row reconstruction. -/
theorem row_equation (a b : Data.Vector Int genus)
    (aEq : ∀ index, vget a index = -(SpanningCoordinates.intersection (cut.rows.get index).b.span) row.span)
    (bEq : ∀ index, vget b index = (SpanningCoordinates.intersection (cut.rows.get index).a.span) row.span)
    (physical : Data.Vector Int lifted.cutBoundaryWord.alphabet.count)
    (physicalEq : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisPhysicalEquation cut row a b
      physical) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisEquation cut row a b physical := by
  intro column
  have paired := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.paired_spanning cut row column
  change row.coordinates.totals column - row.span.physical column = _ at paired
  have expanded : FiniteSum.Fin.sumFin (fun index : Fin genus => vget a index * (cut.rows.get
    index).a.coordinates.totals column +
      vget b index * (cut.rows.get index).b.coordinates.totals column) -
      FiniteSum.Fin.sumFin (fun index : Fin genus => vget a index * (cut.rows.get index).a.span.physical column +
        vget b index * (cut.rows.get index).b.span.physical column) = row.coordinates.totals column - row.span.physical
          column := by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply Eq.trans _ paired.symm
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [aEq, bEq]
    unfold PairedRowReadback.pairedReadback
    ring1
  rw [physicalEq]
  calc
    _ = (row.coordinates.totals column - row.span.physical column) + row.span.physical column := by ring1
    _ = _ := (congrArg (· + row.span.physical column) expanded.symm).trans (by ring1)

/-- Compute the original A/B intersection coefficients and physical remainder once, retaining their exact full row
reconstruction. -/
@[expose] def build : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates cut row :=
  let a := Data.Vector.Basic.vectorOfFn fun index : Fin genus => -(SpanningCoordinates.intersection (cut.rows.get
    index).b.span) row.span
  let b := Data.Vector.Basic.vectorOfFn fun index : Fin genus => (SpanningCoordinates.intersection (cut.rows.get
    index).a.span) row.span
  let physical := Data.Vector.Basic.vectorOfFn fun column => row.span.physical column - FiniteSum.Fin.sumFin (fun index
    : Fin genus =>
    vget a index * (cut.rows.get index).a.span.physical column + vget b index * (cut.rows.get index).b.span.physical
      column)
  ⟨a, b, Data.Vector.Basic.vectorOfFn_apply _, Data.Vector.Basic.vectorOfFn_apply _, physical,
    Data.Vector.Basic.vectorOfFn_apply _,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates.row_equation cut row a b
      (Data.Vector.Basic.vectorOfFn_apply _) (Data.Vector.Basic.vectorOfFn_apply _) physical
      (Data.Vector.Basic.vectorOfFn_apply _)⟩

variable {cut row} (coordinates : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates
  cut row)

/-- The retained physical remainder vanishes at every paired column of the original cut alphabet. -/
theorem physical_paired_zero (column : Fin lifted.cutBoundaryWord.alphabet.count)
    (paired : lifted.cutBoundaryWord.alphabet.oneSided column = false) : vget coordinates.physical column = 0 := by
  rw [coordinates.physical_eq, row.span.physical_eq, paired]
  have zero : FiniteSum.Fin.sumFin (fun index : Fin genus => vget coordinates.a index * (cut.rows.get
    index).a.span.physical column +
      vget coordinates.b index * (cut.rows.get index).b.span.physical column) = 0 := by
    apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) FiniteSum.Fin.sumFin_zero
    rw [(cut.rows.get index).a.span.physical_eq, (cut.rows.get index).b.span.physical_eq, paired]
    change vget coordinates.a index * 0 + vget coordinates.b index * 0 = 0
    ring1
  rw [zero]
  rfl

end BasisCoordinates
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows

module

import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece
import Purelib.Data.List.DependentProduct
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Approximation.AccuracyRequest
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

/-! # Whole factory readbacks of actual retained scalar partition caches

The clients consume supplied complete original coarse and fine Layers.
They split those same caches once and identify each actual retained local
Layer with its original parent programme. Original finite-sum additivity
then reads the same whole fine sample without reconstructing local models.
The all-import is solely for the quantified former Partition.layer body.
-/

namespace TestPurelib.Curves.Legendre.ParallelPartitionFactory

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Radial.Differential.Refinement
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {radicand : Pair.Polynomial.Coefficients}
variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Radial.Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {initial : Piece data actual accuracy} {coarse extra : Nat}

/-- One partition of the supplied complete factories keeps every actual local Layer at its original parent ordinal. -/
def retainedPartition
    (parents : {kept : Layer initial coarse // kept = initial.layerAt coarse})
    (fine : {kept : Layer initial (coarse + extra) // kept = initial.layerAt (coarse + extra)}) :
    {grouped : Layer.Partition parents.val fine.val //
      grouped = Layer.partition parents.val parents.property fine.val fine.property ∧
        ∀ index : Fin parents.val.pieces.length,
          grouped.layer index = (parents.val.pieces[index.val]'index.isLt).layerAt extra} := by
  let grouped := Layer.partition parents.val parents.property fine.val fine.property
  exact ⟨grouped, rfl, fun index => Layer.Partition.layer_factory
    parents.val parents.property fine.val fine.property index ⟨parents.val.pieces[index.val]'index.isLt, rfl⟩⟩

/-- The supplied whole fine numerical sample equals the original ordered parent-programme samples at the same depth.

The same actual partition cache supplies both sides. Original cached-slice
additivity and whole local factory readback are composed pointwise; no new
Gaussian sum proof, scalar model or source observation is introduced.
-/
theorem supplied_samples
    (parents : {kept : Layer initial coarse // kept = initial.layerAt coarse})
    (fine : {kept : Layer initial (coarse + extra) // kept = initial.layerAt (coarse + extra)}) :
    fine.val.model.integralSample = sumFin (fun index : Fin parents.val.pieces.length =>
      ((parents.val.pieces[index.val]'index.isLt).program.model extra).integralSample) := by
  let grouped := Layer.partition parents.val parents.property fine.val fine.property
  apply grouped.integralSample_eq_sum.trans
  apply sumFin_congr
  intro index
  have cells := grouped.layer_cells index
  have cached : (PathModel.mk (grouped.get index).2.val).integralSample =
      (grouped.layer index).model.integralSample :=
    congrArg (fun values => (PathModel.mk values).integralSample) cells.symm
  have factory := congrArg (fun layer : Layer (parents.val.pieces[index.val]'index.isLt) extra =>
    layer.model.integralSample) (Layer.Partition.layer_factory
      parents.val parents.property fine.val fine.property index ⟨parents.val.pieces[index.val]'index.isLt, rfl⟩)
  exact cached.trans (factory.trans
    (congrArg PathModel.integralSample ((parents.val.pieces[index.val]'index.isLt).model_eq extra)).symm)

/-- The original partition retains its former complete Sigma and both whole flatten certificates. -/
example (parents : Layer initial coarse) (fine : Layer initial (coarse + extra)) :
    Layer.Partition parents fine =
      {blocks : DependentProduct parents.pieces (fun index =>
          Σ group : {pieces : List (Piece data actual fine.accuracy) //
              pieces.map (fun piece => piece.span) =
                Interval.Bisection.parts extra (parents.pieces[index.val]'index.isLt).span},
            {cells : List CellModel // cells = Piece.models group.val}) //
        (DependentProduct.mapToList parents.pieces blocks (fun _ block => block.1.val)).flatten = fine.pieces ∧
          (DependentProduct.mapToList parents.pieces blocks (fun _ block => block.2.val)).flatten =
            fine.model.cells} := (rfl)

/-- Extracting the count proof preserves the entire former local Layer operation on every original supplied input.

The whole data value includes the original accuracy, all actual Piece and
CellModel slices and their model. This checks the old expression directly;
its count certificate is the original proof moved to Entry.count.
-/
example {parents : Layer initial coarse} {fine : Layer initial (coarse + extra)}
    (partition : Layer.Partition parents fine) (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy // kept = parents.pieces[index.val]'index.isLt}) :
    partition.layer index parent = (
      show Layer parent.val extra from by
        let original : Layer (parents.pieces[index.val]'index.isLt) extra := by
          let retained := partition.get index
          let pieces := retained.1.val
          let model : PathModel := ⟨retained.2.val⟩
          have radii : ∀ amount : Fraction.Rational,
              Geometric.Basic.quarterRadius (Geometric.Basic.quarterRadius amount coarse) extra =
                Geometric.Basic.quarterRadius amount (coarse + extra) := by
            intro amount
            rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow, pow_add]
            ring1
          have outer : pieces ∈
              DependentProduct.mapToList parents.pieces partition.val (fun _ block => block.1.val) := by
            have occurrence := DependentProduct.get_mapToList parents.pieces partition.val
              (fun _ block => block.1.val) index
            exact Eq.mp (congrArg (fun group => group ∈
              DependentProduct.mapToList parents.pieces partition.val (fun _ block => block.1.val)) occurrence)
                (List.getElem_mem ((DependentProduct.length_mapToList parents.pieces partition.val
                  (fun _ block => block.1.val)).symm ▸ index.isLt))
          have original : ∀ piece, piece ∈ pieces → piece ∈ fine.pieces := by
            intro piece member
            exact Eq.mp (congrArg (fun list => piece ∈ list) partition.property.1)
              (mem_flatten_of_mem outer member)
          have parentMember : parents.pieces[index.val]'index.isLt ∈ parents.pieces := List.getElem_mem index.isLt
          exact
            { accuracy := fine.accuracy
              accuracy_eq := fine.accuracy_eq.trans ((radii accuracy.tolerance).symm.trans
                (congrArg (fun amount => Geometric.Basic.quarterRadius amount extra) parents.accuracy_eq.symm))
              pieces
              count := by
                have counts := congrArg List.length retained.1.property
                rewrite [Map.length_map] at counts
                have row := congrArg List.length
                  (DyadicTrace.tail_eq_parts_upper extra (parents.pieces[index.val]'index.isLt).span)
                rewrite [DyadicSteps.tail_length, Map.length_map] at row
                exact counts.trans row.symm
              widths := by
                intro piece member
                exact (fine.widths piece (original piece member)).trans
                  ((radii (initial.span.width ^ 2)).symm.trans
                    (congrArg (fun amount => Geometric.Basic.quarterRadius amount extra)
                      (parents.widths _ parentMember).symm))
              allowances := by
                intro piece member
                exact (fine.allowances piece (original piece member)).trans
                  ((radii initial.cell.allowance).symm.trans
                    (congrArg (fun amount => Geometric.Basic.quarterRadius amount extra)
                      (parents.allowances _ parentMember).symm))
              model
              model_cells := retained.2.property }
        exact Eq.mp (congrArg (fun kept : Piece data actual parents.accuracy => Layer kept extra)
          parent.property.symm) original
      ) := (rfl)

end TestPurelib.Curves.Legendre.ParallelPartitionFactory

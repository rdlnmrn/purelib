module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Data.List.Membership
import Purelib.Data.Fin

/-! # The original six source-polynomial restrictions at one retained shifted child

One six-entry dependent bank materializes each original polynomial restriction
once on the SAME child's actual left/request endpoint. Both adjacent derivative
orders share these same stored tables. No query or new allocation is executed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Data.List

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (source : PreparedParent patch count floor covered targets)

include retained index child_eq in
/-- The actual retained child inherits the SAME original supplied sheet occurrence, independently of query labels. -/
theorem child_sheet : child.edge.sheet = parent.edge.sheet := by
  have bounded : index.val <
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers).length :=
    Eq.mp (congrArg (fun length => index.val < length) (congrArg List.length retained.parents.parents_eq)) index.isLt
  have selected : child =
      (centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
        retained.acquired.traced.prepared.subdivision retained.parents.centers)[index.val]'bounded :=
    child_eq.trans (getElem_congr retained.parents.parents_eq rfl index.isLt)
  have member : child ∈ centeredEdges (Fibre.frameCurve target) basis parent.edge.sheet
      retained.acquired.traced.prepared.subdivision retained.parents.centers :=
    selected.symm ▸ List.getElem_mem bounded
  exact Riemann.Integration.PreparedSubdivisionModelCore.centeredEdges_sheet
    (Fibre.frameCurve target) basis parent.edge.sheet retained.acquired.traced.prepared.subdivision
    retained.parents.centers child member

/-- Cache all SIX original source polynomials on the SAME actual child's retained parameter endpoints.

Every entry retains its complete canonical restriction equation and its
original source model/allowance. The original child and source stay indices.
This one bank shares the first-derivative tables between the value slope
and first-derivative base; no root or observation is constructed here.
-/
@[expose] def Restrictions :=
  Data.Vector.DependentVector (fun channel : Fin 6 =>
    { cached : Cached (source.preparation.cell.models.cell channel).polynomial
        (Cast.Path.ofCoordinate child.edge.left.parameter)
        (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter) //
      cached = Cached.canonical (source.preparation.cell.models.cell channel).polynomial
        (Cast.Path.ofCoordinate child.edge.left.parameter)
        (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter) })

namespace Restrictions

variable {source}

/-- Compile all six child restrictions once, preserving the original value/first factory arguments and order.

The original value-zero and first-zero tables are retained before the four
additional tables. The finite selector only reads those six materialized
caches and never executes a canonical restriction factory again. -/
def build : Restrictions (child := child) source :=
  let value := Cached.canonical source.preparation.cell.models.valueZero.model.polynomial
    (Cast.Path.ofCoordinate child.edge.left.parameter) (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter)
  let first := Cached.canonical source.preparation.cell.models.firstZero.model.polynomial
    (Cast.Path.ofCoordinate child.edge.left.parameter) (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter)
  let valueOne := Cached.canonical source.preparation.cell.models.valueOne.model.polynomial
    (Cast.Path.ofCoordinate child.edge.left.parameter) (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter)
  let firstOne := Cached.canonical source.preparation.cell.models.firstOne.model.polynomial
    (Cast.Path.ofCoordinate child.edge.left.parameter) (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter)
  let secondZero := Cached.canonical source.preparation.cell.models.secondZero.model.polynomial
    (Cast.Path.ofCoordinate child.edge.left.parameter) (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter)
  let secondOne := Cached.canonical source.preparation.cell.models.secondOne.model.polynomial
    (Cast.Path.ofCoordinate child.edge.left.parameter) (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter)
  let entry := fun channel : Fin 6 =>
    { cached : Cached (source.preparation.cell.models.cell channel).polynomial
        (Cast.Path.ofCoordinate child.edge.left.parameter)
        (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter) //
      cached = Cached.canonical (source.preparation.cell.models.cell channel).polynomial
        (Cast.Path.ofCoordinate child.edge.left.parameter)
        (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter) }
  Data.Vector.DependentVector.ofFn (fun channel : Fin 6 =>
    Data.Fin.casesDependent (motive := entry) ⟨value, rfl⟩
      (Data.Fin.casesDependent (motive := fun index : Fin 5 => entry index.succ) ⟨valueOne, rfl⟩
        (Data.Fin.casesDependent (motive := fun index : Fin 4 => entry index.succ.succ) ⟨first, rfl⟩
          (Data.Fin.casesDependent (motive := fun index : Fin 3 => entry index.succ.succ.succ) ⟨firstOne, rfl⟩
            (Data.Fin.casesDependent (motive := fun index : Fin 2 => entry index.succ.succ.succ.succ) ⟨secondZero, rfl⟩
              (Data.Fin.casesDependent (motive := fun index : Fin 1 => entry index.succ.succ.succ.succ.succ)
                ⟨secondOne, rfl⟩ (fun index => Fin.elim0 index)))))) channel)

variable (restrictions : Restrictions (child := child) source)

/-- Read one SAME original retained canonical restriction at its original six-form channel index. -/
@[expose] def cache (channel : Fin 6) := (restrictions.get channel).val

/-- The selected cached restriction retains its entire original canonical factory at the SAME physical interval. -/
theorem cache_eq (channel : Fin 6) : restrictions.cache channel =
    Cached.canonical (source.preparation.cell.models.cell channel).polynomial
      (Cast.Path.ofCoordinate child.edge.left.parameter)
      (Cast.Path.ofCoordinate child.edge.request.endpoint.parameter) :=
  (restrictions.get channel).property

/-- Read the actual old child model consuming that SAME retained restriction and its original unchanged allowance. -/
@[expose] def model (channel : Fin 6) :=
  Restriction.model (source.preparation.cell.models.cell channel) (restrictions.cache channel)

include retained index child_eq in
/-- Every selected original child-model point is the SAME physical point of the retained centered child. -/
theorem point_eq (channel : Fin 6) (input : Rational) :
    (restrictions.model channel).point input = child.edge.point input := by
  change (Restriction.model (source.preparation.cell.models.cell channel) (restrictions.cache channel)).point input = _
  rewrite [Restriction.point_eq, source.preparation.cell.models.cell_point]
  change source.preparation.cell.models.coordinate.point
    (child.edge.left.parameter + input * (child.edge.request.endpoint.parameter - child.edge.left.parameter)) = _
  rewrite [← PreparedSheetContinuation.parameterAt_eq_affine child.edge.left child.edge.request input]
  exact (source.queryPoint_eq _).trans (retained.originalPoint_eq index child_eq input).symm

include retained index child_eq in
/-- Every selected restricted source model starts at the SAME original child's nominal physical source. -/
theorem model_start (channel : Fin 6) :
    (restrictions.model channel).start = (startPoint child).coordinate :=
  (restrictions.model channel).point_zero.symm.trans
    ((restrictions.point_eq retained index child_eq channel 0).trans child.edge.point_zero)

include retained index child_eq in
/-- Every selected restricted source model finishes at that SAME child's exact original request endpoint. -/
theorem model_finish (channel : Fin 6) :
    (restrictions.model channel).finish = (finishPoint child).coordinate :=
  (restrictions.model channel).point_one.symm.trans
    ((restrictions.point_eq retained index child_eq channel 1).trans child.edge.point_one)

end Restrictions

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end

module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Polynomial.Readings
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Polynomial
import Purelib.Polynomial.Geometry.Grid.AxisWalks.Gaussian
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order

/-! # A retained numerator word against one actual ordinary source model

Every literal fragment uses the same given source model and its own already
retained endpoint/numerical caches. The original increasing partition gives
the exact source primitive telescope. The finite bound keeps every actual
occurrence and its independent per-piece allowance.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets.Word.PolynomialComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Indexed
  (sumFin_eq_gaussianSum sumFin_map normSq_sumFin_sub_le_count_mul_sumFin)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus count modelFloor : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational} {request : LocalRequest parent count target}
variable {partition : AxisPartition 0 1 (axes.parameters parent)}
variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
variable {entries : FragmentSheets domains request fragments}
variable {differential : OddPowerDifferential curve.polynomial}
variable {sourceBounds : UniformBounds (request.patch.neighborhood count)}
variable {allowance : Rational} {positive : 0 < allowance}
variable {uniform : UniformRequest sourceBounds 0 (differential.numerator.scale differential.scale)
  modelFloor (allowance / 4)}
variable {first last : Canonical} {coordinate : Spatial.Coordinate first last}
variable (model : PolynomialModel (curve := curve) (differential := differential) uniform coordinate positive)
variable {points : List Canonical} {index : Nat}
variable {budgets : FaceMeshBudgets source points tolerance
  (numerator := differential.numerator.scale differential.scale) domains}
variable {numerics : FacePrimitiveBank source index
  (numerator := differential.numerator.scale differential.scale) domains}
variable {shared : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale) budgets numerics}
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points}
variable (kept : Word shared entries included)

/-- One original full-model comparison for each SAME retained bounded leaf, with its complete source-read identity. -/
abbrev Leaves := DependentProduct partition.intervals fun position =>
  PolynomialModelComparison.EndpointCache
    (leafAt shared entries kept.leaves position).pair.2 model
    (leafAt shared entries kept.leaves position).occurrence.view

/-- Materialize only the analytic comparisons on the existing leaf product in its original occurrence order. -/
def compareLeaves (ordinary : differential.denominatorPairs = 0) : Leaves model kept :=
  DependentProduct.ofFn partition.intervals fun position =>
    (PolynomialModelComparison.fromEndpoints
      (leafAt shared entries kept.leaves position).pair.2 model
      (leafAt shared entries kept.leaves position).occurrence.view ordinary).val

/-- Read one retained analytic result at its actual original fragment position, without replaying its producer. -/
@[expose] def comparisonAt (comparisons : Leaves model kept) (position : Fin partition.intervals.length) :
    PolynomialModelComparison.EndpointCache
      (leafAt shared entries kept.leaves position).pair.2 model
      (leafAt shared entries kept.leaves position).occurrence.view :=
  DependentProduct.get partition.intervals comparisons position

/-- The literal retained parent-parameter increment for the GIVEN source primitive. -/
@[expose] def sourceIncrement (position : Fin partition.intervals.length) : Canonical :=
  model.primitive.primitive.value.eval (parent.edge.point (partition.intervals[position.val]'position.isLt).upper) -
    model.primitive.primitive.value.eval (parent.edge.point (partition.intervals[position.val]'position.isLt).lower)

/-- Actual fragment endpoint factories attach each comparison to the same original parameter interval. -/
theorem fragment_accurate (comparisons : Leaves model kept) (position : Fin partition.intervals.length) :
    normSq (((leafAt shared entries kept.leaves position).occurrence.terminal -
      (leafAt shared entries kept.leaves position).occurrence.initial) - sourceIncrement model position) ≤
        (comparisonAt model kept comparisons position).comparison.bound := by
  let leaf := leafAt shared entries kept.leaves position
  let compared := comparisonAt model kept comparisons position
  have endpoints : model.primitive.primitive.value.eval leaf.pair.1.located.last -
      model.primitive.primitive.value.eval leaf.pair.1.located.first = sourceIncrement model position :=
    congrArg₂ (fun last first : Canonical => last - first)
      (congrArg model.primitive.primitive.value.eval leaf.pair.1.located.last_eq)
      (congrArg model.primitive.primitive.value.eval leaf.pair.1.located.first_eq)
  have bound := PolynomialModelComparison.endpoint_increment_le compared
  exact Eq.mp (congrArg (fun value : Canonical =>
    normSq ((leaf.occurrence.terminal - leaf.occurrence.initial) - value) ≤ compared.comparison.bound) endpoints) bound

/-- The SAME increasing partition telescopes the given source primitive on the literal original parent endpoints. -/
private theorem source_sum : sumFin (sourceIncrement model (partition := partition)) =
    model.primitive.primitive.value.eval (parent.edge.point 1) -
      model.primitive.primitive.value.eval (parent.edge.point 0) := by
  let increment := fun interval : Interval =>
    model.primitive.primitive.value.eval (parent.edge.point interval.upper) -
      model.primitive.primitive.value.eval (parent.edge.point interval.lower)
  have indexed := sumFin_map partition.intervals increment
  have edges := congrArg (fun intervals : List Interval => gaussianSum (intervals.map increment)) partition.walk_edges
  exact indexed.trans (edges.symm.trans (AxisWalks.IncreasingWalk.telescope
    (fun parameter => model.primitive.primitive.value.eval (parent.edge.point parameter)) partition.walk))

/-- The exact count times the sum of actual fragment charges bounds the whole retained word's primitive error. -/
theorem accurate (comparisons : Leaves model kept) :
    normSq (gaussianSum kept.increments -
      (model.primitive.primitive.value.eval (parent.edge.point 1) -
        model.primitive.primitive.value.eval (parent.edge.point 0))) ≤
      (partition.intervals.length : Rational) * sumFin (fun position : Fin partition.intervals.length =>
        (comparisonAt model kept comparisons position).comparison.bound) := by
  have bounded := normSq_sumFin_sub_le_count_mul_sumFin
    (fun position : Fin partition.intervals.length =>
      (leafAt shared entries kept.leaves position).occurrence.terminal -
        (leafAt shared entries kept.leaves position).occurrence.initial)
    (sourceIncrement model (partition := partition))
    (fun position : Fin partition.intervals.length => (comparisonAt model kept comparisons position).comparison.bound)
    (fragment_accurate model kept comparisons)
  have leftSum : sumFin (fun position : Fin partition.intervals.length =>
      (leafAt shared entries kept.leaves position).occurrence.terminal -
        (leafAt shared entries kept.leaves position).occurrence.initial) = gaussianSum kept.increments :=
    sumFin_eq_gaussianSum _
  exact Eq.mp (congrArg (fun value : Canonical => normSq value ≤
      (partition.intervals.length : Rational) * sumFin (fun position : Fin partition.intervals.length =>
        (comparisonAt model kept comparisons position).comparison.bound))
    (congrArg₂ (fun left right : Canonical => left - right) leftSum
      (source_sum model (partition := partition)))) bounded

/-- The ordered errors against the SAME retained source primitive, used only in the finite comparison proof. -/
@[expose] def errors : List Canonical := List.ofFn fun position : Fin partition.intervals.length =>
  ((leafAt shared entries kept.leaves position).occurrence.terminal -
    (leafAt shared entries kept.leaves position).occurrence.initial) - sourceIncrement model position

/-- Sum the actual per-fragment charges without evaluating the source polynomial. -/
@[expose] def chargeSum (comparisons : Leaves model kept) : Rational :=
  sumFin fun position : Fin partition.intervals.length =>
    (comparisonAt model kept comparisons position).comparison.bound

/-- The actual comparison proof retains every original fragment occurrence, including repeated or stationary ones. -/
theorem errors_length : (errors model kept).length = partition.intervals.length :=
  Data.List.OfFn.Basic.length_ofFn

/-- Summing the ordered errors subtracts the SAME source primitive's whole original parent increment. -/
theorem errors_sum : gaussianSum (errors model kept) = gaussianSum kept.increments -
    (model.primitive.primitive.value.eval (parent.edge.point 1) -
      model.primitive.primitive.value.eval (parent.edge.point 0)) := by
  have indexed := (sumFin_eq_gaussianSum (fun position : Fin partition.intervals.length =>
    ((leafAt shared entries kept.leaves position).occurrence.terminal -
      (leafAt shared entries kept.leaves position).occurrence.initial) - sourceIncrement model position)).symm
  have subtract := Purelib.Algebra.FiniteSum.Fin.sumFin_sub
    (fun position : Fin partition.intervals.length =>
      (leafAt shared entries kept.leaves position).occurrence.terminal -
        (leafAt shared entries kept.leaves position).occurrence.initial)
    (sourceIncrement model (partition := partition))
  have leftSum : sumFin (fun position : Fin partition.intervals.length =>
      (leafAt shared entries kept.leaves position).occurrence.terminal -
        (leafAt shared entries kept.leaves position).occurrence.initial) = gaussianSum kept.increments :=
    sumFin_eq_gaussianSum _
  exact indexed.trans (subtract.trans
    (congrArg₂ (fun left right : Canonical => left - right) leftSum (source_sum model (partition := partition))))

/-- The norm-square sum uses the literal same per-fragment bounds, without an extra parent-count multiplier. -/
theorem errors_bounded (comparisons : Leaves model kept) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (errors model kept) ≤ chargeSum model kept comparisons := by
  have actual := Data.Gaussian.Norm.Sum.Indexed.gaussianNormSqSum_ofFn
    (fun position : Fin partition.intervals.length =>
      ((leafAt shared entries kept.leaves position).occurrence.terminal -
        (leafAt shared entries kept.leaves position).occurrence.initial) - sourceIncrement model position)
  have bounded := Purelib.Algebra.FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun position : Fin partition.intervals.length => normSq
      (((leafAt shared entries kept.leaves position).occurrence.terminal -
        (leafAt shared entries kept.leaves position).occurrence.initial) - sourceIncrement model position))
    (fun position : Fin partition.intervals.length => (comparisonAt model kept comparisons position).comparison.bound)
    (fragment_accurate model kept comparisons)
  exact Eq.mpr (congrArg (fun value : Rational => value ≤ chargeSum model kept comparisons) actual) bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets.Word.PolynomialComparison

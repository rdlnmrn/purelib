module

import Purelib.Data.Nat.Order
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Paths
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
import Purelib.Data.Vector.Dependent
import Purelib.Data.Gaussian.Norm.Basic

namespace TestPurelib.Curves.Legendre.SourcePrimitiveComparison

open Purelib.Data
open Purelib
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairBudget)
open Purelib.Riemann.Normalization
open ContinuedInverseRoot (ContinuedNeighborhood)
open InverseModelEdgeTransition (EdgeTransition)

variable {parameter : Canonical} {leftCount rightCount : Nat}
  {left : ContinuedNeighborhood (Paths.polynomial parameter) leftCount}
  {right : ContinuedNeighborhood (Paths.polynomial parameter) rightCount}
  {start finish : Canonical}

/-- Two actual shared source requests pay every retained odd-power channel at one finite common floor.

The actual six budgets and selections are stored before either model is
requested. Both requests and both complete cell banks remain original
owners. One unflipped original edge is computed from the two supplied
point owners and their root relation, then transported through the retained
whole-model equalities without refining either model again.
-/
def paidCells (leftCache : Source.Cache left) (rightCache : Source.Cache right)
    (firstPoint : ContinuedNeighborhood.Point left start) (lastPoint : ContinuedNeighborhood.Point right start)
    (leftStart : left.box.Contains start) (leftFinish : left.box.Contains finish)
    (rightStart : right.box.Contains start) (rightFinish : right.box.Contains finish)
    (roots : Approximation.Gaussian.Equivalence.NamedEquivalent
      firstPoint.certificate.value.name lastPoint.certificate.value.name)
    (current : Nat) (target allowance : Rational) (positive : 0 < target) (nonnegative : 0 ≤ allowance) :
    Σ budgets : DependentVector (fun channel : Fin 6 => PrimitivePairBudget left right
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale) start finish
      (Specification.Table.forms parameter channel).denominatorPairs),
    Σ selections : DependentVector (fun channel : Fin 6 => Search.Selection (budgets.get channel).scale current target),
    let floor := max current (selections.maximum (fun _ selected => selected.stage))
    Σ first : Source.Request leftCache floor target,
    Σ last : Source.Request rightCache floor target,
    Σ _edge : {actual : EdgeTransition (left.base.refine first.selection.stage)
        (right.base.refine last.selection.stage) start finish // actual.sample.alignment.flip = false},
    Σ firstCells : Source.CellModels first start finish allowance,
    {lastCells : Source.CellModels last start finish allowance //
      ∀ channel : Fin 6, Data.Gaussian.Norm.Basic.normSq
        ((firstCells.cell channel).integralSample - (lastCells.cell channel).integralSample) < target} :=
  let budgets := DependentVector.ofFn (fun channel : Fin 6 => PrimitivePairBudget.build left right
    ((Specification.Table.forms parameter channel).numerator.scale
      (Specification.Table.forms parameter channel).scale) start finish
    (Specification.Table.forms parameter channel).denominatorPairs)
  let selections := DependentVector.ofFn (fun channel : Fin 6 => (budgets.get channel).choose current target positive)
  let floor := max current (selections.maximum (fun _ selected => selected.stage))
  let first := leftCache.request floor target positive
  let last := rightCache.request floor target positive
  let retainedEdge := ContinuedInverseRootOverlap.EdgeTransition.ofEquivalentPoints firstPoint lastPoint
    leftStart leftFinish rightStart rightFinish roots first.selection.stage last.selection.stage
    first.model last.model
    (congrArg (fun model => model.value.eval start) first.model_eq)
    (congrArg (fun model => model.value.eval start) last.model_eq)
  let signed : {actual : EdgeTransition first.model last.model start finish //
      actual.sample.alignment.flip = false} := ⟨retainedEdge, rfl⟩
  let firstChanged := Eq.mp (congrArg (fun model =>
    {actual : EdgeTransition model last.model start finish // actual.sample.alignment.flip = false}) first.model_eq)
    signed
  let edge := Eq.mp (congrArg (fun model =>
    {actual : EdgeTransition (left.base.refine first.selection.stage) model start finish //
      actual.sample.alignment.flip = false}) last.model_eq) firstChanged
  let firstCells := Source.CellModels.build first start finish allowance nonnegative
  let lastCells := Source.CellModels.build last start finish allowance nonnegative
  ⟨budgets, selections, first, last, edge, firstCells, lastCells, by
    intro channel
    have belowMaximum := selections.get_le_maximum (fun _ selected => selected.stage) channel
    have belowFloor : (selections.get channel).stage ≤ floor :=
      belowMaximum.trans (Nat.Order.le_max_right _ _)
    exact firstCells.pair_integral_difference_lt lastCells channel (budgets.get channel)
      (selections.get channel) edge.val edge.property (belowFloor.trans first.selection.lower)
      (belowFloor.trans last.selection.lower)⟩

end TestPurelib.Curves.Legendre.SourcePrimitiveComparison

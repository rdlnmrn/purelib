module

import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Search

namespace TestPurelib.Riemann.PrimitiveOverlap

open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairBudget)
open Purelib.Riemann.Normalization
open ContinuedInverseRoot (ContinuedNeighborhood)
open InverseRootPolynomial (Polynomial Gaussian Coordinate)
open InverseRootPrimitive (PrimitiveModel)
open InverseModelEdgeTransition (EdgeTransition)

variable {polynomial numerator : Polynomial} {leftCount rightCount : Nat}
  {left : ContinuedNeighborhood polynomial leftCount} {right : ContinuedNeighborhood polynomial rightCount}
  {start finish : Gaussian}

/-- The omitted pair count keeps the complete original cached bounds and scalar tuple. -/
private theorem former_pair_budget (left : ContinuedNeighborhood polynomial leftCount)
    (right : ContinuedNeighborhood polynomial rightCount) (numerator : Polynomial) (start finish : Gaussian) :
    PrimitivePairBudget.build left right numerator start finish =
      (let bounds := PrimitiveOverlapBounds.build
        (Purelib.Riemann.Readings.SeededPrimitiveBounds.clearance left.base) numerator
       (⟨bounds, 12 * (left.base.model.bound + right.base.model.bound) *
         (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start), rfl⟩ :
         PrimitivePairBudget left right numerator start finish)) := (rfl)

/-- The old inverse primitive call retains its original scalar estimate with omitted pair arguments. -/
private theorem former_increment {leftIndex rightIndex : Nat}
    (budget : PrimitivePairBudget left right numerator start finish)
    (first : PrimitiveModel left leftIndex numerator) (second : PrimitiveModel right rightIndex numerator)
    (edge : EdgeTransition (left.base.refine leftIndex) (right.base.refine rightIndex) start finish)
    (unflipped : edge.sample.alignment.flip = false) (index : Nat)
    (leftLater : index ≤ leftIndex) (rightLater : index ≤ rightIndex) :
    normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
      (second.primitive.value.eval start - second.primitive.value.eval finish)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius budget.scale index :=
  budget.increment_le first second edge unflipped index leftLater rightLater

/-- One actual higher-pair selection pays the two retained primitive increments on their original common edge.

The input root relation identifies the two supplied original point owners.
The finite selection, model refinements, power caches, primitives and edge
are constructed here; no residual bound or successful payment is supplied.
-/
def paidHigherPair (firstPoint : ContinuedNeighborhood.Point left start)
    (secondPoint : ContinuedNeighborhood.Point right start)
    (leftStart : left.box.Contains start) (leftFinish : left.box.Contains finish)
    (rightStart : right.box.Contains start) (rightFinish : right.box.Contains finish)
    (roots : Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      firstPoint.certificate.value.name secondPoint.certificate.value.name)
    (remaining current : Nat) (target : Coordinate) (positive : 0 < target) :
    Σ budget : PrimitivePairBudget left right numerator start finish (remaining + 1),
    Σ selection : Search.Selection budget.scale current target,
    Σ first : PrimitiveModel left selection.stage numerator (remaining + 1),
    Σ second : PrimitiveModel right selection.stage numerator (remaining + 1),
    {edge : EdgeTransition (left.base.refine selection.stage) (right.base.refine selection.stage) start finish //
      edge.sample.alignment.flip = false ∧
      normSq (first.primitive.value.eval finish - first.primitive.value.eval start +
        (second.primitive.value.eval start - second.primitive.value.eval finish)) < target} :=
  let budget := PrimitivePairBudget.build left right numerator start finish (remaining + 1)
  let selection := budget.choose current target positive
  let leftModel := left.base.refine selection.stage
  let rightModel := right.base.refine selection.stage
  let leftPowers := OddPowers.build leftModel.value
  let rightPowers := OddPowers.build rightModel.value
  let first := PrimitiveModel.ofPowers left selection.stage numerator leftModel rfl leftPowers (remaining + 1)
  let second := PrimitiveModel.ofPowers right selection.stage numerator rightModel rfl rightPowers (remaining + 1)
  let edge := ContinuedInverseRootOverlap.EdgeTransition.ofEquivalentPoints firstPoint secondPoint
    leftStart leftFinish rightStart rightFinish roots selection.stage selection.stage leftModel rightModel rfl rfl
  ⟨budget, selection, first, second, edge, rfl,
    budget.selected_increment_lt selection first second edge rfl (Nat.le_refl _) (Nat.le_refl _)⟩

end TestPurelib.Riemann.PrimitiveOverlap

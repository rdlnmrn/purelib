module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Bounds
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Rat.Interval.Basic
import Purelib.Approximation.AccuracyRequest
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Geometry.Gaussian.UnitCircle.Quarter

/-! # Paid cached cubic and fifth-power scalar coefficient comparisons

The actual original root comparison is constructed from the retained signed
link. Both derivative cases consume the existing shared cubic/fifth reading
and original power readback laws. The zero-pair check retains the exact
former bound, with no extra magnitude premise or changed constants.
-/

namespace TestPurelib.Curves.Legendre.ParallelOddPowerResidual

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Normalization
open ContinuedInverseRoot (ContinuedNeighborhood)
open ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveReading)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Radial
open Radial.Differential
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Algebra.Quadratic (Pair)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {radicand : Pair.Polynomial.Coefficients} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {source : Transport.Reading actual span.lower inside} {accuracy : AccuracyRequest}
variable {polynomial : Pair.Polynomial.Coefficients} {count : Nat}
variable {patch : ContinuedNeighborhood polynomial count}
variable {point : ContinuedNeighborhood.Point patch
  (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base}
variable {depth : Nat} {inverse : InverseRootPolynomial.Model polynomial patch.base.box}
variable {powers : OddPowers inverse.value}

/-- Construct the actual same-root comparison and bound either retained derivative power.

The original shared reading supplies its cached cubic or fifth value and
its exact original readback. The source/patch floors are derived internally
from the retained regular cell and original Point. The supplied domain and
coefficient equation remain explicit mathematical conditions; this producer
does not assert their whole-quarter construction or a requested decay rate.
-/
def compared (model : Cells.Model data source accuracy) (kind : Fin 2)
    (pairs : differential.denominatorPairs = kind.val + 1)
    (shared : PrimitiveReading point depth inverse powers)
    (related : Equivalence.NamedEquivalent source.lift.value.name point.certificate.value.name)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    (target : Fraction.Rational) (positiveTarget : 0 < target)
    (coefficient : Pair.Polynomial.Coefficients)
    (compiled : coefficient.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base =
        (differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            (if kind.val = 0 then shared.cube else shared.fifth)) :
    {comparison : Equivalence.Observation.Comparison model.rootReading shared.rootReading target //
      let floor := Cells.Model.comparisonFloor source patch
      let error := 2 * (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale depth +
        (floor⁻¹ * floor⁻¹) * comparison.bound)
      let upper := 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) + floor⁻¹
      model.primitiveResidual coefficient ≤
        normSq ((differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            Tangent.baseVelocity site parameter 2 quarter span.lower) *
          (Norm.Power.differenceFactor upper (2 * (kind.val + 1) + 1) * error)} := by
  let comparison := model.comparePrimitive related shared target positiveTarget
  have floorPaid := Cells.Model.comparisonFloor_paid source patch model.regular
  have firstLower := floorPaid.2.1.trans model.rootReading_lower
  have lastLower := floorPaid.2.2.trans (point.candidate_lower _ shared.possible)
  rewrite [← Norm.Basic.normSq_eq_canonical] at lastLower
  have selected : (if kind.val = 0 then shared.cube else shared.fifth) =
      shared.inverse ^ (2 * (kind.val + 1) + 1) := by
    refine Fin.cases ?_ ?_ kind
    · change shared.cube = shared.inverse ^ 3
      exact shared.cube_readback
    · intro next
      refine Fin.cases ?_ (fun absent => Fin.elim0 absent) next
      change shared.fifth = shared.inverse ^ 5
      exact shared.fifth_readback
  have coefficient_eq : coefficient.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base =
        (differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            (match differential.denominatorPairs with
            | 0 => shared.inverse
            | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1)) := by
    rewrite [pairs]
    exact compiled.trans (congrArg (fun value =>
      (differential.scale * differential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) * value) selected)
  have paid := model.primitiveResidual_le shared contained comparison (Cells.Model.comparisonFloor source patch)
    floorPaid.1 firstLower lastLower coefficient coefficient_eq
  rewrite [pairs] at paid
  exact ⟨comparison, paid⟩

/-- The complete original zero-pair inequality retains its exact input conditions and factor two. -/
example (model : Cells.Model data source accuracy) (pairs : differential.denominatorPairs = 0)
    (shared : PrimitiveReading point depth inverse powers)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    {target : Fraction.Rational}
    (comparison : Equivalence.Observation.Comparison model.rootReading shared.rootReading target)
    (floor : Fraction.Rational) (floorPositive : 0 < floor)
    (firstLower : floor ≤ normSq model.rootReading.value) (lastLower : floor ≤ normSq shared.root)
    (coefficient : Pair.Polynomial.Coefficients)
    (compiled : coefficient.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base =
        (differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) * shared.inverse) :
    model.primitiveResidual coefficient ≤
      normSq ((differential.scale * differential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
          Tangent.baseVelocity site parameter 2 quarter span.lower) *
        (2 * (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale depth +
          (floor⁻¹ * floor⁻¹) * comparison.bound)) := by
  have actual : coefficient.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base =
        (differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            (match differential.denominatorPairs with
            | 0 => shared.inverse
            | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1)) := by
    rewrite [pairs]
    exact compiled
  have retained := model.primitiveResidual_le shared contained comparison floor floorPositive
    firstLower lastLower coefficient actual
  rewrite [pairs] at retained
  exact retained

end TestPurelib.Curves.Legendre.ParallelOddPowerResidual

module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Bounds
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Rat.Interval.Basic
import Purelib.Approximation.AccuracyRequest
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Geometry.Gaussian.UnitCircle.Quarter

/-! # Original coefficient requests from the six retained primitive owners

Each selected channel uses the original Table form, reweights the supplied
scalar sample, and consumes a primitive with that actual scaled numerator
and odd-power index. The complete former zero-pair acquisition is checked
against its original root/readModel/comparison construction.
-/

namespace TestPurelib.Curves.Legendre.ParallelCoefficientRequests

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
open Purelib.Curves.Legendre.Periods.Jets
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

open InverseRootPrimitive (PrimitiveModel)
open Purelib.Polynomial.Dense
open Basic.DensePolynomial

/-- Request the selected original form using its actual scaled primitive and the existing scalar sample.

The pair alignment and scaled-numerator equation are derived from the
original form and polynomial evaluation law. The supplied common primitive
and power cache remain whole original inputs. The point's signed relation
and genuine domain remain explicit; no successful comparison or residual
bound is requested from the caller. This acquires one selected channel;
it does not claim a once-materialized six-request bank.
-/
def requested (model : Cells.Model data source accuracy) (channel : Fin 6)
    (related : Equivalence.NamedEquivalent source.lift.value.name point.certificate.value.name)
    (sameModel : inverse = patch.base.refine depth)
    (common : PrimitiveModel patch depth
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    let next := model.reweight (Waist.Differential.Bounds.Data.build site parameter
      (Specification.Table.forms parameter channel))
    Cells.Model.CoefficientRequest (sample := point) (powers := powers) next sameModel common :=
  let next := model.reweight (Waist.Differential.Bounds.Data.build site parameter
    (Specification.Table.forms parameter channel))
  next.coefficientRequest related rfl (fun location => by rewrite [eval_scale]; rfl) sameModel common contained

/-- Each actual selected-channel request retains the exact original computed root and selected stage. -/
example (model : Cells.Model data source accuracy) (channel : Fin 6)
    (related : Equivalence.NamedEquivalent source.lift.value.name point.certificate.value.name)
    (sameModel : inverse = patch.base.refine depth)
    (common : PrimitiveModel patch depth
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    (requested (powers := powers) model channel related sameModel common contained).1.val =
      point.selectPrimitiveRoot depth accuracy.tolerance accuracy.positive := rfl

/-- The complete former zero-pair acquisition, retaining its three actual caches and original full result type. -/
private def former (model : Cells.Model data source accuracy)
    (related : Equivalence.NamedEquivalent source.lift.value.name point.certificate.value.name)
    (pairs : differential.denominatorPairs = 0) (scale : differential.scale = 1)
    (sameModel : inverse = patch.base.refine depth)
    (common : PrimitiveModel patch depth differential.numerator)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    Cells.Model.CoefficientRequest (sample := point) (powers := powers) model sameModel common :=
  let root := point.selectPrimitiveRoot depth accuracy.tolerance accuracy.positive
  let shared := root.readModel inverse sameModel powers
  let comparison := model.comparePrimitive related shared accuracy.tolerance accuracy.positive
  have paid := (model.coefficientRequest (powers := powers) related pairs
    (fun location => ((congrArg (fun factor : Canonical =>
      factor * differential.numerator.eval location) scale).trans (Basic.one_mul _)).symm)
    sameModel common contained).2.2.property
  ⟨⟨root, rfl⟩, ⟨shared, rfl⟩, ⟨comparison, paid⟩⟩

/-- Every complete former zero-pair request agrees with the generalized original procedure for all original inputs. -/
example (model : Cells.Model data source accuracy)
    (related : Equivalence.NamedEquivalent source.lift.value.name point.certificate.value.name)
    (pairs : differential.denominatorPairs = 0) (scale : differential.scale = 1)
    (sameModel : inverse = patch.base.refine depth)
    (common : PrimitiveModel patch depth differential.numerator)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    model.coefficientRequest (powers := powers) related pairs
      (fun location => ((congrArg (fun factor : Canonical =>
        factor * differential.numerator.eval location) scale).trans (Basic.one_mul _)).symm)
      sameModel common contained = former (powers := powers) model related pairs scale sameModel common contained := rfl

/-- Every odd-power acquisition retains the complete former root, shared reading and comparison factory result. -/
example (model : Cells.Model data source accuracy) {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    (related : Equivalence.NamedEquivalent source.lift.value.name point.certificate.value.name)
    (pairs : differential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = differential.scale * differential.numerator.eval location)
    (sameModel : inverse = patch.base.refine depth)
    (common : PrimitiveModel patch depth numerator pairCount)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    model.coefficientRequest (powers := powers) related pairs scale sameModel common contained =
    (show Cells.Model.CoefficientRequest (sample := point) (powers := powers) model sameModel common from by
      let root := point.selectPrimitiveRoot depth accuracy.tolerance accuracy.positive
      let shared := root.readModel inverse sameModel powers
      let comparison := model.comparePrimitive related shared accuracy.tolerance accuracy.positive
      have paid := (model.coefficientRequest (powers := powers) related pairs scale
        sameModel common contained).2.2.property
      exact ⟨⟨root, rfl⟩, ⟨shared, rfl⟩, ⟨comparison, paid⟩⟩) := rfl

/-- Reweighting retains the complete original root, model reading and comparison objects.

The new original coefficient and its denominator index may differ. The
same retained primitive Point, inverse cache, power cache and accuracy
remain indices, and no new root request or readModel is run.
-/
example (model : Cells.Model data source accuracy) {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    (sameModel : inverse = patch.base.refine depth)
    (common : PrimitiveModel patch depth numerator pairCount)
    (request : Cells.Model.CoefficientRequest (sample := point) (powers := powers) model sameModel common)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : Waist.Differential.Bounds.Data site parameter nextDifferential)
    {nextNumerator : Pair.Polynomial.Coefficients} {nextPairs : Nat}
    (pairs : nextDifferential.denominatorPairs = nextPairs)
    (scale : ∀ point, nextNumerator.eval point = nextDifferential.scale * nextDifferential.numerator.eval point)
    (nextCommon : PrimitiveModel patch depth nextNumerator nextPairs)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    let next := Cells.Model.CoefficientRequest.reweight model sameModel common request nextData
      pairs scale nextCommon contained
    (next.1.val, next.2.1.val) = (request.1.val, request.2.1.val) ∧
      HEq next.2.2.val request.2.2.val := by
  dsimp only
  refine ⟨rfl, ?_⟩
  let equal := congrArg (fun retained => Equivalence.Observation.Comparison retained request.2.1.val.rootReading
    accuracy.tolerance) (model.rootReading_reweight nextData)
  change HEq (Eq.mpr equal request.2.2.val) request.2.2.val
  exact cast_heq _ _

end TestPurelib.Curves.Legendre.ParallelCoefficientRequests

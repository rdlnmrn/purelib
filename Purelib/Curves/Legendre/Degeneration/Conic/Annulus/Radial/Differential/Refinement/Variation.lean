module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Quadrature
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Weighted
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Parameter remainders on the original parallel quadrature weights

The original dyadic layer supplies its retained physical nodes, oriented
weights and exact count. Arithmetic observations at those same nodes retain
their source and target cubic certificates and parameter increment. The
existing weighted bank consumes those observations once. Fixed boxes and
common actual observation floors then give fourth-order parameter bounds
independent of the spatial refinement depth.

Agreement of these finite weighted samples with the prescribed geometric
integral programs remains a separate certificate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

open Purelib
open Purelib.Algebra
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter increment : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {initial : Piece data actual accuracy} {depth : Nat}

variable (layer : Layer initial depth)
variable {sources : (node : Fin layer.pieces.length) →
  CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter (layer.points node))}
variable {targets : (node : Fin layer.pieces.length) →
  CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) (layer.points node))}
variable {unit : Norm.Basic.normSq increment ≤ 1}
variable {jets : (node : Fin layer.pieces.length) →
  Sampling.SampledJet parameter increment (layer.points node) (sources node) (targets node) unit}
variable {observations : Arithmetic.Weighted.NodeObservations jets}

/-- The common fixed-box value ceiling bounds the same cached weighted bank on the original parallel mesh. -/
theorem parameter_value_factor_le (bank : Arithmetic.Weighted.Bank observations layer.weights)
    (coordinate : Fin 2) (sourceFloor targetFloor sumFloor : Fraction.Rational)
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor)
    (floors : ∀ node, (jets node).clearance.sourceFloor = sourceFloor ∧
      (jets node).clearance.targetFloor = targetFloor ∧ (jets node).clearance.sumFloor = sumFloor) :
    (bank.value coordinate).factor ≤
      (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        Arithmetic.valueCeiling parameter increment coordinate (spatialBox site) sourceFloor targetFloor sumFloor := by
  apply bank.value_factor_le coordinate depth layer.count _ _
    (Arithmetic.valueCeiling_nonnegative parameter increment coordinate (spatialBox site)
      sourcePositive targetPositive sumPositive)
    (fun node => layer.weights_normSq_le node)
  intro node
  have bound := (observations node).value_factor_le coordinate (layer.points_inside node)
  have equalities := floors node
  rewrite [equalities.1, equalities.2.1, equalities.2.2] at bound
  exact bound

/-- The same original weights bound the cached first bank using its separately retained second derivative readings. -/
theorem parameter_first_factor_le (bank : Arithmetic.Weighted.Bank observations layer.weights)
    (coordinate : Fin 2) (inverseBox : Box) (sourceFloor targetFloor sumFloor : Fraction.Rational)
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor)
    (sourceInverseInside : ∀ node, inverseBox.Contains (jets node).sourceSample.reading⁻¹)
    (targetInverseInside : ∀ node, inverseBox.Contains (jets node).targetSample.reading⁻¹)
    (floors : ∀ node, (jets node).clearance.sourceFloor = sourceFloor ∧
      (jets node).clearance.targetFloor = targetFloor ∧ (jets node).clearance.sumFloor = sumFloor) :
    (bank.first coordinate).factor ≤
      (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        Arithmetic.firstCeiling parameter increment coordinate (spatialBox site) inverseBox
          sourceFloor targetFloor sumFloor := by
  apply bank.first_factor_le coordinate depth layer.count _ _
    (Arithmetic.firstCeiling_nonnegative parameter increment coordinate (spatialBox site) inverseBox
      sourcePositive targetPositive sumPositive)
    (fun node => layer.weights_normSq_le node)
  intro node
  have bound := (observations node).first_factor_le coordinate (layer.points_inside node)
    (sourceInverseInside node) (targetInverseInside node)
  have equalities := floors node
  rewrite [equalities.1, equalities.2.1, equalities.2.2] at bound
  exact bound

/-- Actual weighted value samples on the original nodes have a uniform fourth-order parameter bound. -/
theorem parameter_value_remainder_le (bank : Arithmetic.Weighted.Bank observations layer.weights)
    (coordinate : Fin 2) (sourceFloor targetFloor sumFloor : Fraction.Rational)
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor)
    (floors : ∀ node, (jets node).clearance.sourceFloor = sourceFloor ∧
      (jets node).clearance.targetFloor = targetFloor ∧ (jets node).clearance.sumFloor = sumFloor) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node => layer.weights node * ((observations node).targetValue coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node => layer.weights node * ((observations node).sourceValue coordinate).reading) -
        increment *
          FiniteSum.Fin.sumFin (fun node =>
            layer.weights node * ((observations node).sourceFirst coordinate).reading)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        Arithmetic.valueCeiling parameter increment coordinate (spatialBox site) sourceFloor targetFloor sumFloor) *
          Canonical.normSq increment ^ 2 :=
  (bank.value_remainder_le coordinate).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (layer.parameter_value_factor_le bank coordinate sourceFloor targetFloor sumFloor
        sourcePositive targetPositive sumPositive floors) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Actual weighted first samples retain their independent second slopes in the uniform parameter bound. -/
theorem parameter_first_remainder_le (bank : Arithmetic.Weighted.Bank observations layer.weights)
    (coordinate : Fin 2) (inverseBox : Box) (sourceFloor targetFloor sumFloor : Fraction.Rational)
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor)
    (sourceInverseInside : ∀ node, inverseBox.Contains (jets node).sourceSample.reading⁻¹)
    (targetInverseInside : ∀ node, inverseBox.Contains (jets node).targetSample.reading⁻¹)
    (floors : ∀ node, (jets node).clearance.sourceFloor = sourceFloor ∧
      (jets node).clearance.targetFloor = targetFloor ∧ (jets node).clearance.sumFloor = sumFloor) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node => layer.weights node * ((observations node).targetFirst coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node => layer.weights node * ((observations node).sourceFirst coordinate).reading) -
        increment *
          FiniteSum.Fin.sumFin (fun node =>
            layer.weights node * ((observations node).sourceSecond coordinate).reading)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * initial.span.width ^ 2) *
        Arithmetic.firstCeiling parameter increment coordinate (spatialBox site) inverseBox
          sourceFloor targetFloor sumFloor) *
          Canonical.normSq increment ^ 2 :=
  (bank.first_remainder_le coordinate).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (layer.parameter_first_factor_le bank coordinate inverseBox sourceFloor targetFloor sumFloor
        sourcePositive targetPositive sumPositive sourceInverseInside targetInverseInside floors)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer

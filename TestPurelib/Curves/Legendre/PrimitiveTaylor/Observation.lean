module

import TestPurelib.Curves.Legendre.PrimitiveTaylor
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor.Observation
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Taylor
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! # Actual arithmetic readings of the original Legendre primitives

Both connection rows and the scalar residual reuse the complete source and
nonsquare target caches of the spatial primitive fixture. Their original
independent derivative specifications and evaluator caches select three
actual arithmetic witnesses. The original source residual and observation
spread pay a quadratic certificate on those identical retained witnesses.
A constant cell with the actual derivative witness has a finite error against
the independently prescribed primitive endpoints. No primitive edge identity
or closed-cycle cancellation is asserted by this local comparison.
-/

namespace TestPurelib.Curves.Legendre.PrimitiveTaylor.Observation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.RootContinuation

attribute [local irreducible] source target sourceSample targetSample

/-- Every actual source-observation candidate pays the identical original signed-window denominator floor. -/
private theorem source_lower {candidate : Canonical} (possible : sourceSample.observation.Possible candidate) :
    PeriodVariation.Sampling.side.margin ≤ Norm.Basic.normSq candidate := by
  have inside : PeriodVariation.Sampling.window.Contains candidate := by
    unfold sourceSample at possible
    exact PeriodVariation.Sampling.windowJet.sourceCandidates possible
  have lower := PeriodVariation.Sampling.side.margin_le_normSq_sub inside
  rewrite [Gaussian.Basic.sub_zero] at lower
  exact lower

/-- Every candidate of the retained nonsquare target observation pays the same original signed-window floor. -/
private theorem target_lower {candidate : Canonical} (possible : targetSample.observation.Possible candidate) :
    PeriodVariation.Sampling.side.margin ≤ Norm.Basic.normSq candidate := by
  have originalPossible : target.value.name.process.Possible targetSample.state candidate := by
    rewrite [targetSample.observation_eq] at possible
    exact possible
  have inside := CertifiedSquareRoot.Sampling.candidate_in_initial_box targetOwner
    (by unfold target; rfl) originalPossible
  rewrite [target_box] at inside
  have lower := PeriodVariation.Sampling.side.margin_le_normSq_sub inside
  rewrite [Gaussian.Basic.sub_zero] at lower
  exact lower

/-- The original spatial source belongs to the retained fixed polynomial enclosure. -/
private theorem first_inside : box.Contains first :=
  Calculus.Jet.Quadratic.Polynomial.readingBox_first first last

/-- Both original connection primitives retain their independent spatial derivative specifications. -/
private def connectionDerivative (coordinate : Fin 2) :=
  Jets.Connection.Operational.primitiveDerivative parameter coordinate

/-- Both connection primitive and cleared derivative evaluator caches use the identical original source sheet. -/
private def connectionValues (coordinate : Fin 2) :=
  OddPower.Derivative.Specification.Values.build (connectionDerivative coordinate) first
    source.value source.apart source.square

/-- Each connection target evaluator is retained once on the distinct original nonsquare spatial target. -/
private def connectionTarget (coordinate : Fin 2) :=
  (Jets.Connection.Operational.primitiveForm parameter coordinate).value last target.value target.apart

/-- Both connection rows internally attach their three actual arithmetic readings to the same paid spatial expansion. -/
private def connectionObserved (coordinate : Fin 2) :=
  OddPower.Derivative.Taylor.Observation.build (connection coordinate) (connectionDerivative coordinate)
    (connectionValues coordinate) (connectionTarget coordinate) rfl first_inside
    PeriodVariation.Sampling.side.margin PeriodVariation.Sampling.side.margin
    PeriodVariation.Sampling.side.margin_pos PeriodVariation.Sampling.side.margin_pos source_lower target_lower unit

/-- The scalar residual retains the original spatial derivative of its numerator over the sheet cube. -/
private def residualDerivative := Jets.PicardFuchs.Operational.primitiveDerivative parameter

/-- The scalar primitive and derivative caches retain the identical original source square certificate. -/
private def residualValues :=
  OddPower.Derivative.Specification.Values.build residualDerivative first source.value source.apart source.square

/-- The scalar primitive's target evaluator retains its original numerator, scale, cube and target process. -/
private def residualTarget :=
  (Jets.PicardFuchs.Operational.primitiveForm parameter).value last target.value target.apart

/-- The scalar residual internally pays its actual three-reading spatial Taylor expansion. -/
private def residualObserved :=
  OddPower.Derivative.Taylor.Observation.build residual residualDerivative residualValues residualTarget rfl
    first_inside PeriodVariation.Sampling.side.margin PeriodVariation.Sampling.side.margin
    PeriodVariation.Sampling.side.margin_pos PeriodVariation.Sampling.side.margin_pos source_lower target_lower unit

attribute [local irreducible] connectionDerivative connectionValues connectionTarget connectionObserved
  residualDerivative residualValues residualTarget residualObserved

/-- Both connection source observations use the exact original primitive evaluator cache. -/
theorem connection_source_cache (coordinate : Fin 2) :
    (connectionObserved coordinate).sourceValue.original.coefficient = (connectionValues coordinate).primitiveValue :=
  (connectionObserved coordinate).sourceValue.coefficient_eq

/-- Both connection derivative observations retain the identical independently constructed evaluator cache. -/
theorem connection_derivative_cache (coordinate : Fin 2) :
    (connectionObserved coordinate).derivative.original.coefficient = (connectionValues coordinate).derivative :=
  (connectionObserved coordinate).derivative.coefficient_eq

/-- The residual target observation uses the same retained original nonsquare primitive evaluator cache. -/
theorem residual_target_cache : residualObserved.targetReading.original.coefficient = residualTarget :=
  residualObserved.targetReading.coefficient_eq

/-- The residual certificate slope is its actual independently selected cleared derivative arithmetic witness. -/
theorem residual_actual_slope : residualObserved.certificate.slope = residualObserved.derivative.reading :=
  residualObserved.slope_eq

/-- The residual derivative pays both the original arithmetic spread and actual source square-residual discrepancy. -/
theorem residual_derivative_payment :
    Norm.Basic.normSq (residualObserved.derivative.reading - residual.certificate.slope) ≤
      2 * (OddPower.Observation.Cache.allowanceFactor residualDerivative.differential first source
        PeriodVariation.Sampling.side.margin +
          OddPower.Derivative.Residual.factor (Jets.PicardFuchs.Operational.primitiveForm parameter)
            box PeriodVariation.Sampling.side.margin) * Norm.Basic.normSq (last - first) ^ 2 :=
  residualObserved.derivative_le

/-- Both connection rows have finite fourth-order remainder bounds on their actual independent arithmetic witnesses. -/
theorem connection_readings_remainder (coordinate : Fin 2) :
    Canonical.normSq ((connectionObserved coordinate).targetReading.reading -
      (connectionObserved coordinate).sourceValue.reading -
        (last - first) * (connectionObserved coordinate).derivative.reading) ≤
          (connectionObserved coordinate).certificate.factor * Canonical.normSq (last - first) ^ 2 :=
  (connectionObserved coordinate).remainder_le

/-- The actual residual derivative witness is the retained coefficient of this original physical constant cell. -/
private def residualCell : CellModel :=
  CellModel.exact first last (Polynomial.Ascending.Gaussian.Basic.constant residualObserved.derivative.reading)

/-- The same constant cell has a finite error against independently prescribed original primitive endpoint witnesses. -/
theorem residual_cell_error :
    Norm.Basic.normSq (residualObserved.targetReading.reading - residualObserved.sourceValue.reading -
      residualCell.integralSample) ≤
        2 * residualObserved.certificate.factor * Norm.Basic.normSq (last - first) ^ 2 := by
  have constant : residualCell.polynomial =
      Polynomial.Ascending.Gaussian.Basic.constant residualObserved.certificate.slope := by
    rewrite [residualObserved.slope_eq]
    rfl
  have bound := CellModel.quadratic_integral_error_le residualObserved.certificate residualCell
    residualObserved.certificate.slope rfl constant
  rewrite [residualObserved.output_eq, residualObserved.base_eq, Gaussian.Basic.sub_self,
    Norm.Basic.normSq_zero] at bound
  exact bound.trans_eq (by ring1)

section CompleteBuilderDefaults

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The complete bound former default builder, used solely for whole-record kernel comparison. -/
private def formerValuesBuild
    {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    Specification.Values specification point sheet apart :=
  let primitiveValue := primitive.value point sheet apart
  let derivative := specification.differential.value point sheet apart
  let first := specification.first.value point sheet apart
  let last := specification.last.value point sheet apart
  let difference := CoherentNamed.add first (CoherentNamed.neg last)
  { primitiveValue := primitiveValue
    primitiveValue_eq := rfl
    derivative := derivative
    derivative_eq := rfl
    first := first
    first_eq := rfl
    last := last
    last_eq := rfl
    difference := difference
    difference_eq := rfl
    agreement := specification.agrees point sheet apart square }

/-- The complete bound former cache-consuming builder, used solely for exact supplied-cache comparison. -/
private def formerValuesOfPrimitive
    {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name)
    (primitiveValue : CoherentNamed) (primitiveValue_eq : primitiveValue = primitive.value point sheet apart) :
    Specification.Values specification point sheet apart :=
  let derivative := specification.differential.value point sheet apart
  let first := specification.first.value point sheet apart
  let last := specification.last.value point sheet apart
  let difference := CoherentNamed.add first (CoherentNamed.neg last)
  { primitiveValue := primitiveValue
    primitiveValue_eq := primitiveValue_eq
    derivative := derivative
    derivative_eq := rfl
    first := first
    first_eq := rfl
    last := last
    last_eq := rfl
    difference := difference
    difference_eq := rfl
    agreement := specification.agrees point sheet apart square }

/-- Every default call retains the whole previous builder, including its actual operational comparison. -/
private theorem values_build_default
    {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    Specification.Values.build specification point sheet apart square =
      formerValuesBuild specification point sheet apart square := (rfl)

/-- Every supplied-cache call retains the whole former cache builder and all original input indices. -/
private theorem values_build_retained
    {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name)
    (primitiveValue : CoherentNamed) (primitiveValue_eq : primitiveValue = primitive.value point sheet apart) :
    Specification.Values.build specification point sheet apart square primitiveValue primitiveValue_eq =
      formerValuesOfPrimitive specification point sheet apart square primitiveValue primitiveValue_eq := (rfl)

/-- A default cache and its exact supplied view retain one complete actual builder result. -/
private theorem values_build_default_as_supplied
    {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    Specification.Values.build specification point sheet apart square
        (primitive.value point sheet apart) rfl =
      Specification.Values.build specification point sheet apart square :=
  Specification.Values.build_eq_default specification point sheet apart square
    (primitive.value point sheet apart) rfl

end CompleteBuilderDefaults

end TestPurelib.Curves.Legendre.PrimitiveTaylor.Observation

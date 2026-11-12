module

import TestPurelib.Curves.Legendre.PrimitiveTaylor
import TestPurelib.Curves.Legendre.PeriodVariation.Arithmetic
import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Bounds
import Purelib.Calculus.Jet.Quadratic.Polynomial.Bounds
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate

/-! # Uniform bounds on retained primitive and parameter-variation fixtures

The original spatial primitive fixture supplies its identical source and
nonsquare target observations. Their actual reciprocal readings construct the
original cubic polynomial certificate, whose computed hull factor is bounded
by the retained fixed inverse box. The original parameter-variation fixture
reuses its own cached inverse/cubic certificates and ten actual arithmetic
observations. Both original value and first derivative banks consume the same
fixed spatial/inverse boxes and original candidate margins, without root
re-isolation, replacement certificates or new arithmetic sampling.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Bounds

open Purelib
open Purelib.Calculus.Jet
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian
open TestPurelib.Curves.Legendre

attribute [local irreducible] PrimitiveTaylor.source PrimitiveTaylor.target
  PrimitiveTaylor.sourceSample PrimitiveTaylor.targetSample

/-- The spatial source inverse remains in the original fixed inverse box through its retained signed-window reading. -/
private theorem spatial_source_inverse : PrimitiveTaylor.inverseBox.Contains PrimitiveTaylor.sourceSample.reading⁻¹ :=
  PrimitiveTaylor.inverse_inside (PrimitiveTaylor.connection 0).sourceInside

/-- The original nonsquare spatial target inverse retains that same fixed inverse box without another root request. -/
private theorem spatial_target_inverse : PrimitiveTaylor.inverseBox.Contains PrimitiveTaylor.targetSample.reading⁻¹ :=
  PrimitiveTaylor.inverse_inside (PrimitiveTaylor.connection 0).targetInside

/-- The original cubic certificate is constructed once on the two actual primitive-fixture inverse readings. -/
private def spatialPower :=
  Quadratic.Polynomial.certificate (Power.Coordinate.coordinatePositivePower 2)
    PrimitiveTaylor.sourceSample.reading⁻¹ PrimitiveTaylor.targetSample.reading⁻¹

attribute [local irreducible] spatialPower

/-- The original computed cubic hull factor obeys the fixed inverse box while retaining both original observations. -/
theorem spatial_power_factor : spatialPower.factor ≤
    Polynomial.Dense.Gaussian.Bounds.Box.Taylor.denseEvalTaylorRemainderBound
      (Power.Coordinate.coordinatePositivePower 2)
      PrimitiveTaylor.inverseBox := by
  unfold spatialPower
  exact Quadratic.Polynomial.certificate_factor_le_box _ spatial_source_inverse spatial_target_inverse

/-- The polynomial certificate's base is the original cubic evaluation at the actual retained source inverse. -/
theorem spatial_power_base : spatialPower.base =
    (Power.Coordinate.coordinatePositivePower 2).eval PrimitiveTaylor.sourceSample.reading⁻¹ := by
  unfold spatialPower
  exact Quadratic.Polynomial.certificate_base _ _ _

/-- The polynomial certificate's output uses the distinct actual retained nonsquare target inverse. -/
theorem spatial_power_output : spatialPower.output =
    (Power.Coordinate.coordinatePositivePower 2).eval PrimitiveTaylor.targetSample.reading⁻¹ := by
  unfold spatialPower
  exact Quadratic.Polynomial.certificate_output _ _ _

/-- The actual parameter-source inverse uses the same fixed box and original source signed-window evidence. -/
private theorem parameter_source_inverse : PrimitiveTaylor.inverseBox.Contains Sampling.jet.sourceSample.reading⁻¹ :=
  PrimitiveTaylor.inverse_inside Sampling.windowJet.sourceInside

/-- The actual parameter-target inverse retains the same original box through its own window certificate. -/
private theorem parameter_target_inverse : PrimitiveTaylor.inverseBox.Contains Sampling.jet.targetSample.reading⁻¹ :=
  PrimitiveTaylor.inverse_inside Sampling.windowJet.targetInside

/-- The fixed spatial box contains the unchanged physical point of both original parameter-variation banks. -/
private theorem point_inside : PrimitiveTaylor.box.Contains (2 : Canonical) :=
  Quadratic.Polynomial.readingBox_first PrimitiveTaylor.first PrimitiveTaylor.last

/-- The exact original inverse cache has its fixed spatial-box factor bound with all three actual retained margins. -/
theorem original_inverse_factor : Sampling.jet.inverse.factor ≤
    Variation.Sampling.inverseCeiling PrimitiveTaylor.box Sampling.jet.clearance.sourceFloor
      Sampling.jet.clearance.targetFloor Sampling.jet.clearance.sumFloor :=
  Sampling.jet.inverse_factor_le point_inside

/-- The identical original cached cubic composition has the fixed-box bound from its actual inverse readings. -/
theorem original_cubic_factor : Sampling.jet.cubic.factor ≤
    Variation.Sampling.cubicCeiling PrimitiveTaylor.box PrimitiveTaylor.inverseBox Sampling.jet.clearance.sourceFloor
      Sampling.jet.clearance.targetFloor Sampling.jet.clearance.sumFloor :=
  Sampling.jet.cubic_factor_le point_inside parameter_source_inverse parameter_target_inverse

/-- Both original arithmetic value rows obey the same fixed-box ceilings without another observation request. -/
theorem actual_value_factor (coordinate : Fin 2) : (Arithmetic.observations.valueCertificate coordinate).factor ≤
    Variation.Arithmetic.valueCeiling Sampling.parameter Sampling.increment coordinate PrimitiveTaylor.box
      Sampling.jet.clearance.sourceFloor
      Sampling.jet.clearance.targetFloor Sampling.jet.clearance.sumFloor :=
  Arithmetic.observations.value_factor_le coordinate point_inside

/-- Both actual first rows retain their independent second slopes and obey the original fixed-box factor ceilings. -/
theorem actual_first_factor (coordinate : Fin 2) : (Arithmetic.observations.firstCertificate coordinate).factor ≤
    Variation.Arithmetic.firstCeiling Sampling.parameter Sampling.increment coordinate PrimitiveTaylor.box
      PrimitiveTaylor.inverseBox
      Sampling.jet.clearance.sourceFloor Sampling.jet.clearance.targetFloor Sampling.jet.clearance.sumFloor :=
  Arithmetic.observations.first_factor_le coordinate point_inside parameter_source_inverse parameter_target_inverse

/-- Both actual value-row ceilings have the named nonnegativity proof from the same three retained positive margins. -/
theorem value_ceiling_nonnegative (coordinate : Fin 2) :
    0 ≤ Variation.Arithmetic.valueCeiling Sampling.parameter Sampling.increment coordinate PrimitiveTaylor.box
      Sampling.jet.clearance.sourceFloor
      Sampling.jet.clearance.targetFloor Sampling.jet.clearance.sumFloor :=
  Variation.Arithmetic.valueCeiling_nonnegative Sampling.parameter Sampling.increment coordinate PrimitiveTaylor.box
    Sampling.jet.clearance.sourcePositive
    Sampling.jet.clearance.targetPositive Sampling.jet.clearance.sumPositive

/-- Both actual first-row ceilings have the same retained-margin nonnegativity proof needed by weighted consumers. -/
theorem first_ceiling_nonnegative (coordinate : Fin 2) :
    0 ≤ Variation.Arithmetic.firstCeiling Sampling.parameter Sampling.increment coordinate PrimitiveTaylor.box
      PrimitiveTaylor.inverseBox
      Sampling.jet.clearance.sourceFloor Sampling.jet.clearance.targetFloor Sampling.jet.clearance.sumFloor :=
  Variation.Arithmetic.firstCeiling_nonnegative Sampling.parameter Sampling.increment coordinate PrimitiveTaylor.box
    PrimitiveTaylor.inverseBox
    Sampling.jet.clearance.sourcePositive Sampling.jet.clearance.targetPositive Sampling.jet.clearance.sumPositive

end TestPurelib.Curves.Legendre.PeriodVariation.Bounds

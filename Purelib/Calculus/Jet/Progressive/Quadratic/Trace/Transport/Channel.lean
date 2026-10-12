module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
import Purelib.Approximation.Rational.Geometric.Scale
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Approximation.Gaussian.Sequence.Geometric (Channel)
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace (Transport)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_scale_mono)

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib

section Trace

section
open Purelib.Approximation.Gaussian.Sequence.Geometric
section
open Purelib.Data
open Purelib.Calculus.Jet.Quadratic.Basic
namespace CCL.Progressive.AutomaticQuadraticTrace.Trace

/-- Sum the geometric error scales of the five certificate channels. -/
private def totalScale {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Rational :=
  incrementField.errorScale + baseField.errorScale + outputField.errorScale +
    slopeField.errorScale + remainderField.errorScale

end CCL.Progressive.AutomaticQuadraticTrace.Trace

namespace Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

/-- Sum the geometric error scales of the five certificate channels. -/
def
  totalScalePublic
  {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Rational :=
  incrementField.errorScale + baseField.errorScale + outputField.errorScale +
    slopeField.errorScale + remainderField.errorScale

end Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

namespace CCL.Progressive.AutomaticQuadraticTrace.Trace

/-- Sum the quadrance bounds of the five certificate channels. -/
private def totalBound {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Rational :=
  incrementField.centerBound + baseField.centerBound + outputField.centerBound +
    slopeField.centerBound + remainderField.centerBound

end CCL.Progressive.AutomaticQuadraticTrace.Trace

namespace Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

/-- Sum the quadrance bounds of the five certificate channels. -/
def
  totalBoundPublic
  {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Rational :=
  incrementField.centerBound + baseField.centerBound + outputField.centerBound +
    slopeField.centerBound + remainderField.centerBound

end Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

end

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
open Purelib.Data
open Purelib.Calculus.Jet.Quadratic.Basic
namespace CCL.Progressive.AutomaticQuadraticTrace.Trace

/-- Each channel's nonnegative error scale is at most the sum of all five scales. -/
private theorem component_le_totalScale
    {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    incrementField.errorScale ≤
      Transport.Channel.AutomaticQuadraticTrace.totalScalePublic
      incrementField baseField
      outputField
        slopeField remainderField ∧
      baseField.errorScale ≤
        Transport.Channel.AutomaticQuadraticTrace.totalScalePublic
        incrementField baseField outputField
        slopeField remainderField ∧
      outputField.errorScale ≤
        Transport.Channel.AutomaticQuadraticTrace.totalScalePublic
        incrementField baseField
        outputField
        slopeField remainderField ∧
      slopeField.errorScale ≤
        Transport.Channel.AutomaticQuadraticTrace.totalScalePublic
        incrementField baseField
        outputField
        slopeField remainderField ∧
      remainderField.errorScale ≤
        Transport.Channel.AutomaticQuadraticTrace.totalScalePublic
        incrementField baseField
        outputField
        slopeField remainderField := by
  unfold Transport.Channel.AutomaticQuadraticTrace.totalScalePublic
  constructor
  · calc
      incrementField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale :=
        le_add_of_nonneg_right baseField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale :=
        le_add_of_nonneg_right outputField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      baseField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale :=
        le_add_of_nonneg_left incrementField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale :=
        le_add_of_nonneg_right outputField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      outputField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale + outputField.errorScale :=
        le_add_of_nonneg_left (add_nonneg incrementField.errorScale_nonneg
          baseField.errorScale_nonneg)
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      slopeField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale + outputField.errorScale +
            slopeField.errorScale :=
        le_add_of_nonneg_left (add_nonneg (add_nonneg
          incrementField.errorScale_nonneg baseField.errorScale_nonneg)
          outputField.errorScale_nonneg)
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  · exact le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg
      incrementField.errorScale_nonneg baseField.errorScale_nonneg)
      outputField.errorScale_nonneg) slopeField.errorScale_nonneg)

end CCL.Progressive.AutomaticQuadraticTrace.Trace

namespace Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

/-- Each channel's nonnegative error scale is at most the sum of all five scales. -/
theorem
  component_le_totalScalePublic
  {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    incrementField.errorScale ≤ totalScalePublic incrementField baseField
      outputField
        slopeField remainderField ∧
      baseField.errorScale ≤ totalScalePublic incrementField baseField outputField
        slopeField remainderField ∧
      outputField.errorScale ≤ totalScalePublic incrementField baseField
        outputField
        slopeField remainderField ∧
      slopeField.errorScale ≤ totalScalePublic incrementField baseField
        outputField
        slopeField remainderField ∧
      remainderField.errorScale ≤ totalScalePublic incrementField baseField
        outputField
        slopeField remainderField := by
  unfold totalScalePublic
  constructor
  · calc
      incrementField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale :=
        le_add_of_nonneg_right baseField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale :=
        le_add_of_nonneg_right outputField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      baseField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale :=
        le_add_of_nonneg_left incrementField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale :=
        le_add_of_nonneg_right outputField.errorScale_nonneg
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      outputField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale + outputField.errorScale :=
        le_add_of_nonneg_left (add_nonneg incrementField.errorScale_nonneg
          baseField.errorScale_nonneg)
      _ ≤ incrementField.errorScale + baseField.errorScale +
          outputField.errorScale + slopeField.errorScale :=
        le_add_of_nonneg_right slopeField.errorScale_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  constructor
  · calc
      slopeField.errorScale ≤ incrementField.errorScale +
          baseField.errorScale + outputField.errorScale +
            slopeField.errorScale :=
        le_add_of_nonneg_left (add_nonneg (add_nonneg
          incrementField.errorScale_nonneg baseField.errorScale_nonneg)
          outputField.errorScale_nonneg)
      _ ≤ _ := le_add_of_nonneg_right remainderField.errorScale_nonneg
  · exact le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg
      incrementField.errorScale_nonneg baseField.errorScale_nonneg)
      outputField.errorScale_nonneg) slopeField.errorScale_nonneg)

end Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

namespace CCL.Progressive.AutomaticQuadraticTrace.Trace

/-- Each channel's nonnegative quadrance bound is at most the sum of all five bounds. -/
private theorem component_le_totalBound
    {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    incrementField.centerBound ≤
      Transport.Channel.AutomaticQuadraticTrace.totalBoundPublic
      incrementField baseField
      outputField
        slopeField remainderField ∧
      baseField.centerBound ≤
        Transport.Channel.AutomaticQuadraticTrace.totalBoundPublic
        incrementField baseField
        outputField
        slopeField remainderField ∧
      outputField.centerBound ≤
        Transport.Channel.AutomaticQuadraticTrace.totalBoundPublic
        incrementField baseField
        outputField
        slopeField remainderField ∧
      slopeField.centerBound ≤
        Transport.Channel.AutomaticQuadraticTrace.totalBoundPublic
        incrementField baseField
        outputField
        slopeField remainderField ∧
      remainderField.centerBound ≤
        Transport.Channel.AutomaticQuadraticTrace.totalBoundPublic
        incrementField baseField
        outputField
        slopeField remainderField := by
  unfold Transport.Channel.AutomaticQuadraticTrace.totalBoundPublic
  constructor
  · calc
      incrementField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound :=
        le_add_of_nonneg_right baseField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound :=
        le_add_of_nonneg_right outputField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      baseField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound :=
        le_add_of_nonneg_left incrementField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound :=
        le_add_of_nonneg_right outputField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      outputField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound + outputField.centerBound :=
        le_add_of_nonneg_left (add_nonneg incrementField.centerBound_nonneg
          baseField.centerBound_nonneg)
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      slopeField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound + outputField.centerBound +
            slopeField.centerBound :=
        le_add_of_nonneg_left (add_nonneg (add_nonneg
          incrementField.centerBound_nonneg baseField.centerBound_nonneg)
          outputField.centerBound_nonneg)
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  · exact le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg
      incrementField.centerBound_nonneg baseField.centerBound_nonneg)
      outputField.centerBound_nonneg) slopeField.centerBound_nonneg)

end CCL.Progressive.AutomaticQuadraticTrace.Trace

namespace Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

/-- Each channel's nonnegative quadrance bound is at most the sum of all five bounds. -/
theorem
  component_le_totalBoundPublic
  {increment : Nat → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    incrementField.centerBound ≤ totalBoundPublic incrementField baseField
      outputField
        slopeField remainderField ∧
      baseField.centerBound ≤ totalBoundPublic incrementField baseField
        outputField
        slopeField remainderField ∧
      outputField.centerBound ≤ totalBoundPublic incrementField baseField
        outputField
        slopeField remainderField ∧
      slopeField.centerBound ≤ totalBoundPublic incrementField baseField
        outputField
        slopeField remainderField ∧
      remainderField.centerBound ≤ totalBoundPublic incrementField baseField
        outputField
        slopeField remainderField := by
  unfold totalBoundPublic
  constructor
  · calc
      incrementField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound :=
        le_add_of_nonneg_right baseField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound :=
        le_add_of_nonneg_right outputField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      baseField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound :=
        le_add_of_nonneg_left incrementField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound :=
        le_add_of_nonneg_right outputField.centerBound_nonneg
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      outputField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound + outputField.centerBound :=
        le_add_of_nonneg_left (add_nonneg incrementField.centerBound_nonneg
          baseField.centerBound_nonneg)
      _ ≤ incrementField.centerBound + baseField.centerBound +
          outputField.centerBound + slopeField.centerBound :=
        le_add_of_nonneg_right slopeField.centerBound_nonneg
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  constructor
  · calc
      slopeField.centerBound ≤ incrementField.centerBound +
          baseField.centerBound + outputField.centerBound +
            slopeField.centerBound :=
        le_add_of_nonneg_left (add_nonneg (add_nonneg
          incrementField.centerBound_nonneg baseField.centerBound_nonneg)
          outputField.centerBound_nonneg)
      _ ≤ _ := le_add_of_nonneg_right remainderField.centerBound_nonneg
  · exact le_add_of_nonneg_left (add_nonneg (add_nonneg (add_nonneg
      incrementField.centerBound_nonneg baseField.centerBound_nonneg)
      outputField.centerBound_nonneg) slopeField.centerBound_nonneg)

end Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel.AutomaticQuadraticTrace

end

namespace Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Combine five geometric channels into transport for their exact certificate sequence.

The common scale and bound are the sums of the corresponding channel values. Each original estimate is enlarged to the
common value while preserving the indexed increment and certificate sequence. -/
def transportOfChannels {increment : Nat
  → Canonical}
    {certificates : (index : Nat) → Certificate (increment index)}
    (incrementField : Channel increment)
    (baseField : Channel (fun index => (certificates index).base))
    (outputField : Channel (fun index => (certificates index).output))
    (slopeField : Channel (fun index => (certificates index).slope))
    (remainderField : Channel (fun index => (certificates index).remainder)) :
    Trace.Transport
      increment certificates := by
  let scale := AutomaticQuadraticTrace.totalScalePublic incrementField baseField outputField slopeField
    remainderField
  let bound := AutomaticQuadraticTrace.totalBoundPublic incrementField baseField outputField slopeField
    remainderField
  have scaleNonnegative : 0 ≤ scale := by
    dsimp only [scale, AutomaticQuadraticTrace.totalScalePublic]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      incrementField.errorScale_nonneg baseField.errorScale_nonneg)
      outputField.errorScale_nonneg) slopeField.errorScale_nonneg)
      remainderField.errorScale_nonneg
  have boundNonnegative : 0 ≤ bound := by
    dsimp only [bound, AutomaticQuadraticTrace.totalBoundPublic]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      incrementField.centerBound_nonneg baseField.centerBound_nonneg)
      outputField.centerBound_nonneg) slopeField.centerBound_nonneg)
      remainderField.centerBound_nonneg
  rcases AutomaticQuadraticTrace.component_le_totalScalePublic incrementField baseField outputField
    slopeField remainderField with ⟨incrementScale, baseScale, outputScale,
      slopeScale, remainderScale⟩
  rcases AutomaticQuadraticTrace.component_le_totalBoundPublic incrementField baseField outputField
    slopeField remainderField with ⟨incrementBound, baseBound, outputBound,
      slopeBound, remainderBound⟩
  exact
    { errorScale := scale
      errorScale_nonneg := scaleNonnegative
      increment_later_close := fun order => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (incrementField.later_close order).trans
          (quarterRadius_scale_mono incrementScale _)
      base_later_close := fun order => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (baseField.later_close order).trans
          (quarterRadius_scale_mono baseScale _)
      output_later_close := fun order => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (outputField.later_close order).trans
          (quarterRadius_scale_mono outputScale _)
      slope_later_close := fun order => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (slopeField.later_close order).trans
          (quarterRadius_scale_mono slopeScale _)
      remainder_later_close := fun order => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (remainderField.later_close order).trans
          (quarterRadius_scale_mono remainderScale _)
      centerBound := bound
      centerBound_nonneg := boundNonnegative
      increment_bounded := fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (incrementField.bounded index).trans incrementBound
      base_bounded := fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (baseField.bounded index).trans baseBound
      output_bounded := fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (outputField.bounded index).trans outputBound
      slope_bounded := fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (slopeField.bounded index).trans slopeBound
      remainder_bounded := fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (remainderField.bounded index).trans remainderBound }

end Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel

end

end Trace

end Purelib

end

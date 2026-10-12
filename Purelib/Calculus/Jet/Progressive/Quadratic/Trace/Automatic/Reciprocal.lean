module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Channel
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel.Reciprocal
import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
public section

/-!
# Automatic reciprocal transport for progressive quadratic traces

Uniform positive lower quadrance bounds certify both inverse channels. The
retained slope and residual channels assemble the same indexed reciprocal
certificates, and division uses this transport for the denominator.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal

section Trace

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace in
open Purelib.Data in
/-- Invert a quadratic trace using uniform positive base and output quadrance bounds.

The rational lower bounds prove pointwise nonzeroness and provide reciprocal channel estimates. The inverse slope and
exact residual channels then determine the common transport for the reciprocal certificates. -/
@[expose] def reciprocalAutomatic {increment : Nat → Canonical} (trace : Trace increment)
    (baseLower outputLower : Rational)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Gaussian.Norm.Basic.normSq (trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Gaussian.Norm.Basic.normSq (trace.certificate index).output) :
    Trace increment := by
  let baseNonzero : ∀ index, (trace.certificate index).base ≠ 0 := by
    intro index zero
    have bound := baseApart index
    rw [zero, Gaussian.Norm.Basic.normSq_zero] at bound
    exact (not_le_of_gt baseLowerPositive) bound
  let outputNonzero : ∀ index, (trace.certificate index).output ≠ 0 := by
    intro index zero
    have bound := outputApart index
    rw [zero, Gaussian.Norm.Basic.normSq_zero] at bound
    exact (not_le_of_gt outputLowerPositive) bound
  let certificates := fun index =>
    (trace.certificate index).reciprocal (baseNonzero index)
      (outputNonzero index)
  let incrementChannel := (Channel.incrementField trace)
  let baseInverse := (Channel.baseField trace).reciprocal baseLower baseLowerPositive
    baseApart
  let outputInverse := (Channel.outputField trace).reciprocal outputLower
    outputLowerPositive outputApart
  let slopeChannel :=
    ((Channel.slopeField trace).mul (baseInverse.mul baseInverse)).neg
  let remainderChannel :=
    (outputInverse.sub baseInverse).sub (incrementChannel.mul slopeChannel)
  have baseChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).base) :=
    baseInverse.map (by
      intro index
      change (trace.certificate index).base⁻¹ =
        Gaussian.Field.inv (trace.certificate index).base
      exact Gaussian.Field.inv_eq _)
  have outputChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).output) :=
    outputInverse.map (by
      intro index
      change (trace.certificate index).output⁻¹ =
        Gaussian.Field.inv (trace.certificate index).output
      exact Gaussian.Field.inv_eq _)
  have slopeChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by
      intro index
      change
        -((trace.certificate index).slope *
            ((trace.certificate index).base⁻¹ *
              (trace.certificate index).base⁻¹)) =
          -((trace.certificate index).slope *
            (Gaussian.Field.inv (trace.certificate index).base *
              Gaussian.Field.inv (trace.certificate index).base))
      simp only [-eq_self, -iff_self, Gaussian.Field.inv_eq]
      rfl)
  have remainderChannel' :
      Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by
      intro index
      change
        (trace.certificate index).output⁻¹ -
            (trace.certificate index).base⁻¹ - increment index *
              -((trace.certificate index).slope *
                ((trace.certificate index).base⁻¹ *
                  (trace.certificate index).base⁻¹)) =
          Gaussian.Field.inv (trace.certificate index).output -
            Gaussian.Field.inv (trace.certificate index).base - increment index *
              -((trace.certificate index).slope *
                (Gaussian.Field.inv (trace.certificate index).base *
                  Gaussian.Field.inv (trace.certificate index).base))
      simp only [-eq_self, -iff_self, Gaussian.Field.inv_eq]
      rfl)
  exact Trace.ofTransport
    (Transport.Channel.transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic
open Purelib.Data
/-- Each automatic reciprocal certificate is the displayed reciprocal of the original indexed certificate. -/
@[simp] theorem reciprocalAutomatic_certificate
    {increment : Nat → Canonical} (trace : Trace increment)
    (baseLower outputLower : Rational)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Gaussian.Norm.Basic.normSq (trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Gaussian.Norm.Basic.normSq (trace.certificate index).output)
    (index : Nat) :
    (reciprocalAutomatic trace baseLower outputLower baseLowerPositive
      outputLowerPositive baseApart outputApart).certificate index =
      (trace.certificate index).reciprocal
        (by
          intro zero
          have bound := baseApart index
          rw [zero, Gaussian.Norm.Basic.normSq_zero] at bound
          exact (not_le_of_gt baseLowerPositive) bound)
        (by
          intro zero
          have bound := outputApart index
          rw [zero, Gaussian.Norm.Basic.normSq_zero] at bound
          exact (not_le_of_gt outputLowerPositive) bound) := rfl

/-- Divide two traces by automatically multiplying with the certified reciprocal denominator.

The inputs share their increment sequence. Uniform positive rational lower bounds for the denominator's base and output
quadrances supply the reciprocal transport. -/
@[expose] def divAutomatic {increment : Nat → Canonical}
    (numerator denominator : Trace increment)
    (baseLower outputLower : Rational)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Gaussian.Norm.Basic.normSq (denominator.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Gaussian.Norm.Basic.normSq (denominator.certificate index).output) :
    Trace increment :=
  Arithmetic.mulAutomatic numerator
    (reciprocalAutomatic denominator baseLower outputLower baseLowerPositive
      outputLowerPositive baseApart outputApart)
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal

end

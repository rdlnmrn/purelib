module

import TestPurelib.Curves.Legendre.ParallelDifferential
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Bounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Data.Rat.Fraction.Cast

/-! # Paid parameter rows on an actual original parallel layer

The existing first labelled parallel quarter supplies its original paid
piece and one actual midpoint-refined layer. The actual parameter sampler
retains every node's source preparation, cofactor certificate, accepted
parameter step, full cubic roots, paired requests and arithmetic rows.
Its original physical weights assemble both finite row banks, whose
uniform remainder bounds and common inverse enclosure are derived internally.

This construction-chain regression checks source declarations and complete
code emission; it does not execute the full sampling bank or identify its
finite samples with a geometric target period.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Parallel

open Purelib
open Purelib.Algebra
open Purelib.Curves.Legendre.Degeneration
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
open TestPurelib.Curves.Legendre

/-- The actual midpoint-refined layer comes from the identical existing original first-quarter scalar piece. -/
private def layer := (ParallelDifferential.valuePiece 0 .first).layerAt 1

/-- The small nonzero parameter increment uses the original direct integer denominator conversion. -/
private def increment : Canonical := ⟨1 / Fraction.Cast.fromInt 256, 0⟩

/-- The closed original parameter increment is nonzero. -/
private theorem increment_nonzero : increment ≠ 0 := by
  decide +kernel

/-- The increment pays the exact original common admission at the unchanged first labelled parameter. -/
private theorem admitted : Radial.Parameter.IncrementBound 0 (ParallelDifferential.parameter 0) increment := by
  unfold Radial.Parameter.IncrementBound
  change Norm.Basic.normSq increment ≤
    (1 / 256 : Fraction.Rational) * Norm.Basic.normSq (⟨1 / 16, 0⟩ : Canonical)
  have cast256 : (256 : Fraction.Rational) = Fraction.Cast.fromInt (256 : Int) :=
    (Fraction.Cast.natCast_eq_fromInt (256 : Nat)).trans (by decide +kernel)
  have cast16 : (16 : Fraction.Rational) = Fraction.Cast.fromInt (16 : Int) :=
    (Fraction.Cast.natCast_eq_fromInt (16 : Nat)).trans (by decide +kernel)
  rewrite [cast256, cast16]
  unfold increment
  decide +kernel

/-- Build the complete original dependent node-cache chain once on that retained actual layer. -/
private def samples : Layer.Parameter.Samples layer (ParallelDifferential.regular 0) increment admitted
    increment_nonzero :=
  Layer.Parameter.build layer (ParallelDifferential.regular 0) increment admitted increment_nonzero

attribute [local irreducible] layer samples

/-- The original dyadic layer count supplies the direct zero index without a replacement finite enumeration. -/
private def node0 : Fin layer.pieces.length :=
  ⟨0, by rewrite [layer.count]; decide +kernel⟩

/-- The actual original refined layer contains its two retained midpoint pieces. -/
theorem node_count : layer.pieces.length = 2 := layer.count

/-- Node zero retains the exact division-preparation constructor on its original geometric source lift. -/
theorem original_preparation : (samples.preparations.get node0).val =
    (layer.node node0).source.parallelPrepared (ParallelDifferential.regular 0) :=
  samples.preparation_eq node0

/-- The source cubic certificate's two exact index casts keep the same cached original prepared coherent value. -/
theorem source_value : (Layer.Parameter.sourceRoot layer samples.roots node0).value =
    (samples.preparations.get node0).val.denominator := by
  unfold Layer.Parameter.sourceRoot
  rewrite [CertifiedSquareRoot.Certificate.castParameter_value,
    Radial.Parameter.Roots.Sampling.Jet.sourceRoot_value]
  exact (samples.roots.get node0).val.source_value

/-- The full source cubic certificate remains operationally linked to the identical original geometric input process. -/
def source_agrees : Approximation.Gaussian.Equivalence.NamedEquivalent
    (layer.node node0).source.lift.value.name (samples.roots.get node0).val.sourceRoot.value.name :=
  (samples.roots.get node0).val.source_agrees

/-- The target forward-coordinate channel uses the complete original source cofactor certificate cache. -/
theorem cofactor_cache : (samples.steps.get node0).val.channels.unitRoot = (layer.node node0).source.lift.unitRoot :=
  (samples.steps.get node0).val.channels_unitRoot

/-- The saved paired request is the complete original request on those identical stored full cubic root caches. -/
theorem original_request : (samples.requests.get node0).val =
    Radial.Parameter.Roots.Sampling.Jet.request (samples.roots.get node0).val increment_nonzero :=
  samples.request_eq node0

/-- The physical-node source observation is the identical original paid observation of that same cached pair. -/
theorem source_observation : (samples.jets.get node0).val.sourceSample.observation =
    (samples.requests.get node0).val.pair.source.observation :=
  samples.sourceObservation_pair node0

/-- The distinct target observation is unchanged by the scalar core's exact physical-node index transport. -/
theorem target_observation : (samples.jets.get node0).val.targetSample.observation =
    (samples.requests.get node0).val.pair.target.observation :=
  samples.targetObservation_pair node0

/-- The physical-node source still uses the exact original square-comparison sampling index. -/
theorem source_index : (samples.jets.get node0).val.sourceSample.comparison.leftIndex =
    (samples.requests.get node0).val.pair.source.comparison.leftIndex :=
  samples.sourceIndex_pair node0

/-- The independently selected target square-comparison index remains linked to the identical original pair. -/
theorem target_index : (samples.jets.get node0).val.targetSample.comparison.leftIndex =
    (samples.requests.get node0).val.pair.target.comparison.leftIndex :=
  samples.targetIndex_pair node0

/-- The same actual ten-entry arithmetic row bank consumes the identical original saved node core. -/
theorem original_rows : (samples.rows.get node0).val = Variation.Arithmetic.request (samples.jets.get node0).val :=
  samples.row_eq node0

/-- The single saved physical-weight vector is exactly the original layer's oriented weight materialization. -/
theorem original_weights : samples.weights = layer.weights := samples.weights_eq

/-- The exact source reading uses the reciprocal enclosure computed internally from retained geometric floors. -/
theorem source_inverse : samples.inverseBox.Contains (samples.jets.get node0).val.sourceSample.reading⁻¹ :=
  samples.sourceInverse_inside node0

/-- The distinct actual target inverse shares that internally computed common box without another request. -/
theorem target_inverse : samples.inverseBox.Contains (samples.jets.get node0).val.targetSample.reading⁻¹ :=
  samples.targetInverse_inside node0

/-- Both actual value rows satisfy their internally computed uniform factors on the same original physical weights. -/
theorem value_factor (coordinate : Fin 2) : (samples.bank.value coordinate).factor ≤
    (((25 / 4) * Norm.Basic.normSq (halfGap 0 (ParallelDifferential.parameter 0))) *
      (ParallelDifferential.valuePiece 0 .first).span.width ^ 2) * samples.valueCeiling coordinate :=
  samples.value_factor_le coordinate

/-- Both first rows keep the original shared inverse/cubic caches and their independent actual second slopes. -/
theorem first_factor (coordinate : Fin 2) : (samples.bank.first coordinate).factor ≤
    (((25 / 4) * Norm.Basic.normSq (halfGap 0 (ParallelDifferential.parameter 0))) *
      (ParallelDifferential.valuePiece 0 .first).span.width ^ 2) * samples.firstCeiling coordinate :=
  samples.first_factor_le coordinate

/-- The actual weighted value samples and first slopes have the internally derived finite fourth-order bound. -/
theorem value_remainder (coordinate : Fin 2) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.targetValue coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceValue coordinate).reading) -
        increment * FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceFirst coordinate).reading)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap 0 (ParallelDifferential.parameter 0))) *
        (ParallelDifferential.valuePiece 0 .first).span.width ^ 2) * samples.valueCeiling coordinate) *
          Canonical.normSq increment ^ 2 :=
  samples.value_remainder_le coordinate

/-- The actual first samples retain their independently observed second derivatives in the same finite bound. -/
theorem first_remainder (coordinate : Fin 2) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.targetFirst coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceFirst coordinate).reading) -
        increment * FiniteSum.Fin.sumFin (fun node =>
          samples.weights node * ((samples.rows.get node).val.sourceSecond coordinate).reading)) ≤
      ((((25 / 4) * Norm.Basic.normSq (halfGap 0 (ParallelDifferential.parameter 0))) *
        (ParallelDifferential.valuePiece 0 .first).span.width ^ 2) * samples.firstCeiling coordinate) *
          Canonical.normSq increment ^ 2 :=
  samples.first_remainder_le coordinate

end TestPurelib.Curves.Legendre.PeriodVariation.Parallel

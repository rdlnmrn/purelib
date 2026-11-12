module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Variation
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling.Jet
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Transport
import Purelib.Data.Vector.Dependent
import Purelib.Data.Nat.BinaryNormalization

/-! # Actual parameter samples on an original parallel refinement layer

Successive dependent vectors retain each original piece's preparation,
normalized anchor, parameter step, full cubic roots, paired scalar request
and arithmetic rows. Exact spatial-index transports align those same cached
cores with the original materialized physical points. One retained weight
vector and the existing weighted bank consume these identical observations.

The construction starts from the actual layer, source regularity and the
common admitted nonzero increment. It accepts no separate root or sample
factor bounds, and does not identify the weighted samples with a geometric
integral.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
open Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling (SampledJet)

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter increment : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Radial.Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {initial : Radial.Differential.Refinement.Piece data actual accuracy} {depth : Nat}

/-- Exact spatial readback identifies each original source point with the retained materialized layer node. -/
theorem point_eq (layer : Layer initial depth) (node : Fin layer.pieces.length) :
    (Radial.Parameter.sourcePoint site parameter
      (Waist.direction quarter (layer.node node).span.lower)).base = layer.points node :=
  (layer.points_apply node).symm

/-- Materialized preparations keep each original piece's complete parallel cubic source and constructor equation. -/
@[expose] def Preparations (layer : Layer initial depth) (regular : parameter ≠ criticalValue site) : Type 2 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { prepared : Division.Prepared (layer.node node).source.lift.value //
      prepared = (layer.node node).source.parallelPrepared regular })

/-- Each retained anchor belongs to its exact original piece's lift and original quarter admission. -/
@[expose] def Anchors (layer : Layer initial depth) (regular : parameter ≠ criticalValue site) : Type 2 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { anchor : Radial.Parameter.Anchor (layer.node node).source.lift //
      anchor = Radial.Parameter.Anchor.build (layer.node node).source.lift regular actual.data.bound })

/-- The original common increment advances each exact cached anchor once. -/
@[expose] def Steps (layer : Layer initial depth) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : Radial.Parameter.IncrementBound site parameter increment)
    (anchors : Anchors layer regular) : Type 2 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { step : Radial.Parameter.Step (anchors.get node).val increment //
      step = Radial.Parameter.Step.build (anchors.get node).val increment admitted })

/-- Both complete cubic certificates at each original node consume the same retained preparation and step caches. -/
@[expose] def Roots (layer : Layer initial depth) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : Radial.Parameter.IncrementBound site parameter increment)
    (preparations : Preparations layer regular) (anchors : Anchors layer regular)
    (steps : Steps layer regular increment admitted anchors) : Type 2 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { roots : Radial.Parameter.Roots (steps.get node).val (preparations.get node).val //
      roots = Radial.Parameter.Roots.build (steps.get node).val (preparations.get node).val })

/-- Every original node stores one actual paired request and its same cached scalar core. -/
@[expose] def Requests (layer : Layer initial depth) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : Radial.Parameter.IncrementBound site parameter increment)
    (nonzero : increment ≠ 0) (preparations : Preparations layer regular) (anchors : Anchors layer regular)
    (steps : Steps layer regular increment admitted anchors)
    (roots : Roots layer regular increment admitted preparations anchors steps) : Type 1 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { requested : Roots.Sampling.Jet.Requested (roots.get node).val nonzero //
      requested = Roots.Sampling.Jet.request (roots.get node).val nonzero })

/-- The original dyadic count gives a direct zero index into the nonempty actual node list. -/
private def firstNode (layer : Layer initial depth) : Fin layer.pieces.length :=
  ⟨0, by
    rewrite [layer.count]
    exact (Nat.zero_lt_succ depth).trans_le (Nat.BinaryNormalization.succ_le_two_pow depth)⟩

/-- The first retained original step supplies the common unit-quadrance range of the admitted parameter increment. -/
theorem unit (layer : Layer initial depth) {regular : parameter ≠ criticalValue site}
    {increment : Canonical} {admitted : Radial.Parameter.IncrementBound site parameter increment}
    {anchors : Anchors layer regular} (steps : Steps layer regular increment admitted anchors) :
    Norm.Basic.normSq increment ≤ 1 :=
  Roots.Sampling.Jet.increment_unit (steps.get (firstNode layer)).val

/-- Spatial readback casts the complete original source certificate onto the identical materialized physical node. -/
@[expose] def sourceRoot (layer : Layer initial depth) {regular : parameter ≠ criticalValue site}
    {increment : Canonical} {admitted : Radial.Parameter.IncrementBound site parameter increment}
    {preparations : Preparations layer regular} {anchors : Anchors layer regular}
    {steps : Steps layer regular increment admitted anchors}
    (roots : Roots layer regular increment admitted preparations anchors steps) (node : Fin layer.pieces.length) :
    CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter (layer.points node)) :=
  (Roots.Sampling.Jet.sourceRoot (roots.get node).val).castParameter
    (congrArg (Polynomials.curveValue parameter) (point_eq layer node))

/-- The changed-parameter full certificate retains its same original root cache under the matching physical readback. -/
@[expose] def targetRoot (layer : Layer initial depth) {regular : parameter ≠ criticalValue site}
    {increment : Canonical} {admitted : Radial.Parameter.IncrementBound site parameter increment}
    {preparations : Preparations layer regular} {anchors : Anchors layer regular}
    {steps : Steps layer regular increment admitted anchors}
    (roots : Roots layer regular increment admitted preparations anchors steps) (node : Fin layer.pieces.length) :
    CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) (layer.points node)) :=
  (Roots.Sampling.Jet.targetRoot (roots.get node).val).castParameter
    (congrArg (Polynomials.curveValue (parameter + increment)) (point_eq layer node))

/-- The same original sampled core is reindexed onto the physical node without reconstructing any scalar certificate. -/
@[expose] def core (layer : Layer initial depth) {regular : parameter ≠ criticalValue site}
    {increment : Canonical} {admitted : Radial.Parameter.IncrementBound site parameter increment}
    {nonzero : increment ≠ 0} {preparations : Preparations layer regular} {anchors : Anchors layer regular}
    {steps : Steps layer regular increment admitted anchors}
    {roots : Roots layer regular increment admitted preparations anchors steps}
    (requests : Requests layer regular increment admitted nonzero preparations anchors steps roots)
    (node : Fin layer.pieces.length) :
    SampledJet parameter increment (layer.points node)
      (sourceRoot layer roots node) (targetRoot layer roots node) (unit layer steps) :=
  (requests.get node).val.core.castPoint (point_eq layer node)

/-- Store each exactly transported original core in a dependent spine for shared arithmetic-row consumption. -/
@[expose] def Jets (layer : Layer initial depth) {regular : parameter ≠ criticalValue site}
    {increment : Canonical} {admitted : Radial.Parameter.IncrementBound site parameter increment}
    {nonzero : increment ≠ 0} {preparations : Preparations layer regular} {anchors : Anchors layer regular}
    {steps : Steps layer regular increment admitted anchors}
    {roots : Roots layer regular increment admitted preparations anchors steps}
    (requests : Requests layer regular increment admitted nonzero preparations anchors steps roots) : Type 1 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { jet : SampledJet parameter increment (layer.points node)
        (sourceRoot layer roots node) (targetRoot layer roots node) (unit layer steps) //
      jet = core layer requests node })

/-- Each materialized arithmetic row bank consumes the identical cached original node core once. -/
@[expose] def Rows (layer : Layer initial depth) {regular : parameter ≠ criticalValue site}
    {increment : Canonical} {admitted : Radial.Parameter.IncrementBound site parameter increment}
    {nonzero : increment ≠ 0} {preparations : Preparations layer regular} {anchors : Anchors layer regular}
    {steps : Steps layer regular increment admitted anchors}
    {roots : Roots layer regular increment admitted preparations anchors steps}
    {requests : Requests layer regular increment admitted nonzero preparations anchors steps roots}
    (jets : Jets layer requests) : Type 2 :=
  Vector.DependentVector (fun node : Fin layer.pieces.length =>
    { rows : Variation.Arithmetic.Observations (jets.get node).val //
      rows = Variation.Arithmetic.request (jets.get node).val })

/-- The complete retained original node-construction chain and its same weighted arithmetic bank.

All expensive dependent families are actual stored spines. Constructor
equations certify the original preparation, anchor, step, cubic root,
paired request and arithmetic-row operations at each identical node.
The final bank consumes those exact stored rows and the single retained
original physical-weight vector.
-/
@[expose] def Samples (layer : Layer initial depth) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : Radial.Parameter.IncrementBound site parameter increment)
    (nonzero : increment ≠ 0) : Type 2 :=
  Σ preparations : Preparations layer regular,
  Σ anchors : Anchors layer regular,
  Σ steps : Steps layer regular increment admitted anchors,
  Σ roots : Roots layer regular increment admitted preparations anchors steps,
  Σ requests : Requests layer regular increment admitted nonzero preparations anchors steps roots,
  Σ jets : Jets layer requests,
  Σ rows : Rows layer jets,
  Σ weights : { weights : Data.Vector Canonical layer.pieces.length // weights = layer.weights },
    { bank : Variation.Arithmetic.Weighted.Bank (fun node => (rows.get node).val) weights.val //
      bank = Variation.Arithmetic.Weighted.Bank.build (fun node => (rows.get node).val) weights.val }

/-- Build every original dependent cache once and assemble the existing weighted bank from those stored node rows. -/
def build (layer : Layer initial depth) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : Radial.Parameter.IncrementBound site parameter increment)
    (nonzero : increment ≠ 0) : Samples layer regular increment admitted nonzero :=
  let preparations : Preparations layer regular := Vector.DependentVector.ofFn
    (fun node => ⟨(layer.node node).source.parallelPrepared regular, rfl⟩)
  let anchors : Anchors layer regular := Vector.DependentVector.ofFn
    (fun node => ⟨Radial.Parameter.Anchor.build (layer.node node).source.lift regular actual.data.bound, rfl⟩)
  let steps : Steps layer regular increment admitted anchors := Vector.DependentVector.ofFn
    (fun node => ⟨Radial.Parameter.Step.build (anchors.get node).val increment admitted, rfl⟩)
  let roots : Roots layer regular increment admitted preparations anchors steps := Vector.DependentVector.ofFn
    (fun node => ⟨Radial.Parameter.Roots.build (steps.get node).val (preparations.get node).val, rfl⟩)
  let requests : Requests layer regular increment admitted nonzero preparations anchors steps roots :=
    Vector.DependentVector.ofFn
      (fun node => ⟨Roots.Sampling.Jet.request (roots.get node).val nonzero, rfl⟩)
  let jets : Jets layer requests := Vector.DependentVector.ofFn (fun node => ⟨core layer requests node, rfl⟩)
  let rows : Rows layer jets := Vector.DependentVector.ofFn
    (fun node => ⟨Variation.Arithmetic.request (jets.get node).val, rfl⟩)
  let weights := layer.weights
  let bank := Variation.Arithmetic.Weighted.Bank.build (fun node => (rows.get node).val) weights
  ⟨preparations, ⟨anchors, ⟨steps, ⟨roots, ⟨requests, ⟨jets, ⟨rows, ⟨⟨weights, rfl⟩, ⟨bank, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩

namespace Samples

variable {layer : Layer initial depth} {regular : parameter ≠ criticalValue site}
variable {admitted : Radial.Parameter.IncrementBound site parameter increment} {nonzero : increment ≠ 0}

/-- Read the original dependent preparation spine without preparing any node again. -/
@[expose] def preparations (samples : Samples layer regular increment admitted nonzero) :
    Preparations layer regular := samples.1

/-- Read the retained original normalized-anchor spine. -/
@[expose] def anchors (samples : Samples layer regular increment admitted nonzero) :
    Anchors layer regular := samples.2.1

/-- Read the actual accepted parameter steps on those identical cached anchors. -/
@[expose] def steps (samples : Samples layer regular increment admitted nonzero) :
    Steps layer regular increment admitted samples.anchors := samples.2.2.1

/-- Read both full original cubic-root certificates at each cached node. -/
@[expose] def roots (samples : Samples layer regular increment admitted nonzero) :
    Roots layer regular increment admitted samples.preparations samples.anchors samples.steps := samples.2.2.2.1

/-- Read the original paired requests and their same cached scalar cores. -/
@[expose] def requests (samples : Samples layer regular increment admitted nonzero) :
    Requests layer regular increment admitted nonzero samples.preparations samples.anchors samples.steps
      samples.roots := samples.2.2.2.2.1

/-- Read the stored spatial reindexings of those exact original scalar cores. -/
@[expose] def jets (samples : Samples layer regular increment admitted nonzero) :
    Jets layer samples.requests := samples.2.2.2.2.2.1

/-- Read the actual cached arithmetic rows on each retained original transported core. -/
@[expose] def rows (samples : Samples layer regular increment admitted nonzero) :
    Rows layer samples.jets := samples.2.2.2.2.2.2.1

/-- Read the single retained original physical-weight vector. -/
@[expose] def weights (samples : Samples layer regular increment admitted nonzero) :
    Data.Vector Canonical layer.pieces.length := samples.2.2.2.2.2.2.2.1.val

/-- Read the existing weighted bank consuming the same original arithmetic-row and weight caches. -/
@[expose] def bank (samples : Samples layer regular increment admitted nonzero) :
    Variation.Arithmetic.Weighted.Bank (fun node => (samples.rows.get node).val) samples.weights :=
  samples.2.2.2.2.2.2.2.2.val

/-- The cached preparation is the original operation on the same piece's original source lift. -/
theorem preparation_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.preparations.get node).val = (layer.node node).source.parallelPrepared regular :=
  (samples.preparations.get node).property

/-- Each actual retained anchor is the original known-root seed constructor on the same source lift. -/
theorem anchor_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.anchors.get node).val =
      Radial.Parameter.Anchor.build (layer.node node).source.lift regular actual.data.bound :=
  (samples.anchors.get node).property

/-- Each accepted original step uses its same cached anchor and the common admitted increment. -/
theorem step_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.steps.get node).val = Radial.Parameter.Step.build (samples.anchors.get node).val increment admitted :=
  (samples.steps.get node).property

/-- Both full cubic roots are the original construction on the same saved preparation and parameter step. -/
theorem roots_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.roots.get node).val =
      Radial.Parameter.Roots.build (samples.steps.get node).val (samples.preparations.get node).val :=
  (samples.roots.get node).property

/-- Each retained scalar request is the single original paired request on those same stored full cubic roots. -/
theorem request_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.requests.get node).val =
      Roots.Sampling.Jet.request (samples.roots.get node).val nonzero :=
  (samples.requests.get node).property

/-- The exact retained physical-node jet is solely the original cached core's spatial-index transport. -/
theorem jet_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.jets.get node).val = core layer samples.requests node := (samples.jets.get node).property

/-- Each actual arithmetic bank is requested once on its identical saved scalar core. -/
theorem row_eq (samples : Samples layer regular increment admitted nonzero) (node : Fin layer.pieces.length) :
    (samples.rows.get node).val = Variation.Arithmetic.request (samples.jets.get node).val :=
  (samples.rows.get node).property

/-- The weight cache is the complete original physical-weight materialization of the same layer. -/
theorem weights_eq (samples : Samples layer regular increment admitted nonzero) : samples.weights = layer.weights :=
  samples.2.2.2.2.2.2.2.1.property

/-- The final weighted bank is the original assembly on the actual saved row and weight vectors. -/
theorem bank_eq (samples : Samples layer regular increment admitted nonzero) :
    samples.bank = Variation.Arithmetic.Weighted.Bank.build (fun node => (samples.rows.get node).val) samples.weights :=
  samples.2.2.2.2.2.2.2.2.property

/-- The physical-node source observation is the exact original paid observation of its same cached pair. -/
theorem sourceObservation_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.sourceSample.observation =
    (samples.requests.get node).val.pair.source.observation := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_sourceObservation, (samples.requests.get node).val.core_eq]
  exact Roots.Sampling.Jet.ofPair_sourceObservation _ _

/-- The distinct target observation survives its same original cached core's exact spatial-index transport. -/
theorem targetObservation_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.targetSample.observation =
    (samples.requests.get node).val.pair.target.observation := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_targetObservation, (samples.requests.get node).val.core_eq]
  exact Roots.Sampling.Jet.ofPair_targetObservation _ _

/-- The physical-node source retains its exact original square-comparison sampling index. -/
theorem sourceIndex_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.sourceSample.comparison.leftIndex =
    (samples.requests.get node).val.pair.source.comparison.leftIndex := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_sourceIndex, (samples.requests.get node).val.core_eq]
  exact Roots.Sampling.Jet.ofPair_sourceIndex _ _

/-- The independent target square-comparison sampling index remains owned by the identical cached pair. -/
theorem targetIndex_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.targetSample.comparison.leftIndex =
    (samples.requests.get node).val.pair.target.comparison.leftIndex := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_targetIndex, (samples.requests.get node).val.core_eq]
  exact Roots.Sampling.Jet.ofPair_targetIndex _ _

/-- A node's transported jet retains the source floor of its identical original paid geometric pair. -/
theorem sourceFloor_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) :
    (samples.jets.get node).val.clearance.sourceFloor =
      (samples.requests.get node).val.pair.clearance.sourceFloor := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_sourceFloor]
  exact (congrArg (fun jet : Roots.Sampling.Jet.Core (samples.roots.get node).val =>
    jet.clearance.sourceFloor) (samples.requests.get node).val.core_eq).trans
      (Roots.Sampling.Jet.ofPair_sourceFloor (samples.requests.get node).val.pair rfl)

/-- The distinct target floor is read from the same retained paired request after spatial transport. -/
theorem targetFloor_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) :
    (samples.jets.get node).val.clearance.targetFloor =
      (samples.requests.get node).val.pair.clearance.targetFloor := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_targetFloor]
  exact (congrArg (fun jet : Roots.Sampling.Jet.Core (samples.roots.get node).val =>
    jet.clearance.targetFloor) (samples.requests.get node).val.core_eq).trans
      (Roots.Sampling.Jet.ofPair_targetFloor (samples.requests.get node).val.pair rfl)

/-- The same-pair sum clearance is preserved by the exact scalar-core spatial-index transport. -/
theorem sumFloor_pair (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) :
    (samples.jets.get node).val.clearance.sumFloor = (samples.requests.get node).val.pair.clearance.sumFloor := by
  rewrite [samples.jet_eq]
  unfold core
  rewrite [SampledJet.castPoint_sumFloor]
  exact (congrArg (fun jet : Roots.Sampling.Jet.Core (samples.roots.get node).val =>
    jet.clearance.sumFloor) (samples.requests.get node).val.core_eq).trans
      (Roots.Sampling.Jet.ofPair_sumFloor (samples.requests.get node).val.pair rfl)

/-- Every actual node's source floor equals the internally derived common half-gap margin. -/
theorem sourceFloor_uniform (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.clearance.sourceFloor =
    (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) :=
  (samples.sourceFloor_pair node).trans (samples.requests.get node).val.pair.clearance_sourceFloor

/-- Every actual target observation retains its stronger common half-gap margin. -/
theorem targetFloor_uniform (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.clearance.targetFloor =
    (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter) :=
  (samples.targetFloor_pair node).trans (samples.requests.get node).val.pair.clearance_targetFloor

/-- The actual paired sum margin is the identical common positive half-gap expression at every original node. -/
theorem sumFloor_uniform (samples : Samples layer regular increment admitted nonzero)
    (node : Fin layer.pieces.length) : (samples.jets.get node).val.clearance.sumFloor =
    (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) :=
  (samples.sumFloor_pair node).trans (samples.requests.get node).val.pair.clearance_sumFloor

end Samples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

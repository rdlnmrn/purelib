module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Samples
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sources.Radial
public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled.Radial
import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization.Roots
import Purelib.Data.Gaussian.Norm.Bounds
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original higher circle owners and their actual tower readings

One original argument's separation floor, radius and collar prepare every
source request before observation. Its same retained samples then supply
one original source expansion and one paid reading of the original formal
tower. Each original root reading inherits its owner's quantitative radial
side through the ordered sample correspondence.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial
open Dense.Basic (DensePolynomial)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Roots (Tower)
open Dense.Roots.Tower
open Dense.Roots.Tower.Reading
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open CenterProduct (Approximation)

universe u

namespace Higher

variable {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
variable {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
variable (argument : Approximation locations)
variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {formal : DensePolynomial K}
variable {tower : Tower K ring equality formal} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius}
variable (budget : Budget parameters target tolerance) {embed : Canonical → K}
variable (leading : Leading tower embed polynomial.leadingCoeff)

/-- The source request uses the fixed tower radius and this same original argument's separation and collar. -/
@[expose] def Request :=
  Sources.Radial budget leading argument.request.gaps.bound locations.request.collar.width

/-- The original formal budget supplies exactly one target per same original Gaussian factor root. -/
theorem targets_count (request : Request argument budget leading) (reading : GaussianReading parent embed)
    (sourceEq : polynomial = Dense.Map.map reading.read formal) :
    request.sources.targets.length = polynomial.natDegree :=
  request.sources.targets_length_eq_degree.trans
    (leading.observed_degree reading (DensePolynomial.leadingCoeff_ne_zero clearance.nonzero)
      polynomial sourceEq).symm

variable {argument budget leading}

/-- The same scheduled original sample type retains its original argument and complete source schedule. -/
@[expose] def Samples (request : Request argument budget leading) :=
  Roots.Samples argument request.sources.schedule.val

/-- The paid original model type retains the same sample nodes, budget, parent reading and radial cap. -/
@[expose] def Model (request : Request argument budget leading) (samples : Samples request)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain) :=
  Sampled budget reading gain_eq samples.nodes (request.radial.cap * request.sources.inverseNorm)

end Higher

set_option genInjectivity false in
/-- An original higher owner family and its same source-paid formal root reading.

The original argument, tower budget and initial reading remain indices. The
request is prepared before samples; those exact retained samples and their
original expansion construct the cached final reading. No root enumeration,
geometric label or final radial assertion is supplied separately.
The fixed tower radius covers the same original argument's sample ceiling.
-/
structure Higher {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
    {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
    (argument : Approximation locations) {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {formal : DensePolynomial K} {tower : Tower K ring equality formal} {parent : Weight K}
    {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K}
    (leading : Leading tower embed polynomial.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (sourceEq : polynomial = Dense.Map.map reading.read formal)
    (radiusBound : argument.request.radius ≤ radius) where
  /-- The source-fixed original radial cap and complete sufficient source schedule. -/
  request : Higher.Request argument budget leading
  /-- The request is the original automatic preparation on these same source bounds. -/
  request_eq : request = Sources.Radial.prepare budget leading argument.request.gaps.bound
    locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive
  /-- The actual scheduled continuations of the same original geometric samples. -/
  samples : Higher.Samples request
  /-- The samples use that exact retained original source schedule. -/
  samples_eq : samples = Roots.Samples.prepare argument request.sources.schedule.val
    request.sources.schedule.property (Higher.targets_count argument budget leading request reading sourceEq)
  /-- The original formal tower reading constructed from those same retained samples and divisions. -/
  model : Higher.Model request samples reading gain_eq
  /-- The model consumes the same original Gaussian factor and actual expansion without replay. -/
  model_eq : model = request.sources.realize reading gain_eq polynomial sourceEq samples.nodes
    samples.expansion (fun point member => (samples.node_bounds point member).trans radiusBound) samples.payment

constructive_injectivity Higher

namespace Higher

variable {polynomial : CoefficientPolynomial} {clearance : Certificate polynomial}
variable {source : FTA.Squarefree.BoxResult polynomial} {locations : HigherLocations clearance source}
variable {argument : Approximation locations} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {formal : DensePolynomial K} {tower : Tower K ring equality formal} {parent : Weight K}
variable {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
variable {budget : Budget parameters target tolerance} {embed : Canonical → K}
variable {leading : Leading tower embed polynomial.leadingCoeff} {reading : GaussianReading parent embed}
variable {gain_eq : reading.gain = gain} {sourceEq : polynomial = Dense.Map.map reading.read formal}
variable {radiusBound : argument.request.radius ≤ radius}

/-- Retain the actual original request, samples and model with their complete procedure equations. -/
@[expose] def ofModel (argument : Approximation locations) (budget : Budget parameters target tolerance)
    (leading : Leading tower embed polynomial.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (sourceEq : polynomial = Dense.Map.map reading.read formal)
    (radiusBound : argument.request.radius ≤ radius)
    (request : Request argument budget leading)
    (requestEq : request = Sources.Radial.prepare budget leading argument.request.gaps.bound
      locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive)
    (samples : Samples request)
    (samplesEq : samples = Roots.Samples.prepare argument request.sources.schedule.val
      request.sources.schedule.property (targets_count argument budget leading request reading sourceEq))
    (model : Model request samples reading gain_eq)
    (modelEq : model = request.sources.realize reading gain_eq polynomial sourceEq samples.nodes
      samples.expansion (fun point member => (samples.node_bounds point member).trans radiusBound) samples.payment) :
    Higher argument budget leading reading gain_eq sourceEq radiusBound :=
  { request, request_eq := requestEq, samples, samples_eq := samplesEq, model, model_eq := modelEq }

/-- Read the same original tower from retained scheduled samples, constructing its model once. -/
@[expose] def ofSamples (argument : Approximation locations) (budget : Budget parameters target tolerance)
    (leading : Leading tower embed polynomial.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (sourceEq : polynomial = Dense.Map.map reading.read formal)
    (radiusBound : argument.request.radius ≤ radius)
    (request : Request argument budget leading)
    (requestEq : request = Sources.Radial.prepare budget leading argument.request.gaps.bound
      locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive)
    (samples : Samples request)
    (samplesEq : samples = Roots.Samples.prepare argument request.sources.schedule.val
      request.sources.schedule.property (targets_count argument budget leading request reading sourceEq)) :
    Higher argument budget leading reading gain_eq sourceEq radiusBound :=
  let model := request.sources.realize reading gain_eq polynomial sourceEq samples.nodes
    samples.expansion (fun point member => (samples.node_bounds point member).trans radiusBound) samples.payment
  ofModel argument budget leading reading gain_eq sourceEq radiusBound request requestEq samples samplesEq model rfl

/-- Prepare all sufficient bounds before continuing the same original samples and reading their retained expansion. -/
@[expose] def prepare (argument : Approximation locations) (budget : Budget parameters target tolerance)
    (leading : Leading tower embed polynomial.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (sourceEq : polynomial = Dense.Map.map reading.read formal)
    (radiusBound : argument.request.radius ≤ radius) :
    Higher argument budget leading reading gain_eq sourceEq radiusBound :=
  let request := Sources.Radial.prepare budget leading argument.request.gaps.bound
    locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive
  let samples := Roots.Samples.prepare argument request.sources.schedule.val request.sources.schedule.property
    (targets_count argument budget leading request reading sourceEq)
  ofSamples argument budget leading reading gain_eq sourceEq radiusBound request rfl samples rfl

/-- Restoring the same original cached components returns the complete automatic association. -/
theorem ofModel_eq_prepare (argument : Approximation locations) (budget : Budget parameters target tolerance)
    (leading : Leading tower embed polynomial.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (sourceEq : polynomial = Dense.Map.map reading.read formal)
    (radiusBound : argument.request.radius ≤ radius)
    (request : Request argument budget leading)
    (requestEq : request = Sources.Radial.prepare budget leading argument.request.gaps.bound
      locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive)
    (samples : Samples request)
    (samplesEq : samples = Roots.Samples.prepare argument request.sources.schedule.val
      request.sources.schedule.property (targets_count argument budget leading request reading sourceEq))
    (model : Model request samples reading gain_eq)
    (modelEq : model = request.sources.realize reading gain_eq polynomial sourceEq samples.nodes
      samples.expansion (fun point member => (samples.node_bounds point member).trans radiusBound) samples.payment) :
    ofModel argument budget leading reading gain_eq sourceEq radiusBound
        request requestEq samples samplesEq model modelEq =
      prepare argument budget leading reading gain_eq sourceEq radiusBound := by
  cases requestEq
  cases samplesEq
  cases modelEq
  rfl

/-- Restoring the same scheduled sample bank preserves the complete automatic original association. -/
theorem ofSamples_eq_prepare (argument : Approximation locations) (budget : Budget parameters target tolerance)
    (leading : Leading tower embed polynomial.leadingCoeff) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (sourceEq : polynomial = Dense.Map.map reading.read formal)
    (radiusBound : argument.request.radius ≤ radius) (request : Request argument budget leading)
    (requestEq : request = Sources.Radial.prepare budget leading argument.request.gaps.bound
      locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive)
    (samples : Samples request)
    (samplesEq : samples = Roots.Samples.prepare argument request.sources.schedule.val
      request.sources.schedule.property (targets_count argument budget leading request reading sourceEq)) :
    ofSamples argument budget leading reading gain_eq sourceEq radiusBound request requestEq samples samplesEq =
      prepare argument budget leading reading gain_eq sourceEq radiusBound :=
  ofModel_eq_prepare argument budget leading reading gain_eq sourceEq radiusBound request requestEq samples samplesEq
    (request.sources.realize reading gain_eq polynomial sourceEq samples.nodes samples.expansion
      (fun point member => (samples.node_bounds point member).trans radiusBound) samples.payment) rfl

/-- Preserve the original local root coordinate while transporting its bound to the same sample family. -/
@[expose] def localIndex (_higher : Higher argument budget leading reading gain_eq sourceEq radiusBound)
    (index : Fin tower.blocks.length) : Fin argument.request.regions.length :=
  let counts : tower.blocks.length = argument.request.regions.length :=
    tower.blocks_length.trans
      ((leading.observed_degree reading (DensePolynomial.leadingCoeff_ne_zero clearance.nonzero)
        polynomial sourceEq).symm.trans argument.request.count.symm)
  ⟨index.val, counts ▸ index.isLt⟩

/-- The same original bounded formal-root position reads its actual retained geometric continuation. -/
theorem node_eq (higher : Higher argument budget leading reading gain_eq sourceEq radiusBound)
    (index : Fin tower.blocks.length) :
    higher.samples.nodes[index.val]'(higher.model.matched.nodeBound index) =
      (higher.samples.sampleAt (higher.localIndex index)).point :=
  higher.samples.nodeAt_eq (higher.localIndex index)

/-- The cached endpoint has the same gain fixed before any original samples were continued. -/
theorem final_gain (higher : Higher argument budget leading reading gain_eq sourceEq radiusBound) :
    higher.model.realization.finalReading.gain = parameters.finalGain := higher.model.realization.final_gain

/-- A paid initial reading error gives the requested error for this same actual geometric association. -/
theorem error_lt (higher : Higher argument budget leading reading gain_eq sourceEq radiusBound)
    (paid : reading.error < tolerance) : higher.model.realization.finalReading.error < target :=
  higher.model.realization.error_lt paid

/-- Each original higher root reading inherits its same original owner's quantitative strict radial side. -/
theorem radial (higher : Higher argument budget leading reading gain_eq sourceEq radiusBound)
    (index : Fin tower.blocks.length) :
    match (locations.refinementAt (argument.request.trackIndex (higher.localIndex index))).side with
    | .negative _ => Norm.Basic.normSq (higher.model.realization.finalReading.read
        (tower.blocks[index.val]'index.isLt).point) ≤ higher.request.originalRadial.ceiling
    | .positive _ => higher.request.originalRadial.floor ≤ Norm.Basic.normSq
        (higher.model.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) := by
  let request := higher.request.originalRadial
  let sampled : Sampled budget reading gain_eq higher.samples.nodes
      (request.cap * higher.request.sources.inverseNorm) :=
    { realization := higher.model.realization
      matched := (congrArg (fun cap => Matched higher.model.realization.finalReading.read
        (cap * higher.request.sources.inverseNorm) tower.blocks higher.samples.nodes)
          higher.request.originalRadial_cap).symm ▸ higher.model.matched }
  have candidateBound : Norm.Basic.normSq
      (higher.samples.nodes[index.val]'(sampled.matched.nodeBound index)) ≤ radius := by
    rewrite [higher.node_eq index]
    exact (higher.samples.sampleAt (higher.localIndex index)).node_bound.trans radiusBound
  have collar : locations.request.collar.width ^ 2 <
      (Norm.Basic.normSq (higher.samples.nodes[index.val]'(sampled.matched.nodeBound index)) - 1) ^ 2 := by
    rewrite [higher.node_eq index, Norm.Basic.normSq_eq_canonical]
    exact higher.samples.radial_gap (higher.localIndex index)
  have original := (higher.samples.sampleAt (higher.localIndex index)).radial
  cases side : (locations.refinementAt (argument.request.trackIndex (higher.localIndex index))).side with
  | negative _ =>
      rewrite [side] at original
      have inside : Norm.Basic.normSq
          (higher.samples.nodes[index.val]'(sampled.matched.nodeBound index)) < 1 := by
        rewrite [higher.node_eq index, Norm.Basic.normSq_eq_canonical]
        exact original
      exact sampled.inside request index candidateBound collar inside
  | positive _ =>
      rewrite [side] at original
      have outside : 1 < Norm.Basic.normSq
          (higher.samples.nodes[index.val]'(sampled.matched.nodeBound index)) := by
        rewrite [higher.node_eq index, Norm.Basic.normSq_eq_canonical]
        exact original
      exact sampled.outside request index candidateBound collar outside

/-- The original cached inside label supplies the quantitative ceiling for its same actual formal-root reading. -/
theorem inside (higher : Higher argument budget leading reading gain_eq sourceEq radiusBound)
    (index : Fin tower.blocks.length)
    (label : locations.insideAt (argument.request.trackIndex (higher.localIndex index)) = true) :
    Norm.Basic.normSq (higher.model.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤
      higher.request.originalRadial.ceiling := by
  have bounded := higher.radial index
  change (locations.refinementAt (argument.request.trackIndex (higher.localIndex index))).side.isNegative = true
    at label
  cases side : (locations.refinementAt (argument.request.trackIndex (higher.localIndex index))).side with
  | negative _ =>
      rewrite [side] at bounded
      exact bounded
  | positive _ =>
      rewrite [side] at label
      cases label

/-- The original cached outside label supplies the quantitative floor for its same actual formal-root reading. -/
theorem outside (higher : Higher argument budget leading reading gain_eq sourceEq radiusBound)
    (index : Fin tower.blocks.length)
    (label : locations.insideAt (argument.request.trackIndex (higher.localIndex index)) = false) :
    higher.request.originalRadial.floor ≤
      Norm.Basic.normSq (higher.model.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) := by
  have bounded := higher.radial index
  change (locations.refinementAt (argument.request.trackIndex (higher.localIndex index))).side.isNegative = false
    at label
  cases side : (locations.refinementAt (argument.request.trackIndex (higher.localIndex index))).side with
  | negative _ =>
      rewrite [side] at label
      cases label
  | positive _ =>
      rewrite [side] at bounded
      exact bounded

end Higher

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

end

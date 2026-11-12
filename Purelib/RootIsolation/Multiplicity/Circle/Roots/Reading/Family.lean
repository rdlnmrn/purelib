module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Factor
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Realization
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Origins
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Leading
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading.Source
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid associations across the same original factor family

Each original context consumes its retained geometric argument and physical
bounds. Its selected exact or higher association supplies the same cached
reading consumed by the next context. The original stage realization and a
trace of those same association payloads share one common final endpoint.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots (Stages factor)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading renaming
  Parameters → StageParameters, Budget → StageBudget, Realization → StageRealization
open Purelib.Polynomial.Dense.Roots (Tower Block)
open Purelib.Polynomial.Dense.Roots.Tower.Reading renaming
  Parameters → TowerParameters, Request → TowerRequest, Budget → TowerBudget, Realization → TowerRealization
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Algebra.Ring (Weight GaussianReading)

universe u

variable {source opposite : CoefficientPolynomial} {clearance : Certificate source}
variable {input : PositiveSideInput source opposite} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family}

namespace Family

/-- The same original factor payload at its retained mapped source, tower budget and incoming reading. -/
abbrev Observation (argument : PositiveArgument inventory) (bounds : Bounds.Family argument)
    {index : Fin input.contexts.length} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {mapped : DensePolynomial K}
    (mappedEq : mapped = Purelib.Polynomial.Dense.Map.map function (factor input.contexts index))
    {tower : Tower K ring equality mapped} {parent : Weight K} {gain target tolerance : Rational}
    {parameters : TowerParameters tower parent gain (bounds.radii index)}
    (budget : TowerBudget parameters target tolerance)
    (leading : Tower.Leading tower function (factor input.contexts index).leadingCoeff)
    (reading : GaussianReading parent function) (gainEq : reading.gain = gain) :=
  Factor (inventory.factorAt index).observation (inventory.factorAt index).locations (argument.argumentAt index)
    (bounds.boundsAt index) budget leading reading gainEq
      (Stages.Reading.factor_eq_map reading mappedEq) (Fraction.Order.Basic.le_refl _)

set_option genInjectivity false in
/-- The retained original factor associations certifying one same original stage realization.

Each constructor retains its actual selected payload. The next association
uses precisely that payload's cached realization endpoint, while the index
is the original stage constructor on those same realizations.
-/
inductive Trace (argument : PositiveArgument inventory) (bounds : Bounds.Family argument) :
    {indices : List (Fin input.contexts.length)} → {K : Type u} →
    [ring : CommRing K] → [equality : DecidableEq K] → {function : Canonical → K} →
    {stages : Stages input.contexts indices K ring equality function} → {parent : Weight K} →
    {gain target tolerance : Rational} → {parameters : StageParameters bounds.radii stages parent gain} →
    (budget : StageBudget parameters target tolerance) → (reading : GaussianReading parent function) →
    (gainEq : reading.gain = gain) → StageRealization budget reading gainEq → Type (u + 1)
  /-- No original context remains, so the same original input reading is the endpoint. -/
  | done {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {parent : Weight K} {gain target : Rational} {gainNonnegative : 0 ≤ gain}
      {reading : GaussianReading parent function} {gainEq : reading.gain = gain} (positive : 0 < target) :
      Trace argument bounds (.done positive : StageBudget
        (.done gainNonnegative : StageParameters bounds.radii
          (.done : Stages input.contexts [] K ring equality function) parent gain) target target)
        reading gainEq (StageRealization.done reading gainEq positive)
  /-- Retain the current original association and its same actual next-context realization. -/
  | adjoin {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
      {index : Fin input.contexts.length} {indices : List (Fin input.contexts.length)} {mapped : DensePolynomial K}
      {mappedEq : mapped = Purelib.Polynomial.Dense.Map.map function (factor input.contexts index)}
      {normalized : mapped.normalize = mapped} {degree : mapped.natDegree = (factor input.contexts index).natDegree}
      {tower : Tower K ring equality mapped} {roots : List (Block tower.Scalar)}
      {rootsEq : roots = tower.blocks}
      {remaining : Stages input.contexts indices tower.Scalar inferInstance inferInstance
        (fun value => tower.embed (function value))} {parent : Weight K} {gain target tolerance : Rational}
      {current : TowerParameters tower parent gain (bounds.radii index)}
      {next : StageParameters bounds.radii remaining current.finalWeight current.finalGain}
      {reading : GaussianReading parent function} {gainEq : reading.gain = gain}
      (tail : StageBudget next target tolerance) (request : TowerRequest current tolerance)
      (leading : Tower.Leading tower function (factor input.contexts index).leadingCoeff)
      (observation : Observation argument bounds mappedEq request.budget leading reading gainEq)
      (rest : StageRealization tail observation.realization.finalReading observation.realization.final_gain)
      (associations : Trace argument bounds tail observation.realization.finalReading
        observation.realization.final_gain rest) :
      Trace argument bounds (.adjoin tail request : StageBudget
        (.adjoin current next : StageParameters bounds.radii
          (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining) parent gain)
        target request.tolerance) reading gainEq
        (StageRealization.adjoin tail request observation.realization rest)

constructive_injectivity Trace

end Family

set_option genInjectivity false in
/-- The same original common stage model with its retained original geometric associations.

The model stores its actual endpoint for execution. The separate trace
retains each original exact or higher payload and certifies that those same
cached realizations, rather than new models, produced the original model.
-/
structure Family (argument : PositiveArgument inventory) (bounds : Bounds.Family argument)
    {indices : List (Fin input.contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {function : Canonical → K} {stages : Stages input.contexts indices K ring equality function}
    {parent : Weight K} {gain target tolerance : Rational}
    {parameters : StageParameters bounds.radii stages parent gain} (budget : StageBudget parameters target tolerance)
    (reading : GaussianReading parent function) (gainEq : reading.gain = gain) where
  /-- The original stage realization with its same common cached endpoint. -/
  model : StageRealization budget reading gainEq
  /-- Each original association payload supplies the same retained tower realization in this model. -/
  trace : Family.Trace argument bounds budget reading gainEq model

constructive_injectivity Family

namespace Family

variable (argument : PositiveArgument inventory) (bounds : Bounds.Family argument)

/-- Keep the same original reading when the original context chain has ended. -/
@[expose] def done {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {parent : Weight K} {gain target : Rational} {gainNonnegative : 0 ≤ gain}
    (reading : GaussianReading parent function) (gainEq : reading.gain = gain) (positive : 0 < target) :
    Family argument bounds (.done positive : StageBudget
      (.done gainNonnegative : StageParameters bounds.radii
        (.done : Stages input.contexts [] K ring equality function) parent gain) target target) reading gainEq :=
  { model := StageRealization.done reading gainEq positive, trace := .done positive }

/-- Compose the same cached factor payload and original next-context model without replaying either. -/
@[expose] def adjoin {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {index : Fin input.contexts.length} {indices : List (Fin input.contexts.length)} {mapped : DensePolynomial K}
    {mappedEq : mapped = Purelib.Polynomial.Dense.Map.map function (factor input.contexts index)}
    {normalized : mapped.normalize = mapped} {degree : mapped.natDegree = (factor input.contexts index).natDegree}
    {tower : Tower K ring equality mapped} {roots : List (Block tower.Scalar)}
    {rootsEq : roots = tower.blocks}
    {remaining : Stages input.contexts indices tower.Scalar inferInstance inferInstance
      (fun value => tower.embed (function value))} {parent : Weight K} {gain target tolerance : Rational}
    {current : TowerParameters tower parent gain (bounds.radii index)}
    {next : StageParameters bounds.radii remaining current.finalWeight current.finalGain}
    {reading : GaussianReading parent function} {gainEq : reading.gain = gain}
    (tail : StageBudget next target tolerance) (request : TowerRequest current tolerance)
    (leading : Tower.Leading tower function (factor input.contexts index).leadingCoeff)
    (observation : Observation argument bounds mappedEq request.budget leading reading gainEq)
    (observationModel : TowerRealization request.budget reading gainEq)
    (observationModelEq : observationModel = observation.realization)
    (rest : Family argument bounds tail observationModel.finalReading observationModel.final_gain) :
    Family argument bounds (.adjoin tail request : StageBudget
      (.adjoin current next : StageParameters bounds.radii
        (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining) parent gain)
      target request.tolerance) reading gainEq :=
  let model := StageRealization.adjoin tail request observationModel rest.model
  let trace : Trace argument bounds (.adjoin tail request) reading gainEq model := by
    cases observationModelEq
    exact .adjoin tail request leading observation rest.model rest.trace
  { model, trace }

/-- Associate every same original factor once, using its actual endpoint as the next original input reading. -/
@[expose] def prepare {indices : List (Fin input.contexts.length)} {K : Type u}
    [ring : CommRing K] [equality : DecidableEq K] {function : Canonical → K}
    {stages : Stages input.contexts indices K ring equality function} {parent : Weight K}
    {gain target tolerance : Rational} {parameters : StageParameters bounds.radii stages parent gain}
    (leading : Stages.Leading stages) (budget : StageBudget parameters target tolerance)
    (reading : GaussianReading parent function) (gainEq : reading.gain = gain) :
    Family argument bounds budget reading gainEq :=
  match indices, stages, parameters, target, tolerance, budget with
  | [], .done, .done _, _, _, .done positive => done argument bounds reading gainEq positive
  | index :: _, .adjoin _ mappedEq _ degree _ _ _ _, .adjoin _ _, _, _, .adjoin tail request =>
      let original := inventory.factorAt index
      let physical := bounds.boundsAt index
      let observation := Factor.prepare original.observation original.locations (argument.argumentAt index)
        physical request.budget leading.current reading gainEq
          (Stages.Reading.factor_eq_map reading mappedEq) degree (Fraction.Order.Basic.le_refl _)
      let observationModel := Factor.realization (observation := original.observation) observation
      let rest := prepare leading.next tail observationModel.finalReading observationModel.final_gain
      adjoin argument bounds tail request leading.current observation observationModel rfl rest

variable {argument bounds}
variable {indices : List (Fin input.contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {function : Canonical → K} {stages : Stages input.contexts indices K ring equality function}
variable {parent : Weight K} {gain target tolerance : Rational}
variable {parameters : StageParameters bounds.radii stages parent gain}
variable {budget : StageBudget parameters target tolerance}
variable {reading : GaussianReading parent function} {gainEq : reading.gain = gain}

/-- The complete same original family has its fixed pre-observation final gain. -/
theorem final_gain (retained : Family argument bounds budget reading gainEq) :
    retained.model.finalReading.gain = parameters.finalGain := retained.model.final_gain

/-- A paid initial model gives the requested weak error bound at the same common endpoint. -/
theorem error_le (retained : Family argument bounds budget reading gainEq) (paid : reading.error ≤ tolerance) :
    retained.model.finalReading.error ≤ target := retained.model.error_le paid

/-- A strictly paid initial model gives the requested strict error bound at the same common endpoint. -/
theorem error_lt (retained : Family argument bounds budget reading gainEq) (paid : reading.error < tolerance) :
    retained.model.finalReading.error < target := retained.model.error_lt paid

/-- The same common endpoint preserves each original coefficient's exact input reading. -/
theorem final_read_embed (retained : Family argument bounds budget reading gainEq) (value : K) :
    retained.model.finalReading.read (stages.embed value) = reading.read value := retained.model.final_read_embed value

/-- Both original geometric labels bound their same formal-root reading in the common endpoint.

The original bounded context and local-root occurrence select the retained
inventory row and physical bounds. The point is the same retained final
image of that original formal root, read by the actual composed model.
-/
@[expose] def Radial (model : StageRealization budget reading gainEq) (images : Images stages)
    (origin : Images.Origin stages images) : Prop :=
  let original := inventory.factorAt origin.contextIndex
  let label := Locations.insideAt original.observation original.locations origin.localIndex
  let physical := bounds.boundsAt origin.contextIndex
  let quadrance := Norm.Basic.normSq (model.finalReading.read origin.point)
  (label = true → quadrance ≤ physical.ceiling) ∧ (label = false → physical.floor ≤ quadrance)

/-- Every same cached association trace transports its original owner bounds to its actual common endpoint. -/
private theorem trace_radial {model : StageRealization budget reading gainEq}
    (associations : Trace argument bounds budget reading gainEq model) :
    ∀ (images : Images stages) (origin : Images.Origin stages images),
      Radial (bounds := bounds) model images origin := by
  induction associations with
  | done =>
      intro images origin
      exact Fin.elim0 origin.factor
  | @adjoin K ring equality function index indices mapped mappedEq normalized degree tower roots rootsEq
      remaining parent gain target tolerance current next reading gainEq tail request leading observation
      rest associations previous =>
      intro images origin
      rcases origin with ⟨⟨position, positionBound⟩, root⟩
      cases position with
      | zero =>
          have originalBound : root.val < roots.length := images.1.roots_length ▸ root.isLt
          let sourceIndex : Fin tower.blocks.length :=
            ⟨root.val, (congrArg List.length rootsEq) ▸ originalBound⟩
          have mappedBound : root.val < (roots.map (Block.map remaining.embed)).length :=
            images.1.roots_eq ▸ root.isLt
          have cached := _root_.getElem_congr images.1.roots_eq (Eq.refl root.val) root.isLt
          have mapped := List.Map.getElem_map (Block.map remaining.embed) roots root.val originalBound mappedBound
          have original := _root_.getElem_congr rootsEq (Eq.refl root.val) originalBound
          have pointEq : (images.1.roots.get root).point =
              remaining.embed (tower.blocks[sourceIndex.val]'sourceIndex.isLt).point := by
            have readback := congrArg Block.point (cached.trans mapped)
            change (images.1.roots.get root).point = remaining.embed (roots[root.val]'originalBound).point at readback
            exact readback.trans (congrArg (fun block => remaining.embed block.point) original)
          have readEq : rest.finalReading.read (images.1.roots.get root).point =
              observation.realization.finalReading.read (tower.blocks[sourceIndex.val]'sourceIndex.isLt).point :=
            (congrArg rest.finalReading.read pointEq).trans (rest.final_read_embed _)
          constructor
          · intro label
            have bounded := Factor.inside observation degree sourceIndex label
            change Norm.Basic.normSq (rest.finalReading.read (images.1.roots.get root).point) ≤
              (bounds.boundsAt index).ceiling
            rewrite [readEq]
            exact bounded
          · intro label
            have bounded := Factor.outside observation degree sourceIndex label
            change (bounds.boundsAt index).floor ≤
              Norm.Basic.normSq (rest.finalReading.read (images.1.roots.get root).point)
            rewrite [readEq]
            exact bounded
      | succ position =>
          exact previous images.2 ⟨⟨position, Nat.lt_of_succ_lt_succ positionBound⟩, root⟩

/-- Every original factor-root occurrence inherits both quantitative radial bounds in the same common reading. -/
theorem radial (retained : Family argument bounds budget reading gainEq) (images : Images stages)
    (origin : Images.Origin stages images) : Radial (bounds := bounds) retained.model images origin :=
  trace_radial retained.trace images origin

/-- The same original inside label bounds its actual common-endpoint root reading by its cached physical ceiling. -/
theorem inside (retained : Family argument bounds budget reading gainEq) (images : Images stages)
    (origin : Images.Origin stages images)
    (label : Locations.insideAt (inventory.factorAt origin.contextIndex).observation
      (inventory.factorAt origin.contextIndex).locations origin.localIndex = true) :
    Norm.Basic.normSq (retained.model.finalReading.read origin.point) ≤
      (bounds.boundsAt origin.contextIndex).ceiling := (retained.radial images origin).1 label

/-- The same original outside label bounds its actual common-endpoint root reading by its cached physical floor. -/
theorem outside (retained : Family argument bounds budget reading gainEq) (images : Images stages)
    (origin : Images.Origin stages images)
    (label : Locations.insideAt (inventory.factorAt origin.contextIndex).observation
      (inventory.factorAt origin.contextIndex).locations origin.localIndex = false) :
    (bounds.boundsAt origin.contextIndex).floor ≤
      Norm.Basic.normSq (retained.model.finalReading.read origin.point) := (retained.radial images origin).2 label

end Family

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

end

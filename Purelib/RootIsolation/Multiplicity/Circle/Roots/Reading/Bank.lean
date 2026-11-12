module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Family
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Owners
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Original prepared Banks at their paid geometric readings

The retained Bank already owns its factor stages, images and original root
occurrences. Its cached context equality transports the original physical
radii once. The same original stage parameters remain available before
observation, and their retained request constructs the original family
association without rebuilding any formal or geometric parent.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots (Stages Prepared)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading renaming
  Parameters → StageParameters, Budget → StageBudget, Request → StageRequest, Realization → StageRealization
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Algebra.Ring (GaussianReading)

variable {source opposite : CoefficientPolynomial} {clearance : Certificate source}
variable {input : PositiveSideInput source opposite} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory}

/-- Pull the same retained physical radii back along the original cached context-list equality. -/
@[expose] def radii {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (bounds : Bounds.Family argument) (index : Fin contexts.length) : Rational :=
  bounds.radii ⟨index.val, (congrArg List.length same) ▸ index.isLt⟩

/-- Every pulled-back radius retains the same original cached nonnegative bound. -/
theorem radii_nonnegative {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (bounds : Bounds.Family argument) (index : Fin contexts.length) : 0 ≤ radii same bounds index :=
  bounds.radii_nonnegative ⟨index.val, (congrArg List.length same) ▸ index.isLt⟩

/-- The original fixed stage-parameter type at the same prepared Bank, physical radii and Gaussian base reading. -/
abbrev Parameters (prepared : Prepared input) (bounds : Bounds.Family argument) :=
  StageParameters (radii prepared.separation.prepared.contexts_eq bounds)
    prepared.separation.prepared.stages Norm.weight 1

/-- Prepare the same original stage parameters once, before any new model observations. -/
@[expose] def prepareParameters (prepared : Prepared input) (bounds : Bounds.Family argument) :
    Parameters prepared bounds :=
  StageParameters.prepare prepared.separation.prepared.stages Norm.weight 1
    (radii prepared.separation.prepared.contexts_eq bounds) (by decide +kernel)
      (radii_nonnegative prepared.separation.prepared.contexts_eq bounds)

/-- The exact original family type transported once along its cached context equality.

All dependent original stages and parameters remain arguments to this
single equality elimination. The resulting value is the original family
payload, with no replacement context list, frame, model or coefficient ring.
-/
@[expose] def Association {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (argument : PositiveArgument inventory) (bounds : Bounds.Family argument)
    {indices : List (Fin contexts.length)}
    {stages : Stages contexts indices Canonical inferInstance inferInstance id}
    {target tolerance : Rational} {parameters : StageParameters (radii same bounds) stages Norm.weight 1}
    (budget : StageBudget parameters target tolerance) : Type 1 := by
  cases same
  exact Family argument bounds budget GaussianReading.identity rfl

namespace Association

/-- Construct the original transported family from the same retained leading ownership and fixed budget. -/
@[expose] def prepare {contexts : List (PositiveContext input.entries)} (same : contexts = input.contexts)
    (argument : PositiveArgument inventory) (bounds : Bounds.Family argument)
    {indices : List (Fin contexts.length)}
    {stages : Stages contexts indices Canonical inferInstance inferInstance id} {target tolerance : Rational}
    {parameters : StageParameters (radii same bounds) stages Norm.weight 1}
    (leading : Stages.Leading stages) (budget : StageBudget parameters target tolerance) :
    Association same argument bounds budget := by
  cases same
  exact Family.prepare argument bounds leading budget GaussianReading.identity rfl

variable {contexts : List (PositiveContext input.entries)} {same : contexts = input.contexts}
variable {indices : List (Fin contexts.length)}
variable {stages : Stages contexts indices Canonical inferInstance inferInstance id}
variable {bounds : Bounds.Family argument} {target tolerance : Rational}
variable {parameters : StageParameters (radii same bounds) stages Norm.weight 1}
variable {budget : StageBudget parameters target tolerance}

/-- Project the same actual original stage realization through the single context transport. -/
@[expose] def model (retained : Association same argument bounds budget) :
    StageRealization budget GaussianReading.identity rfl := by
  cases same
  exact retained.model

/-- The actual common reading has the same gain fixed by the retained original stage parameters. -/
theorem final_gain (retained : Association same argument bounds budget) :
    retained.model.finalReading.gain = parameters.finalGain := retained.model.final_gain

/-- The canonical zero-error input pays the same original request's positive tolerance automatically. -/
theorem error_lt (retained : Association same argument bounds budget) : retained.model.finalReading.error < target :=
  retained.model.error_lt budget.tolerance_positive

/-- Each original Gaussian coefficient retains its exact value in the same original common algebra. -/
theorem read_scalar (retained : Association same argument bounds budget) (value : Canonical) :
    retained.model.finalReading.read (stages.embed value) = value := retained.model.final_read_embed value

/-- The original zero-error base also gives the requested weak endpoint error bound. -/
theorem error_le (retained : Association same argument bounds budget) : retained.model.finalReading.error ≤ target :=
  retained.model.error_le budget.tolerance_positive.le

/-- The same original inside occurrence bounds its retained image in the transported common reading. -/
theorem inside (retained : Association same argument bounds budget) (images : Stages.Images stages)
    (origin : Stages.Images.Origin stages images)
    (label : (Occurrence.ofContext same origin.contextIndex origin.localIndex).inside inventory = true) :
    Norm.Basic.normSq (retained.model.finalReading.read origin.point) ≤
      (bounds.boundsAt (Occurrence.ofContext same origin.contextIndex origin.localIndex).context).ceiling := by
  cases same
  exact Family.inside retained images origin label

/-- The same original outside occurrence bounds its retained image in the transported common reading. -/
theorem outside (retained : Association same argument bounds budget) (images : Stages.Images stages)
    (origin : Stages.Images.Origin stages images)
    (label : (Occurrence.ofContext same origin.contextIndex origin.localIndex).inside inventory = false) :
    (bounds.boundsAt (Occurrence.ofContext same origin.contextIndex origin.localIndex).context).floor ≤
      Norm.Basic.normSq (retained.model.finalReading.read origin.point) := by
  cases same
  exact Family.outside retained images origin label

end Association

/-- Associate the original prepared Bank using its same fixed parameter cache and complete backward request.

The original leading invariant comes from the retained stage owner. The
single context-transport primitive invokes the original family producer;
no stage, image, Bank, owner, argument or bound constructor is replayed.
-/
@[expose] def prepare (prepared : Prepared input) (argument : PositiveArgument inventory)
    (bounds : Bounds.Family argument) {parameters : Parameters prepared bounds} {target : Rational}
    (request : StageRequest parameters target) :
    Association prepared.separation.prepared.contexts_eq argument bounds request.budget :=
  Association.prepare prepared.separation.prepared.contexts_eq argument bounds
    prepared.separation.prepared.leading request.budget

/-- The same retained owner label bounds its actual prepared Bank block in the common final reading. -/
theorem inside (prepared : Prepared input) (owners : Owners prepared inventory)
    {bounds : Bounds.Family argument} {parameters : Parameters prepared bounds} {target tolerance : Rational}
    {budget : StageBudget parameters target tolerance}
    (retained : Association prepared.separation.prepared.contexts_eq argument bounds budget)
    (index : Fin prepared.bank.blocks.length) (label : (owners.occurrences index).inside inventory = true) :
    Norm.Basic.normSq (retained.model.finalReading.read (prepared.bank.block index).point) ≤
      (bounds.boundsAt (owners.occurrences index).context).ceiling := by
  have same : owners.occurrences index = Occurrence.ofOrigin prepared (prepared.origin index) :=
    (congrArg (fun entries => entries index) owners.occurrences_eq).trans (vectorOfFn_apply _ index)
  have original := (congrArg (fun occurrence => occurrence.inside inventory) same).symm.trans label
  have ceilingEq := congrArg (fun occurrence : Occurrence input =>
    (bounds.boundsAt occurrence.context).ceiling) same
  rewrite [prepared.origin_point index, ceilingEq]
  exact Association.inside retained prepared.separation.images (prepared.origin index) original

/-- The same retained outside label bounds its actual prepared Bank block in the common final reading. -/
theorem outside (prepared : Prepared input) (owners : Owners prepared inventory)
    {bounds : Bounds.Family argument} {parameters : Parameters prepared bounds} {target tolerance : Rational}
    {budget : StageBudget parameters target tolerance}
    (retained : Association prepared.separation.prepared.contexts_eq argument bounds budget)
    (index : Fin prepared.bank.blocks.length) (label : (owners.occurrences index).inside inventory = false) :
    (bounds.boundsAt (owners.occurrences index).context).floor ≤
      Norm.Basic.normSq (retained.model.finalReading.read (prepared.bank.block index).point) := by
  have same : owners.occurrences index = Occurrence.ofOrigin prepared (prepared.origin index) :=
    (congrArg (fun entries => entries index) owners.occurrences_eq).trans (vectorOfFn_apply _ index)
  have original := (congrArg (fun occurrence => occurrence.inside inventory) same).symm.trans label
  have floorEq := congrArg (fun occurrence : Occurrence input =>
    (bounds.boundsAt occurrence.context).floor) same
  rewrite [prepared.origin_point index, floorEq]
  exact Association.outside retained prepared.separation.images (prepared.origin index) original

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank

end

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Seam
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization

/-! # A next paid quarter on the previous actual finishOwner

The retained full-cubic seam produces the next source agreement and only
reindexes the previous stored finishOwner across the exact physical seam.
The total paid-quarter factory consumes that same Owner and witness on the
unchanged next original Quarter. Both whole factory results are retained.
The concrete first-to-second constructor uses the existing Circuit field;
it requires neither a new Source attachment nor a final agreement input.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Continuation

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Meshes
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical}

section ActualInputs

variable {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {left : Transport.Leg site parameter leftQuarter} {right : Transport.Leg site parameter rightQuarter}
variable {leftInput : Input left}
variable {sourceOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) leftInput.sourceEndpoint}
variable {agreement : InitialAgreement leftInput.sourceEndpoint leftInput.sourceReading sourceOwner}
variable (previous : Input.Realization leftInput sourceOwner agreement) (nextInput : Input right)
variable (directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0)
variable (stored : Transport.Seam left right)

namespace Result

/-- The original continuation caches one actual full-cubic seam and the next original paid producer's complete result.

Both geometry inputs retain their actual original parent caches. Each
realization is literally its existing corresponding paid producer. The
same stored seam Owner and Type-valued witness enter that producer once;
no new Source attachment or substitute original Steps execution is used.
-/
@[expose] def Cache :=
  Σ seam : { retained : Transport.Seam.Receipt (left := left) (right := right)
        previous.finishReading nextInput.sourceReading previous.finishOwner previous.finishEquivalent
        previous.finish_time nextInput.source_time directions stored //
      retained = previous.seam nextInput directions stored },
    { paid : Input.Realization nextInput seam.val.owner seam.val.nextAgreement //
      paid = Input.Realization.build nextInput seam.val.owner seam.val.nextAgreement }

namespace Cache

/-- Retain the actual seam and next paid factory results without replaying either constructor. -/
@[expose] def ofCompleted
    (seam : { retained : Transport.Seam.Receipt (left := left) (right := right)
          previous.finishReading nextInput.sourceReading previous.finishOwner previous.finishEquivalent
          previous.finish_time nextInput.source_time directions stored //
        retained = previous.seam nextInput directions stored })
    (paid : { retained : Input.Realization nextInput seam.val.owner seam.val.nextAgreement //
        retained = Input.Realization.build nextInput seam.val.owner seam.val.nextAgreement }) :
    Cache previous nextInput directions stored := ⟨seam, paid⟩

/-- Construct the same original seam once and pass its literal Owner/witness to the actual next paid producer. -/
def build : Cache previous nextInput directions stored :=
  let seam := previous.seam nextInput directions stored
  let paid := Input.Realization.build nextInput seam.owner seam.nextAgreement
  ofCompleted previous nextInput directions stored ⟨seam, rfl⟩ ⟨paid, rfl⟩

variable (cache : Cache previous nextInput directions stored)

/-- Read the identical whole original signed seam cache. -/
@[expose] def seam : Transport.Seam.Receipt (left := left) (right := right)
    previous.finishReading nextInput.sourceReading previous.finishOwner previous.finishEquivalent
    previous.finish_time nextInput.source_time directions stored := cache.1.val

/-- Read the complete next actual paid realization on the SAME stored seam Owner and operational source witness. -/
@[expose] def paid : Input.Realization nextInput cache.seam.owner cache.seam.nextAgreement := cache.2.val

/-- Read the literal terminal Owner of the SAME retained next paid realization. -/
@[expose] def finishOwner : OwnerAt site parameter rightQuarter (of_decide_eq_true rfl)
    cache.paid.finishEndpoint := Input.Realization.finishOwner cache.paid

/-- The terminal Owner is the original realization readback on the identical stored paid cache. -/
theorem finishOwner_eq : cache.finishOwner = Input.Realization.finishOwner cache.paid :=
  rfl

/-- The retained seam is the exact shared endpoint operation on the SAME original geometry inputs. -/
theorem seam_eq : cache.seam = previous.seam nextInput directions stored := cache.1.property

/-- The retained next paid realization is exactly its original corresponding producer on those same stored inputs. -/
theorem paid_eq : cache.paid = Input.Realization.build nextInput cache.seam.owner cache.seam.nextAgreement :=
  cache.2.property

end Cache

end Result

end ActualInputs

section General

variable {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {left : Transport.Leg site parameter leftQuarter} {right : Transport.Leg site parameter rightQuarter}
variable {current : Endpoint} {reading : ReadingAt left.actual current}
variable {originalOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) current}
variable {original : Steps.Quarter left.actual left.regular current reading originalOwner}
variable {sourceOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) current}
variable {agreement : InitialAgreement current reading sourceOwner}
variable (previous : Quarter original sourceOwner agreement)
variable (previousInitial : current = UniformPrimitiveMesh.firstEndpoint)
variable {nextCurrent : Endpoint} {nextReading : ReadingAt right.actual nextCurrent}
variable {nextOriginalOwner : OwnerAt site parameter rightQuarter (of_decide_eq_true rfl) nextCurrent}
variable (nextOriginal : Steps.Quarter right.actual right.regular nextCurrent nextReading nextOriginalOwner)
variable (nextInitial : nextCurrent = UniformPrimitiveMesh.firstEndpoint)
variable (directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0)
variable (stored : Transport.Seam left right)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The old Steps-quarter entry specializes the SAME continuation cache to its two original parent inputs.

Its paid result remains literally the existing Quarter type. The exact old
seam and next Quarter factories are retained by the shared implementation;
no old execution is replaced or compared to an unrelated finer one.
-/
@[expose] def Result :=
  Result.Cache (left := left) (right := right)
    (leftInput := Input.ofSteps original previousInitial) (sourceOwner := sourceOwner) (agreement := agreement)
    previous (Input.ofSteps nextOriginal nextInitial) directions stored

/-- The old handoff factory is exactly the shared endpoint operation on those SAME two original Steps inputs. -/
theorem seamFactory_eq :
    Input.Realization.seam (leg := left) (input := Input.ofSteps original previousInitial)
        (sourceOwner := sourceOwner) (agreement := agreement) previous
        (Input.ofSteps nextOriginal nextInitial) directions stored =
      Seam.Receipt.build (left := left) (right := right)
        previous previousInitial nextReading nextInitial directions stored :=
  (Input.Realization.seam_eq (leg := left) (input := Input.ofSteps original previousInitial)
      (sourceOwner := sourceOwner) (agreement := agreement) previous
      (Input.ofSteps nextOriginal nextInitial) directions stored).trans
    (Seam.Receipt.build_eq (left := left) (right := right)
      previous previousInitial nextReading nextInitial directions stored).symm

namespace Result

/-- Retain already completed seam and next-quarter caches with their exact whole factory identities. -/
@[expose] def ofCompleted
    (seam : { retained : Seam.Receipt (left := left) (right := right)
          previous previousInitial nextReading nextInitial directions stored //
        retained = Seam.Receipt.build (left := left) (right := right)
          previous previousInitial nextReading nextInitial directions stored })
    (paid : { retained : Quarter nextOriginal seam.val.owner seam.val.nextAgreement //
        retained = Quarter.build nextOriginal seam.val.owner seam.val.nextAgreement }) :
    Result previous previousInitial nextOriginal nextInitial directions stored :=
  ⟨⟨seam.val, seam.property.trans
      (seamFactory_eq previous previousInitial nextOriginal nextInitial directions stored).symm⟩,
    ⟨paid.val, paid.property.trans (Input.Realization.build_ofSteps
      (leg := right) (original := nextOriginal) (oldSourceOwner := seam.val.owner)
      (oldAgreement := seam.val.nextAgreement) nextInitial).symm⟩⟩

/-- Construct the full-cubic seam once and pass its identical retained Owner and witness to the next paid factory. -/
def build : Result previous previousInitial nextOriginal nextInitial directions stored :=
  Cache.build (left := left) (right := right) (leftInput := Input.ofSteps original previousInitial)
    (sourceOwner := sourceOwner) (agreement := agreement)
    previous (Input.ofSteps nextOriginal nextInitial) directions stored

/-- The old entry is exactly the shared continuation factory on the SAME two original Steps inputs. -/
theorem build_eq : build previous previousInitial nextOriginal nextInitial directions stored =
    Cache.build (left := left) (right := right) (leftInput := Input.ofSteps original previousInitial)
      (sourceOwner := sourceOwner) (agreement := agreement)
      previous (Input.ofSteps nextOriginal nextInitial) directions stored := by
  unfold build
  rfl

variable (result : Result previous previousInitial nextOriginal nextInitial directions stored)

/-- Read the same entire actual full-cubic seam cache retained before the next quarter was constructed. -/
@[expose] def seam : Seam.Receipt (left := left) (right := right)
    previous previousInitial nextReading nextInitial directions stored := result.1.val

/-- Read the complete next paid quarter on the unchanged original target, query and Geometry caches. -/
@[expose] def paid : Quarter nextOriginal result.seam.owner result.seam.nextAgreement := result.2.val

/-- The retained seam is the exact original full-cubic handoff factory on the unchanged quarter inputs. -/
theorem seam_eq : result.seam = Seam.Receipt.build (left := left) (right := right)
    previous previousInitial nextReading nextInitial directions stored :=
  result.1.property.trans (seamFactory_eq previous previousInitial nextOriginal nextInitial directions stored)

/-- The retained next quarter is the exact paid factory on that stored seam's Owner and comparison witness. -/
theorem paid_eq : result.paid = Quarter.build nextOriginal result.seam.owner result.seam.nextAgreement :=
  result.2.property.trans (Input.Realization.build_ofSteps
    (leg := right) (original := nextOriginal) (oldSourceOwner := result.seam.owner)
    (oldAgreement := result.seam.nextAgreement) nextInitial)

/-- The next paid source is the same whole previous actual finishOwner with only its proved geometric index changed. -/
theorem sourceOwner_heq : HEq result.seam.owner previous.finishOwner := result.seam.owner_heq

/-- The next realization preserves the supplied complete original Quarter rather than rebuilding its query chain. -/
theorem originalQuarter_eq : result.paid.originalQuarter = nextOriginal := result.paid.originalQuarter_eq

/-- Read the literal actual finishOwner of this retained next paid quarter. -/
@[expose] def finishOwner : OwnerAt site parameter rightQuarter (of_decide_eq_true rfl)
    (finalTarget nextCurrent result.paid.originalQuarter.cache.val) :=
  Cache.finishOwner (left := left) (right := right)
    (leftInput := Input.ofSteps original previousInitial) (sourceOwner := sourceOwner) (agreement := agreement)
    (previous := previous) (nextInput := Input.ofSteps nextOriginal nextInitial)
    (directions := directions) (stored := stored) result

/-- The old Steps-only readback remains the literal terminal Owner of its identical stored next quarter. -/
theorem finishOwner_eq : result.finishOwner = result.paid.finishOwner := by
  unfold finishOwner Cache.finishOwner
  rfl

/-- Read the same original final Reading retained by the next quarter's unchanged complete Steps cache. -/
@[expose] def finishReading : ReadingAt right.actual
    (finalTarget nextCurrent result.paid.originalQuarter.cache.val) := result.paid.finishReading

/-- This actual next-quarter finishOwner agrees with its identical retained independent original final cubic Lift. -/
def finishEquivalent : NamedEquivalent (ownerRootName result.finishOwner.parameterNonzero result.finishOwner)
    result.finishReading.lift.value.name := result.paid.finishEquivalent

/-- The actual next quarter retains all one hundred twenty-eight paid blocks on the unchanged original target cache. -/
theorem block_count : result.paid.receipt.blockCount = 128 := result.paid.block_count

/-- The actual next quarter reuses the original one hundred twenty-nine source/target query caches. -/
theorem query_count : result.paid.receipt.nodes.length = 129 := result.paid.query_count

end Result

end General

/-- Continue the first paid quarter through the existing circuit's actual full-cubic seam into its second quarter.

The previous and next original Reading caches remain distinct supplied
inputs. Their local endpoint comparisons are derived by the seam factory;
the stored Circuit.first_second comparison supplies the exact full sheet
handoff. The next paid factory introduces no Source attachment.
-/
def first_second (circuit : Transport.Circuit site parameter)
    {current : Endpoint} {reading : ReadingAt circuit.first.actual current}
    {originalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) current}
    {original : Steps.Quarter circuit.first.actual circuit.first.regular current reading originalOwner}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) current}
    {agreement : InitialAgreement current reading sourceOwner}
    (previous : Quarter original sourceOwner agreement)
    (previousInitial : current = UniformPrimitiveMesh.firstEndpoint)
    {nextCurrent : Endpoint} {nextReading : ReadingAt circuit.second.actual nextCurrent}
    {nextOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl) nextCurrent}
    (nextOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
      nextCurrent nextReading nextOriginalOwner)
    (nextInitial : nextCurrent = UniformPrimitiveMesh.firstEndpoint) :
    Result (left := circuit.first) (right := circuit.second)
      previous previousInitial nextOriginal nextInitial Waist.directions_join.1 circuit.first_second :=
  Result.build (left := circuit.first) (right := circuit.second)
    previous previousInitial nextOriginal nextInitial Waist.directions_join.1 circuit.first_second

end Steps.Acquisition.Quarter.Continuation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Continuation
public import Purelib.Data.Sigma

/-! # Four actual paid quarters on the retained original circuit

An existing first paid quarter is retained unchanged. Three total next
quarter factories use the original circuit's ordered full-cubic seams.
The fourth-to-first seam only derives the closing endpoint comparison;
it does not build the first quarter again. All original quarters, Readings,
actual Owners, operational witnesses and whole factory receipts remain
distinct. The initial supplied Owner is never attached again.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Steps.Acquisition.Quarter.Continuation

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (finalTarget)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical}
section ActualInputs

variable {circuit : Transport.Circuit site parameter}
variable {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable (initial : Input.Realization firstInput sourceOwner agreement)
variable (secondInput : Input circuit.second) (thirdInput : Input circuit.third) (fourthInput : Input circuit.fourth)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName

namespace Execution

namespace Cache

section ClosingType

variable {fourthSourceOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl) fourthInput.sourceEndpoint}
variable {fourthAgreement : InitialAgreement fourthInput.sourceEndpoint fourthInput.sourceReading fourthSourceOwner}
variable (fourthPaid : Input.Realization fourthInput fourthSourceOwner fourthAgreement)

/-- The exact original closing-receipt carrier retains an abstract actual fourth paid realization.

Its fields remain the original full-cubic seam caches and actual terminal
Owner. Naming this dependent carrier does not construct another seam.
-/
@[expose] def Closing :=
  Transport.Seam.Receipt (left := circuit.fourth) (right := circuit.first)
    fourthPaid.finishReading firstInput.sourceReading fourthPaid.finishOwner fourthPaid.finishEquivalent
    fourthPaid.finish_time firstInput.source_time Waist.directions_join.2.2.2 circuit.fourth_first

/-- The exact original closing-factory equation retains the same actual paid endpoint cache. -/
@[expose] def ClosingFactory
    (retained : Closing (circuit := circuit) (firstInput := firstInput) (fourthInput := fourthInput) fourthPaid) :
    Prop := retained = fourthPaid.seam firstInput Waist.directions_join.2.2.2 circuit.fourth_first

end ClosingType

end Cache

/-- Four actual paid realizations retain the same original ordered continuation and closing factories.

Each Input retains its whole original Steps quarter or actual numerical
Layer. The first paid realization is supplied unchanged. Three actual
continuations pass the literal stored finish Owner and operational witness
forward; the last original signed seam derives closure without rebuilding
the first quarter. No desired return relation is an input.
-/
@[expose] def Cache :=
  Σ first : { retained : Input.Realization firstInput sourceOwner agreement // retained = initial },
    Σ second : { retained : Result.Cache (left := circuit.first) (right := circuit.second)
          (leftInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
          first.val secondInput Waist.directions_join.1 circuit.first_second //
        retained = Result.Cache.build (left := circuit.first) (right := circuit.second)
          (leftInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
          first.val secondInput Waist.directions_join.1 circuit.first_second },
      Σ third : { retained : Result.Cache (left := circuit.second) (right := circuit.third)
            (leftInput := secondInput) (sourceOwner := second.val.seam.owner)
            (agreement := second.val.seam.nextAgreement)
            second.val.paid thirdInput Waist.directions_join.2.1 circuit.second_third //
          retained = Result.Cache.build (left := circuit.second) (right := circuit.third)
            (leftInput := secondInput) (sourceOwner := second.val.seam.owner)
            (agreement := second.val.seam.nextAgreement)
            second.val.paid thirdInput Waist.directions_join.2.1 circuit.second_third },
        Σ fourth : { retained : Result.Cache (left := circuit.third) (right := circuit.fourth)
              (leftInput := thirdInput) (sourceOwner := third.val.seam.owner)
              (agreement := third.val.seam.nextAgreement)
              third.val.paid fourthInput Waist.directions_join.2.2.1 circuit.third_fourth //
            retained = Result.Cache.build (left := circuit.third) (right := circuit.fourth)
              (leftInput := thirdInput) (sourceOwner := third.val.seam.owner)
              (agreement := third.val.seam.nextAgreement)
              third.val.paid fourthInput Waist.directions_join.2.2.1 circuit.third_fourth },
          Σ closing : { retained : Cache.Closing
                (circuit := circuit) (firstInput := firstInput) (fourthInput := fourthInput) fourth.val.paid //
              Cache.ClosingFactory (circuit := circuit) (firstInput := firstInput) (fourthInput := fourthInput)
                fourth.val.paid retained },
            { returned : NamedEquivalent
                  (ownerRootName fourth.val.paid.finishOwner.parameterNonzero fourth.val.paid.finishOwner)
                  (ownerRootName sourceOwner.parameterNonzero sourceOwner) //
                returned = closing.val.joined.trans agreement }

/-- Naming the closing carrier preserves the complete original dependent tuple type for every input. -/
private theorem cache_type_eq_original :
    Cache initial secondInput thirdInput fourthInput =
  Σ first : { retained : Input.Realization firstInput sourceOwner agreement // retained = initial },
    Σ second : { retained : Result.Cache (left := circuit.first) (right := circuit.second)
          (leftInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
          first.val secondInput Waist.directions_join.1 circuit.first_second //
        retained = Result.Cache.build (left := circuit.first) (right := circuit.second)
          (leftInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
          first.val secondInput Waist.directions_join.1 circuit.first_second },
      Σ third : { retained : Result.Cache (left := circuit.second) (right := circuit.third)
            (leftInput := secondInput) (sourceOwner := second.val.seam.owner)
            (agreement := second.val.seam.nextAgreement)
            second.val.paid thirdInput Waist.directions_join.2.1 circuit.second_third //
          retained = Result.Cache.build (left := circuit.second) (right := circuit.third)
            (leftInput := secondInput) (sourceOwner := second.val.seam.owner)
            (agreement := second.val.seam.nextAgreement)
            second.val.paid thirdInput Waist.directions_join.2.1 circuit.second_third },
        Σ fourth : { retained : Result.Cache (left := circuit.third) (right := circuit.fourth)
              (leftInput := thirdInput) (sourceOwner := third.val.seam.owner)
              (agreement := third.val.seam.nextAgreement)
              third.val.paid fourthInput Waist.directions_join.2.2.1 circuit.third_fourth //
            retained = Result.Cache.build (left := circuit.third) (right := circuit.fourth)
              (leftInput := thirdInput) (sourceOwner := third.val.seam.owner)
              (agreement := third.val.seam.nextAgreement)
              third.val.paid fourthInput Waist.directions_join.2.2.1 circuit.third_fourth },
          Σ closing : { retained : Transport.Seam.Receipt (left := circuit.fourth) (right := circuit.first)
                fourth.val.paid.finishReading firstInput.sourceReading
                fourth.val.paid.finishOwner fourth.val.paid.finishEquivalent
                fourth.val.paid.finish_time firstInput.source_time
                Waist.directions_join.2.2.2 circuit.fourth_first //
              retained = fourth.val.paid.seam firstInput Waist.directions_join.2.2.2 circuit.fourth_first },
            { returned : NamedEquivalent
                  (ownerRootName fourth.val.paid.finishOwner.parameterNonzero fourth.val.paid.finishOwner)
                  (ownerRootName sourceOwner.parameterNonzero sourceOwner) //
                returned = closing.val.joined.trans agreement } := by
  unfold Cache Cache.Closing Cache.ClosingFactory
  rfl

namespace Cache

/-- Retain the identical first paid realization and execute the same ordered next-quarter/seam factories once. -/
def build : Cache initial secondInput thirdInput fourthInput :=
  let second := Result.Cache.build (left := circuit.first) (right := circuit.second)
    (leftInput := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
    initial secondInput Waist.directions_join.1 circuit.first_second
  let third := Result.Cache.build (left := circuit.second) (right := circuit.third)
    (leftInput := secondInput) (sourceOwner := second.seam.owner) (agreement := second.seam.nextAgreement)
    second.paid thirdInput Waist.directions_join.2.1 circuit.second_third
  let fourth := Result.Cache.build (left := circuit.third) (right := circuit.fourth)
    (leftInput := thirdInput) (sourceOwner := third.seam.owner) (agreement := third.seam.nextAgreement)
    third.paid fourthInput Waist.directions_join.2.2.1 circuit.third_fourth
  let closing := fourth.paid.seam firstInput Waist.directions_join.2.2.2 circuit.fourth_first
  let returned := closing.joined.trans agreement
  ⟨⟨initial, rfl⟩, ⟨second, rfl⟩, ⟨third, rfl⟩, ⟨fourth, rfl⟩, ⟨closing, rfl⟩, ⟨returned, rfl⟩⟩

variable (cache : Cache initial secondInput thirdInput fourthInput)

/-- Read the SAME supplied complete first paid realization. -/
@[expose] def first : Input.Realization firstInput sourceOwner agreement := cache.1.val

/-- The retained first realization is literally the supplied value, without another paid execution. -/
theorem first_eq : cache.first = initial := cache.1.property

/-- Read the complete actual first-to-second continuation on the SAME initial Owner and witness. -/
@[expose] def second : Result.Cache
    (site := site) (parameter := parameter) (leftQuarter := .first) (rightQuarter := .second)
    (left := circuit.first) (right := circuit.second) (leftInput := firstInput)
    (sourceOwner := sourceOwner) (agreement := agreement)
    (first (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache)
    secondInput Waist.directions_join.1 circuit.first_second :=
  cache.2.1.val

/-- Read the complete actual second-to-third continuation on the SAME preceding stored Owner and witness. -/
@[expose] def third : Result.Cache
    (site := site) (parameter := parameter) (leftQuarter := .second) (rightQuarter := .third)
    (left := circuit.second) (right := circuit.third) (leftInput := secondInput)
    (sourceOwner := (second (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).seam.owner)
    (agreement := (second (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).seam.nextAgreement)
    (second (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).paid
    thirdInput Waist.directions_join.2.1 circuit.second_third :=
  Data.Sigma.thirdSubtypeValue cache

/-- Read the complete actual third-to-fourth continuation on the SAME preceding stored Owner and witness. -/
@[expose] def fourth : Result.Cache
    (site := site) (parameter := parameter) (leftQuarter := .third) (rightQuarter := .fourth)
    (left := circuit.third) (right := circuit.fourth) (leftInput := thirdInput)
    (sourceOwner := (third (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).seam.owner)
    (agreement := (third (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).seam.nextAgreement)
    (third (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).paid
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth :=
  Data.Sigma.fourthSubtypeValue cache

/-- Read the original signed fourth-to-first handoff on the SAME actual paid terminal Owner. -/
@[expose] def closing : Closing
    (site := site) (parameter := parameter) (circuit := circuit) (firstInput := firstInput)
    (fourthInput := fourthInput)
    (fourthSourceOwner := (fourth (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).seam.owner)
    (fourthAgreement := (fourth (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).seam.nextAgreement)
    (fourth (site := site) (parameter := parameter) (circuit := circuit)
      (firstInput := firstInput) (sourceOwner := sourceOwner)
      (agreement := agreement) (initial := initial)
      (secondInput := secondInput) (thirdInput := thirdInput)
      (fourthInput := fourthInput) cache).paid :=
  Data.Sigma.fifthSubtypeValue cache

/-- Read the literal actual terminal full-cubic Owner of the fourth paid realization. -/
@[expose] def finishOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
    cache.fourth.paid.finishEndpoint :=
  Result.Cache.finishOwner (left := circuit.third) (right := circuit.fourth)
    (leftInput := thirdInput) (sourceOwner := cache.third.seam.owner) (agreement := cache.third.seam.nextAgreement)
    (previous := cache.third.paid) (nextInput := fourthInput)
    (directions := Waist.directions_join.2.2.1) (stored := circuit.third_fourth) cache.fourth

/-- Read that SAME complete actual returned Owner at the original first source point. -/
@[expose] def returnOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint :=
  cache.closing.owner

/-- The returned Owner retains the whole actual terminal Owner with only the proved geometric index changed. -/
theorem returnOwner_heq : HEq cache.returnOwner cache.finishOwner := cache.closing.owner_heq

/-- Read the derived actual terminal-to-initial full-cubic comparison. -/
@[expose] def returnEquivalent : NamedEquivalent
    (ownerRootName cache.finishOwner.parameterNonzero cache.finishOwner)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner) := Data.Sigma.sixthSubtypeValue cache

/-- The stored second continuation is the exact original shared continuation factory on its actual inputs. -/
theorem second_eq : cache.second = Result.Cache.build
    (left := circuit.first) (right := circuit.second) (leftInput := firstInput)
    (sourceOwner := sourceOwner) (agreement := agreement)
    cache.first secondInput Waist.directions_join.1 circuit.first_second := cache.2.1.property

/-- The stored third continuation is the exact original shared continuation factory on its actual inputs. -/
theorem third_eq : cache.third = Result.Cache.build
    (left := circuit.second) (right := circuit.third) (leftInput := secondInput)
    (sourceOwner := cache.second.seam.owner) (agreement := cache.second.seam.nextAgreement)
    cache.second.paid thirdInput Waist.directions_join.2.1 circuit.second_third := cache.2.2.1.property

/-- The stored fourth continuation is the exact original shared continuation factory on its actual inputs. -/
theorem fourth_eq : cache.fourth = Result.Cache.build
    (left := circuit.third) (right := circuit.fourth) (leftInput := thirdInput)
    (sourceOwner := cache.third.seam.owner) (agreement := cache.third.seam.nextAgreement)
    cache.third.paid fourthInput Waist.directions_join.2.2.1 circuit.third_fourth := cache.2.2.2.1.property

/-- The closing receipt is exactly the original signed seam factory on these SAME retained endpoints. -/
theorem closing_eq : cache.closing =
    cache.fourth.paid.seam firstInput Waist.directions_join.2.2.2 circuit.fourth_first :=
  Data.Sigma.fifthSubtypeValue_property cache

/-- The final comparison composes the SAME original closing witness and original initial source agreement. -/
theorem returnEquivalent_eq : cache.returnEquivalent = cache.closing.joined.trans agreement :=
  Data.Sigma.sixthSubtypeValue_property cache

/-- Exact geometric Owner-name transport retains the SAME derived full-cubic return comparison schedule. -/
def returnEquivalentAt : NamedEquivalent
    (ownerRootName cache.returnOwner.parameterNonzero cache.returnOwner)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner) :=
  NamedEquivalent.transport cache.closing.name_eq.symm rfl cache.returnEquivalent

end Cache

end Execution

end ActualInputs

variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable (initial : Quarter firstOriginal sourceOwner agreement)
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable (secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner)
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable (thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner)
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable (fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The old four-Steps-quarter entry specializes the SAME original six-cache execution to its exact inputs.

Each retained paid quarter remains literally the old Quarter type. The
shared implementation selects the same old factories for these Inputs;
all old public cache projections and count specializations remain valid.
-/
@[expose] def Execution :=
  Execution.Cache (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
    (sourceOwner := sourceOwner) (agreement := agreement) initial
    (Input.ofSteps secondOriginal rfl) (Input.ofSteps thirdOriginal rfl) (Input.ofSteps fourthOriginal rfl)

namespace Execution

/-- Retain the existing first paid quarter and construct the remaining three in their exact circuit order. -/
def build : Execution initial secondOriginal thirdOriginal fourthOriginal :=
  Cache.build (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
    (sourceOwner := sourceOwner) (agreement := agreement) initial
    (Input.ofSteps secondOriginal rfl) (Input.ofSteps thirdOriginal rfl) (Input.ofSteps fourthOriginal rfl)

/-- The old entry is exactly the shared original execution on the SAME four whole original Steps inputs. -/
theorem build_eq : build initial secondOriginal thirdOriginal fourthOriginal =
    Cache.build (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
      (sourceOwner := sourceOwner) (agreement := agreement) initial
      (Input.ofSteps secondOriginal rfl) (Input.ofSteps thirdOriginal rfl) (Input.ofSteps fourthOriginal rfl) := by
  unfold build
  rfl

variable (execution : Execution initial secondOriginal thirdOriginal fourthOriginal)

/-- Read the identical already completed first paid quarter without calling its factory again. -/
@[expose] def first : Quarter firstOriginal sourceOwner agreement := execution.1.val

/-- The first whole paid execution is literally the supplied cache. -/
theorem first_eq : execution.first = initial := execution.1.property

/-- Read the complete stored first-to-second handoff and second paid quarter, preserving all input caches. -/
@[expose] def second : Continuation.Result (left := circuit.first) (right := circuit.second)
    execution.first rfl secondOriginal rfl Waist.directions_join.1 circuit.first_second := execution.2.1.val

/-- Read the stored second-to-third handoff and third paid quarter on the identical actual second finishOwner. -/
@[expose] def third : Continuation.Result (left := circuit.second) (right := circuit.third)
    execution.second.paid rfl thirdOriginal rfl Waist.directions_join.2.1 circuit.second_third :=
  Cache.third (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
    (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
    (secondInput := Input.ofSteps secondOriginal rfl) (thirdInput := Input.ofSteps thirdOriginal rfl)
    (fourthInput := Input.ofSteps fourthOriginal rfl) execution

/-- Read the stored third-to-fourth handoff and fourth paid quarter on the identical actual third finishOwner. -/
@[expose] def fourth : Continuation.Result (left := circuit.third) (right := circuit.fourth)
    execution.third.paid rfl fourthOriginal rfl Waist.directions_join.2.2.1 circuit.third_fourth :=
  Cache.fourth (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
    (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
    (secondInput := Input.ofSteps secondOriginal rfl) (thirdInput := Input.ofSteps thirdOriginal rfl)
    (fourthInput := Input.ofSteps fourthOriginal rfl) execution

/-- The shared readback is the identical literal old fourth cached value. -/
private theorem fourth_eq_projection : execution.fourth = execution.2.2.2.1.val := by
  unfold fourth Cache.fourth
  exact Data.Sigma.fourthSubtypeValue_eq execution

/-- Read the complete fourth-to-first full-cubic endpoint comparison without executing the first quarter again. -/
@[expose] def closing : Seam.Receipt (left := circuit.fourth) (right := circuit.first)
    execution.fourth.paid rfl firstReading rfl Waist.directions_join.2.2.2 circuit.fourth_first :=
  Cache.closing (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
    (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
    (secondInput := Input.ofSteps secondOriginal rfl) (thirdInput := Input.ofSteps thirdOriginal rfl)
    (fourthInput := Input.ofSteps fourthOriginal rfl) execution

/-- Read the literal actual final Owner of the same retained fourth paid quarter. -/
@[expose] def finishOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
    (finalTarget UniformPrimitiveMesh.firstEndpoint execution.fourth.paid.originalQuarter.cache.val) :=
  execution.fourth.paid.finishOwner

/-- Read the same actual final Owner at the first original source's physical index. -/
@[expose] def returnOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
    UniformPrimitiveMesh.firstEndpoint := execution.closing.owner

/-- The returned physical Owner retains the same whole actual final Owner, track and clearance data. -/
theorem returnOwner_heq : HEq execution.returnOwner execution.finishOwner := execution.closing.owner_heq

/-- Read the retained derived full-cubic return comparison between the actual final and original initial Owners. -/
@[expose] def returnEquivalent : NamedEquivalent
    (ownerRootName execution.finishOwner.parameterNonzero execution.finishOwner)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner) :=
  Cache.returnEquivalent (circuit := circuit) (firstInput := Input.ofSteps firstOriginal rfl)
    (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
    (secondInput := Input.ofSteps secondOriginal rfl) (thirdInput := Input.ofSteps thirdOriginal rfl)
    (fourthInput := Input.ofSteps fourthOriginal rfl) execution

/-- The second whole paid quarter and seam are the exact stored factory on the unchanged actual first quarter. -/
theorem second_eq : execution.second = Continuation.Result.build (left := circuit.first) (right := circuit.second)
    execution.first rfl secondOriginal rfl Waist.directions_join.1 circuit.first_second :=
  execution.2.1.property.trans
    (Continuation.Result.build_eq (left := circuit.first) (right := circuit.second)
      execution.first rfl secondOriginal rfl Waist.directions_join.1 circuit.first_second).symm

/-- The third whole paid quarter and seam are the exact stored factory on the unchanged actual second quarter. -/
theorem third_eq : execution.third = Continuation.Result.build (left := circuit.second) (right := circuit.third)
    execution.second.paid rfl thirdOriginal rfl Waist.directions_join.2.1 circuit.second_third :=
  execution.2.2.1.property.trans
    (Continuation.Result.build_eq (left := circuit.second) (right := circuit.third)
      execution.second.paid rfl thirdOriginal rfl Waist.directions_join.2.1 circuit.second_third).symm

/-- The fourth whole paid quarter and seam are the exact stored factory on the unchanged actual third quarter. -/
theorem fourth_eq : execution.fourth = Continuation.Result.build (left := circuit.third) (right := circuit.fourth)
    execution.third.paid rfl fourthOriginal rfl Waist.directions_join.2.2.1 circuit.third_fourth :=
  execution.2.2.2.1.property.trans
    (Continuation.Result.build_eq (left := circuit.third) (right := circuit.fourth)
      execution.third.paid rfl fourthOriginal rfl Waist.directions_join.2.2.1 circuit.third_fourth).symm

/-- The closing receipt is the exact original fourth-to-first seam on the SAME stored actual final quarter. -/
theorem closing_eq : execution.closing = Seam.Receipt.build (left := circuit.fourth) (right := circuit.first)
    execution.fourth.paid rfl firstReading rfl Waist.directions_join.2.2.2 circuit.fourth_first :=
  execution.2.2.2.2.1.property.trans
    (Continuation.seamFactory_eq (left := circuit.fourth) (right := circuit.first)
      execution.fourth.paid rfl firstOriginal rfl Waist.directions_join.2.2.2 circuit.fourth_first)

/-- The retained return witness is derived from the stored closing endpoint and exact original initial agreement. -/
theorem returnEquivalent_eq : execution.returnEquivalent = execution.closing.joined.trans agreement :=
  execution.2.2.2.2.2.property

/-- Exact physical endpoint transport preserves the same derived final-to-initial full-cubic return relation. -/
def returnEquivalentAt : NamedEquivalent
    (ownerRootName execution.returnOwner.parameterNonzero execution.returnOwner)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner) :=
  NamedEquivalent.transport execution.closing.name_eq.symm rfl execution.returnEquivalent

/-- The four retained actual paid quarters contain exactly five hundred twelve paid blocks in geometric order. -/
theorem block_count : execution.first.receipt.blockCount + execution.second.paid.receipt.blockCount +
    execution.third.paid.receipt.blockCount + execution.fourth.paid.receipt.blockCount = 512 := by
  rewrite [execution.first.block_count, execution.second.paid.block_count,
    execution.third.paid.block_count, execution.fourth.paid.block_count]
  rfl

/-- The four unchanged original Reading sequences retain five hundred sixteen source and target caches in total. -/
theorem query_count : execution.first.receipt.nodes.length + execution.second.paid.receipt.nodes.length +
    execution.third.paid.receipt.nodes.length + execution.fourth.paid.receipt.nodes.length = 516 := by
  rewrite [execution.first.query_count, execution.second.paid.query_count,
    execution.third.paid.query_count, execution.fourth.paid.query_count]
  rfl

end Execution

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Observation
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Append
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.OwnerPath
import Purelib.Approximation.AccuracyRequest
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment

/-! # Same-cache quarter observations of the actual paid closed circuit

The original complete Closed acquisition and its literal closing comparison
remain retained inputs. Exact whole-path transport and three prefix splits
expose the four complete old quarter spines. All original states, requests,
stationary outcomes and signed occurrences are reused; only cache views are
constructed. Moving integrals and canonical attachments remain distinct.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

namespace Trace.Result

variable (traced : Trace.Result execution)
variable {expression : Expression (Paths.polynomial parameter)} {accuracy : AccuracyRequest}
variable (observed : Primitive.Spine expression accuracy traced.path)

/-- The SAME whole old spine at the actual four stored path append's exact original index.

The retained path factory equality transports the complete observation
execution. It does not rerun that execution or identify different spines
by their vertex lists or winding values.
-/
@[expose] def Aligned := Primitive.Spine expression accuracy
  (traced.first.append (traced.second.append (traced.third.append traced.fourth)))

/-- Three actual original split caches retain every complete quarter view of this SAME old whole spine. -/
@[expose] def Quarters :=
  Σ aligned : { retained : Aligned (expression := expression) (accuracy := accuracy) traced // retained =
    Primitive.Spine.castPath traced.path_eq observed },
    Σ first : { retained : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
          traced.first (traced.second.append (traced.third.append traced.fourth)) //
        retained = Primitive.Spine.split traced.first
          (traced.second.append (traced.third.append traced.fourth)) aligned.val },
      Σ second : { retained : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
            traced.second (traced.third.append traced.fourth) //
          retained = Primitive.Spine.split traced.second (traced.third.append traced.fourth)
            first.val.after },
        { third : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
            traced.third traced.fourth //
          third = Primitive.Spine.split traced.third traced.fourth second.val.after }

namespace Quarters

/-- Split the exact retained old execution once at each actual stored quarter boundary. -/
def build : Quarters traced observed :=
  let aligned := Primitive.Spine.castPath traced.path_eq observed
  let first := Primitive.Spine.split traced.first
    (traced.second.append (traced.third.append traced.fourth)) aligned
  let second := Primitive.Spine.split traced.second (traced.third.append traced.fourth) first.after
  let third := Primitive.Spine.split traced.third traced.fourth second.after
  ⟨⟨aligned, rfl⟩, ⟨first, rfl⟩, ⟨second, rfl⟩, ⟨third, rfl⟩⟩

variable {observed}
variable (divided : Quarters traced observed)

/-- Read the SAME entire old observation execution at the exact original append index. -/
@[expose] def aligned : Aligned (expression := expression) (accuracy := accuracy) traced := divided.1.val

/-- Read the complete retained first boundary split, including both whole old child spines. -/
@[expose] def firstSplit : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    traced.first (traced.second.append (traced.third.append traced.fourth)) := divided.2.1.val

/-- Read the complete original second boundary split of that SAME stored first suffix. -/
@[expose] def secondSplit : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    traced.second (traced.third.append traced.fourth) := divided.2.2.1.val

/-- Read the complete third boundary split on that SAME original second suffix. -/
@[expose] def thirdSplit : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    traced.third traced.fourth := divided.2.2.2.val

/-- Read the complete old first-quarter observation spine, retaining every actual stationary outcome. -/
@[expose] def first : Primitive.Spine expression accuracy traced.first := divided.firstSplit.before

/-- Read the complete old second-quarter observation spine at the identical literal seam vertex. -/
@[expose] def second : Primitive.Spine expression accuracy traced.second := divided.secondSplit.before

/-- Read the complete old third-quarter observation spine from the SAME ordered original suffix. -/
@[expose] def third : Primitive.Spine expression accuracy traced.third := divided.thirdSplit.before

/-- Read the complete old fourth-quarter observation spine, with the actual final returned Owner. -/
@[expose] def fourth : Primitive.Spine expression accuracy traced.fourth := divided.thirdSplit.after

/-- The whole append-index cache is the exact transport of the supplied old complete observation spine. -/
theorem aligned_eq : divided.aligned = Primitive.Spine.castPath traced.path_eq observed := divided.1.property

/-- The first full split cache is the actual original factory on the identical stored append-index spine. -/
theorem firstSplit_eq : divided.firstSplit = Primitive.Spine.split traced.first
    (traced.second.append (traced.third.append traced.fourth)) divided.aligned := divided.2.1.property

/-- The second split consumes the SAME complete old suffix, rather than a reconstructed observation execution. -/
theorem secondSplit_eq : divided.secondSplit = Primitive.Spine.split traced.second
    (traced.third.append traced.fourth) divided.firstSplit.after := divided.2.2.1.property

/-- The final split consumes the SAME complete original second suffix. -/
theorem thirdSplit_eq : divided.thirdSplit = Primitive.Spine.split traced.third traced.fourth
    divided.secondSplit.after := divided.2.2.2.property

/-- The first quarter retains the literal complete original whole-spine source vertex. -/
theorem first_eq : divided.first.first = observed.first := by
  have retained := congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy :=
    accuracy)
    traced.first (traced.second.append (traced.third.append traced.fourth)) => split.before.first)
    divided.firstSplit_eq
  exact retained.trans ((Primitive.Spine.split_first divided.aligned).trans
    ((congrArg (fun old : Aligned (expression := expression) (accuracy := accuracy) traced => old.first)
      divided.aligned_eq).trans
      (Primitive.Spine.castPath_first traced.path_eq observed)))

/-- Both old views at the first seam share one literal complete vertex cache. -/
theorem first_second : divided.second.first = divided.first.last := by
  have retained := congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy :=
    accuracy)
    traced.second (traced.third.append traced.fourth) => split.before.first) divided.secondSplit_eq
  exact (retained.trans (Primitive.Spine.split_first divided.firstSplit.after)).trans
    divided.firstSplit.shared

/-- Both old views at the second seam share the SAME complete original source/target vertex. -/
theorem second_third : divided.third.first = divided.second.last := by
  have retained := congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy :=
    accuracy)
    traced.third traced.fourth => split.before.first) divided.thirdSplit_eq
  exact (retained.trans (Primitive.Spine.split_first divided.secondSplit.after)).trans
    divided.secondSplit.shared

/-- The last two quarter views retain their identical literal old seam vertex. -/
theorem third_fourth : divided.fourth.first = divided.third.last := divided.thirdSplit.shared

/-- The fourth quarter retains the complete old returned vertex, including its original state and request. -/
theorem last_eq : divided.fourth.last = observed.last := by
  have thirdLast := congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy :=
    accuracy)
    traced.third traced.fourth => split.after.last) divided.thirdSplit_eq
  have secondLast := congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy :=
    accuracy)
    traced.second (traced.third.append traced.fourth) => split.after.last) divided.secondSplit_eq
  have firstLast := congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy :=
    accuracy)
    traced.first (traced.second.append (traced.third.append traced.fourth)) => split.after.last)
    divided.firstSplit_eq
  exact (thirdLast.trans (Primitive.Spine.split_last divided.secondSplit.after)).trans
    ((secondLast.trans (Primitive.Spine.split_last divided.firstSplit.after)).trans
      ((firstLast.trans (Primitive.Spine.split_last divided.aligned)).trans
        ((congrArg (fun old : Aligned (expression := expression) (accuracy := accuracy) traced => old.last)
          divided.aligned_eq).trans
          (Primitive.Spine.castPath_last traced.path_eq observed))))

/-- Reassemble the SAME complete quarter caches in their original physical append order.

Only the proved literal vertex-cache identities pass each old suffix to
its old prefix. Every original stationary occurrence is retained, and no
root, trace, observation or comparison producer is run.
-/
@[expose] def reassembled : Aligned (expression := expression) (accuracy := accuracy) traced :=
  let lastPair := Primitive.Spine.append divided.third divided.fourth divided.third_fourth
  let lastThree := Primitive.Spine.append divided.second lastPair
    ((Primitive.Spine.append_first divided.third divided.fourth divided.third_fourth).trans
      divided.second_third)
  Primitive.Spine.append divided.first lastThree
    ((Primitive.Spine.append_first divided.second lastPair
      ((Primitive.Spine.append_first divided.third divided.fourth divided.third_fourth).trans
        divided.second_third)).trans divided.first_second)

/-- The three split caches reassemble to the WHOLE identical old append-index spine, including all comparison data. -/
theorem reassembled_eq : divided.reassembled = divided.aligned := by
  have lastPair := (congrArg (fun split : Primitive.Spine.Split
      (expression := expression) (accuracy := accuracy) traced.third traced.fourth =>
      Primitive.Spine.append split.before split.after split.shared) divided.thirdSplit_eq).trans
    (Primitive.Spine.append_split divided.secondSplit.after)
  have lastThree := (Primitive.Spine.append_congr (before := divided.second) (nextBefore := divided.second)
      (after := Primitive.Spine.append divided.third divided.fourth divided.third_fourth)
      (nextAfter := divided.secondSplit.after) rfl lastPair
      ((Primitive.Spine.append_first divided.third divided.fourth divided.third_fourth).trans
        divided.second_third) divided.secondSplit.shared).trans
    ((congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
      traced.second (traced.third.append traced.fourth) =>
      Primitive.Spine.append split.before split.after split.shared) divided.secondSplit_eq).trans
        (Primitive.Spine.append_split divided.firstSplit.after))
  exact (Primitive.Spine.append_congr (before := divided.first) (nextBefore := divided.first)
      (nextAfter := divided.firstSplit.after) rfl lastThree
      ((Primitive.Spine.append_first divided.second
        (Primitive.Spine.append divided.third divided.fourth divided.third_fourth)
        ((Primitive.Spine.append_first divided.third divided.fourth divided.third_fourth).trans
          divided.second_third)).trans divided.first_second) divided.firstSplit.shared).trans
    ((congrArg (fun split : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
      traced.first (traced.second.append (traced.third.append traced.fourth)) =>
      Primitive.Spine.append split.before split.after split.shared) divided.firstSplit_eq).trans
        (Primitive.Spine.append_split divided.aligned))

/-- Exact physical whole-path transport and reassembly retain the WHOLE supplied old observation spine. -/
theorem reassembled_heq : HEq divided.reassembled observed :=
  (heq_of_eq divided.reassembled_eq).trans ((heq_of_eq divided.aligned_eq).trans
    (Primitive.Spine.castPath_heq traced.path_eq observed))

/-- The exact endpoint identities reindex the SAME old literal closing comparison at the four-quarter views.

The generic comparison's original states, tail choices, root relation,
residual and radius charges are retained together by type equality. No
comparison factory or observation producer is executed by this view.
-/
def closing {join : OwnerJoin execution.returnOwner sourceOwner}
    (compared : Primitive.Closing.Comparison observed join) :
    Observation.Comparison divided.fourth.last.observation divided.first.first.observation
      (Primitive.tailRequest accuracy).tolerance := by
  have indices := congrArg₂ (fun
      (last : Primitive.Vertex expression
        (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
        execution.returnOwner accuracy)
      (first : Primitive.Vertex expression
        (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
        sourceOwner accuracy) =>
      Observation.Comparison last.observation first.observation (Primitive.tailRequest accuracy).tolerance)
    divided.last_eq divided.first_eq
  exact indices.mpr compared.val

/-- Reindexing quarter endpoints preserves the WHOLE original closing operational comparison heterogeneously. -/
theorem closing_heq {join : OwnerJoin execution.returnOwner sourceOwner}
    (compared : Primitive.Closing.Comparison observed join) :
    HEq (closing traced divided compared) compared.val := by
  unfold closing
  have transport {first last : Sort _} (same : first = last) (value : last) :
      HEq (same.mpr value) value := by
    cases same
    rfl
  exact transport _ _

/-- The old closing comparison retains the actual signed quarter-return jump and its original local allowance. -/
theorem closing_jump_lt {join : OwnerJoin execution.returnOwner sourceOwner}
    (compared : Primitive.Closing.Comparison observed join) :
    Norm.Basic.normSq (divided.first.first.value - divided.fourth.last.value) < accuracy.tolerance :=
  Primitive.Stationary.jump_lt divided.fourth.last divided.first.first (closing traced divided compared)

end Quarters

end Trace.Result

namespace Closure.Result

variable (result : Closure.Result execution)
variable (expression : Expression (Paths.polynomial parameter))
variable (defined : Primitive.Defined expression result.traced.path) (request : AccuracyRequest)

/-- Retain one actual old closed acquisition and the complete four-quarter views of that SAME old spine.

The original acquisition computes its own count-paid requests before any
observation. Its exact stored closing Comparison remains on those same old
last and first vertices and the original literal paid OwnerJoin.
-/
@[expose] def Partitioned :=
  Σ observed : { retained : Primitive.Closed result.traced.path defined result.join request //
      retained = result.observe expression defined request },
    { divided : Trace.Result.Quarters result.traced observed.val.observations.observed //
      divided = Trace.Result.Quarters.build result.traced observed.val.observations.observed }

namespace Partitioned

/-- Retain a completed original closed acquisition, then split its identical old whole spine without observing again. -/
def ofObserved (observed : Primitive.Closed result.traced.path defined result.join request) :
    Partitioned result expression defined request :=
  let divided := Trace.Result.Quarters.build result.traced observed.observations.observed
  let same := observed.eq_build.trans (result.observe_eq expression defined request).symm
  ⟨⟨observed, same⟩, ⟨divided, rfl⟩⟩

/-- Construct the original count-paid observation spine once, then retain its actual four complete quarter views. -/
def build : Partitioned result expression defined request :=
  let observed := result.observe expression defined request
  let divided := Trace.Result.Quarters.build result.traced observed.observations.observed
  ⟨⟨observed, rfl⟩, ⟨divided, rfl⟩⟩

variable (retained : Partitioned result expression defined request)

/-- Read the complete original paid-circuit primitive acquisition and its literal stored closing comparison. -/
@[expose] def observed : Primitive.Closed result.traced.path defined result.join request :=
  retained.1.val

/-- The completed-input constructor retains the SAME whole old closed cache literally, without observing again. -/
theorem ofObserved_observed (observed : Primitive.Closed result.traced.path defined result.join request) :
    (ofObserved result expression defined request observed).observed = observed := by
  unfold ofObserved
  rfl

/-- Read all four complete old quarter views of that SAME retained whole-spine observation execution. -/
@[expose] def quarters : Trace.Result.Quarters result.traced retained.observed.observations.observed :=
  retained.2.val

/-- The original closed observation execution is retained with its exact factory equation. -/
theorem observed_eq : retained.observed = result.observe expression defined request := retained.1.property

/-- The complete four-quarter split cache is the original factory on that identical old complete spine. -/
theorem quarters_eq : retained.quarters = Trace.Result.Quarters.build result.traced
    retained.observed.observations.observed := retained.2.property

/-- Read the SAME original closing cache through the exact endpoint identities of the complete quarter views. -/
def closing : Observation.Comparison retained.quarters.fourth.last.observation
    retained.quarters.first.first.observation
    (Primitive.tailRequest retained.observed.observations.accuracy).tolerance :=
  Trace.Result.Quarters.closing result.traced retained.quarters retained.observed.closing

/-- The quarter endpoint view retains every field of the SAME old literal closing comparison cache. -/
theorem closing_heq : HEq (closing result expression defined request retained) retained.observed.closing.val :=
  Trace.Result.Quarters.closing_heq result.traced retained.quarters retained.observed.closing

/-- The literal original closing relation pays the return jump between the SAME retained quarter endpoint values. -/
theorem closing_jump_lt : Norm.Basic.normSq
    (retained.quarters.first.first.value - retained.quarters.fourth.last.value) <
      retained.observed.observations.accuracy.tolerance :=
  Trace.Result.Quarters.closing_jump_lt result.traced retained.quarters retained.observed.closing

/-- The original computed requests pay all old stationary occurrences and the SAME literal closing join. -/
theorem error_lt : Norm.Basic.normSq
    (Norm.Sum.Basic.gaussianSum retained.observed.closing.jumps) < request.tolerance := retained.observed.error_lt

end Partitioned

end Closure.Result

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

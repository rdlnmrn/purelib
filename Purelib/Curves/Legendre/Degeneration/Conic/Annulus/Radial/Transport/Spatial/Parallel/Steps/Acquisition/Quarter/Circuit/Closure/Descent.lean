module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Partition
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Seam.Observation
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Algebra.Quadratic.Pair.Polynomial

/-! # Complete old physical segment views of the same paid closed circuit

The original partition supplies four complete old quarter spines. Only the
literal stored path equations and the original seam endpoint casts change
their indices. Every resulting Block and physical Segment is the original
paid acquisition, and every primitive observation is the identical old cache.
The original whole closing comparison stays in the retained input.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

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

namespace Closure.Result.Partitioned

variable {result : Closure.Result execution}
variable {expression : Expression (Paths.polynomial parameter)}
variable {defined : Primitive.Defined expression result.traced.path} {request : AccuracyRequest}
variable (retained : Partitioned result expression defined request)

/-- View the same old first-quarter cache at its identical stored seam trace index. -/
@[expose, macro_inline] def firstInput : Primitive.Spine expression
    retained.observed.observations.accuracy execution.second.seam.trace :=
  Primitive.Spine.castPath result.traced.first_eq retained.quarters.first

/-- View the same old second-quarter cache at its identical stored seam trace index. -/
@[expose, macro_inline] def secondInput : Primitive.Spine expression
    retained.observed.observations.accuracy execution.third.seam.trace :=
  Primitive.Spine.castPath result.traced.second_eq retained.quarters.second

/-- View the same old third-quarter cache at its identical stored seam trace index. -/
@[expose, macro_inline] def thirdInput : Primitive.Spine expression
    retained.observed.observations.accuracy execution.fourth.seam.trace :=
  Primitive.Spine.castPath result.traced.third_eq retained.quarters.third

/-- View the same old fourth-quarter cache at its identical stored returning seam trace index. -/
@[expose, macro_inline] def fourthInput : Primitive.Spine expression
    retained.observed.observations.accuracy execution.closing.trace :=
  Primitive.Spine.castPath result.traced.fourth_eq retained.quarters.fourth

/-- Retain all actual old quarter/Block/Segment descents with their complete original factory identities.

The SAME original closed observation acquisition remains an index. These
four factories only partition old caches and reverse exact endpoint casts;
none runs a primitive observer, a paid acquisition or a source attachment.
-/
@[expose] def Descent :=
  Σ _first : { old : Quarter.Observations execution.first
        (execution.second.seam.quarterSpine retained.firstInput) //
      old = execution.second.seam.quarterViews retained.firstInput },
    Σ _second : { old : Quarter.Observations execution.second.paid
          (execution.third.seam.quarterSpine retained.secondInput) //
        old = execution.third.seam.quarterViews retained.secondInput },
      Σ _third : { old : Quarter.Observations execution.third.paid
            (execution.fourth.seam.quarterSpine retained.thirdInput) //
          old = execution.fourth.seam.quarterViews retained.thirdInput },
        { fourth : Quarter.Observations execution.fourth.paid
              (execution.closing.quarterSpine retained.fourthInput) //
            fourth = execution.closing.quarterViews retained.fourthInput }

namespace Descent

/-- Materialize each actual old quarter's physical descent once on the SAME old closed execution. -/
def build : Descent retained :=
  let first := execution.second.seam.quarterViews retained.firstInput
  let second := execution.third.seam.quarterViews retained.secondInput
  let third := execution.fourth.seam.quarterViews retained.thirdInput
  let fourth := execution.closing.quarterViews retained.fourthInput
  ⟨⟨first, rfl⟩, ⟨second, rfl⟩, ⟨third, rfl⟩, ⟨fourth, rfl⟩⟩

variable {retained}
variable (descended : Descent retained)

/-- Read the complete actual first-quarter descent through its same retained paid Blocks and physical Segments. -/
@[expose] def first : Quarter.Observations execution.first
    (execution.second.seam.quarterSpine retained.firstInput) := descended.1.val

/-- Read the complete actual second-quarter descent, preserving every old stationary occurrence. -/
@[expose] def second : Quarter.Observations execution.second.paid
    (execution.third.seam.quarterSpine retained.secondInput) := descended.2.1.val

/-- Read the complete actual third-quarter descent, retaining its literal stored Segment acquisitions. -/
@[expose] def third : Quarter.Observations execution.third.paid
    (execution.fourth.seam.quarterSpine retained.thirdInput) := descended.2.2.1.val

/-- Read the complete actual returned-quarter descent, without altering the original closing cache. -/
@[expose] def fourth : Quarter.Observations execution.fourth.paid
    (execution.closing.quarterSpine retained.fourthInput) := descended.2.2.2.val

/-- The complete first descent is its actual cache-only factory on the identical old first seam spine. -/
theorem first_eq : descended.first = execution.second.seam.quarterViews retained.firstInput :=
  descended.1.property

/-- The complete second descent is its actual cache-only factory on the identical old second seam spine. -/
theorem second_eq : descended.second = execution.third.seam.quarterViews retained.secondInput :=
  descended.2.1.property

/-- The complete third descent is its actual cache-only factory on the identical old third seam spine. -/
theorem third_eq : descended.third = execution.fourth.seam.quarterViews retained.thirdInput :=
  descended.2.2.1.property

/-- The complete fourth descent is its actual cache-only factory on the identical old returned seam spine. -/
theorem fourth_eq : descended.fourth = execution.closing.quarterViews retained.fourthInput :=
  descended.2.2.2.property

/-- Every field of the old first spine survives the actual seam and full-quarter descent. -/
theorem first_heq : HEq descended.first.original retained.quarters.first :=
  (heq_of_eq descended.first.original_eq).trans
    ((execution.second.seam.quarterSpine_heq retained.firstInput).trans
      (Primitive.Spine.castPath_heq result.traced.first_eq retained.quarters.first))

/-- Every field of the old second spine survives the actual seam and full-quarter descent. -/
theorem second_heq : HEq descended.second.original retained.quarters.second :=
  (heq_of_eq descended.second.original_eq).trans
    ((execution.third.seam.quarterSpine_heq retained.secondInput).trans
      (Primitive.Spine.castPath_heq result.traced.second_eq retained.quarters.second))

/-- Every field of the old third spine survives the actual seam and full-quarter descent. -/
theorem third_heq : HEq descended.third.original retained.quarters.third :=
  (heq_of_eq descended.third.original_eq).trans
    ((execution.fourth.seam.quarterSpine_heq retained.thirdInput).trans
      (Primitive.Spine.castPath_heq result.traced.third_eq retained.quarters.third))

/-- Every field of the old fourth spine survives its returning seam and actual full-quarter descent. -/
theorem fourth_heq : HEq descended.fourth.original retained.quarters.fourth :=
  (heq_of_eq descended.fourth.original_eq).trans
    ((execution.closing.quarterSpine_heq retained.fourthInput).trans
      (Primitive.Spine.castPath_heq result.traced.fourth_eq retained.quarters.fourth))

end Descent

end Closure.Result.Partitioned

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

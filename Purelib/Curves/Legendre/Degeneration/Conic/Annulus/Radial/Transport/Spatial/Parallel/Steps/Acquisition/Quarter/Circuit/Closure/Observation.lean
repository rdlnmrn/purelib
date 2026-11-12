module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure
public import Purelib.Riemann.Paths.OwnerTraceReadings.Observation
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.OwnerPath
import Purelib.Approximation.AccuracyRequest

/-! # Primitive observations on the actual paid circuit's closing join

The stored Closure.Result supplies its literal original OwnerJoin. Two old
coefficient observations on that join's exact returned and initial Owners
are compared without acquiring a join, root, denotation or reading again.
The original closed-realization and join factory caches remain untouched.
This pays the supplied closing observations; it does not identify omitted
per-step stationary observations or different local primitive constants.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Algebra.Quadratic.Pair.Polynomial.Expression (Denotation)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

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

namespace Closure.Result

variable (result : Closure.Result execution)
variable {primitive : Expression (Paths.polynomial parameter)}
variable (returned : Denotation primitive
  (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
  (execution.returnOwner.certificate execution.returnOwner.parameterNonzero).value)
variable (initialValue : Denotation primitive
  (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
  (sourceOwner.certificate sourceOwner.parameterNonzero).value)

/-- Compare old primitive-channel observations through the exact stored closing join of this actual paid circuit.

The signed full-root relation is derived from that literal join. The
original observation states and values, coefficient caches, returned Owner,
initial Owner and original complete closure result remain the inputs.
-/
def comparePrimitive
    (returnedReading : Observation.Reading returned.channel)
    (initialReading : Observation.Reading initialValue.channel) (request : AccuracyRequest) :
    Observation.Comparison returnedReading initialReading request.tolerance :=
  result.join.compareDenotations returned initialValue returnedReading initialReading request

include result in
/-- The actual closing comparison charges both unchanged old primitive-state radii and its finite tail target. -/
theorem comparePrimitive_error_le
    (returnedReading : Observation.Reading returned.channel)
    (initialReading : Observation.Reading initialValue.channel) (request : AccuracyRequest) :
    Norm.Basic.normSq (returnedReading.value - initialReading.value) ≤
      16 * (returnedReading.radius + initialReading.radius) + 4 * request.tolerance :=
  (result.comparePrimitive returned initialValue returnedReading initialReading request).reading_error_le

/-- Observe an exact supplied primitive expression on the SAME paid trace and literal stored closing join.

The denominator guards belong to the original expression at every retained
vertex. The complete original acquisition and closing caches stay together;
no coefficient normalization or replacement trace is inferred.
-/
def observe (expression : Expression (Paths.polynomial parameter))
    (defined : OwnerPath.Primitive.Defined expression result.traced.path) (request : AccuracyRequest) :
    OwnerPath.Primitive.Closed result.traced.path defined result.join request :=
  OwnerPath.Primitive.Closed.build result.traced.path defined result.join request

/-- The whole generic observation result is its original closing factory on these identical expression/guard indices. -/
theorem observe_eq (expression : Expression (Paths.polynomial parameter))
    (defined : OwnerPath.Primitive.Defined expression result.traced.path) (request : AccuracyRequest) :
    result.observe expression defined request =
      OwnerPath.Primitive.Closed.build result.traced.path defined result.join request := by
  unfold observe
  rfl

/-- Construct coefficient observations on the exact paid path and compare old endpoints through its stored join.

The original odd-power coefficient supplies its denominator guards from
each retained full-root Owner. The actual path and literal closing join
are consumed unchanged, with computed requests paying all stationary
occurrences and the closing edge. Moving integral comparison and primitive
identities remain separate certificates.
-/
def observeCoefficient (differential : OddPowerDifferential (Paths.polynomial parameter))
    (request : AccuracyRequest) :
    OddPower.Observation.OwnerPath.Closed differential result.traced.path result.join request :=
  OddPower.Observation.OwnerPath.Closed.build differential result.traced.path result.join request

/-- The original coefficient entry preserves the SAME whole generic cache at its exact coefficient and guard indices. -/
theorem observeCoefficient_eq (differential : OddPowerDifferential (Paths.polynomial parameter))
    (request : AccuracyRequest) : result.observeCoefficient differential request =
      result.observe differential.coefficient (OddPower.Observation.OwnerPath.defined differential result.traced.path)
        request :=
  (OddPower.Observation.OwnerPath.Closed.build_eq differential result.traced.path result.join request).trans
    (result.observe_eq differential.coefficient
      (OddPower.Observation.OwnerPath.defined differential result.traced.path) request).symm

/-- The computed requests bound the stationary jumps on this same paid path, including its literal closing join. -/
theorem observeCoefficient_error_lt (differential : OddPowerDifferential (Paths.polynomial parameter))
    (request : AccuracyRequest) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum
      (result.observeCoefficient differential request).closing.jumps) < request.tolerance :=
  (result.observeCoefficient differential request).error_lt

end Closure.Result

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

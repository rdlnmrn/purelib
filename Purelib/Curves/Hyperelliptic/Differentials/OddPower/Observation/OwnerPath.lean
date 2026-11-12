module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Provenance.Power

/-! # Original odd-power coefficient observations on a retained owner path

The original indexed differential supplies its already cached coefficient
expression and existing denominator-guard theorem. Every actual vertex's
original full-root Owner supplies square/apartness evidence, so admission
of the same coefficient at every vertex is derived internally. The finite
stationary-observation acquisition then computes sufficient original
requests on the SAME path. A returning path's literal supplied closing join
reuses its exact last and first observations without reexecuting that path.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.OwnerPath

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)

variable {polynomial : Coefficients}

/-- The actual vertex Owner's original square/apartness evidence admits the retained differential coefficient. -/
private theorem vertex_defined (differential : OddPowerDifferential polynomial) (point : Canonical)
    (owner : Owner (polynomial.eval point)) : differential.coefficient.Defined point :=
  let certificate := owner.certificate owner.parameterNonzero
  differential.defined point certificate.value (PowerIdentity.ofSquare certificate.square) certificate.apart

/-- The SAME cached odd-power coefficient is defined at every exact original vertex of this retained path.

The original differential's guard theorem consumes each supplied Owner's
own original square certificate and apartness data. No coefficient table,
root continuation or final owner relation is supplied or reconstructed.
-/
theorem defined (differential : OddPowerDifferential polynomial) :
    ∀ {start finish : Canonical} {left : Owner (polynomial.eval start)}
      {right : Owner (polynomial.eval finish)} (path : OwnerTracePath.OwnerPath polynomial start left finish right),
      Primitive.Defined differential.coefficient path
  | _, _, _, _, .nil point owner => vertex_defined differential point owner
  | start, _, left, _, .cons _ tail =>
      ⟨vertex_defined differential start left, defined differential tail⟩

/-- Compute sufficient original primitive requests on the SAME retained path using its actual cached coefficient.

All vertex denominator guards are derived internally from the original
Owners. The acquisition retains the original path's vertex list, actual
count-dependent request and complete observation/comparison spine. It does
not acquire a replacement path, Owner, geometric attachment or join.
-/
def acquire (differential : OddPowerDifferential polynomial) {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    (path : OwnerTracePath.OwnerPath polynomial start left finish right) (request : AccuracyRequest) :
    Primitive.Acquisition (expression := differential.coefficient) path (defined differential path) request :=
  Primitive.Acquisition.build (expression := differential.coefficient) path (defined differential path) request

variable {base : Canonical} {source target : Owner (polynomial.eval base)}
variable (differential : OddPowerDifferential polynomial)
variable (returning : OwnerTracePath.OwnerPath polynomial base source base target)
variable (join : OwnerJoin target source) (request : AccuracyRequest)

/-- Retain one actual original coefficient-observation acquisition and its comparison across the literal closing join.

The complete acquisition and complete closing Comparison each carry their
original factory equation. The closing comparison consumes the same old
last and first observations; no new request or OwnerJoin is selected there.
-/
abbrev Closed :=
  Primitive.Closed returning (defined differential returning) join request

namespace Closed

/-- Retain the actual finite observation spine once and compare its old endpoints with this SAME join. -/
def build : Closed differential returning join request :=
  let observations := acquire differential returning request
  Primitive.Closed.ofAcquisition returning (defined differential returning) join request observations

/-- The coefficient entry retains the SAME complete generic closing execution at its unchanged original guards. -/
theorem build_eq : build differential returning join request =
    Primitive.Closed.build returning (defined differential returning) join request :=
  Primitive.Closed.eq_build (build differential returning join request)

variable (retained : Closed differential returning join request)

/-- Read the entire original coefficient-observation acquisition unchanged. -/
@[expose] def observations : Primitive.Acquisition (expression := differential.coefficient)
    returning (defined differential returning) request := retained.1.val

/-- Read the actual closing Comparison on the SAME last/first observation caches and the literal supplied join. -/
@[expose] def closing : Primitive.Closing.Comparison (expression := differential.coefficient) (returning := returning)
    (accuracy := retained.observations.accuracy) retained.observations.observed join := retained.2.val

/-- The complete stored observation acquisition is the original factory on the same differential and retained path. -/
theorem observations_eq : retained.observations = acquire differential returning request := retained.1.property

/-- The complete closing cache is the original comparison factory on those identical old observation inputs. -/
theorem closing_eq : retained.closing = Primitive.Closing.Comparison.build
    (expression := differential.coefficient) (returning := returning) (accuracy := retained.observations.accuracy)
    retained.observations.observed join :=
  retained.2.property

/-- Computed original requests pay every stationary sample jump, including the actual retained closing join. -/
theorem error_lt : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum retained.closing.jumps) < request.tolerance :=
  Primitive.Closing.Comparison.error_lt (expression := differential.coefficient) (returning := returning)
    (accuracy := retained.observations.accuracy) (observed := retained.observations.observed) (join := join)
    retained.closing (request := request) retained.observations.accuracy_tolerance.le

end Closed

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.OwnerPath

end

module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

public import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Cached assembly of heterogeneous primitive requests

Each piece retains its own polynomial tolerance and checked request. A
common upper tolerance permits concatenating these data without constructing
new polynomials or subdivisions. The assembled primitive and integral sums
read the per-piece caches; no polynomial evaluation or integration is rerun.
The independent comparison values pay both factors of the actual piece count.
-/

namespace Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches

open Purelib.Data.List
open Purelib.Data
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum)
open Purelib.Riemann.Integration
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data in
/-- The canonical Gaussian rational scalar type for batch values. -/
abbrev BatchGaussian := Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {localTarget coefficientTarget errorBound : Coordinate}

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain one checked numerical request and an independently compared value.

Each part keeps its own parent list and target, with evidence fitting common local and coefficient tolerances and a
squared-error bound against its cached primitive sum. -/
structure RequestPart (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus) (count : Nat)
    (localTarget coefficientTarget errorBound : Coordinate) where
  /-- The original parent list for this request part. -/ parents : List (CenteredEdge curve differential)
  /-- The original target of the retained numerical request. -/ target : Coordinate
  /-- The retained controlled primitive request with its original caches. -/ request : ControlledSumRequest parents
    count target
  /-- The independently computed comparison value. -/ value : BatchGaussian
  /-- The original local tolerance fits the common batch tolerance. -/ local_le : request.localTarget ≤ localTarget
  /-- The original coefficient-error maximum is strictly below the common coefficient target. -/ coefficient_lt :
    coefficientMaximum request.requests < coefficientTarget
  /-- The independent value and retained primitive sum satisfy the common squared-error bound. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (value - request.primitiveSum) ≤ errorBound

constructive_injectivity RequestPart

namespace RequestBatch

/-- An ordered finite list of request parts sharing only the batch bounds. -/
abbrev Parts := List (RequestPart curve differential count localTarget coefficientTarget errorBound)

/-- Concatenate the original parent lists in their retained part order. -/
def parents : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound) →
    List (CenteredEdge curve differential)
  | [] => []
  | part :: parts => part.parents ++ parents parts

/-- Concatenate the retained requests after weakening their tolerances to the common bound.

The original polynomials, subdivisions and numerical caches are reused. -/
def requests : (parts : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound)) →
    RequestedParents count localTarget (parents parts)
  | [] => .nil
  | part :: parts => (part.request.requests.weaken part.local_le).append (requests parts)

/-- Concatenate the cached primitive increments in original part order. -/
def increments : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound) → List
      BatchGaussian
  | [] => []
  | part :: parts => part.request.increments ++ increments parts

/-- Add the retained primitive sums without reevaluating the polynomials. -/
def primitiveSum : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound) → BatchGaussian
  | [] => 0
  | part :: parts => part.request.primitiveSum + primitiveSum parts

/-- Add the retained integral samples without rerunning integration. -/
def integralSample : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound) → BatchGaussian
  | [] => 0
  | part :: parts => part.request.integralSample + integralSample parts

/-- The ordered independent comparison values of the retained parts. -/
def values : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound) → List
      BatchGaussian
  | [] => []
  | part :: parts => part.value :: values parts

/-- The ordered differences between each independent value and its cached primitive sum. -/
def errors : Parts (curve := curve) (differential := differential) (count := count)
    (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound) → List
      BatchGaussian
  | [] => []
  | part :: parts => (part.value - part.request.primitiveSum) :: errors parts

variable (parts : Parts (curve := curve) (differential := differential) (count := count)
  (localTarget := localTarget) (coefficientTarget := coefficientTarget) (errorBound := errorBound))

/-- The concatenated increment cache reads back to the assembled retained requests. -/
theorem increments_eq : increments parts = (requests parts).increments := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
      change part.request.increments ++ increments parts =
        ((part.request.requests.weaken part.local_le).append (requests parts)).increments
      rw [RequestedParents.increments_append, RequestedParents.weaken_increments, part.request.increments_eq, ih]

open Purelib.Data in
/-- The sum of cached primitive sums equals the sum of the concatenated increment cache. -/
theorem primitiveSum_eq : primitiveSum parts = Data.Gaussian.Norm.Sum.Basic.gaussianSum (increments parts) := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
      simp only [primitiveSum, increments, Data.Gaussian.Norm.Sum.Basic.gaussianSum_append]
      rw [part.request.primitiveSum_eq, ih]

open Purelib.Integration in
/-- The sum of cached integral samples reads back to the assembled requests' actual child models. -/
theorem integralSample_eq : integralSample parts =
    (Polynomial.Gaussian.Path.Basic.PathModel.mk ((requests parts).blocks.children.map
      CenteredEdge.model)).integralSample := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
      change part.request.integralSample + integralSample parts =
        (Polynomial.Gaussian.Path.Basic.PathModel.mk (((part.request.requests.weaken part.local_le).append (requests
          parts)).blocks.children.map
          CenteredEdge.model)).integralSample
      simp only [RequestedParents.children_append, RequestedParents.weaken_blocks,
        Map.map_append, Polynomial.Gaussian.Path.Basic.PathModel.integralSample_mk_append]
      rw [part.request.integralSample_eq, part.request.blocks_eq, ih]

/-- A positive common coefficient target bounds the assembled coefficient-error maximum strictly. -/
theorem coefficient_lt (positive : 0 < coefficientTarget) : coefficientMaximum (requests parts) < coefficientTarget :=
  by
  induction parts with
  | nil => exact positive
  | cons part parts ih =>
      change coefficientMaximum ((part.request.requests.weaken part.local_le).append (requests parts)) <
        coefficientTarget
      rw [RequestedParents.coefficientMaximum_append, RequestedParents.weaken_coefficientMaximum]
      cases Fraction.Order.Basic.le_total
          (coefficientMaximum part.request.requests)
          (coefficientMaximum (requests parts)) with
      | inl ordered =>
          rw [Fraction.Order.Basic.max_eq_right ordered]
          exact ih
      | inr ordered =>
          rw [Fraction.Order.Basic.max_eq_left ordered]
          exact part.coefficient_lt

/-- There is exactly one retained error for each request part. -/
theorem errors_length : (errors parts).length = parts.length := by
  induction parts with
  | nil => rfl
  | cons part parts ih => exact congrArg Nat.succ ih

/-- There is exactly one independent value for each request part. -/
theorem values_length : (values parts).length = parts.length := by
  induction parts with
  | nil => rfl
  | cons part parts ih => exact congrArg Nat.succ ih

section
open Purelib.Data
/-- The sum of retained errors equals the difference of the independent-value sum and cached primitive sum. -/
theorem errors_sum : Data.Gaussian.Norm.Sum.Basic.gaussianSum (errors parts) = Data.Gaussian.Norm.Sum.Basic.gaussianSum
  (values parts) - primitiveSum parts := by
  induction parts with
  | nil => change (0 : BatchGaussian) = 0 - 0; ring1
  | cons part parts ih => simp only [errors, values, primitiveSum, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]; ring1

/-- Every retained per-part error satisfies the common squared-error bound. -/
theorem errors_bounded : ∀ error ∈ errors parts, Data.Gaussian.Norm.Basic.normSq error ≤ errorBound := by
  induction parts with
  | nil => intro error member; cases member
  | cons part parts ih =>
      intro error member
      cases member with
      | head => exact part.accurate
      | tail _ member => exact ih error member

/-- The complete comparison pays both factors of the actual request-part count. -/
theorem error_le : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values parts) -
  primitiveSum parts) ≤
    (parts.length : Coordinate) * ((parts.length : Coordinate) * errorBound) := by
  rw [← errors_sum parts]
  have bounded := Gaussian.Norm.Sum.Bounds.normSq_sum_le (errors parts) errorBound (errors_bounded parts)
  rw [errors_length parts] at bounded
  exact bounded

end

open Purelib.Approximation in
/-- Assemble a controlled request from the original per-part caches.

The supplied common-tolerance, movement-mass and coefficient-payment equations certify the concatenation. Executable
work adds retained scalar values and joins existing lists without new polynomial evaluation or integration. -/
def assemble (target : Coordinate) (positive : 0 < target)
    (localEq : localTarget = Rational.Budget.Aggregate.perTerm target (parents parts).length)
    (mass : Coordinate) (massEq : mass = PreparedRefinementMovement.movementMass (parents parts))
    (coefficientEq : coefficientTarget = (target / 2) / (mass + 1))
    (coefficientPositive : 0 < coefficientTarget) : ControlledSumRequest (parents parts) count target :=
  let cachedRequests := requests parts
  { target_positive := positive
    localTarget := localTarget
    localTarget_eq := localEq
    localTarget_positive := localEq ▸ Rational.Budget.Aggregate.perTerm_positive positive _
    requests := cachedRequests
    blocks := cachedRequests.blocks
    blocks_eq := rfl
    increments := increments parts
    increments_eq := increments_eq parts
    primitiveSum := primitiveSum parts
    primitiveSum_eq := primitiveSum_eq parts
    integralSample := integralSample parts
    integralSample_eq := integralSample_eq parts
    mass := mass
    mass_eq := massEq
    coefficientTarget := coefficientTarget
    coefficientTarget_eq := coefficientEq
    coefficient_accurate := coefficient_lt parts coefficientPositive
    minimumIndex := 0
    indices_ge := cachedRequests.indices_zero }

end RequestBatch

namespace ControlledSumRequest

/-- Transport a retained controlled request along an exact equality of its parent lists. -/
def castParents {parents remaining : List (CenteredEdge curve differential)} {target : Coordinate}
    (request : ControlledSumRequest parents count target) (equation : parents = remaining) :
    ControlledSumRequest remaining count target := equation ▸ request

/-- Exact parent-list transport preserves the cached primitive sum. -/
theorem castParents_primitiveSum {parents remaining : List (CenteredEdge curve differential)} {target : Coordinate}
    (request : ControlledSumRequest parents count target) (equation : parents = remaining) :
    (castParents request equation).primitiveSum = request.primitiveSum := by
  cases equation
  rfl

/-- Parent-list transport retains the controlled request's minimum index.

Equality elimination leaves the original request and its selected minimum
unchanged; no request preparation or index selection is repeated. -/
theorem castParents_minimumIndex {parents remaining : List (CenteredEdge curve differential)} {target : Coordinate}
    (request : ControlledSumRequest parents count target) (equation : parents = remaining) :
    (castParents request equation).minimumIndex = request.minimumIndex := by
  cases equation
  rfl

/-- Parent-list transport retains the complete controlled request heterogeneously.

The equality changes only the parent-list index. Eliminating that equality
identifies the transported record with the same original request. -/
theorem castParents_heq {parents remaining : List (CenteredEdge curve differential)} {target : Coordinate}
    (request : ControlledSumRequest parents count target) (equation : parents = remaining) :
    HEq (castParents request equation) request := by
  cases equation
  rfl

end ControlledSumRequest
end Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches

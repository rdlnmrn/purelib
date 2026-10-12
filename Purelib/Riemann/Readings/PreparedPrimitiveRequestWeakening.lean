module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Spatial
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Mathlib.Order.Basic

public section

/-!
# Reusing checked primitive requests under a larger tolerance

Changing a tolerance copies the retained polynomial, root diameter and
subdivision block. No index selection, root preparation or integration is
repeated. These operations assemble independently requested path pieces into
one comparison with their original concatenated period-parent list.
-/

namespace Purelib.Approximation.Rational.Budget.Spatial.SpatialBudget

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Rational.Budget.Spatial (SpatialBudget)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Weaken the requested tolerance while retaining the same executable preparation data.

Only the accuracy inequalities are transported to the larger target; the original models, indices, child blocks and
request order remain unchanged. -/
@[expose] def weaken {first second movement taylorWeight errorWeight preparedScale denominatorLower : Fraction.Rational}
    {preparationDepth : Fraction.Rational → Nat}
    (budget : Budget.Spatial.SpatialBudget first movement taylorWeight errorWeight preparedScale denominatorLower
      preparationDepth)
    (order : first ≤ second) :
    Budget.Spatial.SpatialBudget second movement taylorWeight errorWeight preparedScale denominatorLower
      preparationDepth :=
  { budget with
    taylor_le := budget.taylor_le.trans (Fraction.Order.Field.divide_mono order (by decide))
    error_le := budget.error_le.trans (Fraction.Order.Field.divide_mono order (by decide)) }

end Purelib.Approximation.Rational.Budget.Spatial.SpatialBudget

namespace Purelib.Riemann.Readings.PreparedPrimitiveRequests.Request

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate Request)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Weaken the requested tolerance while retaining the same executable preparation data.

Only the accuracy inequalities are transported to the larger target; the original models, indices, child blocks and
request order remain unchanged. -/
@[expose] def weaken {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {parent : CenteredEdge curve differential} {patch : ContinuedNeighborhood curve.polynomial count}
    {first second : Fraction.Rational} (request : Request parent patch first) (order : first ≤ second) : Request parent
      patch second :=
  { request with
    polynomial_accurate := request.polynomial_accurate.trans_le (Fraction.Order.Field.divide_mono order (by decide))
    budget := request.budget.weaken order }

end Purelib.Riemann.Readings.PreparedPrimitiveRequests.Request

namespace Purelib.Riemann.Readings.UniformPreparedRequests

open Purelib.Data.List
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum remainderMaximum)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (IndicesAbove)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {first second target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Rat in
/-- Weaken the requested tolerance while retaining the same executable preparation data.

Only the accuracy inequalities are transported to the larger target; the original models, indices, child blocks and
request order remain unchanged. -/
@[expose] def LocalRequest.weaken {parent : CenteredEdge curve differential}
    (request : LocalRequest parent count first) (order : first ≤ second) : LocalRequest parent count second :=
  { request with request := request.request.weaken (Fraction.Order.Field.divide_mono order (by decide)) }

namespace RequestedParents

/-- Weaken the requested tolerance while retaining the same executable preparation data.

Only the accuracy inequalities are transported to the larger target; the original models, indices, child blocks and
request order remain unchanged. -/
@[expose] def weaken {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count first
  parents)
    (order : first ≤ second) : RequestedParents count second parents :=
  match requests with
  | .nil => .nil
  | .cons request tail => .cons (request.weaken order) (tail.weaken order)

/-- Read the original parent list retained by this request family. -/
@[expose] def parentList : {parents : List (CenteredEdge curve differential)} → RequestedParents count target parents →
    List (CenteredEdge curve differential)
  | _, .nil => []
  | parent :: remaining, .cons _ _ => parent :: remaining

/-- The request family's retained parent-list readback equals its exact index list. -/
theorem parentList_eq {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents) :
    requests.parentList = parents := by cases requests <;> rfl

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A retained concatenated parent list and request family with its exact list identity.

The data list keeps the actual original request owners; its equality permits transport back to the specified
concatenation without rebuilding the tail. -/
structure AppendCache (parents : List (CenteredEdge curve differential)) (count : Nat) (target : Fraction.Rational)
  where
  /-- The actual retained concatenated parent list. -/ data : List (CenteredEdge curve differential)
  /-- Exact equality with the specified original concatenation. -/ data_eq : data = parents
  /-- The original requests indexed by that same retained data list. -/ requests : RequestedParents count target data

constructive_injectivity AppendCache

/-- Append the original request families while retaining the exact tail list as cached data. -/
@[expose] def appendCache {parents remaining : List (CenteredEdge curve differential)} (requests : RequestedParents
  count target parents)
    (tail : RequestedParents count target remaining) : AppendCache (parents ++ remaining) count target :=
  match requests with
  | .nil => ⟨tail.parentList, tail.parentList_eq, tail.parentList_eq.symm ▸ tail⟩
  | .cons request rest =>
      let joined := appendCache rest tail
      ⟨_ :: joined.data, congrArg (List.cons _) joined.data_eq, .cons request joined.requests⟩

/-- Append original request families through their retained concatenation cache. -/
@[expose] def append {parents remaining : List (CenteredEdge curve differential)} (requests : RequestedParents count
  target parents)
    (tail : RequestedParents count target remaining) : RequestedParents count target (parents ++ remaining) :=
  let joined := appendCache requests tail
  joined.data_eq ▸ joined.requests

/-- Appending an empty original request family retains the exact tail family. -/
theorem append_nil {remaining : List (CenteredEdge curve differential)} (tail : RequestedParents count target remaining)
  :
    RequestedParents.append .nil tail = tail := by cases tail <;> rfl

/-- Transporting a cons request preserves its head and transports only the exact tail-list identity. -/
private theorem cast_cons {parent : CenteredEdge curve differential} {parents remaining : List (CenteredEdge curve
  differential)}
    (equation : parents = remaining) (request : LocalRequest parent count target) (tail : RequestedParents count target
      parents) :
    (congrArg (List.cons parent) equation ▸ RequestedParents.cons request tail) = .cons request (equation ▸ tail) := by
  cases equation
  rfl

/-- Appending a nonempty request family retains its original head and recursively appended tail. -/
theorem append_cons {parent : CenteredEdge curve differential} {parents remaining : List (CenteredEdge curve
  differential)}
    (request : LocalRequest parent count target) (rest : RequestedParents count target parents)
    (tail : RequestedParents count target remaining) :
    (RequestedParents.cons request rest).append tail = .cons request (rest.append tail) := by
  simp only [append, appendCache]
  exact cast_cons (appendCache rest tail).data_eq request (appendCache rest tail).requests

/-- Weakening tolerance preserves the original primitive increment list. -/
theorem weaken_increments {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count first parents) (order : first ≤ second) :
    (requests.weaken order).increments = requests.increments := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg (List.cons _) ih

/-- Weakening tolerance preserves the exact original direct-refinement blocks. -/
theorem weaken_blocks {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count first parents) (order : first ≤ second) :
    (requests.weaken order).blocks = requests.blocks := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg (DirectBlockRefinement.cons request.request.block) ih

/-- Weakening tolerance preserves the original local coefficient maximum. -/
theorem weaken_coefficientMaximum {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count first parents) (order : first ≤ second) :
    coefficientMaximum (requests.weaken order) = coefficientMaximum requests := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg (max _) ih

/-- Weakening tolerance preserves the original primitive remainder maximum. -/
theorem weaken_remainderMaximum {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count first parents) (order : first ≤ second) :
    remainderMaximum (requests.weaken order) = remainderMaximum requests := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg (max _) ih

/-- Weakening tolerance preserves all original lower bounds on refinement indices. -/
theorem weaken_indices {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count first parents) (order : first ≤ second) {minimum : Nat}
    (indices : IndicesAbove minimum requests) : IndicesAbove minimum (requests.weaken order) := by
  induction requests with
  | nil => trivial
  | cons request tail ih => exact ⟨indices.1, ih indices.2⟩

/-- The appended requests retain the original ordered concatenation of primitive increments. -/
theorem increments_append {parents remaining : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (tail : RequestedParents count target remaining) :
    (requests.append tail).increments = requests.increments ++ tail.increments := by
  induction requests with
  | nil => rw [append_nil]; rfl
  | cons request rest ih => rw [append_cons]; exact congrArg (List.cons _) ih

/-- The appended requests retain the original ordered concatenation of child blocks. -/
theorem children_append {parents remaining : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (tail : RequestedParents count target remaining) :
    (requests.append tail).blocks.children = requests.blocks.children ++ tail.blocks.children := by
  induction requests with
  | nil => rw [append_nil]; rfl
  | cons request rest ih =>
      rw [append_cons]
      change request.request.block.children ++ (rest.append tail).blocks.children =
        (request.request.block.children ++ rest.blocks.children) ++ tail.blocks.children
      rw [ih, Append.append_assoc]

/-- The appended coefficient maximum is the maximum of the original family maxima. -/
theorem coefficientMaximum_append {parents remaining : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (tail : RequestedParents count target remaining) :
    coefficientMaximum (requests.append tail) = max (coefficientMaximum requests) (coefficientMaximum tail) := by
  induction requests with
  | nil =>
    rw [append_nil]; exact (Fraction.Order.Basic.max_eq_right
      (PreparedPrimitiveChargeBounds.coefficientMaximum_nonnegative tail)).symm
  | cons request rest ih =>
      rw [append_cons]
      change max _ (coefficientMaximum (rest.append tail)) = max (max _ (coefficientMaximum rest)) _
      rw [ih, Fraction.Order.Basic.max_assoc]

/-- Every retained request index is at least zero. -/
theorem indices_zero {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents) :
    IndicesAbove 0 requests := by
  induction requests with
  | nil => trivial
  | cons request tail ih => exact ⟨Nat.zero_le _, ih⟩

end RequestedParents
end Purelib.Riemann.Readings.UniformPreparedRequests

namespace Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass_nonnegative)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parents : List (CenteredEdge curve differential)} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Approximation.Rational in
/-- The retained per-parent target is at most the original controlled sum target. -/
theorem localTarget_le (request : ControlledSumRequest parents count target) : request.localTarget ≤ target := by
  rw [request.localTarget_eq]
  exact Budget.Aggregate.perTerm_le request.target_positive.le _

open Purelib.Data.Rat in
/-- The retained mass-based coefficient target is at most the original sum target. -/
theorem coefficientTarget_le (request : ControlledSumRequest parents count target) : request.coefficientTarget ≤ target
  := by
  rw [request.coefficientTarget_eq]
  have massNonnegative : 0 ≤ request.mass := by
    rw [request.mass_eq]
    exact movementMass_nonnegative parents
  exact (Fraction.Order.Field.divide_le_self
    (Fraction.Order.Field.div_pos_direct request.target_positive (by decide)).le
    (le_add_of_nonneg_left massNonnegative)).trans
    (Fraction.Order.Field.divide_le_self request.target_positive.le (by decide))

end Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest

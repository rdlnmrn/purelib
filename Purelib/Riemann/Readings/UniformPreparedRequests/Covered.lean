module

public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
public import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

/-! # Original patch coverage read from retained primitive requests

The ordered request spine already retains each original patch and its
finish admission. Reading those fields forms the same covered spine;
acquisition readbacks identify that view with the supplied original cover.
No neighborhood, primitive request or observation is acquired by the view.
-/

public section

namespace Purelib.Riemann.Readings

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open UniformPreparedRequests (LocalRequest RequestedParents)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}

namespace UniformPreparedRequests.LocalRequest

/-- The retained neighborhood equation admits the same parent finish in its original patch neighborhood. -/
theorem patch_finishInside {parent : CenteredEdge curve basis} {target : Rational}
    (request : LocalRequest parent count target) :
    (request.patch.neighborhood count).box.Contains (parent.edge.point 1) := by
  rewrite [← request.neighborhood_eq]
  exact request.finishInside

/-- View the whole given primitive under its original patch-neighborhood factory equality.

Only the coupled neighborhood index changes. The actual selected model,
primitive polynomial, reading index and source request stay unchanged.
-/
@[expose] def patchPrimitive {parent : CenteredEdge curve basis} {target : Rational}
    (request : LocalRequest parent count target) :
    Normalization.InverseRootPrimitive.PrimitiveModel (request.patch.neighborhood count) request.request.index
      (PreparedPrimitiveSamples.differentialNumerator basis) :=
  Eq.mp (congrArg (fun neighborhood => Normalization.InverseRootPrimitive.PrimitiveModel neighborhood
    request.request.index (PreparedPrimitiveSamples.differentialNumerator basis)) request.neighborhood_eq)
    request.request.model

/-- Neighborhood-index transport retains the complete actual selected primitive model. -/
theorem patchPrimitive_heq {parent : CenteredEdge curve basis} {target : Rational}
    (request : LocalRequest parent count target) : HEq request.patchPrimitive request.request.model := by
  cases request with
  | mk patch neighborhood same requested inside =>
      cases same
      rfl

/-- The patch-neighborhood view retains the identical original primitive polynomial. -/
theorem patchPrimitive_value {parent : CenteredEdge curve basis} {target : Rational}
    (request : LocalRequest parent count target) :
    request.patchPrimitive.primitive.value = request.request.model.primitive.value := by
  cases request with
  | mk patch neighborhood same requested inside =>
      cases same
      rfl

end UniformPreparedRequests.LocalRequest

namespace UniformPreparedRequests.RequestedParents

/-- Read original patches and their retained endpoint admissions in the same dependent request order.

The exposed body lets the existing PreparedParents family reduce on the
actual retained request spine. Every parent, repeated occurrence and patch
is the original data; this operation performs no acquisition.
-/
@[expose] def covered {target : Rational} : {parents : List (CenteredEdge curve basis)} →
    RequestedParents count target parents → CoveredParents count parents
  | _, .nil => .nil
  | _, .cons request tail => .cons request.patch request.patch_finishInside tail.covered

/-- Ordinary acquisition retains the whole supplied cover, including each original patch and finish witness. -/
theorem acquire_covered : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (target : Rational) → (positive : 0 < target) →
    (proper : AllParentsProper parents) → (acquire covered target positive proper).covered = covered
  | _, .nil, _, _, _ => rfl
  | _, .cons patch inside tail, target, positive, proper => by
      change CoveredParents.cons patch _ (acquire tail target positive proper.2).covered =
        CoveredParents.cons patch inside tail
      exact congrArg (CoveredParents.cons patch inside) (acquire_covered tail target positive proper.2)

end UniformPreparedRequests.RequestedParents

namespace PreparedControlledPrimitiveRequests.ControlledParents

/-- Controlled acquisition retains the entire supplied cover in its original request-patch view. -/
private theorem packaged_acquire_covered : {parents : List (CenteredEdge curve basis)} →
    (covered : CoveredParents count parents) → (target coefficientTarget : Rational) →
    (positive : 0 < target) → (coefficientPositive : 0 < coefficientTarget) →
    (proper : AllParentsProper parents) → (minimum : Nat) →
    (acquire covered target coefficientTarget positive coefficientPositive proper minimum).requests.covered = covered
  | _, .nil, _, _, _, _, _, _ => rfl
  | _, .cons patch inside tail, target, coefficientTarget, positive, coefficientPositive, proper, minimum => by
    change CoveredParents.cons patch _
      (acquire tail target coefficientTarget positive coefficientPositive proper.2 minimum).requests.covered =
        CoveredParents.cons patch inside tail
    exact congrArg (CoveredParents.cons patch inside)
      (packaged_acquire_covered tail target coefficientTarget positive coefficientPositive proper.2 minimum)

/-- Controlled acquisition retains the entire supplied cover in its original request-patch view. -/
theorem acquire_covered {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count parents) (target coefficientTarget : Rational)
    (positive : 0 < target) (coefficientPositive : 0 < coefficientTarget)
    (proper : AllParentsProper parents) (minimum : Nat) :
    (acquire covered target coefficientTarget positive coefficientPositive proper minimum).requests.covered = covered :=
  packaged_acquire_covered covered target coefficientTarget positive coefficientPositive proper minimum

end PreparedControlledPrimitiveRequests.ControlledParents

namespace PreparedPrimitiveRequestBatches.ControlledSumRequest

/-- The transported request cover is the SAME whole cached covering spine under its original parent transport. -/
theorem castParents_covered {target : Rational} {first last : List (CenteredEdge curve basis)}
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest first count target) (same : first = last) :
    (castParents request same).requests.covered = request.requests.covered.castParents same := by
  cases same
  rfl

end PreparedPrimitiveRequestBatches.ControlledSumRequest

namespace PreparedControlledPrimitiveRequests.ControlledSumRequest

/-- The controlled sum's actual request-patch view is the original supplied finite cover. -/
private theorem packaged_acquire_covered {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count parents) (proper : AllParentsProper parents)
    (target : Rational) (positive : 0 < target) (minimum : Nat) :
    (acquire covered proper target positive minimum).requests.covered = covered := by
  let mass := movementMass parents
  let coefficientTarget := (target / 2) / (mass + 1)
  have coefficientPositive : 0 < coefficientTarget := Data.Rat.Fraction.Order.Field.div_pos_direct
    (Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
    (Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (movementMass_nonnegative parents) (by decide +kernel))
  change (PreparedControlledPrimitiveRequests.ControlledParents.acquire covered
    (Aggregate.perTerm target parents.length) coefficientTarget
    (Aggregate.perTerm_positive positive parents.length) coefficientPositive proper minimum).requests.covered = covered
  exact PreparedControlledPrimitiveRequests.ControlledParents.acquire_covered covered
    (Aggregate.perTerm target parents.length) coefficientTarget
    (Aggregate.perTerm_positive positive parents.length) coefficientPositive proper minimum

/-- The controlled sum's actual request-patch view is the original supplied finite cover. -/
theorem acquire_covered {parents : List (CenteredEdge curve basis)}
    (covered : CoveredParents count parents) (proper : AllParentsProper parents)
    (target : Rational) (positive : 0 < target) (minimum : Nat) :
    (acquire covered proper target positive minimum).requests.covered = covered :=
  packaged_acquire_covered covered proper target positive minimum

/-- The retained mass-based coefficient target is positive by its original target equation. -/
theorem coefficientTarget_positive {parents : List (CenteredEdge curve basis)} {target : Rational}
    (request : ControlledSumRequest parents count target) : 0 < request.coefficientTarget := by
  have massNonnegative : 0 ≤ request.mass := by
    rewrite [request.mass_eq]
    exact movementMass_nonnegative parents
  rewrite [request.coefficientTarget_eq]
  exact Data.Rat.Fraction.Order.Field.div_pos_direct
    (Data.Rat.Fraction.Order.Field.div_pos_direct request.target_positive (by decide +kernel))
    (Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct massNonnegative (by decide +kernel))

/-- The same retained coefficient target pays its original count-weighted movement mass within half the target. -/
theorem mass_mul_coefficientTarget_le {parents : List (CenteredEdge curve basis)} {target : Rational}
    (request : ControlledSumRequest parents count target) :
    movementMass parents * request.coefficientTarget ≤ target / 2 := by
  have massNonnegative : 0 ≤ request.mass := by
    rewrite [request.mass_eq]
    exact movementMass_nonnegative parents
  have enlarged : request.mass ≤ request.mass + 1 := by
    have shifted := Data.Rat.Fraction.Order.Arithmetic.add_le_add_right_direct
      (by decide +kernel : (0 : Rational) ≤ 1) request.mass
    exact (show request.mass = 0 + request.mass by ring1).trans_le (shifted.trans_eq (by ring1))
  have scaled := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    enlarged request.coefficientTarget_positive.le
  have denominatorPositive : 0 < request.mass + 1 :=
    Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct massNonnegative (by decide +kernel)
  have paid : (request.mass + 1) * request.coefficientTarget = target / 2 := by
    rewrite [request.coefficientTarget_eq, Data.Rat.Fraction.Field.mul_comm]
    exact Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  rewrite [← request.mass_eq]
  exact scaled.trans_eq paid

end PreparedControlledPrimitiveRequests.ControlledSumRequest

end Purelib.Riemann.Readings

end

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Seam.Trace
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest

/-! # Whole old quarter observations across the same actual seam endpoint cast

The original full trace equation and original point/Owner identities reverse
only the literal seam cast. The complete old observation spine and every
stationary occurrence survive together. The unchanged paid quarter receipt
then supplies the actual Block and physical Segment descent.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Seam.Receipt

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

variable {site : Fin 2} {parameter : Canonical} {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {left : Transport.Leg site parameter leftQuarter} {right : Transport.Leg site parameter rightQuarter}
variable {current : Endpoint} {reading : ReadingAt left.actual current}
variable {originalOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) current}
variable {original : Steps.Quarter left.actual left.regular current reading originalOwner}
variable {sourceOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) current}
variable {agreement : InitialAgreement current reading sourceOwner}
variable {previous : Quarter original sourceOwner agreement}
variable {previousInitial : current = UniformPrimitiveMesh.firstEndpoint}
variable {nextCurrent : Endpoint} {nextReading : ReadingAt right.actual nextCurrent}
variable {nextInitial : nextCurrent = UniformPrimitiveMesh.firstEndpoint}
variable {directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0}
variable {stored : Transport.Seam left right}
variable (receipt : Receipt (left := left) (right := right)
  previous previousInitial nextReading nextInitial directions stored)

variable {expression : Expression (Paths.polynomial parameter)} {accuracy : AccuracyRequest}

/-- View the SAME old seam-index spine at the original trace constructor's exact whole-path index. -/
@[macro_inline] private def aligned
    (observed : Primitive.Spine expression accuracy receipt.trace) :
    Primitive.Spine expression accuracy
      (OwnerPath.castEndpoints rfl
        (point_eq (left := left) previous previousInitial nextInitial directions) HEq.rfl receipt.owner_heq.symm
          previous.receipt.trace) :=
  Primitive.Spine.castPath receipt.trace_eq observed

/-- Reverse only the exact original seam endpoint/Owner transport of the complete SAME old quarter observation cache. -/
def quarterSpine (observed : Primitive.Spine expression accuracy receipt.trace) :
    Primitive.Spine expression accuracy previous.receipt.trace :=
  Primitive.Spine.uncastEndpoints rfl
    (point_eq (left := left) previous previousInitial nextInitial directions) HEq.rfl receipt.owner_heq.symm
      (aligned receipt observed)

/-- The full original old spine, all actual states and every stationary comparison survive seam reversal together. -/
theorem quarterSpine_heq (observed : Primitive.Spine expression accuracy receipt.trace) :
    HEq (receipt.quarterSpine observed) observed := by
  unfold quarterSpine
  exact (Primitive.Spine.uncastEndpoints_heq _ _ _ _ (aligned receipt observed)).trans
    (Primitive.Spine.castPath_heq receipt.trace_eq observed)

/-- The exact same old seam-index source observation keeps its original selected value. -/
theorem quarterSpine_first_value (observed : Primitive.Spine expression accuracy receipt.trace) :
    (receipt.quarterSpine observed).first.value = observed.first.value := by
  unfold quarterSpine
  exact (Primitive.Spine.uncastEndpoints_first_value _ _ _ _ (aligned receipt observed)).trans
    (Primitive.Spine.castPath_first_value receipt.trace_eq observed)

/-- The actual returned observation retains its selected value across the original seam Owner-index transport. -/
theorem quarterSpine_last_value (observed : Primitive.Spine expression accuracy receipt.trace) :
    (receipt.quarterSpine observed).last.value = observed.last.value := by
  unfold quarterSpine
  exact (Primitive.Spine.uncastEndpoints_last_value _ _ _ _ (aligned receipt observed)).trans
    (Primitive.Spine.castPath_last_value receipt.trace_eq observed)

/-- Descend the SAME complete old seam spine through its unchanged actual paid quarter and all physical Segments. -/
def quarterViews (observed : Primitive.Spine expression accuracy receipt.trace) :
    Quarter.Observations previous (receipt.quarterSpine observed) :=
  Quarter.Observations.build previous (receipt.quarterSpine observed)

end Steps.Acquisition.Quarter.Seam.Receipt

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

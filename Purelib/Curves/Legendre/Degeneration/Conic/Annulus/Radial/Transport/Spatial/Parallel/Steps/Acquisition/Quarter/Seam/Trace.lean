module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Seam
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Trace
import Purelib.Riemann.Paths.OwnerTracePath

/-! # The identical paid trace across an exact quarter seam

Only the previous actual paid path's final point and Owner index change.
The original castEndpoints operation consumes the derived geometric point
identity and the seam's whole-Owner HEq certificate. Its original ordered
links and vertices remain unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Seam.Receipt

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

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

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

/-- Transport only the identical previous paid trace's exact final endpoint and whole actual Owner across this seam. -/
def trace : OwnerPath (Paths.polynomial parameter)
    (coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) current.parameter) sourceOwner
    (coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) nextCurrent.parameter) receipt.owner :=
  Transport.Seam.Receipt.trace (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored)
    receipt previous.receipt.trace

attribute [local irreducible] coordinate

/-- The whole actual seam trace is its original exact endpoint/Owner transport of the SAME retained paid quarter. -/
theorem trace_eq : receipt.trace =
    @OwnerPath.castEndpoints (Paths.polynomial parameter)
      (coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) current.parameter)
      (coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl)
        (finalTarget current previous.originalQuarter.cache.val).parameter)
      (coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) current.parameter)
      (coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) nextCurrent.parameter)
      sourceOwner previous.receipt.finishOwner sourceOwner receipt.owner rfl
      (point_eq (left := left) previous previousInitial nextInitial directions) HEq.rfl receipt.owner_heq.symm
      previous.receipt.trace := by
  unfold trace
  exact Transport.Seam.Receipt.trace_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored)
    receipt previous.receipt.trace

/-- Geometric seam transport retains the exact original ordered vertices of the same actual previous paid trace. -/
theorem trace_vertices : receipt.trace.vertices = previous.receipt.trace.vertices :=
  Transport.Seam.Receipt.trace_vertices (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored)
    receipt previous.receipt.trace

/-- The old entry is exactly the same shared seam operation on the literal original paid Quarter trace. -/
theorem trace_shared : receipt.trace = Transport.Seam.Receipt.trace (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored)
    receipt previous.receipt.trace := by
  unfold trace
  rfl

end Steps.Acquisition.Quarter.Seam.Receipt

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

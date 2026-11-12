module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Receipt
public import Purelib.Riemann.Paths.OwnerTracePath

/-! # Exact endpoint transport of the SAME actual paid path across a signed seam

The supplied OwnerPath is the complete retained paid realization. Only
its final physical coordinate and Owner index are changed by the original
time/direction certificate and the same retained handoff's whole Owner HEq.
Every stationary/moving occurrence and original root cache remains intact.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

namespace Seam.Receipt

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {site : Fin 2} {parameter : Canonical} {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {left : Leg site parameter leftQuarter} {right : Leg site parameter rightQuarter}
variable {finishTime sourceTime : Fraction.Rational}
variable {finishInside : FixedRootBoxPath.Inside finishTime} {sourceInside : FixedRootBoxPath.Inside sourceTime}
variable {finishReading : Reading left.actual finishTime finishInside}
variable {sourceReading : Reading right.actual sourceTime sourceInside}
variable {finishOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) finishTime))}
variable {previousAgreement : NamedEquivalent (ownerRootName finishOwner.parameterNonzero finishOwner)
  finishReading.lift.value.name}
variable {atFinish : finishTime = 1} {atSource : sourceTime = 0}
variable {directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0}
variable {stored : Seam left right}
variable (receipt : Receipt (left := left) (right := right)
  finishReading sourceReading finishOwner previousAgreement atFinish atSource directions stored)
variable {start : Canonical} {sourceOwner : Owner ((Paths.polynomial parameter).eval start)}
variable (path : OwnerPath (Paths.polynomial parameter) start sourceOwner
  (Spatial.coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) finishTime) finishOwner)

attribute [local irreducible] Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName
attribute [local irreducible] CertifiedSquareRoot.rawRoot

/-- Transport the SAME actual paid path's final physical point and complete original Owner across this exact seam. -/
def trace : OwnerPath (Paths.polynomial parameter) start sourceOwner
    (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime) receipt.owner :=
  OwnerPath.castEndpoints rfl
    (Seam.point_eq (site := site) (parameter := parameter)
      (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions)
    HEq.rfl receipt.owner_heq.symm path

/-- The complete seam trace is exactly its original endpoint/Owner transport of this SAME supplied paid path. -/
theorem trace_eq : receipt.trace path =
    @OwnerPath.castEndpoints (Paths.polynomial parameter)
      start (Spatial.coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) finishTime)
      start (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)
      sourceOwner finishOwner sourceOwner receipt.owner rfl
      (Seam.point_eq (site := site) (parameter := parameter)
        (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions)
      HEq.rfl receipt.owner_heq.symm path := by
  unfold trace
  rfl

/-- Exact seam transport retains all ordered signed vertices of the SAME complete actual paid path. -/
theorem trace_vertices : (receipt.trace path).vertices = path.vertices :=
  OwnerPath.castEndpoints_vertices rfl
    (Seam.point_eq (site := site) (parameter := parameter)
      (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions)
    HEq.rfl receipt.owner_heq.symm path

end Seam.Receipt

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

end

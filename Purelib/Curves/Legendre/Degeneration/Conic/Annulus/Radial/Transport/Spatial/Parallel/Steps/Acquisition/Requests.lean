module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation.Spine
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Original prepared-request counts of the same actual paid circuit

Every count follows the SAME original target list, paid Block and retained
physical acquisition spine. The actual subdivision request lengths are
read before source preparation or primitive observation. No geometry, path,
Owner or acquisition is reconstructed to obtain these finite counts.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
  (widthRequest)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Steps.Acquisition

namespace Spine

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site}

/-- Read the exact original prepared moving-request count across all literal physical Segments of these SAME paid
Blocks. -/
@[expose] def requestCount : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) → Acquisition original sourceOwner agreement → Nat
  | [] => fun _ _ _ _ _ _ _ => 0
  | target :: targets => fun _ _ _ original sourceOwner _ paid =>
      CoveredTracedPath.Acquisition.Spine.requestCount
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine +
      requestCount targets target original.nextReading original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail
termination_by structural targets => targets

end Spine

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site}
variable {targets : List Endpoint} {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {original : Steps actual regular current reading originalOwner targets}
variable {agreement : InitialAgreement current reading sourceOwner}

/-- Read the finite actual source-error term count without constructing an observation or source preparation. -/
@[expose] def requestCount (paid : Acquisition original sourceOwner agreement) : Nat :=
  Spine.requestCount targets current reading originalOwner original sourceOwner agreement paid

namespace Quarter

variable {original : Steps.Quarter actual regular current reading originalOwner}
variable (quarter : Quarter original sourceOwner agreement)

/-- Count the SAME original moving requests in this actual whole paid quarter's retained opaque target-list
execution. -/
@[expose] def requestCount : Nat := quarter.receipt.requestCount

end Quarter

end Steps.Acquisition

namespace Steps.Acquisition.Quarter.Circuit.Execution

open Purelib.Riemann.Meshes

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
variable (execution : Execution initial secondOriginal thirdOriginal fourthOriginal)

/-- Count every actual prepared moving request of the SAME four retained paid quarters before any source observation. -/
@[expose] def requestCount : Nat := execution.first.requestCount +
  (execution.second.paid.requestCount + (execution.third.paid.requestCount + execution.fourth.paid.requestCount))

end Steps.Acquisition.Quarter.Circuit.Execution

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

module

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block

/- The complete former Block.build body is retained only for this private
   all-input kernel comparison. import permits the original unexposed
   build body; no production constructor or arithmetic loop is duplicated. -/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site}
variable {current target : Endpoint} {reading : ReadingAt actual current}
variable (queried : { retained : ReadingAt actual target // QueryCache actual target retained })
variable {payment : (target.parameter - current.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable (geometry : Geometry reading queried.val regular payment)
variable (sourceOwner : OwnerAt site parameter unitQuarter positive current)
variable (sourceAgreement : InitialAgreement current reading sourceOwner)

namespace Block

variable (block : Block queried geometry sourceOwner sourceAgreement)

open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)

variable {degreeBound : Nat} {ambient : Box}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {firstAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter positive current.parameter)).Refines ambient}
variable {lastAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter positive target.parameter)).Refines ambient}
variable (source : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter positive current.parameter) firstAmbient)
variable (targetLines : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter positive target.parameter) lastAmbient)
variable {grid : ClearGrid (Paths.polynomial parameter) ambient}
variable {sourceOn : FromStates.ContainsVertex grid source.point}
variable {targetOn : FromStates.ContainsVertex grid targetLines.point}

/-- Consume the same supplied Owner and relation through the original public three-cache builder. -/
private def suppliedStart
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) ⊕
      WindingOneLoop (Paths.polynomial parameter) source.point)
    (sourceInside : (box site parameter unitQuarter current.parameter regular).Contains source.point)
    (targetInside : (box site parameter unitQuarter current.parameter regular).Contains targetLines.point)
    (walk : {value : Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn})
    (entry : ClearBoxPaths.Route (Paths.polynomial parameter)
      (box site parameter unitQuarter current.parameter regular)
      (coordinate site parameter 2 unitQuarter positive current.parameter) source.point)
    (returned : ClearBoxPaths.Route (Paths.polynomial parameter)
      (box site parameter unitQuarter current.parameter regular) targetLines.point
      (coordinate site parameter 2 unitQuarter positive target.parameter))
    (supplied : Start sourceOwner) :=
  block.prepareDetour source targetLines reference sourceInside targetInside walk entry returned (some supplied)

end Block

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

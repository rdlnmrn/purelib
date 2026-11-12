module

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Paths.PreparedPathWinding
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block

/- The complete former Block.build body is retained only for this private
   all-input kernel comparison. import all permits the original unexposed
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

/-- The complete original paid block factory, retained only for kernel agreement. -/
private def formerBuild : Block queried geometry sourceOwner sourceAgreement :=
  let anchor := Parameter.Anchor.build reading.lift regular actual.data.bound
  let budgets := Factors.Budgets.build (source := reading) anchor
  let factors := Factors.Route.build budgets geometry
  let paid := Factors.Route.Acquisition.build factors sourceOwner
  let initial := Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement
  let compared := Comparison.Initial.Result.build (geometry := geometry) initial paid
  let endpoint := Comparison.Initial.Result.Endpoint.build (geometry := geometry) initial compared
  let following := endpoint.finish.symm
  ofCompleted queried geometry sourceOwner sourceAgreement
    ⟨anchor, by unfold AnchorCache; rfl⟩ ⟨budgets, by unfold BudgetsCache; rfl⟩
    ⟨factors, by unfold FactorsCache; rfl⟩ ⟨paid, by unfold PaidCache; rfl⟩
    ⟨compared, by unfold ComparisonCache; rfl⟩ ⟨endpoint, by unfold EndpointCache; rfl⟩ ⟨following, rfl⟩

/-- Every original input keeps the complete former paid Block construction. -/
private theorem whole_former_build :
    formerBuild queried geometry sourceOwner sourceAgreement =
      build queried geometry sourceOwner sourceAgreement := by
  unfold formerBuild build
  rfl

variable {queried : { retained : ReadingAt actual target // QueryCache actual target retained }}
variable {geometry : Geometry reading queried.val regular payment}
variable {sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {sourceAgreement : InitialAgreement current reading sourceOwner}
variable (block : Block queried geometry sourceOwner sourceAgreement)

section Detour

open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths
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

/-- The complete former source-reference endpoint comparison, private for kernel agreement. -/
private def formerDetourEquivalent
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter))
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
    (first : CoveredTracedPath entry.path sourceOwner)
    (middle : CoveredTracedPath
      (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path first.traced.finishOwner)
    (last : CoveredTracedPath returned.path middle.traced.finishOwner) :
    NamedEquivalent (ownerName last.traced.finishOwner) (ownerName block.finishOwner) := by
  let physical := block.paid.covered.traced
  let joined := first.traced.trace.get.append (middle.traced.trace.get.append last.traced.trace.get)
  have degreePositive : 0 < (Paths.polynomial parameter).natDegree := by
    rewrite [Paths.polynomial_natDegree]
    decide
  have initialInside : (box site parameter unitQuarter current.parameter regular).Contains
      (coordinate site parameter 2 unitQuarter positive current.parameter) :=
    source_inside (positive := positive) regular
  have firstWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive entry initialInside
  have lastWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive returned targetInside
  have oldWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive geometry.route
    initialInside
  have movedWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive
    (geometry.detour elimination clearances source targetLines) sourceInside
  have middleWinding : PreparedPathWinding.ClearPath.rawWinding
      (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path =
      PreparedPathWinding.ClearPath.rawWinding
        (geometry.detour elimination clearances source targetLines).path := by
    rewrite [Winding.Walk.castEndpoints_winding, walk.property]
    exact geometry.detourWalk_winding elimination clearances source targetLines grid sourceOn targetOn
  have winding : PreparedPathWinding.ClearPath.rawWinding geometry.route.path =
      chainRaw (Paths.polynomial parameter)
        (coordinate site parameter 2 unitQuarter positive current.parameter) joined.vertices := by
    dsimp only [joined]
    rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.append_winding,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original first.traced,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original middle.traced,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original last.traced,
      middleWinding, firstWinding, movedWinding, lastWinding, oldWinding]
    omega0
  let frame := OwnerFrame.build block.finishOwner.parameterNonzero
  exact (ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections reference geometry.route.within
    physical joined frame (frame.select physical.finishOwner) (frame.select last.traced.finishOwner) winding).symm

/-- Both genuine reference bases retain the same complete endpoint comparison procedure. -/
private theorem reference_results_agree
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter))
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
    (first : CoveredTracedPath entry.path sourceOwner)
    (middle : CoveredTracedPath
      (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path first.traced.finishOwner)
    (last : CoveredTracedPath returned.path middle.traced.finishOwner)
    (movedReference : WindingOneLoop (Paths.polynomial parameter) source.point) :
    block.detourEquivalent source targetLines (.inl reference) sourceInside targetInside walk
      entry returned first middle last (NamedEquivalent.refl _) =
      block.detourEquivalent source targetLines (.inr movedReference) sourceInside targetInside walk
        entry returned first middle last (NamedEquivalent.refl _) := by
  unfold detourEquivalent ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections
  rfl

/-- The old source-reference branch retains the complete former endpoint comparison. -/
private theorem whole_former_detour_equivalent
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter))
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
    (first : CoveredTracedPath entry.path sourceOwner)
    (middle : CoveredTracedPath
      (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path first.traced.finishOwner)
    (last : CoveredTracedPath returned.path middle.traced.finishOwner) :
    block.detourEquivalent source targetLines (.inl reference) sourceInside targetInside walk
      entry returned first middle last (NamedEquivalent.refl _) =
      formerDetourEquivalent block source targetLines reference sourceInside targetInside walk
        entry returned first middle last := by
  unfold detourEquivalent formerDetourEquivalent
  rfl

/-- The complete former three-path preparation, private for kernel agreement. -/
private def formerPrepareDetour
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter))
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
      (coordinate site parameter 2 unitQuarter positive target.parameter)) :
    Σ first : {value : CoveredTracedPath entry.path sourceOwner //
      value = CoveredTracedPath.build entry.path entry.within sourceOwner},
    Σ middle : {value : CoveredTracedPath
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path first.val.traced.finishOwner //
      value = CoveredTracedPath.build
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).withinAmbient
        first.val.traced.finishOwner},
    Σ last : {value : CoveredTracedPath returned.path middle.val.traced.finishOwner //
      value = CoveredTracedPath.build returned.path returned.within middle.val.traced.finishOwner},
      NamedEquivalent (ownerName last.val.traced.finishOwner) (ownerName block.finishOwner) :=
  let actualWalk := walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm
  let first := CoveredTracedPath.build entry.path entry.within sourceOwner
  let middle := CoveredTracedPath.build actualWalk.path actualWalk.withinAmbient first.traced.finishOwner
  let last := CoveredTracedPath.build returned.path returned.within middle.traced.finishOwner
  let compared := formerDetourEquivalent block source targetLines reference sourceInside targetInside walk
    entry returned first middle last
  ⟨⟨first, rfl⟩, ⟨middle, rfl⟩, ⟨last, rfl⟩, compared⟩

/-- The old source-reference request retains the complete former three-cache result. -/
private theorem whole_former_prepare_detour
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter))
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
      (coordinate site parameter 2 unitQuarter positive target.parameter)) :
    block.prepareDetour source targetLines (.inl reference) sourceInside targetInside walk entry returned =
      formerPrepareDetour block source targetLines reference sourceInside targetInside walk entry returned := by
  unfold prepareDetour formerPrepareDetour detourEquivalent formerDetourEquivalent
  rfl

end Detour

end Block

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Purelib.Riemann.RootContinuation.RootPathTransport.PathTransport

open Purelib
open scoped Purelib.Data.Nat
open Purelib.Riemann.Paths
open Purelib.Data
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)

variable {polynomial : Dense} {ambient : Box} {start finish : Canonical}
variable {path : ClearPath polynomial ambient start finish}
variable {first : OwnerFrame (polynomial.eval start)} {last : OwnerFrame (polynomial.eval finish)}

/-- The complete original two-row factory, retained only for kernel agreement. -/
private def formerBuild (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient)
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish)) : PathTransport path first
      last :=
  ⟨TransportRow.build path within first last 0, TransportRow.build path within first last 1⟩

/-- The same inputs retain the complete original two-row factory result. -/
private theorem whole_former_build (path : ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish)) :
    build path within first last = formerBuild path within first last := by rfl

/-- The complete original identity record, retained only for kernel agreement. -/
private def formerIdentity (frame : OwnerFrame (polynomial.eval start)) :
    PathTransport (.nil (ambient := ambient) start) frame frame :=
  ⟨⟨TracedPath.build (.nil start) (.nil start) (frame.owners 0), ⟨0, Equivalence.NamedEquivalent.refl _⟩⟩,
    ⟨TracedPath.build (.nil start) (.nil start) (frame.owners 1), ⟨1, Equivalence.NamedEquivalent.refl _⟩⟩⟩

/-- The same original frame retains the complete identity record. -/
private theorem whole_former_identity (frame : OwnerFrame (polynomial.eval start)) :
    identity (ambient := ambient) frame = formerIdentity (ambient := ambient) frame := by rfl

/-- The complete original finite bijection record, retained only for kernel agreement. -/
private def formerBijection {backPath : Polynomial.Geometry.ClearPath polynomial ambient finish start}
    (firstReference : WindingOneLoop polynomial start) (lastReference : WindingOneLoop polynomial finish)
    (forward : PathTransport path first last) (backward : PathTransport backPath last first)
    (cancel : PreparedPathWinding.ClearPath.rawWinding path + PreparedPathWinding.ClearPath.rawWinding backPath = 0) :
    Data.Fin.Bijection 2 2 where
  forward := forward.target
  backward := backward.target
  backward_forward := forward.roundTrip_index firstReference backward cancel
  forward_backward := backward.roundTrip_index lastReference forward (by omega)

/-- Both actual original row caches retain the entire original bijection record. -/
private theorem whole_former_bijection {backPath : ClearPath polynomial ambient finish start}
    (firstReference : WindingOneLoop polynomial start) (lastReference : WindingOneLoop polynomial finish)
    (forward : PathTransport path first last) (backward : PathTransport backPath last first)
    (cancel : Paths.PreparedPathWinding.ClearPath.rawWinding path +
      Paths.PreparedPathWinding.ClearPath.rawWinding backPath = 0) :
    bijection firstReference lastReference forward backward cancel =
      formerBijection firstReference lastReference forward backward cancel := by rfl

end Purelib.Riemann.RootContinuation.RootPathTransport.PathTransport

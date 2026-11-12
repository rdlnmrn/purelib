module

import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Input
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Receipt
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Reading
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath.Primitive
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Data.Int.Arithmetic
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance

/-! # The original paid realization of each actual retained quarter input

The original Steps branch is literally the existing Quarter type and its
existing factory. The numerical branch retains the actual ofLayer result
and its complete factory identity on the same supplied Layer/query caches.
Shared endpoint and trace operations inspect these original realizations;
they introduce neither a substitute owner nor a second four-quarter stack.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Int
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Acquisition → LayerAcquisition
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.RootIsolation.SquareRoot
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection NameSelection)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName

namespace Input.Numerical

variable {radicand : CoefficientPolynomial} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable (input : Input.Numerical (data := data) leg)
variable (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.initial.lowerEndpoint)
variable (agreement : InitialAgreement input.initial.lowerEndpoint input.initial.source sourceOwner)

/-- The exact existing paid Layer type on the retained decomposition, source Owner and complete source witness. -/
@[expose] def Paid :=
  LayerAcquisition leg.regular input.finish input.parts.remaining input.parts.first
    (fun piece member => input.layer.queried_of_factory input.layer_eq input.queried piece
      (input.parts.remaining_member piece member))
    (input.parts.startOwner sourceOwner input.layer_eq)
    (input.parts.startAgreement sourceOwner input.layer_eq input.queried agreement)

/-- The SAME actual numerical paid realization with its whole original ofLayer factory identity. -/
@[expose] def Realization :=
  { paid : Paid input sourceOwner agreement //
    paid = LayerAcquisition.ofLayer (regular := leg.regular) input.parts input.layer_eq input.queried input.finish
      sourceOwner agreement input.enough }

namespace Realization

/-- Execute the existing paid Layer producer once on these SAME original caches and supplied initial Owner. -/
def build : Realization input sourceOwner agreement :=
  let paid := LayerAcquisition.ofLayer (regular := leg.regular) input.parts input.layer_eq input.queried input.finish
    sourceOwner agreement input.enough
  ⟨paid, rfl⟩

variable {input sourceOwner agreement} (retained : Realization input sourceOwner agreement)

/-- Read the actual complete original paid fold without reconstructing any head/tail cache. -/
@[expose] def paid : Paid input sourceOwner agreement := retained.val

/-- The retained fold is exactly its original ofLayer producer on the literal stored parent caches. -/
theorem paid_eq : retained.paid =
    LayerAcquisition.ofLayer (regular := leg.regular) input.parts input.layer_eq input.queried input.finish
    sourceOwner agreement input.enough := retained.property

/-- Read the SAME actual final Owner of the retained numerical paid fold. -/
@[expose] def finishOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl)
    input.initial.upperEndpoint := LayerAcquisition.finishOwner retained.paid

/-- The actual paid finish agrees with the SAME original retained final query's full cubic channel. -/
@[expose] def finishEquivalent : NamedEquivalent
    (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner) input.finish.val.lift.value.name :=
  LayerAcquisition.finishEquivalent retained.paid

/-- Restore only the original initial physical index of the SAME paid trace and complete supplied Owner.

The actual ofLayer trace starts at the retained first piece. Its exact
original start-time law and startOwner HEq reverse that index transport.
All stationary/moving links, root advances and primitive owners remain the
literal trace of the same retained paid realization.
-/
def trace : OwnerPath (Paths.polynomial parameter)
    (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.initial.span.lower) sourceOwner
    (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.initial.span.upper)
      retained.finishOwner :=
  OwnerPath.castEndpoints
    (congrArg (fun time : Fraction.Rational =>
      coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time) (input.parts.start_time input.layer_eq))
    rfl (input.parts.startOwner_heq sourceOwner input.layer_eq) HEq.rfl (LayerAcquisition.trace retained.paid)

/-- The transported numerical trace is the exact original endpoint transport of this SAME retained paid trace. -/
theorem trace_eq : retained.trace = OwnerPath.castEndpoints
    (congrArg (fun time : Fraction.Rational =>
      coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time) (input.parts.start_time input.layer_eq))
    rfl (input.parts.startOwner_heq sourceOwner input.layer_eq) HEq.rfl (LayerAcquisition.trace retained.paid) := by
  unfold trace
  rfl

/-- Exact source-index transport preserves all original ordered signed vertices of the SAME numerical paid trace. -/
theorem trace_vertices : retained.trace.vertices = (LayerAcquisition.trace retained.paid).vertices :=
  OwnerPath.castEndpoints_vertices
    (congrArg (fun time : Fraction.Rational =>
      coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time) (input.parts.start_time input.layer_eq))
    rfl (input.parts.startOwner_heq sourceOwner input.layer_eq) HEq.rfl (LayerAcquisition.trace retained.paid)

end Realization

end Input.Numerical

namespace Input

/-- The retained paid realization is the corresponding existing original producer's actual result type.

The original branch is definitionally the old Quarter, including its whole
original-quarter cache and paid Acquisition receipt. The numerical branch
is its exact original ofLayer factory cache. No geometry, Reading or Owner
is converted to the other branch's execution.
-/
@[expose] def Realization : (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (_agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) → Type 1
  | .inl original => fun sourceOwner agreement => Quarter original.quarter sourceOwner agreement
  | .inr fine => fun sourceOwner agreement => Numerical.Realization (leg := leg) fine.numerical sourceOwner agreement

namespace Realization

/-- Execute the SAME existing paid producer for the retained parent, without attaching a new initial Source. -/
def build : (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) →
      Realization input sourceOwner agreement
  | .inl original => fun sourceOwner agreement => Quarter.build original.quarter sourceOwner agreement
  | .inr fine => fun sourceOwner agreement =>
      Numerical.Realization.build (leg := leg) fine.numerical sourceOwner agreement

/-- Read the actual terminal endpoint from the retained realization's own exact nominal parent cache. -/
@[expose] def finishEndpoint : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    Realization input sourceOwner agreement → Endpoint
  | .inl original, _sourceOwner, _agreement, retained =>
      finalTarget original.current (Quarter.originalQuarter retained).cache.val
  | .inr fine, _sourceOwner, _agreement, _retained => fine.numerical.initial.upperEndpoint

/-- Read the SAME actual terminal Owner of the corresponding retained original paid realization. -/
@[expose] def finishOwner : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
      OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint
  | .inl _original, _sourceOwner, _agreement, retained => Quarter.finishOwner retained
  | .inr _fine, _sourceOwner, _agreement, retained => Numerical.Realization.finishOwner (leg := leg) retained

/-- Read the SAME independent original final Reading retained by the actual producer. -/
@[expose] def finishReading : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) → ReadingAt leg.actual retained.finishEndpoint
  | .inl _original, _sourceOwner, _agreement, retained => Quarter.finishReading retained
  | .inr fine, _sourceOwner, _agreement, _retained => fine.numerical.finish.val

/-- The SAME actual final Owner retains its producer-derived full-cubic agreement with the original final Reading. -/
@[expose] def finishEquivalent : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
      NamedEquivalent (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner)
        retained.finishReading.lift.value.name
  | .inl _original, _sourceOwner, _agreement, retained => Quarter.finishEquivalent retained
  | .inr _fine, _sourceOwner, _agreement, retained =>
      Numerical.Realization.finishEquivalent (leg := leg) retained

/-- Both actual retained producers terminate at chart time one by their own original geometric certificates. -/
theorem finish_time : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) → retained.finishEndpoint.parameter = 1
  | .inl original, _sourceOwner, _agreement, retained =>
      congrArg Endpoint.parameter (Quarter.finalEndpoint_eq retained original.initial)
  | .inr fine, _sourceOwner, _agreement, _retained => fine.numerical.atFinish

/-- Read the complete same actual paid trace, with only its producer's exact initial-index transport where needed. -/
@[expose] def trace : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
      OwnerPath (Paths.polynomial parameter)
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter) sourceOwner
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)
          retained.finishOwner
  | .inl _original, _sourceOwner, _agreement, retained => (Quarter.receipt retained).trace
  | .inr _fine, _sourceOwner, _agreement, retained => Numerical.Realization.trace (leg := leg) retained

/-- Count the actual retained paid Blocks of this SAME original producer. -/
@[expose] def blockCount : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    Realization input sourceOwner agreement → Nat
  | .inl _original, _sourceOwner, _agreement, retained => (Quarter.receipt retained).blockCount
  | .inr _fine, _sourceOwner, _agreement, retained =>
      LayerAcquisition.blockCount (Numerical.Realization.paid (leg := leg) retained)

variable {input : Input leg}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
variable {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
variable (retained : Realization input sourceOwner agreement)
variable {nextQuarter : UnitCircuitQuarter} {nextLeg : Transport.Leg site parameter nextQuarter}

/-- Construct the SAME original full-cubic handoff from actual retained paid endpoints of either geometry input. -/
def seam (next : Input nextLeg)
    (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg) :
    Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored :=
  Transport.Seam.Receipt.build (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
    retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored

/-- The shared handoff is the exact original six-cache factory on the literal retained producer endpoints. -/
theorem seam_eq (next : Input nextLeg)
    (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg) :
    retained.seam next directions stored = Transport.Seam.Receipt.build (left := leg) (right := nextLeg)
      retained.finishReading next.sourceReading retained.finishOwner retained.finishEquivalent
      retained.finish_time next.source_time directions stored := by
  unfold seam
  rfl

variable {current : Endpoint} {reading : ReadingAt leg.actual current}
variable {originalOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) current}
variable {original : Steps.Quarter leg.actual leg.regular current reading originalOwner}
variable {oldSourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) current}
variable {oldAgreement : InitialAgreement current reading oldSourceOwner}

/-- The shared producer on an old Steps input is exactly the original old Quarter factory, with no extra execution. -/
theorem build_ofSteps (initial : current = Riemann.Meshes.UniformPrimitiveMesh.firstEndpoint) :
    build (Input.ofSteps original initial) oldSourceOwner oldAgreement =
      Quarter.build original oldSourceOwner oldAgreement := by
  unfold build
  rfl

/-- The shared trace on an old Steps input is literally the original complete paid trace. -/
theorem trace_ofSteps (initial : current = Riemann.Meshes.UniformPrimitiveMesh.firstEndpoint)
    (old : Quarter original oldSourceOwner oldAgreement) :
    trace (input := Input.ofSteps original initial) old = old.receipt.trace := by
  unfold trace
  rfl

/-- Read the literal endpoint occurrences from the corresponding original paid spine.

The fine branch follows its SAME numerical Pieces and complete final query;
the original branch follows its SAME stored Quarter target cache. Neither
branch constructs or coerces a realization of the other kind.
-/
@[expose] def endpointList : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    Realization input sourceOwner agreement → List Endpoint
  | .inl original, _sourceOwner, _agreement, retained =>
      original.current :: (Quarter.originalQuarter retained).cache.val
  | .inr _fine, _sourceOwner, _agreement, retained => retained.paid.endpointList

/-- The exact shared line bank for this SAME branch's original endpoint list. -/
abbrev Lines {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) :=
  Geometry.Lines.Bank elimination clearances leg.regular leg.actual.data.bound retained.endpointList
    (fun endpoint : Endpoint => coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) endpoint.parameter)
    (fun endpoint => coordinate_inside site parameter 2 unitQuarter (of_decide_eq_true rfl)
      leg.actual.data.lower leg.actual.data.upper leg.actual.data.bound endpoint.parameter)

/-- Read the exact original bounded-occurrence Walk product for this retained input branch.

The old branch retains its actual target cache. The fine branch retains
its literal first/remaining pieces and final supplied query. This view
never converts one branch's realization into the other.
-/
@[expose] def DetourWalks {degreeBound : Nat} : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound) →
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) → Type
  | .inl original, _sourceOwner, _agreement, retained, elimination, grid =>
      Steps.Acquisition.DetourWalks (site := site) (unitQuarter := unitQuarter)
        (positive := of_decide_eq_true rfl) (regular := leg.regular) elimination grid original.current
          (Quarter.originalQuarter retained).cache.val
  | .inr fine, _sourceOwner, _agreement, _retained, elimination, grid =>
      LayerAcquisition.DetourWalks (regular := leg.regular) (finish := fine.numerical.initial.upperEndpoint)
        elimination grid fine.numerical.parts.first fine.numerical.parts.remaining

/-- Retain this SAME paid branch's actual head Walks and aggregate on one supplied grid.

The original branch consumes its stored Steps receipt. The fine branch
consumes its actual paid Piece spine and uses only the original start-time
readback to restore its physical input index. Both use the same shared
line bank without constructing any replacement quarter or acquisition.
-/
def prepareDetourOn {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (lines : Lines retained elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    DetourWalks retained elimination grid ×
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter))
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)) //
      Grid.FromStates.ContainsVertex grid
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter))} :=
  match input, sourceOwner, agreement, retained, lines, onGrid with
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid =>
      Steps.Acquisition.prepareDetourOn elimination clearances retained.receipt lines grid onGrid
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid =>
      let result := LayerAcquisition.prepareDetourOn elimination clearances retained.paid lines grid onGrid
      ⟨result.1, ⟨result.2.val.castEndpoints
          (congrArg (fun time : Fraction.Rational => Geometry.move elimination leg.regular
            (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))
            (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl,
        result.2.property⟩⟩

/-- Read this SAME paid branch's numeric detour on one supplied grid containing its retained moved occurrences.

The original branch consumes its stored Steps receipt. The fine branch
consumes its actual paid Piece spine and uses only the original start-time
readback to restore its physical input index. Both use the same shared
line bank without constructing any replacement quarter or acquisition.
-/
def detourOn {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (lines : Lines retained elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    {_walk : Grid.Walks.Walk grid
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter))
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)) //
      Grid.FromStates.ContainsVertex grid
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter))} :=
  (prepareDetourOn retained elimination clearances lines grid onGrid).2

/-- Construct this SAME realized quarter's numeric detour on its own grid extension using the retained paired lines. -/
def detour {degreeBound : Nat} {input : Input leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
    (retained : Realization input sourceOwner agreement)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (lines : Lines retained elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    let pairs := Geometry.Lines.Bank.pairs
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines
    {_walk : Grid.Walks.Walk (Grid.Extension.extend base (pairs.map Prod.fst) (pairs.map Prod.snd))
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter))
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)) //
      Grid.FromStates.ContainsVertex (Grid.Extension.extend base (pairs.map Prod.fst) (pairs.map Prod.snd))
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter))} :=
  detourOn retained elimination clearances lines _
    (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines base)

end Realization

namespace Numerical.Realization

attribute [local irreducible] NamedEquivalent
attribute [local irreducible]
  Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Decomposition.startOwner

variable {radicand : CoefficientPolynomial} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

/-- Transport the retained source comparison through the existing first-piece name equalities. -/
private def startEquivalent (input : Input.Numerical (data := data) leg)
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.initial.lowerEndpoint)
    (value : Block.Start sourceOwner) :
    NamedEquivalent (ownerName (input.parts.startOwner value.1 input.layer_eq))
      (ownerName (input.parts.startOwner sourceOwner input.layer_eq)) := by
  have actualName := input.parts.startOwner_name value.1 input.layer_eq
  have originalName := input.parts.startOwner_name sourceOwner input.layer_eq
  unfold ownerRootName at actualName originalName
  exact NamedEquivalent.transport actualName.symm originalName.symm value.2

/-- Reindex an actual supplied detour start through the same original first-piece identity.

The optional default remains absent. An actual supplied Owner keeps its
whole track and stored comparison under the existing startOwner transport;
no source query, attachment or comparison procedure is rebuilt here.
-/
def detourStart (input : Input.Numerical (data := data) leg)
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.initial.lowerEndpoint)
    (supplied : Option (Block.Start sourceOwner)) :
    Option (Block.Start (input.parts.startOwner sourceOwner input.layer_eq)) :=
  match supplied with
  | none => none
  | some value => some ⟨input.parts.startOwner value.1 input.layer_eq, startEquivalent input sourceOwner value⟩

/-- The selected optional start is exactly the existing first-piece transport of the same actual Owner. -/
theorem detourStart_owner_eq (input : Input.Numerical (data := data) leg)
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.initial.lowerEndpoint)
    (supplied : Option (Block.Start sourceOwner)) :
    Block.Start.owner (current := input.parts.first.lowerEndpoint)
      (input.parts.startOwner sourceOwner input.layer_eq) (detourStart input sourceOwner supplied) =
      input.parts.startOwner
        (Block.Start.owner (current := input.initial.lowerEndpoint) sourceOwner supplied) input.layer_eq := by
  cases supplied with
  | none => rfl
  | some _ =>
      unfold detourStart Block.Start.owner
      rfl

/-- The transported optional start retains the same entire Owner, including its original track and caches. -/
theorem detourStart_owner_heq (input : Input.Numerical (data := data) leg)
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.initial.lowerEndpoint)
    (supplied : Option (Block.Start sourceOwner)) :
    HEq (Block.Start.owner (current := input.parts.first.lowerEndpoint)
      (input.parts.startOwner sourceOwner input.layer_eq) (detourStart input sourceOwner supplied))
      (Block.Start.owner (current := input.initial.lowerEndpoint) sourceOwner supplied) :=
  (heq_of_eq (detourStart_owner_eq input sourceOwner supplied)).trans
    (input.parts.startOwner_heq
      (Block.Start.owner (current := input.initial.lowerEndpoint) sourceOwner supplied) input.layer_eq)

end Numerical.Realization

namespace Realization

variable {input : Input leg}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
variable {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}

section SignedDetour

variable {degreeBound : Nat}
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (grid : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))

/-- The same original branch's literal numeric head bank with its complete factory identity. -/
@[expose] def DetourWalkCache
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :=
  {value // value = (prepareDetourOn retained elimination clearances lines grid onGrid).1}

namespace DetourWalkCache

/-- Read the same original Steps branch's stored head bank and factory equation. -/
def steps {original : Input.Original leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) original.current}
    {agreement : InitialAgreement original.current original.reading sourceOwner}
    (retained : Quarter original.quarter sourceOwner agreement)
    (lines : Lines (input := .inl original) retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid (input := .inl original) retained lines onGrid) :
    Steps.Acquisition.DetourWalkCache elimination clearances grid retained.receipt lines onGrid :=
  ⟨cached.val, cached.property.trans (by unfold prepareDetourOn; rfl)⟩

/-- Read the same fine branch's stored head bank and its original paid Layer factory equation. -/
def numerical {fine : Input.Fine leg}
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) fine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement fine.numerical.initial.lowerEndpoint fine.numerical.initial.source sourceOwner}
    (retained : Numerical.Realization fine.numerical sourceOwner agreement)
    (lines : Lines (input := .inr fine) retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid (input := .inr fine) retained lines onGrid) :
    LayerAcquisition.DetourWalkCache elimination clearances grid retained.paid lines onGrid :=
  ⟨cached.val, cached.property.trans (by unfold prepareDetourOn; rfl)⟩

end DetourWalkCache

attribute [local irreducible] DetourWalkCache.steps DetourWalkCache.numerical

/-- The actual retained branch's signed detour spine on its same numeric heads and supplied initial Owner.

The two cases retain their original paid producers. The fine case only
reindexes the same supplied initial Owner through its existing first-piece
identity; no old Steps realization is manufactured for a fine Layer.
-/
@[expose] def DetourSpine
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point) :
    (input : Input leg) →
    (sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint) →
    (agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner) →
    (retained : Realization input sourceOwner agreement) →
    (lines : Lines retained elimination clearances) →
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) →
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid) →
    (supplied : Option (Block.Start sourceOwner)) → Type
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied =>
      Acquisition.DetourSpine elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied =>
      LayerAcquisition.DetourSpine elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied)

/-- Prepare the actual branch's signed cofold without repeating numeric heads, old Blocks or source acquisition. -/
def prepareDetour
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner) := none) :
    DetourSpine elimination clearances grid reference input sourceOwner agreement retained lines onGrid
      cached supplied :=
  match input, sourceOwner, agreement, retained, lines, onGrid, cached, supplied with
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied =>
      Steps.Acquisition.prepareDetour elimination clearances grid reference
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied =>
      LayerAcquisition.prepareDetour elimination clearances grid reference
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied)

end SignedDetour

end Realization

end Input

end Steps.Acquisition.Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

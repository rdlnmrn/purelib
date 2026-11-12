module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Preparation

import Purelib.RootIsolation.SquareRoot.Owner.Transport

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Input
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Receipt
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

/-! # Readback and seam comparisons for retained signed-quarter detour spines -/

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

namespace Input

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

namespace DetourSpine

open Steps.Acquisition.DetourSpine (LastReturn)

/-- Read the actual final Owner from the same original branch's signed cofold. -/
def finishOwner
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      Acquisition.DetourSpine.finishOwner elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      LayerAcquisition.DetourSpine.finishOwner elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared

/-- Read the actual last middle and retained return of the original paid quarter branch.

Both branches retain their old source, numerical bank and signed spine.
The original quarter's nonempty target proof is derived internally from
its stored depth-seven count; the fine branch keeps its actual last piece.
-/
@[expose] def lastReturn
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    LastReturn (site := site) (parameter := parameter)
      (unitQuarter := unitQuarter) (positive := of_decide_eq_true rfl) (regular := leg.regular)
      (finish := retained.finishEndpoint) elimination
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      Acquisition.DetourSpine.lastReturn elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
        (Quarter.targets_nonempty retained)
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      LayerAcquisition.DetourSpine.lastReturn elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared

/-- The retained final return keeps the entire actual shared signed-quarter finish Owner. -/
theorem lastReturn_finishOwner
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    (lastReturn elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared).2.2.1 =
      finishOwner elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared := by
  intro input
  cases input with
  | inl original =>
    intro sourceOwner agreement retained lines onGrid cached supplied prepared
    exact Acquisition.DetourSpine.lastReturn_finishOwner elimination clearances grid reference
      _ _ _ _ _ _ _ retained.receipt lines onGrid
      (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
      (Quarter.targets_nonempty retained)
  | inr fine =>
    intro sourceOwner agreement retained lines onGrid cached supplied prepared
    exact LayerAcquisition.DetourSpine.lastReturn_finishOwner elimination clearances grid reference
      _ _ _ _ _ retained.paid lines onGrid
      (cached.numerical elimination clearances grid retained lines onGrid)
      (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared

/-- Either retained quarter realization derives its actual final return's sharp-square winding from intrinsic bounds.

The original Steps branch supplies its own nonempty target certificate;
the fine branch uses its saved final numerical piece. The original Leg's
parameter bound constructs the target-square clearance internally. Both
branches retain their literal return path and original endpoint owners.
-/
theorem lastReturn_winding
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    let returned := lastReturn elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared
    chainRaw (Paths.polynomial parameter) returned.1.val returned.2.2.2.vertices =
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter retained.finishEndpoint.parameter leg.regular)
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter) -
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter retained.finishEndpoint.parameter leg.regular) returned.1.val := by
  intro input
  cases input with
  | inl original =>
    intro sourceOwner agreement retained lines onGrid cached supplied prepared
    let clearance := Radial.Clearance.clearance site parameter
      (Waist.direction unitQuarter retained.finishEndpoint.parameter) leg.regular leg.actual.data.bound
    exact Acquisition.DetourSpine.lastReturn_winding elimination clearances grid reference
      _ _ _ _ _ _ _ retained.receipt lines onGrid
      (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
      (Quarter.targets_nonempty retained) clearance
  | inr fine =>
    intro sourceOwner agreement retained lines onGrid cached supplied prepared
    let clearance := Radial.Clearance.clearance site parameter
      (Waist.direction unitQuarter retained.finishEndpoint.parameter) leg.regular leg.actual.data.bound
    exact LayerAcquisition.DetourSpine.lastReturn_winding elimination clearances grid reference
      _ _ _ _ _ retained.paid lines onGrid
      (cached.numerical elimination clearances grid retained lines onGrid)
      (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared clearance

/-- Read the stored signed endpoint comparison to the same original quarter's final Owner. -/
def equivalent
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    NamedEquivalent (ownerName (finishOwner elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied prepared)) (ownerName retained.finishOwner)
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      Acquisition.DetourSpine.equivalent elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      LayerAcquisition.DetourSpine.equivalent elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared

/-- Read the same retained signed trace, transporting only the original fine-piece start index. -/
def trace
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)
      (Block.Start.owner sourceOwner supplied)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)
      (finishOwner elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared)
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      (Acquisition.DetourSpine.blocks elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied prepared).trace
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      OwnerPath.castEndpoints
        (congrArg (fun time : Fraction.Rational =>
          coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl
        (Numerical.Realization.detourStart_owner_heq fine.numerical _sourceOwner supplied) HEq.rfl
        (LayerAcquisition.DetourSpine.blocks elimination clearances grid reference _ _ _ _ _
          retained.paid lines onGrid
          (cached.numerical elimination clearances grid retained lines onGrid)
          (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared).trace

variable {nextQuarter : UnitCircuitQuarter} {nextLeg : Transport.Leg site parameter nextQuarter}

/-- Transport the literal signed finish through the same original retained seam.

The original seam's Owner and cached name equality remain comparison
inputs. Only its existing geometric cast is applied to the actual new
finish; the same retained endpoint comparison supplies the following start.
No seam, Reading, query or root preparation is rebuilt.
-/
def nextStart
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :
    Block.Start seam.owner := by
  let actual := finishOwner elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  have actualName := Transport.Seam.castOwner_name (site := site) (parameter := parameter)
    (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
    retained.finish_time next.source_time directions actual
  have originalName := seam.name_eq
  unfold ownerRootName at actualName originalName
  exact ⟨Transport.Seam.castOwner (site := site) (parameter := parameter)
      (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
      retained.finish_time next.source_time directions actual,
    NamedEquivalent.transport actualName.symm originalName.symm
      (equivalent elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared)⟩

/-- The following signed start is exactly the existing seam cast of the literal actual finish Owner. -/
theorem nextStart_owner_eq
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :
    (nextStart elimination clearances grid reference retained lines onGrid cached supplied
      prepared next directions stored seam).1 =
      Transport.Seam.castOwner (site := site) (parameter := parameter)
        (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
        retained.finish_time next.source_time directions
        (finishOwner elimination clearances grid reference input sourceOwner agreement
          retained lines onGrid cached supplied prepared) := (rfl)

/-- The following signed start retains the entire actual preceding finish Owner under that same geometric cast. -/
theorem nextStart_owner_heq
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :
    HEq (nextStart elimination clearances grid reference retained lines onGrid cached supplied
      prepared next directions stored seam).1
      (finishOwner elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared) :=
  (heq_of_eq (nextStart_owner_eq elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam)).trans
    (Transport.Seam.castOwner_heq (site := site) (parameter := parameter)
      (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
      retained.finish_time next.source_time directions
      (finishOwner elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared))

/-- The following start is the original seam transport of this literal retained terminal return Owner.

The exact old seam, both complete quarter inputs and the original
geometric transport remain unchanged. The equality only substitutes the
proved cached returned endpoint; it does not identify middle paths or
cancel connector values.
-/
theorem lastReturn_nextStart
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :
    (nextStart elimination clearances grid reference retained lines onGrid cached supplied
      prepared next directions stored seam).1 =
      Transport.Seam.castOwner (site := site) (parameter := parameter)
        (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
        retained.finish_time next.source_time directions
        (lastReturn elimination clearances grid reference input sourceOwner agreement
          retained lines onGrid cached supplied prepared).2.2.1 :=
  (nextStart_owner_eq elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam).trans
    (congrArg (fun owner => Transport.Seam.castOwner (site := site) (parameter := parameter)
      (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
      retained.finish_time next.source_time directions owner)
      (lastReturn_finishOwner elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared).symm)

/-- Retain the actual terminal return across the same original seam at the next quarter's source endpoint.

The old returned middle owner, moved point and complete saved path are
reused. The original seam supplies exact coordinate equality and its whole
owner transport; the existing `nextStart` is the actual terminal owner.
The return view derives its moved-point identity without another search.
-/
@[expose] def nextReturn
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :
    LastReturn (site := site) (parameter := parameter) (unitQuarter := nextQuarter)
      (positive := of_decide_eq_true rfl) (regular := nextLeg.regular) (finish := next.sourceEndpoint) elimination := by
  let returned := lastReturn elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  let following := nextStart elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  have pointEq := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
    retained.finish_time next.source_time directions
  have ownerEq : HEq returned.2.2.1 following.1 :=
    ((heq_of_eq (lastReturn_nextStart elimination clearances grid reference retained lines onGrid cached supplied
      prepared next directions stored seam)).trans
      (Transport.Seam.castOwner_heq (site := site) (parameter := parameter)
        (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
        retained.finish_time next.source_time directions returned.2.2.1)).symm
  exact LastReturn.atEndpoint (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
    (positive := of_decide_eq_true rfl) (regular := leg.regular) (finish := retained.finishEndpoint)
    (nextQuarter := nextQuarter) elimination returned next.sourceEndpoint pointEq following.1 ownerEq

/-- The next-source return view retains the actual preceding quarter's entire original ordered vertex list. -/
theorem nextReturn_vertices
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored) :
    (nextReturn elimination clearances grid reference retained lines onGrid cached supplied
      prepared next directions stored seam).2.2.2.vertices =
      (lastReturn elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared).2.2.2.vertices := by
  let returned := lastReturn elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  let following := nextStart elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  have pointEq := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
    retained.finish_time next.source_time directions
  have ownerEq : HEq returned.2.2.1 following.1 :=
    ((heq_of_eq (lastReturn_nextStart elimination clearances grid reference retained lines onGrid cached supplied
      prepared next directions stored seam)).trans
      (Transport.Seam.castOwner_heq (site := site) (parameter := parameter)
        (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
        retained.finish_time next.source_time directions returned.2.2.1)).symm
  dsimp only [nextReturn]
  exact LastReturn.atEndpoint_vertices (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
    (positive := of_decide_eq_true rfl) (regular := leg.regular) (finish := retained.finishEndpoint)
    (nextQuarter := nextQuarter) elimination returned next.sourceEndpoint pointEq following.1 ownerEq

/-- Read the first actual middle Owner of either complete retained signed-quarter realization.

The original Steps target-count certificate excludes its empty branch
internally. The fine branch reads its retained first piece and transports
only the certified original source-time index. Both cases preserve the
entire actual entry-finish Owner, without requiring a successful final
comparison or an externally supplied nonemptiness certificate.
-/
@[expose] def middleSource
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)))
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      Acquisition.DetourSpine.middleSource elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid
        (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
        (Quarter.targets_nonempty retained)
  | .inr fine, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      let original := LayerAcquisition.DetourSpine.middleSource elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid
        (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical _sourceOwner supplied) prepared
      RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
        (congrArg (fun time : Fraction.Rational => (Paths.polynomial parameter).eval
          (Geometry.move elimination leg.regular
            (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)))
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) original

/-- Read the actual first entry path of either retained quarter at its original shared middle-source index.

The original branch supplies its own nonempty target proof. The fine branch
transports both physical endpoints and the same cached owners through its
retained start-time equality. Both branches consume their original entry
cover and preserve the supplied signed start.
-/
def entryTrace
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)
      (Block.Start.owner (site := site) (parameter := parameter) (unitQuarter := unitQuarter)
        (positive := of_decide_eq_true rfl) (current := input.sourceEndpoint) sourceOwner supplied)
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter))
      (middleSource elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared)
  | .inl _original, _sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      Acquisition.DetourSpine.entryTrace elimination clearances grid reference _ _ _ _ _ _ _
        retained.receipt lines onGrid (cached.steps elimination clearances grid retained lines onGrid)
        supplied prepared (Quarter.targets_nonempty retained)
  | .inr fine, sourceOwner, _agreement, retained, lines, onGrid, cached, supplied, prepared =>
      let original := LayerAcquisition.DetourSpine.middleSource elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
      let path := LayerAcquisition.DetourSpine.entryTrace elimination clearances grid reference _ _ _ _ _
        retained.paid lines onGrid (cached.numerical elimination clearances grid retained lines onGrid)
        (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
      let equalTime := fine.numerical.parts.start_time fine.numerical.layer_eq
      let startEq := congrArg (fun time : Fraction.Rational =>
        coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time) equalTime
      let finishEq := congrArg (Geometry.move elimination leg.regular) startEq
      let parameterEq := congrArg (fun time : Fraction.Rational => (Paths.polynomial parameter).eval
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))) equalTime
      OwnerPath.castEndpoints startEq finishEq
        (Numerical.Realization.detourStart_owner_heq fine.numerical sourceOwner supplied)
        (Owner.Transport.castOwnerParameter_heq parameterEq original).symm path

/-- Either retained quarter derives its first entry's sharp-source-square winding on the actual shared indices.

The original first Block pays the connector winding. Exact start-time and
owner transports preserve the same saved vertex list in the fine branch;
scalar endpoint transport carries its original potential difference.
-/
theorem entryTrace_winding
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
    (supplied : Option (Block.Start sourceOwner)) →
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied) →
    chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)
      (entryTrace elimination clearances grid reference input sourceOwner agreement
        retained lines onGrid cached supplied prepared).vertices =
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter input.sourceEndpoint.parameter leg.regular)
        (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)) -
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter input.sourceEndpoint.parameter leg.regular)
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter) := by
  intro input
  cases input with
  | inl original =>
    intro sourceOwner agreement retained lines onGrid cached supplied prepared
    exact Acquisition.DetourSpine.entryTrace_winding elimination clearances grid reference
      _ _ _ _ _ _ _ retained.receipt lines onGrid
      (cached.steps elimination clearances grid retained lines onGrid) supplied prepared
      (Quarter.targets_nonempty retained)
  | inr fine =>
    intro sourceOwner agreement retained lines onGrid cached supplied prepared
    let original := LayerAcquisition.DetourSpine.middleSource elimination clearances grid reference _ _ _ _ _
      retained.paid lines onGrid (cached.numerical elimination clearances grid retained lines onGrid)
      (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
    let path := LayerAcquisition.DetourSpine.entryTrace elimination clearances grid reference _ _ _ _ _
      retained.paid lines onGrid (cached.numerical elimination clearances grid retained lines onGrid)
      (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
    let equalTime := fine.numerical.parts.start_time fine.numerical.layer_eq
    let startEq := congrArg (fun time : Fraction.Rational =>
      coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time) equalTime
    let finishEq := congrArg (Geometry.move elimination leg.regular) startEq
    let parameterEq := congrArg (fun time : Fraction.Rational => (Paths.polynomial parameter).eval
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))) equalTime
    have vertices := OwnerPath.castEndpoints_vertices startEq finishEq
      (Numerical.Realization.detourStart_owner_heq fine.numerical sourceOwner supplied)
      (Owner.Transport.castOwnerParameter_heq parameterEq original).symm path
    have originalWinding := LayerAcquisition.DetourSpine.entryTrace_winding elimination clearances grid reference
      _ _ _ _ _ retained.paid lines onGrid (cached.numerical elimination clearances grid retained lines onGrid)
      (Numerical.Realization.detourStart fine.numerical sourceOwner supplied) prepared
    let difference (time : Fraction.Rational) :=
      windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter time leg.regular)
        (Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)) -
      windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter time leg.regular)
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)
    exact ((congrArg (chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl)
        fine.numerical.initial.lowerEndpoint.parameter)) vertices).trans
      (congrArg (fun start => chainRaw (Paths.polynomial parameter) start path.vertices) startEq.symm)).trans
        (originalWinding.trans (congrArg difference equalTime))

end DetourSpine

/-- Read the actual first moved vertex from the retained source-line cache.

The complete cached vertical and horizontal line payloads supply its
coordinates. The old and fine cases retain the same original point rule;
only the fine first-piece time equality restores its displayed index.
The same occurrence membership certifies the returned vertex on the
actual supplied grid, without executing another gap-point search.
-/
def sourceVertex
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    { point : Canonical // point = Geometry.move elimination leg.regular
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter) ∧
      Grid.FromStates.ContainsVertex grid point } := by
  cases input with
  | inl original =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines
      exact ⟨source.point, source.point_eq, onGrid source.point (List.Mem.head _)⟩
  | inr fine =>
      let source := Geometry.Lines.Bank.head
        (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines
      exact ⟨source.point, source.point_eq.trans
        (congrArg (fun time : Fraction.Rational => Geometry.move elimination leg.regular
          (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time))
          (fine.numerical.parts.start_time fine.numerical.layer_eq)), onGrid source.point (List.Mem.head _)⟩

/-- The actual signed-quarter source move belongs to the same retained grid as its line occurrences.

The original endpoint head is retained in both input branches. The fine
branch transports only its certified first-piece time equality; no new
coordinate line, numerical detour or source Owner is constructed.
-/
theorem sourceOnGrid
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point) :
    Grid.FromStates.ContainsVertex grid
      (Geometry.move elimination leg.regular
        (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)) := by
  let vertex := sourceVertex elimination clearances grid retained lines onGrid
  exact Eq.mp (congrArg (Grid.FromStates.ContainsVertex grid) vertex.property.1) vertex.property.2

namespace DetourSpine

variable {nextQuarter : UnitCircuitQuarter} {nextLeg : Transport.Leg site parameter nextQuarter}

/-- Compare the actual retained middle roots across the original quarter seam.

The following spine keeps its actual source Owner and supplied start.
The handoff relates that original start to this quarter's exact cached
seam transport. Both saved connector windings cancel in their shared
sharp square; the original frame selections compare the actual root names.
-/
def nextEntryEquivalent
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored)
    (nextOwner : OwnerAt site parameter nextQuarter (of_decide_eq_true rfl) next.sourceEndpoint)
    (nextAgreement : InitialAgreement next.sourceEndpoint next.sourceReading nextOwner)
    (nextRetained : Realization next nextOwner nextAgreement)
    (nextLines : Lines nextRetained elimination clearances)
    (nextOnGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := nextLeg.regular) nextLines,
      Grid.FromStates.ContainsVertex grid point)
    (nextCached : DetourWalkCache elimination clearances grid nextRetained nextLines nextOnGrid)
    (nextSupplied : Option (Block.Start nextOwner))
    (nextPrepared : DetourSpine elimination clearances grid reference next nextOwner nextAgreement
      nextRetained nextLines nextOnGrid nextCached nextSupplied)
    (handoff : NamedEquivalent
      (ownerName (nextStart elimination clearances grid reference retained lines onGrid cached supplied
        prepared next directions stored seam).1)
      (ownerName (Block.Start.owner (site := site) (parameter := parameter) (unitQuarter := nextQuarter)
        (positive := of_decide_eq_true rfl) (current := next.sourceEndpoint) nextOwner nextSupplied))) := by
  let oldReturn := lastReturn elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  let returned := nextReturn elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  let entered := entryTrace elimination clearances grid reference next nextOwner nextAgreement
    nextRetained nextLines nextOnGrid nextCached nextSupplied nextPrepared
  let incomingOwner := middleSource elimination clearances grid reference next nextOwner nextAgreement
    nextRetained nextLines nextOnGrid nextCached nextSupplied nextPrepared
  let oldPoint := coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter
  let nextPoint := coordinate site parameter 2 nextQuarter (of_decide_eq_true rfl) next.sourceEndpoint.parameter
  let oldBox := box site parameter unitQuarter retained.finishEndpoint.parameter leg.regular
  let nextBox := box site parameter nextQuarter next.sourceEndpoint.parameter nextLeg.regular
  let movedNext := Geometry.move elimination nextLeg.regular nextPoint
  have pointEq : oldPoint = nextPoint := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := unitQuarter) (rightQuarter := nextQuarter)
    retained.finish_time next.source_time directions
  have directionsAt := (congrArg (Waist.direction unitQuarter) retained.finish_time).trans
    (directions.trans (congrArg (Waist.direction nextQuarter) next.source_time).symm)
  have squareEq : oldBox = nextBox :=
    congrArg (fun direction => Radial.Clearance.box site parameter direction leg.regular) directionsAt
  have oldAtNext : oldReturn.1.val = movedNext :=
    oldReturn.1.property.trans (congrArg (Geometry.move elimination leg.regular) pointEq)
  have sameReturnedPoint : returned.1.val = oldReturn.1.val := returned.1.property.trans oldAtNext.symm
  have returnVertices := nextReturn_vertices elimination clearances grid reference retained lines onGrid cached
    supplied prepared next directions stored seam
  have returnReadback : chainRaw (Paths.polynomial parameter) returned.1.val returned.2.2.2.vertices =
      chainRaw (Paths.polynomial parameter) oldReturn.1.val oldReturn.2.2.2.vertices :=
    (congrArg (chainRaw (Paths.polynomial parameter) returned.1.val) returnVertices).trans
      (congrArg (fun point => chainRaw (Paths.polynomial parameter) point oldReturn.2.2.2.vertices)
        sameReturnedPoint)
  have originalWinding := lastReturn_winding elimination clearances grid reference input sourceOwner agreement
    retained lines onGrid cached supplied prepared
  have incomingWinding := entryTrace_winding elimination clearances grid reference next nextOwner nextAgreement
    nextRetained nextLines nextOnGrid nextCached nextSupplied nextPrepared
  have cancellation :
      (windingPotential (Paths.polynomial parameter) oldBox oldPoint -
        windingPotential (Paths.polynomial parameter) oldBox oldReturn.1.val) +
      (windingPotential (Paths.polynomial parameter) nextBox movedNext -
        windingPotential (Paths.polynomial parameter) nextBox nextPoint) = 8 * (0 : Int) := by
    rewrite [squareEq, pointEq, oldAtNext]
    let firstValue := windingPotential (Paths.polynomial parameter) nextBox nextPoint
    let lastValue := windingPotential (Paths.polynomial parameter) nextBox movedNext
    change (firstValue + -lastValue) + (lastValue + -firstValue) = (0 : Int)
    rewrite [Arithmetic.add_assoc firstValue (-lastValue) (lastValue + -firstValue),
      ← Arithmetic.add_assoc (-lastValue) lastValue (-firstValue),
      Arithmetic.neg_add_cancel lastValue, Arithmetic.zero_add (-firstValue),
      Arithmetic.add_comm firstValue (-firstValue)]
    exact Arithmetic.neg_add_cancel firstValue
  have winding : chainRaw (Paths.polynomial parameter) returned.1.val returned.2.2.2.vertices +
      chainRaw (Paths.polynomial parameter) nextPoint entered.vertices = 8 * (0 : Int) :=
    (congrArg₂ (fun left right : Int => left + right)
      (returnReadback.trans originalWinding) incomingWinding).trans cancellation
  have movedOnGrid := sourceOnGrid (leg := nextLeg) (input := next)
    (sourceOwner := nextOwner) (agreement := nextAgreement)
    elimination clearances grid nextRetained nextLines nextOnGrid
  have returnedOnGrid : Grid.FromStates.ContainsVertex grid returned.1.val :=
    Eq.mpr (congrArg (Grid.FromStates.ContainsVertex grid) returned.1.property) movedOnGrid
  let loopReference := reference returned.1.val returnedOnGrid
  exact fun (frame : OwnerFrame ((Paths.polynomial parameter).eval returned.1.val))
      (before : OwnerSelection frame.owners returned.2.1)
      (after : NameSelection (fun index => ownerName (frame.owners index)) (ownerName incomingOwner)) =>
    returned.entryEquivalent (site := site) (parameter := parameter) (unitQuarter := nextQuarter)
      (positive := of_decide_eq_true rfl) (regular := nextLeg.regular) (finish := next.sourceEndpoint)
      (finishPoint := movedNext) (last := incomingOwner)
      elimination (Block.Start.owner nextOwner nextSupplied) handoff entered returned.1.property.symm
      loopReference frame before after 0 winding

/-- Compare the two original primitive observations on the actual adjacent-quarter middle roots.

Both signed spines retain their original starts and numeric caches.
The supplied start handoff and internally derived connector agreement compare these old coefficient
observations of one expression at their certified identical moved point.
Each Vertex keeps its independent request and selected state; only the
comparison's finite tail is prepared here.
-/
def nextEntryComparison
    (reference : ∀ point, Grid.FromStates.ContainsVertex grid point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (retained : Realization input sourceOwner agreement)
    (lines : Lines retained elimination clearances)
    (onGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := leg.regular) lines,
      Grid.FromStates.ContainsVertex grid point)
    (cached : DetourWalkCache elimination clearances grid retained lines onGrid)
    (supplied : Option (Block.Start sourceOwner))
    (prepared : DetourSpine elimination clearances grid reference input sourceOwner agreement
      retained lines onGrid cached supplied)
    (next : Input nextLeg) (directions : Waist.direction unitQuarter 1 = Waist.direction nextQuarter 0)
    (stored : Transport.Seam leg nextLeg)
    (seam : Transport.Seam.Receipt (left := leg) (right := nextLeg) retained.finishReading next.sourceReading
      retained.finishOwner retained.finishEquivalent retained.finish_time next.source_time directions stored)
    (nextOwner : OwnerAt site parameter nextQuarter (of_decide_eq_true rfl) next.sourceEndpoint)
    (nextAgreement : InitialAgreement next.sourceEndpoint next.sourceReading nextOwner)
    (nextRetained : Realization next nextOwner nextAgreement)
    (nextLines : Lines nextRetained elimination clearances)
    (nextOnGrid : ∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := nextLeg.regular) nextLines,
      Grid.FromStates.ContainsVertex grid point)
    (nextCached : DetourWalkCache elimination clearances grid nextRetained nextLines nextOnGrid)
    (nextSupplied : Option (Block.Start nextOwner))
    (nextPrepared : DetourSpine elimination clearances grid reference next nextOwner nextAgreement
      nextRetained nextLines nextOnGrid nextCached nextSupplied)
    (handoff : NamedEquivalent
      (ownerName (nextStart elimination clearances grid reference retained lines onGrid cached supplied
        prepared next directions stored seam).1)
      (ownerName (Block.Start.owner (site := site) (parameter := parameter) (unitQuarter := nextQuarter)
        (positive := of_decide_eq_true rfl) (current := next.sourceEndpoint) nextOwner nextSupplied))) := by
  let returned := nextReturn elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam
  let incomingOwner := middleSource elimination clearances grid reference next nextOwner nextAgreement
    nextRetained nextLines nextOnGrid nextCached nextSupplied nextPrepared
  let movedNext := Geometry.move elimination nextLeg.regular
    (coordinate site parameter 2 nextQuarter (of_decide_eq_true rfl) next.sourceEndpoint.parameter)
  let roots := nextEntryEquivalent elimination clearances grid reference retained lines onGrid cached supplied
    prepared next directions stored seam nextOwner nextAgreement nextRetained nextLines nextOnGrid nextCached
    nextSupplied nextPrepared handoff
  exact fun (frame : OwnerFrame ((Paths.polynomial parameter).eval returned.1.val))
      (before : OwnerSelection frame.owners returned.2.1)
      (after : NameSelection (fun index => ownerName (frame.owners index)) (ownerName incomingOwner))
      (expression : Expression (Paths.polynomial parameter)) (firstAccuracy lastAccuracy : AccuracyRequest)
      (first : OwnerPath.Primitive.Vertex expression returned.1.val returned.2.1 firstAccuracy)
      (last : OwnerPath.Primitive.Vertex expression movedNext incomingOwner lastAccuracy)
      (request : AccuracyRequest) =>
    first.compare last returned.1.property (roots frame before after).symm request

end DetourSpine

end SignedDetour

end Realization

end Input

end Steps.Acquisition.Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

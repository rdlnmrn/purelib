module
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Faces
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction

/-! # Original ordered face assignments of the actual signed four-quarter circuit

The original signed circuit and numeric detour remain retained inputs.
Its four existing quarter folds use one supplied lifted mesh on the
certified identical grid. The result retains their original face carriers
in circuit order.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Steps.Acquisition.Quarter.Input

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}
variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {frame : Paths.Frame parameter} {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {meshBase : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}

namespace Execution.Cache.Lines.DetourCache.Signed

variable {lines : Lines execution elimination clearances}
variable {numericBase : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
attribute [local irreducible] Realization.DetourSpine

/-- The four exact original quarter face carriers on the same retained signed circuit and certified mesh grid.

Each factor remains indexed by its original paid quarter, numerical
heads and signed spine. The three original seam starts are the same
inherited starts used by that signed circuit. Ordered endpoint selections
and complete face assignments remain in their original carriers.
-/
@[expose] def Faces
    (cached : DetourCache lines numericBase)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference)
    (lifted : LiftedPuncturedGrid meshBase)
    (sameGrid : cached.val.1 = meshBase.bank.grid) :=
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  Realization.DetourSpine.Faces (leg := circuit.first)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    firstInput sourceOwner agreement
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1 ×
  Realization.DetourSpine.Faces (leg := circuit.second)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    secondInput execution.second.seam.owner execution.second.seam.nextAgreement
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1 ×
  Realization.DetourSpine.Faces (leg := circuit.third)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    thirdInput execution.third.seam.owner execution.third.seam.nextAgreement
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1 ×
  Realization.DetourSpine.Faces (leg := circuit.fourth)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    fourthInput execution.fourth.seam.owner execution.fourth.seam.nextAgreement
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2

/-- Construct the four original face folds on this same signed circuit in its retained quarter order.

The existing numeric heads and signed paths are supplied unchanged.
The grid identity transports their indices to the one retained lifted
mesh, and each original quarter face producer runs once.
-/
def faces
    (cached : DetourCache lines numericBase)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference)
    (lifted : LiftedPuncturedGrid meshBase)
    (sameGrid : cached.val.1 = meshBase.bank.grid) :
    Faces cached reference prepared lifted sameGrid :=
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let first := Realization.DetourSpine.faces (leg := circuit.first)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    firstInput sourceOwner agreement
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
  let second := Realization.DetourSpine.faces (leg := circuit.second)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    secondInput execution.second.seam.owner execution.second.seam.nextAgreement
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
  let third := Realization.DetourSpine.faces (leg := circuit.third)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    thirdInput execution.third.seam.owner execution.third.seam.nextAgreement
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
  let fourth := Realization.DetourSpine.faces (leg := circuit.fourth)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase)
    lifted elimination clearances cached.val.1 sameGrid reference
    fourthInput execution.fourth.seam.owner execution.fourth.seam.nextAgreement
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
  ⟨first, second, third, fourth⟩

namespace Faces

variable
    {cached : DetourCache lines numericBase}
    {reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {prepared : Signed cached reference}
    {lifted : LiftedPuncturedGrid meshBase}
    {sameGrid : cached.val.1 = meshBase.bank.grid}
variable (retained : Faces cached reference prepared lifted sameGrid)

/-- Read the same complete retained first quarter face carrier in its original circuit position. -/
@[expose] def first := retained.1

/-- Read the same complete retained second quarter face carrier in its original circuit position. -/
@[expose] def second := retained.2.1

/-- Read the same complete retained third quarter face carrier in its original circuit position. -/
@[expose] def third := retained.2.2.1

/-- Read the same complete retained fourth quarter face carrier in its original circuit position. -/
@[expose] def fourth := retained.2.2.2

/-- The actual retained first and second quarter face words share their original lifted seam vertex.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def FirstSecondLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {circuit : Transport.Circuit site parameter}
    {firstInput : Input circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
    {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
    {initial : Input.Realization firstInput sourceOwner agreement}
    {secondInput : Input circuit.second}
    {thirdInput : Input circuit.third}
    {fourthInput : Input circuit.fourth}
    {execution : Execution.Cache initial secondInput thirdInput fourthInput}
    {degreeBound : Nat}
    {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
    {clearances : AxisClearances elimination}
    {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {meshBase : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lines : Lines execution elimination clearances}
    {numericBase : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}
    {cached : DetourCache lines numericBase}
    {reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {prepared : Signed cached reference}
    {lifted : LiftedPuncturedGrid meshBase}
    {sameGrid : cached.val.1 = meshBase.bank.grid}
    (retained : Faces cached reference prepared lifted sameGrid),
    retained.first.lastVertex = retained.second.firstVertex

/-- The actual retained first and second quarter face words share their original lifted seam vertex. -/
theorem first_second : FirstSecondLaw := by
  unfold FirstSecondLaw
  intro site parameter circuit firstInput sourceOwner agreement initial secondInput thirdInput fourthInput
    execution degreeBound elimination clearances frame branches higher meshBase lines numericBase cached
    reference prepared lifted sameGrid retained
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  exact Realization.DetourSpine.Faces.nextVertex_eq
    (site := site) (parameter := parameter) (unitQuarter := .first) (leg := circuit.first)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase) (lifted := lifted)
    (elimination := elimination) (clearances := clearances) (grid := cached.val.1) (sameGrid := sameGrid)
    (reference := reference) (input := firstInput) (sourceOwner := sourceOwner) (agreement := agreement)
    (retained := execution.first) (lines := lines.1) (onGrid := cached.onGrid.1) (cached := heads.1)
    (supplied := none) (prepared := prepared.1) retained.first
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
    execution.second.seam.owner execution.second.seam.nextAgreement execution.second.paid
    lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    (NamedEquivalent.refl (ownerName secondStart.1)) retained.second

/-- The actual retained second and third quarter face words share their original lifted seam vertex.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def SecondThirdLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {circuit : Transport.Circuit site parameter}
    {firstInput : Input circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
    {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
    {initial : Input.Realization firstInput sourceOwner agreement}
    {secondInput : Input circuit.second}
    {thirdInput : Input circuit.third}
    {fourthInput : Input circuit.fourth}
    {execution : Execution.Cache initial secondInput thirdInput fourthInput}
    {degreeBound : Nat}
    {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
    {clearances : AxisClearances elimination}
    {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {meshBase : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lines : Lines execution elimination clearances}
    {numericBase : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}
    {cached : DetourCache lines numericBase}
    {reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {prepared : Signed cached reference}
    {lifted : LiftedPuncturedGrid meshBase}
    {sameGrid : cached.val.1 = meshBase.bank.grid}
    (retained : Faces cached reference prepared lifted sameGrid),
    retained.second.lastVertex = retained.third.firstVertex

/-- The actual retained second and third quarter face words share their original lifted seam vertex. -/
theorem second_third : SecondThirdLaw := by
  unfold SecondThirdLaw
  intro site parameter circuit firstInput sourceOwner agreement initial secondInput thirdInput fourthInput
    execution degreeBound elimination clearances frame branches higher meshBase lines numericBase cached
    reference prepared lifted sameGrid retained
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  exact Realization.DetourSpine.Faces.nextVertex_eq
    (site := site) (parameter := parameter) (unitQuarter := .second) (leg := circuit.second)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase) (lifted := lifted)
    (elimination := elimination) (clearances := clearances) (grid := cached.val.1) (sameGrid := sameGrid)
    (reference := reference) (input := secondInput) (sourceOwner := execution.second.seam.owner)
    (agreement := execution.second.seam.nextAgreement)
    (retained := execution.second.paid) (lines := lines.2.1) (onGrid := cached.onGrid.2.1) (cached := heads.2.1)
    (supplied := (some secondStart)) (prepared := prepared.2.1) retained.second
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
    execution.third.seam.owner execution.third.seam.nextAgreement execution.third.paid
    lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
    (NamedEquivalent.refl (ownerName thirdStart.1)) retained.third

/-- The actual retained third and fourth quarter face words share their original lifted seam vertex.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ThirdFourthLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {circuit : Transport.Circuit site parameter}
    {firstInput : Input circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
    {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
    {initial : Input.Realization firstInput sourceOwner agreement}
    {secondInput : Input circuit.second}
    {thirdInput : Input circuit.third}
    {fourthInput : Input circuit.fourth}
    {execution : Execution.Cache initial secondInput thirdInput fourthInput}
    {degreeBound : Nat}
    {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
    {clearances : AxisClearances elimination}
    {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {meshBase : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lines : Lines execution elimination clearances}
    {numericBase : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}
    {cached : DetourCache lines numericBase}
    {reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {prepared : Signed cached reference}
    {lifted : LiftedPuncturedGrid meshBase}
    {sameGrid : cached.val.1 = meshBase.bank.grid}
    (retained : Faces cached reference prepared lifted sameGrid),
    retained.third.lastVertex = retained.fourth.firstVertex

/-- The actual retained third and fourth quarter face words share their original lifted seam vertex. -/
theorem third_fourth : ThirdFourthLaw := by
  unfold ThirdFourthLaw
  intro site parameter circuit firstInput sourceOwner agreement initial secondInput thirdInput fourthInput
    execution degreeBound elimination clearances frame branches higher meshBase lines numericBase cached
    reference prepared lifted sameGrid retained
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  exact Realization.DetourSpine.Faces.nextVertex_eq
    (site := site) (parameter := parameter) (unitQuarter := .third) (leg := circuit.third)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase) (lifted := lifted)
    (elimination := elimination) (clearances := clearances) (grid := cached.val.1) (sameGrid := sameGrid)
    (reference := reference) (input := thirdInput) (sourceOwner := execution.third.seam.owner)
    (agreement := execution.third.seam.nextAgreement)
    (retained := execution.third.paid) (lines := lines.2.2.1) (onGrid := cached.onGrid.2.2.1) (cached := heads.2.2.1)
    (supplied := (some thirdStart)) (prepared := prepared.2.2.1) retained.third
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
    execution.fourth.seam.owner execution.fourth.seam.nextAgreement execution.fourth.paid
    lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
    (NamedEquivalent.refl (ownerName fourthStart.1)) retained.fourth

/-- The actual retained fourth and first quarter face words share their original lifted seam vertex.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def FourthFirstLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {circuit : Transport.Circuit site parameter}
    {firstInput : Input circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
    {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
    {initial : Input.Realization firstInput sourceOwner agreement}
    {secondInput : Input circuit.second}
    {thirdInput : Input circuit.third}
    {fourthInput : Input circuit.fourth}
    {execution : Execution.Cache initial secondInput thirdInput fourthInput}
    {degreeBound : Nat}
    {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
    {clearances : AxisClearances elimination}
    {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {meshBase : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lines : Lines execution elimination clearances}
    {numericBase : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}
    {cached : DetourCache lines numericBase}
    {reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point}
    {prepared : Signed cached reference}
    {lifted : LiftedPuncturedGrid meshBase}
    {sameGrid : cached.val.1 = meshBase.bank.grid}
    (retained : Faces cached reference prepared lifted sameGrid),
    retained.fourth.lastVertex = retained.first.firstVertex

/-- The actual retained fourth and first quarter face words share their original lifted seam vertex. -/
theorem fourth_first : FourthFirstLaw := by
  unfold FourthFirstLaw
  intro site parameter circuit firstInput sourceOwner agreement initial secondInput thirdInput fourthInput
    execution degreeBound elimination clearances frame branches higher meshBase lines numericBase cached
    reference prepared lifted sameGrid retained
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let closingStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
    firstInput Waist.directions_join.2.2.2 circuit.fourth_first execution.closing
  have same : closingStart.1 = Signed.returnOwner cached reference prepared :=
    Realization.DetourSpine.nextStart_owner_eq elimination clearances cached.val.1 reference
      execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
      firstInput Waist.directions_join.2.2.2 circuit.fourth_first execution.closing
  have handoff := NamedEquivalent.transport (congrArg ownerName same).symm rfl
    (Signed.returnEquivalent cached reference prepared)
  exact Realization.DetourSpine.Faces.nextVertex_eq
    (site := site) (parameter := parameter) (unitQuarter := .fourth) (leg := circuit.fourth)
    (frame := frame) (branches := branches) (higher := higher) (base := meshBase) (lifted := lifted)
    (elimination := elimination) (clearances := clearances) (grid := cached.val.1) (sameGrid := sameGrid)
    (reference := reference) (input := fourthInput) (sourceOwner := execution.fourth.seam.owner)
    (agreement := execution.fourth.seam.nextAgreement)
    (retained := execution.fourth.paid) (lines := lines.2.2.2) (onGrid := cached.onGrid.2.2.2) (cached := heads.2.2.2)
    (supplied := (some fourthStart)) (prepared := prepared.2.2.2) retained.fourth
    firstInput Waist.directions_join.2.2.2 circuit.fourth_first execution.closing
    sourceOwner agreement execution.first
    lines.1 cached.onGrid.1 heads.1 none prepared.1
    handoff retained.first

/-- The complete actual signed circuit face word preserves all four original quarter words in circuit order. -/
@[expose] def word : List (OrientedEdge lifted.vertices.count) :=
  ((retained.first.word ++ retained.second.word) ++ retained.third.word) ++ retained.fourth.word

/-- Read all actual signed-circuit face occurrences in their original four-quarter order.

Each callback sees the original saved face and sheet route. All signed
and repeated occurrences survive, including adjacent-quarter seams;
the operation only folds those retained assignments and appends their lists.
-/
@[expose] def values {α : Type} (read : (edge : OrientedEdge lifted.vertices.count) → EdgeRoute lifted.mesh edge → α) :
    List α :=
  ((retained.first.values read ++ retained.second.values read) ++ retained.third.values read) ++
    retained.fourth.values read

/-- Reading all actual retained face routes preserves the full signed word's occurrence count. -/
theorem values_length {α : Type}
    (read : (edge : OrientedEdge lifted.vertices.count) → EdgeRoute lifted.mesh edge → α) :
    (retained.values read).length = retained.word.length := by
  have lengths {β : Type} (first second third fourth : List β) :
      (((first ++ second) ++ third) ++ fourth).length =
        ((first.length + second.length) + third.length) + fourth.length :=
    (Append.length_append ((first ++ second) ++ third) fourth).trans
      (congrArg (fun size => size + fourth.length)
        ((Append.length_append (first ++ second) third).trans
          (congrArg (fun size => size + third.length) (Append.length_append first second))))
  exact (lengths (retained.first.values read) (retained.second.values read)
    (retained.third.values read) (retained.fourth.values read)).trans
      ((congrArg₂ Nat.add (congrArg₂ Nat.add
        (congrArg₂ Nat.add (retained.first.values_length read) (retained.second.values_length read))
        (retained.third.values_length read)) (retained.fourth.values_length read)).trans
          (lengths retained.first.word retained.second.word retained.third.word retained.fourth.word).symm)

/-- The whole retained circuit face word runs between the original first and fourth lifted endpoint vertices. -/
theorem endpoints : PathEndpoints OrientedEdge.start OrientedEdge.finish retained.word
    retained.first.firstVertex retained.fourth.lastVertex :=
  ((retained.first.endpoints.append (retained.second.endpoints.castStart retained.first_second.symm)).append
    (retained.third.endpoints.castStart retained.second_third.symm)).append
      (retained.fourth.endpoints.castStart retained.third_fourth.symm)

/-- The actual signed circuit face word closes on its original lifted source vertex.

The last join uses the original paid fourth-to-first root certificate and
the first spine's actual entry. No canonical cycle identification or
physical integral equality is inferred from this endpoint certificate.
-/
theorem closed : PathEndpoints OrientedEdge.start OrientedEdge.finish retained.word
    retained.first.firstVertex retained.first.firstVertex :=
  retained.endpoints.castFinish retained.fourth_first

/-- Every occurrence of the complete actual signed word lies on its retained lifted triangulation. -/
theorem supported : CutPath.Supported (triangleEdgeOccurrences lifted.mesh.triangulation.faces) retained.word :=
  CutPath.supported_append
    (CutPath.supported_append (CutPath.supported_append retained.first.supported retained.second.supported)
      retained.third.supported) retained.fourth.supported

/-- The actual word is supported by the original sewn patch on that same lifted mesh. -/
theorem supported_cutPatch : CutPath.Supported
    (SewingConnected.SewnPatch.originalEdges lifted.cutPolygon.patch) retained.word :=
  CutPath.supported_mono retained.supported
    (fun _ member => TourRetraction.originalEdge_on_cutPatch lifted member)

/-- Route the original ordered signed word through one supplied retained sewing retraction.

The existing word-route factory consumes that same retraction and all
original occurrences once. Its cached boundary path and complete signed
face correction remain together in the original WordRoute carrier.
-/
def boundaryRoute
    (retraction : SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary) :
    SewingRetraction.WordRoute lifted.mesh.triangulation.faces lifted.cutPolygon.patch.boundary retained.word :=
  retraction.word retained.word retained.supported_cutPatch

/-- The retained signed boundary route is the whole original word-route factory on the same inputs. -/
theorem boundaryRoute_eq
    (retraction : SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary) :
    retained.boundaryRoute retraction = retraction.word retained.word retained.supported_cutPatch := (rfl)

/-- The retained boundary route closes at the actual signed word's original lifted source vertex. -/
theorem boundaryRoute_closed
    (retraction : SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary) :
    PathEndpoints OrientedEdge.start OrientedEdge.finish (retained.boundaryRoute retraction).path
      retained.first.firstVertex retained.first.firstVertex :=
  (retained.boundaryRoute retraction).endpoints retained.closed

/-- The actual signed word equals its retained boundary route value plus the full signed face correction.

Every antisymmetric reading uses the same original word, boundary path
and correction list. No face or physical-boundary contribution is removed.
-/
theorem boundaryRoute_value
    (retraction : SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary)
    (value : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value retained.word =
      SewingRetraction.wordValue value (retained.boundaryRoute retraction).path +
        SewingRetraction.faceValue lifted.mesh.triangulation.faces value
          (retained.boundaryRoute retraction).correction :=
  (retained.boundaryRoute retraction).value_eq value anti

end Faces

end Execution.Cache.Lines.DetourCache.Signed

namespace Execution.Cache

section Preparation

variable (execution : Execution.Cache initial secondInput thirdInput fourthInput)
variable (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
variable (clearances : AxisClearances elimination)
variable (frame : Paths.Frame parameter)
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable (bank : FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
variable (retained : { value : DetourReference execution elimination clearances frame bank.toBranchCellBank //
  value = execution.detourWithReference elimination clearances frame bank.toBranchCellBank })
variable (prepared : Lines.DetourCache.Signed retained.val.2.1
  (retained.val.2.1.pointReferences retained.val.2.2
    (DetourReference.ambient_eq execution elimination clearances frame bank.toBranchCellBank retained)))

/-- One original refined branch bank, its retained lifted mesh and all four actual signed-quarter face assignments.

The original numerical/reference producer and signed spine remain indices.
The branch-bank and lifted-mesh caches retain their whole original factory
equations. Every face assignment uses those same cached mesh vertices,
root frames and edges on the certified identical numeric grid.
-/
@[expose] def PreparedFaces :=
  Σ incidence : { value :
      { target : FramedBranchCellBank (Fibre.frameCurve frame) branches higher //
        target.grid = retained.val.2.1.val.1 ∧
        ∀ index, (target.cell index).box.Refines (bank.cell index).box } //
      value = DetourReference.framedBank execution elimination clearances frame bank retained.val },
    Σ mesh : { value : LiftedPuncturedGrid (FramedPuncturedGrid.ofBank incidence.val.val) //
        value = LiftedPuncturedGrid.build (FramedPuncturedGrid.ofBank incidence.val.val) },
      Lines.DetourCache.Signed.Faces (frame := frame) retained.val.2.1
        (retained.val.2.1.pointReferences retained.val.2.2
          (DetourReference.ambient_eq execution elimination clearances frame bank.toBranchCellBank retained))
        prepared mesh.val incidence.val.property.1.symm

/-- Construct one retained canonical mesh and the four original face folds on this same supplied signed detour.

The existing framed-bank transport refines the original labelled states
once. Its same returned bank builds one lifted mesh, and that mesh's
cached vertices, root frames and edges are supplied to all four actual
quarter folds. Neither the numerical detour nor its signed preparation
is repeated.
-/
def prepareFaces : PreparedFaces execution elimination clearances frame bank retained prepared :=
  let incidence := DetourReference.framedBank execution elimination clearances frame bank retained.val
  let mesh := LiftedPuncturedGrid.build (FramedPuncturedGrid.ofBank incidence.val)
  let reference := retained.val.2.1.pointReferences retained.val.2.2
    (DetourReference.ambient_eq execution elimination clearances frame bank.toBranchCellBank retained)
  let assignments := Lines.DetourCache.Signed.faces (frame := frame)
    retained.val.2.1 reference prepared mesh incidence.property.1.symm
  ⟨⟨incidence, rfl⟩, ⟨⟨mesh, rfl⟩, assignments⟩⟩

namespace PreparedFaces

variable {execution elimination clearances frame bank retained prepared}
variable (completed : PreparedFaces execution elimination clearances frame bank retained prepared)

/-- Read the original retained framed-bank refinement, including its exact grid and labelled-cell certificates. -/
@[expose] def incidence := completed.1.val

/-- Read the complete same cached mesh with its original vertex, root-frame, edge and face banks. -/
@[expose] def mesh := completed.2.1.val

/-- Read all four actual original quarter assignments on the identical retained mesh. -/
@[expose] def assignments := completed.2.2

/-- The whole retained incidence is the original framed-bank transport on these same numeric/reference caches. -/
theorem incidence_eq : completed.incidence =
    DetourReference.framedBank execution elimination clearances frame bank retained.val :=
  completed.1.property

/-- The whole retained mesh is the original builder on that same actual refined bank. -/
theorem mesh_eq : completed.mesh = LiftedPuncturedGrid.build
    (FramedPuncturedGrid.ofBank completed.incidence.val) := completed.2.1.property

end PreparedFaces

end Preparation

end Execution.Cache

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end

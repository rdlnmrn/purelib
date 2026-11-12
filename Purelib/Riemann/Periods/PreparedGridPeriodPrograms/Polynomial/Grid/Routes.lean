module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Grid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes.Sources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Original current-grid period routes before a genuine P bank

A single actual starting-frame selection and self-resplit face assignment
supply the route and chart geometries. Both true-P requests are prepared
before observations. The actual initial PathSources and signed root chain
read the same source word; a genuine self-resplit chain comparison relates
its cochain to the original cycle on that SAME retained grid.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine.GridFragments

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (RouteRequest canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OccurrenceFrame OwnerFrame OwnerSelection)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {framed : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
    {lifted : LiftedPuncturedGrid framed} {vertex : Fin lifted.vertices.count} {source : Differential 1}
    {walk : PeriodWalk framed.bank.grid (lifted.vertices.coordinate vertex)
      (lifted.vertices.owner lifted.frames vertex) source}
    {spine : PolynomialSpine (parameter := parameter) (frame := frame) walk}
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    {selection : PrimitiveSelection walk sourceStart periodStart tolerance positive}
    {domains : FaceDomainBank lifted.frames framed.faces.regulars}
    (fragments : GridFragments lifted vertex walk spine selection domains)
    (ordinary : Ordinary (Fibre.frameCurve frame).polynomial) (target : Rational) (targetPositive : 0 < target)

/-- The exact original fresh physical source, ordinary numerator and positive route/chart target. -/
@[expose] def Contacts.Inputs : Type _ :=
  {inputs : GridFragments lifted vertex walk spine selection domains ×
      Ordinary (Fibre.frameCurve frame).polynomial × Rational // inputs = (fragments, ordinary, target)}

/-- The same actual starting frame and its original complete lookup factory. -/
@[expose] def Contacts.FrameCache : Type _ :=
  {value : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval
      (lifted.vertices.coordinate vertex)) //
    value = lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex)}

/-- Exact retained selection, self-resplit faces and raw/numerator contact requests on one given frame. -/
@[expose] def Contacts.Execution
    (cachedFrame : Contacts.FrameCache (lifted := lifted) (vertex := vertex)) : Type _ :=
  Σ selected : {value : OwnerSelection
      (lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex)).owners
      (lifted.vertices.owner lifted.frames vertex) //
    value = Eq.mp (congrArg (fun current : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval
      (lifted.vertices.coordinate vertex)) => OwnerSelection current.owners
      (lifted.vertices.owner lifted.frames vertex)) cachedFrame.property)
        (OccurrenceFrame.select (Occurrence := Owner ((Fibre.frameCurve frame).polynomial.eval
          (lifted.vertices.coordinate vertex)))
          (name := ownerName) cachedFrame.val (lifted.vertices.owner lifted.frames vertex))},
  Σ splitWalk : {value : Walk framed.bank.grid (lifted.vertices.coordinate vertex)
      (lifted.vertices.coordinate vertex) //
    value = (CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk
      (lifted.vertices.coordinate_onGrid vertex)},
  Σ faces : {value : OwnerWalkFaces lifted.mesh
      ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex))
      (lifted.vertices.owner lifted.frames vertex) //
    value = OwnerWalkFaces.castWalk splitWalk.property (OwnerWalkFaces.ofSelection lifted.mesh splitWalk.val
      (lifted.vertices.coordinate_onGrid vertex) selected.val)},
  Σ raw : {value : RouteRequest fragments.rooted.pieces target //
    value = RouteRequest.build fragments.rooted.pieces canonicalRoute target targetPositive},
  Σ _routed : {value : RouteRequest fragments.rooted.pieces target (some ordinary) //
    value = raw.val.onNumerator ordinary},
  Σ rawChart : {value : RouteChartRequest faces.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target //
    value = RouteChartRequest.build faces.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target targetPositive},
  {value : RouteChartRequest faces.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target (some ordinary) //
    value = rawChart.val.rebudget target targetPositive (some ordinary)}

attribute [local irreducible] Contacts.Inputs Contacts.FrameCache Contacts.Execution in
set_option genInjectivity false in
/-- The actual current-frame selection, resplit face cache and both pre-bank genuine-P contact requests.

All original frame, root, partial-edge, query and sheet owners remain
those of the retained grid and fresh period. The selected frame is a
cached lookup on the old root bank; it is never built or identified from
coordinates. Numerical stages and primitive offsets are not selected here.
-/
structure Contacts : Type _ where
  /-- The same physical source, genuine numerator and positive target with their whole identity. -/
  inputCache : Contacts.Inputs fragments ordinary target
  /-- The actual original retained frame and lookup factory. -/
  frameData : Contacts.FrameCache (lifted := lifted) (vertex := vertex)
  /-- The original selection, faces and raw/numerator requests computed from that same frame. -/
  execution : Contacts.Execution (fragments := fragments) (ordinary := ordinary)
    (target := target) (targetPositive := targetPositive) frameData

attribute [local irreducible] Contacts.Inputs Contacts.FrameCache Contacts.Execution in
constructive_injectivity Contacts

/-- Retain the actual current-frame lookup and selection, then prepare the two genuine-P request spines once. -/
def contacts : Contacts fragments ordinary target targetPositive :=
  let inputs : Contacts.Inputs fragments ordinary target := ⟨(fragments, ordinary, target), rfl⟩
  let cachedFrame : {value : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval
      (lifted.vertices.coordinate vertex)) //
      value = lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex)} :=
    ⟨lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex), rfl⟩
  let selected : {value : OwnerSelection
      (lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex)).owners
      (lifted.vertices.owner lifted.frames vertex) //
      value = Eq.mp (congrArg (fun current : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval
        (lifted.vertices.coordinate vertex)) => OwnerSelection current.owners
        (lifted.vertices.owner lifted.frames vertex)) cachedFrame.property)
          (OccurrenceFrame.select (Occurrence := Owner ((Fibre.frameCurve frame).polynomial.eval
            (lifted.vertices.coordinate vertex)))
          (name := ownerName) cachedFrame.val (lifted.vertices.owner lifted.frames vertex))} :=
    ⟨Eq.mp (congrArg (fun current : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval (lifted.vertices.coordinate
      vertex)) => OwnerSelection current.owners
      (lifted.vertices.owner lifted.frames vertex)) cachedFrame.property)
        (OccurrenceFrame.select (Occurrence := Owner ((Fibre.frameCurve frame).polynomial.eval
          (lifted.vertices.coordinate vertex)))
          (name := ownerName) cachedFrame.val (lifted.vertices.owner lifted.frames vertex)), rfl⟩
  let splitWalk : {value : Walk framed.bank.grid (lifted.vertices.coordinate vertex)
      (lifted.vertices.coordinate vertex) //
      value = (CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk
        (lifted.vertices.coordinate_onGrid vertex)} :=
    ⟨(CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk
      (lifted.vertices.coordinate_onGrid vertex), rfl⟩
  let faces : {value : OwnerWalkFaces lifted.mesh
      ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex))
      (lifted.vertices.owner lifted.frames vertex) //
      value = OwnerWalkFaces.castWalk splitWalk.property (OwnerWalkFaces.ofSelection lifted.mesh splitWalk.val
        (lifted.vertices.coordinate_onGrid vertex) selected.val)} :=
    ⟨OwnerWalkFaces.castWalk splitWalk.property (OwnerWalkFaces.ofSelection lifted.mesh splitWalk.val
      (lifted.vertices.coordinate_onGrid vertex) selected.val), rfl⟩
  let raw : {value : RouteRequest fragments.rooted.pieces target //
      value = RouteRequest.build fragments.rooted.pieces canonicalRoute target targetPositive} :=
    ⟨RouteRequest.build fragments.rooted.pieces canonicalRoute target targetPositive, rfl⟩
  let routed : {value : RouteRequest fragments.rooted.pieces target (some ordinary) //
      value = raw.val.onNumerator ordinary} := ⟨raw.val.onNumerator ordinary, rfl⟩
  let rawChart : {value : RouteChartRequest faces.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target //
      value = RouteChartRequest.build faces.val.geometry.routeSpine
        (standardDifferential (0 : Fin 1)) domains target targetPositive} :=
    ⟨RouteChartRequest.build faces.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target targetPositive, rfl⟩
  let charts : {value : RouteChartRequest faces.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target (some ordinary) //
      value = rawChart.val.rebudget target targetPositive (some ordinary)} :=
    ⟨rawChart.val.rebudget target targetPositive (some ordinary), rfl⟩
  { inputCache := inputs
    frameData := cachedFrame
    execution := ⟨selected, splitWalk, faces, raw, routed, rawChart, charts⟩ }

namespace Contacts

variable {fragments ordinary target targetPositive}
    (kept : Contacts fragments ordinary target targetPositive)

/-- Rebudget one genuine numerator while retaining every actual contact-geometry and root cache.

The original cached frame, selected Owner, resplit, face assignment, raw
route and raw chart requests are forwarded as complete certified values.
Only the two original numerator-specific rebudget operations execute.
-/
def onNumerator (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    Contacts fragments next target targetPositive :=
  let inputs : Contacts.Inputs fragments next target := ⟨(fragments, next, target), rfl⟩
  let previous : Contacts.Execution (fragments := fragments) (ordinary := ordinary)
      (target := target) (targetPositive := targetPositive) kept.frameData := kept.execution
  let routed : {value : RouteRequest fragments.rooted.pieces target (some next) //
      value = previous.2.2.2.1.val.onNumerator next} :=
    ⟨previous.2.2.2.1.val.onNumerator next, rfl⟩
  let charts : {value : RouteChartRequest previous.2.2.1.val.geometry.routeSpine
      (standardDifferential (0 : Fin 1)) domains target (some next) //
      value = previous.2.2.2.2.2.1.val.rebudget target targetPositive (some next)} :=
    ⟨previous.2.2.2.2.2.1.val.rebudget target targetPositive (some next), rfl⟩
  let execution : Contacts.Execution (fragments := fragments) (ordinary := next)
      (target := target) (targetPositive := targetPositive) kept.frameData :=
    ⟨previous.1, previous.2.1, previous.2.2.1, previous.2.2.2.1,
      routed, previous.2.2.2.2.2.1, charts⟩
  { inputCache := inputs
    frameData := kept.frameData
    execution := execution }

/-- Read the exact actual physical source, genuine numerator and route/chart target. -/
@[expose] def inputs : GridFragments lifted vertex walk spine selection domains ×
    Ordinary (Fibre.frameCurve frame).polynomial × Rational := kept.inputCache.val

/-- All original physical and coefficient inputs are retained with their complete whole factory. -/
theorem inputs_eq : kept.inputs = (fragments, ordinary, target) := kept.inputCache.property

/-- Read the cached whole original frame, rather than recovering an owner from its coordinate. -/
@[expose] def currentFrame : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval (lifted.vertices.coordinate vertex))
  := kept.frameData.val

/-- The actual frame lookup retains its original whole root-frame factory. -/
theorem currentFrame_eq : kept.currentFrame = lifted.frames.frameAt (lifted.vertices.coordinate vertex)
    (lifted.vertices.coordinate_onGrid vertex) := kept.frameData.property

/-- Read the retained operational selection of the original vertex Owner in that SAME frame. -/
@[expose] def selected : OwnerSelection
    (lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex)).owners
    (lifted.vertices.owner lifted.frames vertex) := kept.execution.1.val

/-- Read the retained same-grid resplit of the actual original period walk. -/
@[expose] def splitWalk : Walk framed.bank.grid (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate vertex)
  := kept.execution.2.1.val

/-- The whole resplit cache has the actual original current-grid inclusion factory. -/
theorem splitWalk_eq : kept.splitWalk = (CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk
    (lifted.vertices.coordinate_onGrid vertex) := kept.execution.2.1.property

/-- Read the SAME whole face assignments on the actually cached resplit walk. -/
@[expose] def faces : OwnerWalkFaces lifted.mesh
    ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex))
    (lifted.vertices.owner lifted.frames vertex) := kept.execution.2.2.1.val

/-- The complete face cache consumes the retained whole incoming Owner selection. -/
theorem faces_eq : kept.faces = OwnerWalkFaces.castWalk kept.splitWalk_eq
    (OwnerWalkFaces.ofSelection lifted.mesh kept.splitWalk (lifted.vertices.coordinate_onGrid vertex)
      kept.selected) := kept.execution.2.2.1.property

/-- Read the original canonical-route request before its genuine-numerator rebudgeting. -/
@[expose] def rawRoute : RouteRequest fragments.rooted.pieces target := kept.execution.2.2.2.1.val

/-- The whole raw route comes from the actual retained fragment word and canonical-route geometry. -/
theorem rawRoute_eq : kept.rawRoute = RouteRequest.build fragments.rooted.pieces canonicalRoute target targetPositive :=
  kept.execution.2.2.2.1.property

/-- Read the actual genuine-P request on the SAME original route/contact caches. -/
@[expose] def route : RouteRequest fragments.rooted.pieces target (some ordinary) := kept.execution.2.2.2.2.1.val

/-- The whole P request preserves the retained original route/contact factories. -/
theorem route_eq : kept.route = kept.rawRoute.onNumerator ordinary := kept.execution.2.2.2.2.1.property

/-- Read the original chart/contact request before its genuine-numerator rebudgeting. -/
@[expose] def rawCharts : RouteChartRequest kept.faces.geometry.routeSpine (standardDifferential (0 : Fin 1)) domains
  target := kept.execution.2.2.2.2.2.1.val

/-- Read the actual genuine-P chart request on the SAME retained original chart contacts. -/
@[expose] def charts : RouteChartRequest kept.faces.geometry.routeSpine (standardDifferential (0 : Fin 1)) domains
  target
    (some ordinary) := kept.execution.2.2.2.2.2.2.val

/-- Both request stages enter the same finite numerical minimum before any P-bank observations. -/
@[expose] def minimum : Nat := max kept.route.index kept.charts.index

/-- Numerator rebudgeting retains the SAME complete cached current frame. -/
theorem onNumerator_currentFrame (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).currentFrame = kept.currentFrame := by
  unfold onNumerator currentFrame
  rfl

/-- Numerator rebudgeting retains the original operational Owner selection, including its root comparison. -/
theorem onNumerator_selected (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).selected = kept.selected := by
  unfold onNumerator selected
  rfl

/-- Numerator rebudgeting preserves the literal retained self-resplit walk. -/
theorem onNumerator_splitWalk (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).splitWalk = kept.splitWalk := by
  unfold onNumerator splitWalk
  rfl

/-- Numerator rebudgeting forwards the SAME complete face assignment, without reconstructing it. -/
theorem onNumerator_faces (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).faces = kept.faces := by
  unfold onNumerator faces
  rfl

/-- The retained full face-word count is unchanged by genuine numerator rebudgeting of those SAME caches. -/
theorem onNumerator_length (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).faces.geometry.indexed.length = kept.faces.geometry.indexed.length :=
  congrArg (fun actual : OwnerWalkFaces lifted.mesh
    ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex))
    (lifted.vertices.owner lifted.frames vertex) => actual.geometry.indexed.length) (kept.onNumerator_faces next)

/-- Numerator rebudgeting preserves the original raw route/contact request and every partial endpoint. -/
theorem onNumerator_rawRoute (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).rawRoute = kept.rawRoute := by
  unfold onNumerator rawRoute
  rfl

/-- Numerator rebudgeting preserves the original raw chart/contact request on its same face spine. -/
theorem onNumerator_rawCharts (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    HEq (kept.onNumerator next).rawCharts kept.rawCharts := by
  unfold onNumerator rawCharts
  rfl

/-- The actual new route cache is precisely the original numerator rebudgeting of the retained raw request. -/
theorem onNumerator_route (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    (kept.onNumerator next).route = kept.rawRoute.onNumerator next := by
  unfold onNumerator route rawRoute
  rfl

/-- The actual new chart cache is precisely the original rebudgeting of the retained raw chart request. -/
theorem onNumerator_charts (next : Ordinary (Fibre.frameCurve frame).polynomial) :
    HEq (kept.onNumerator next).charts (kept.rawCharts.rebudget target targetPositive (some next)) := by
  unfold onNumerator charts rawCharts
  rfl

/-- The selected comparison is the actual cached-frame operation under its whole frame equality. -/
theorem selected_eq : kept.selected = Eq.mp
    (congrArg (fun current : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval (lifted.vertices.coordinate vertex))
      => OwnerSelection current.owners (lifted.vertices.owner lifted.frames vertex))
      kept.currentFrame_eq) (kept.currentFrame.select (lifted.vertices.owner lifted.frames vertex)) :=
  kept.execution.1.property

/-- Whole cached-frame transport preserves the actual retained vertex's selected sheet. -/
private theorem cached_selection_index
    (cached : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval (lifted.vertices.coordinate vertex)))
    (same : cached = lifted.frames.frameAt (lifted.vertices.coordinate vertex)
      (lifted.vertices.coordinate_onGrid vertex)) :
    (Eq.mp (congrArg (fun current : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval (lifted.vertices.coordinate
      vertex)) => OwnerSelection current.owners
        (lifted.vertices.owner lifted.frames vertex)) same)
      (cached.select (lifted.vertices.owner lifted.frames vertex))).index = lifted.vertices.sheet vertex := by
  cases same
  exact OwnerFrame.select_self
    (lifted.frames.frameAt (lifted.vertices.coordinate vertex) (lifted.vertices.coordinate_onGrid vertex))
    (lifted.vertices.sheet vertex)

/-- The actual incoming Owner selects its original frame sheet, independently of its local chart label. -/
theorem selected_sheet : kept.selected.index = lifted.vertices.sheet vertex :=
  (congrArg (fun selected => selected.index) kept.selected_eq).trans
    (cached_selection_index kept.currentFrame kept.currentFrame_eq)

/-- The retained face assignment starts on that same genuinely selected original root sheet. -/
theorem faces_sheet : kept.faces.sheet = lifted.vertices.sheet vertex :=
  (congrArg (fun actual => actual.sheet) kept.faces_eq).trans
    ((OwnerWalkFaces.castWalk_sheet kept.splitWalk_eq
      (OwnerWalkFaces.ofSelection lifted.mesh kept.splitWalk (lifted.vertices.coordinate_onGrid vertex)
        kept.selected)).trans kept.selected_sheet)

/-- The retained whole face factory reads the actual default geometry on its own selected sheet.

The cached walk and complete face construction are transported together;
indexed-edge equality alone is not used as a geometry factory.
-/
theorem faces_geometry : kept.faces.geometry = SkeletonFaceAssignments.walkFaces lifted.mesh
    ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex))
    kept.faces.sheet := by
  rcases kept with ⟨_inputs, retainedFrame, execution⟩
  rcases execution with ⟨selected, cachedWalk, faces, _raw, _routed, _rawChart, _charts⟩
  rcases cachedWalk with ⟨picked, pickedFactory⟩
  cases pickedFactory
  change faces.val.geometry = SkeletonFaceAssignments.walkFaces lifted.mesh
    ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex))
    faces.val.sheet
  have geometry : faces.val.geometry = SkeletonFaceAssignments.walkFaces lifted.mesh
      ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk
        (lifted.vertices.coordinate_onGrid vertex)) selected.val.index :=
    congrArg (fun actual => actual.geometry) faces.property
  have sheet : faces.val.sheet = selected.val.index :=
    congrArg (fun actual => actual.sheet) faces.property
  exact geometry.trans (congrArg (SkeletonFaceAssignments.walkFaces lifted.mesh
    ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk (lifted.vertices.coordinate_onGrid vertex)))
    sheet.symm)

/-- A genuine same-grid chain comparison reads this original closed cycle under every antisymmetric valuation.

The actual self-resplit comparison uses the old branch-reference loops
and retains all signed retracings. Coordinate closure alone supplies no
root or cycle relation. The scalar equality is a readback of that actual
comparison on the original retained sheet.
-/
theorem original_value (value : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    wordValue value kept.faces.geometry.indexed = wordValue value
      (lifted.edges.indexedEdges lifted.vertices walk.closed.walk (lifted.vertices.sheet vertex)) := by
  have comparison := framed.bank.grid.self_resplit_comparison lifted.edges lifted.vertices
    (fun point member => (LoopMonodromy.BranchCellBank.referenceAt framed.bank.toBranchCellBank point member).toLoop)
    walk.closed.walk (lifted.vertices.coordinate_onGrid vertex)
  have liftedWord := congrArg (wordValue value) kept.faces.indexed_eq
  exact liftedWord.trans ((comparison.values value anti kept.faces.sheet).trans
    (congrArg (fun sheet => lifted.edges.chainValue lifted.vertices value walk.closed.walk sheet) kept.faces_sheet))

variable {points : List Canonical} {numericTolerance : Rational} {stage : Nat} {numerator : CoefficientPolynomial}
    {budgets : FaceMeshBudgets (standardDifferential (0 : Fin 1)) points numericTolerance
      (numerator := numerator) domains}
    {primitives : FacePrimitiveBank (standardDifferential (0 : Fin 1)) stage
      (numerator := numerator) domains}
    (shared : FaceSharedMeshes budgets primitives)

/-- The real P route retains the exact selected-route values on this SAME actual bank. -/
theorem route_values : kept.route.requests.values shared = fragments.rooted.pieces.map
    (fun piece => Fragment.RouteContacts.routeValue piece (canonicalRoute piece) shared) := by
  have supplied := congrArg (fun actual => actual.requests.values shared) kept.route_eq
  have rebudgeted := congrArg (fun actual => actual.values shared)
    (RouteRequest.onNumerator_requests kept.rawRoute ordinary)
  have original := Fragment.RouteWords.RouteRequests.onNumerator_values ordinary
    (Approximation.Rational.Budget.Aggregate.perTerm_positive kept.rawRoute.positive fragments.rooted.pieces.length)
    shared kept.rawRoute.requests
  have raw := congrArg (fun actual : RouteRequest fragments.rooted.pieces target => actual.requests.values shared)
    kept.rawRoute_eq
  have built := Fragment.RouteWords.RouteRequests.build_values
    (Approximation.Rational.Budget.Aggregate.perTerm target fragments.rooted.pieces.length)
    (Approximation.Rational.Budget.Aggregate.perTerm_positive targetPositive fragments.rooted.pieces.length)
    canonicalRoute fragments.rooted.pieces shared
  exact supplied.trans (rebudgeted.trans (original.trans (raw.trans built)))

/-- The actual cached canonical-route request reads the SAME selected current-grid period mesh word.

The original initial PathSources and cached root closure supply the whole
signed grouping. Stationary fragments keep their original zero route
readings in the source occurrence list, rather than being discarded from
the execution cache or used to identify different root Owners.
-/
theorem routed_sum : gaussianSum (kept.route.requests.values shared) = gaussianSum
    (kept.faces.geometry.values (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route)) := by
  have lists := congrArg gaussianSum (kept.route_values shared)
  have pieces := congrArg (fun actual => gaussianSum (actual.map
    (fun piece => Fragment.RouteContacts.routeValue piece (canonicalRoute piece) shared))) fragments.rooted_pieces
  have grouped := Inclusion.PeriodRoutes.routed_sum_of_sources (period := walk)
    fragments.sources (pathSources lifted vertex walk spine) fragments.roots
    (lifted.vertices.coordinate_onGrid vertex) (CoordinateInclusion.refl framed.bank.grid) kept.faces shared
  have geometry := congrArg (fun assigned : lifted.mesh.PathFaces
      ((CoordinateInclusion.refl framed.bank.grid).resplit walk.closed.walk
        (lifted.vertices.coordinate_onGrid vertex)).path =>
    gaussianSum (assigned.values (fun _ route => Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route)))
      kept.faces_geometry
  exact lists.trans (pieces.trans (grouped.trans geometry.symm))

end Contacts

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine.GridFragments

end

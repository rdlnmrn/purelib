module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.WeightedPair
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! Two standard differential comparisons and the actual cut-area identity
retain the same numerical bank and the same two triangle vectors. -/
open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods (ChordPeriods)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodRelation (PeriodRelationReadings
  PeriodRelationPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests (RouteRequests)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

namespace PairedAreaReadings

/-- The standard cycle's actual intersection row for the lifted grid's canonical integral pairing. -/
def CanonicalIntersectionRow {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree}
    {base : Meshes.FramedPuncturedGrid curve (BranchConfiguration.configurationOfData curve branches).branches higher}
    (lifted : Meshes.LiftedPuncturedGrid base) (cycle : Fin genus) :=
  TourIntersection.IntersectionRow lifted lifted.cutIntegralPairing cycle

end PairedAreaReadings

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {cycle first second : Fin genus}
  {row : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings.CanonicalIntersectionRow lifted
    cycle} {source : Differential genus}
  {programs : CutChordPrograms lifted source}
  {firstComponents : ComponentSamples
    programs.programs first}
  {secondComponents : ComponentSamples
    programs.programs second}

namespace PairedAreaReadings

/-- Both standard differential comparisons share the cut-area bank and exact triangle values.

The two shared-bank predicates retain their original differential owners, and both triangle equalities bind the actual
cut sample. -/
def PairedAreaOwnership
    {firstPeriods : TourChordPeriods.ChordPeriods row.span programs firstComponents}
    {secondPeriods : TourChordPeriods.ChordPeriods row.span programs secondComponents}
    {segments : Data.Vector.DependentVector (fun entry => PeriodSegmentBanks.SegmentBank (programs.programs.programs
      entry).period)}
    {domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {minimum numericalFloor : Nat} {firstTarget secondTarget : Fraction.Rational} {extraPoints : List
      Data.Gaussian.Basic.Canonical}
    {cutTarget : Fraction.Rational} {cutFloor : Nat}
    {cut : RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget cutFloor}
    {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    (left : PeriodRelation.PeriodRelationReadings firstPeriods segments domains minimum numericalFloor firstTarget
      extraPoints)
    (right : PeriodRelation.PeriodRelationReadings secondPeriods segments domains minimum numericalFloor secondTarget
      extraPoints)
    (area : CutPairingRequest.Readings cut cache) : Prop :=
  PeriodRelationReadings.SharedAt left (cache.get first) ∧
  PeriodRelationReadings.SharedAt right (cache.get second) ∧
  area.left.values = left.readings.standard.triangles.values ∧
  area.right.values = right.readings.standard.triangles.values

end PairedAreaReadings

set_option genInjectivity false in
/-- Two standard period comparisons and the actual cut-area reading on one shared numerical bank.

Retained ownership equalities identify both triangle vectors with the standard readers, and the original cut threshold
is already paid. -/
structure PairedAreaReadings
    (firstPeriods : TourChordPeriods.ChordPeriods row.span programs firstComponents)
    (secondPeriods : TourChordPeriods.ChordPeriods row.span programs secondComponents)
    (segments : Data.Vector.DependentVector (fun entry => PeriodSegmentBanks.SegmentBank (programs.programs.programs
      entry).period))
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (minimum numericalFloor : Nat) (firstTarget secondTarget : Fraction.Rational) (extraPoints : List
      Data.Gaussian.Basic.Canonical)
    {cutTarget : Fraction.Rational} {cutFloor : Nat}
    (cut : RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget cutFloor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) : Type 3 where
  /-- The retained first standard differential comparison. -/ left : PeriodRelation.PeriodRelationReadings firstPeriods
    segments domains minimum numericalFloor firstTarget extraPoints
  /-- The retained second standard differential comparison. -/ right : PeriodRelation.PeriodRelationReadings
    secondPeriods segments domains minimum numericalFloor secondTarget extraPoints
  /-- The actual cut-area reading on the supplied shared numerical bank. -/ area : CutPairingRequest.Readings cut cache
  /-- Both comparison readers use this bank and exactly these cut-area triangle values. -/ ownership :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PairedAreaReadings.PairedAreaOwnership left right area
  /-- The original cut comparison threshold is paid by the supplied stage. -/ cut_later : cut.index ≤ stage

constructive_injectivity PairedAreaReadings

namespace PairedAreaReadings
variable {firstPeriods : ChordPeriods
  row.span programs firstComponents}
  {secondPeriods : ChordPeriods row.span
    programs secondComponents}
  {segments : Purelib.Data.Vector.DependentVector (fun entry =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (programs.programs.programs
    entry).period)}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars}
  {minimum numericalFloor : Nat} {firstTarget secondTarget : Rational} {extraPoints : List
    Purelib.Data.Gaussian.Basic.Canonical}
  {cutTarget : Rational} {cutFloor : Nat}

/-- All request floors precede the supplied common stage. The triangle caches acquired by the standard readers become
the cut-area caches directly. -/
def build
    (firstPreparation : PeriodRelation.PeriodRelationPreparation firstPeriods segments domains minimum numericalFloor
      firstTarget)
    (secondPreparation : PeriodRelation.PeriodRelationPreparation secondPeriods segments domains minimum numericalFloor
      secondTarget)
    (firstCharts : FamilyRouteRequests.RouteRequests firstPreparation.budget)
    (secondCharts : FamilyRouteRequests.RouteRequests secondPreparation.budget)
    (firstStandard : PeriodRelationReadings.StandardPreparation firstPreparation firstCharts extraPoints)
    (secondStandard : PeriodRelationReadings.StandardPreparation secondPreparation secondCharts extraPoints)
    (cut : RequestedCutPairing.CutPairingRequest lifted domains first second cutTarget cutFloor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage)
    (later : max cut.index (max firstStandard.index secondStandard.index) ≤ stage) :
    PairedAreaReadings firstPeriods secondPeriods
      segments domains minimum numericalFloor firstTarget secondTarget extraPoints cut cache := by
  have standardLater := (Nat.Order.le_max_right _ _).trans later
  have firstLater := (Nat.Order.le_max_left _ _).trans standardLater
  have secondLater := (Nat.Order.le_max_right _ _).trans standardLater
  let left := PeriodRelationReadings.readWith firstPreparation firstCharts firstStandard (cache.get first) firstLater
  let right := PeriodRelationReadings.readWith secondPreparation secondCharts secondStandard (cache.get second)
    secondLater
  have leftShared := PeriodRelationReadings.readWith_shared firstPreparation firstCharts firstStandard (cache.get first)
    firstLater
  have rightShared := PeriodRelationReadings.readWith_shared secondPreparation secondCharts secondStandard (cache.get
    second) secondLater
  let leftTriangles := left.sharedTriangles (cache.get first) leftShared
  let rightTriangles := right.sharedTriangles (cache.get second) rightShared
  let area := Readings.buildWith cut cache leftTriangles.val rightTriangles.val
  exact ⟨left, right, area, ⟨leftShared, rightShared, leftTriangles.property, rightTriangles.property⟩,
    (Nat.Order.le_max_left _ _).trans later⟩

end PairedAreaReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

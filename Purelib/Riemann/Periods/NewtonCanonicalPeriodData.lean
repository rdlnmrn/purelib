module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
public import Purelib.Riemann.Periods.NewtonRequestedPairedPeriods
public import Purelib.Riemann.Periods.NewtonPeriodGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes

public section

/-! Retained geometric, original-period and routing data for the canonical
comparison on one retained Newton geometry. -/

namespace Purelib.Riemann.Periods.NewtonCanonicalPeriodData

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered
  anchor)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments (walkFaces)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonRequestedPairedPeriods (NewtonPeriodRequest)
open
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  (LiftedSources)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (RouteRequest canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank (FaceScalarBudgets)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {differential cycle : Fin genus}
  {target : Rational} {minimum : Nat}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid in
/-- Retain lifted owner faces for the resplit original A-cycle on the Newton period geometry.

The construction uses the original cycle walk and anchor owner, transporting them through the same retained inclusion
and lifted mesh. -/
@[expose] def aCanonicalFaces (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :=
  OwnerWalkFaces.build boundary.lifted.mesh
    (boundary.grid.shrunk.included.resplit (prepared.aWalk cycle).closed.walk
      (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)))
    (boundary.grid.shrunk.included.vertex (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)))
    (lifted.vertices.owner lifted.frames (BasedBranchBank.anchor lifted sheet))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- Assign the resplit A-cycle walk to faces with the retained canonical lift's sheet. -/
@[expose] def aCanonicalAssigned (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :=
  SkeletonFaceAssignments.walkFaces boundary.lifted.mesh
    (boundary.grid.shrunk.included.resplit (prepared.aWalk cycle).closed.walk
      (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)))
    (aCanonicalFaces (cycle := cycle) prepared boundary).sheet

open Purelib.Approximation.Rational.Budget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Data in
/-- The exact Newton period request for the assigned A-cycle's per-occurrence share.

One thirty-second of the original target is divided among its actual indexed occurrences, preserving the differential,
cycle, stage floor and domain bank. -/
@[expose] def aCanonicalRequestType (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) (minimum : Nat) :=
  NewtonPeriodRequest prepared boundary.grid differential cycle minimum
    (Aggregate.perTerm (target / 32) (aCanonicalAssigned (cycle := cycle) prepared boundary).indexed.length)
      boundary.domains

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- The lifted source bank for the actual A-entries of the retained period request. -/
@[expose] def aCanonicalSourcesType {prepared : PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    (request : aCanonicalRequestType prepared boundary differential cycle target minimum) :=
  SheetEntries.LiftedSources boundary.lifted.mesh request.aEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- The route request on those retained A-source pieces at one thirty-second of the target. -/
@[expose] def aCanonicalRouteType {prepared : PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    {request : aCanonicalRequestType prepared boundary differential cycle target minimum}
    (sources : aCanonicalSourcesType request) :=
  RouteWords.RouteRequest (LiftedSources.pieces sources) (target / 32)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- The stored A-route is the canonical builder's route on those exact source pieces. -/
@[expose] def aCanonicalRouteEq {prepared : PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    {request : aCanonicalRequestType prepared boundary differential cycle target minimum}
    {sources : aCanonicalSourcesType request} (route : aCanonicalRouteType sources) : Prop :=
  route = RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute (target / 32) route.positive

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Data in
/-- The chart request on the assigned A-cycle's original route spine.

It uses the selected standard differential, the retained domain bank and one thirty-second of the target. -/
@[expose] def aCanonicalChartsType (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) :=
  RouteChartRequests.RouteChartRequest
    (aCanonicalAssigned (cycle := cycle) prepared boundary).routeSpine
    (standardDifferential differential) boundary.domains (target / 32)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Data in
set_option genInjectivity false in
/-- Retained period, source, route and chart data for the canonical A-cycle comparison.

Every component uses the same original period geometry, differential, cycle and target. Dependent fields preserve the
actual source pieces and the canonical route's construction equation. -/
structure ACanonicalPreparation (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) (minimum : Nat) : Type 2 where
  /-- The exact A-cycle period request with its original floor and per-occurrence budget. -/ request :
    aCanonicalRequestType prepared boundary differential cycle target minimum
  /-- The retained lifted sources of that request's entries. -/ sources : aCanonicalSourcesType request
  /-- The actual route request on those retained source pieces. -/ route : aCanonicalRouteType sources
  /-- The retained route equals the canonical construction on the same pieces. -/ route_eq : aCanonicalRouteEq route
  /-- The retained standard-differential chart request on the assigned route spine. -/ charts : aCanonicalChartsType
    prepared boundary differential cycle target

constructive_injectivity ACanonicalPreparation

namespace ACanonicalPreparation

variable {prepared : Prepared paired}
  {boundary : PeriodGeometry base.bank.toBranchCellBank}

open Purelib.Approximation.Rational.Budget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests in
open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
/-- Construct the canonical A-cycle preparation from a positive target and minimum stage.

Build the period request and retain its lifted source pieces, canonical route and chart request, all using the original
period geometry and the prescribed target shares. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    ACanonicalPreparation prepared boundary differential cycle target minimum :=
  let partPositive := Field.div_pos_direct positive (by decide +kernel : (0 : Rat.Fraction.Rational) < 32)
  let request := NewtonPeriodRequest.build prepared boundary.grid differential cycle minimum
    (Aggregate.perTerm (target / 32) (aCanonicalAssigned (cycle := cycle) prepared boundary).indexed.length)
    (Aggregate.perTerm_positive partPositive _) boundary.domains
  let sources := LiftedSources.build boundary.lifted.mesh request.aEntries
  let route := RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute (target / 32) partPositive
  let charts := RouteChartRequest.build
    (aCanonicalAssigned (cycle := cycle) prepared boundary).routeSpine
    (standardDifferential differential) boundary.domains (target / 32) partPositive
  ⟨request, sources, route, rfl, charts⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank in
/-- The maximum of the retained scalar, route and chart refinement indices. -/
@[expose] def numericalIndex (data : ACanonicalPreparation prepared boundary differential cycle target minimum) : Nat :=
  max (FaceScalarBudgets.index data.request.scalars) (max data.route.index data.charts.index)

end ACanonicalPreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid in
/-- Retain lifted owner faces for the resplit original B-cycle on the Newton period geometry.

The construction uses the original cycle walk and anchor owner, transporting them through the same retained inclusion
and lifted mesh. -/
@[expose] def bCanonicalFaces (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :=
  OwnerWalkFaces.build boundary.lifted.mesh
    (boundary.grid.shrunk.included.resplit (prepared.bWalk cycle).closed.walk
      (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)))
    (boundary.grid.shrunk.included.vertex (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)))
    (lifted.vertices.owner lifted.frames (BasedBranchBank.anchor lifted sheet))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- Assign the resplit B-cycle walk to faces with the retained canonical lift's sheet. -/
@[expose] def bCanonicalAssigned (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank) :=
  SkeletonFaceAssignments.walkFaces boundary.lifted.mesh
    (boundary.grid.shrunk.included.resplit (prepared.bWalk cycle).closed.walk
      (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)))
    (bCanonicalFaces (cycle := cycle) prepared boundary).sheet

open Purelib.Approximation.Rational.Budget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Data in
/-- The exact Newton period request for the assigned B-cycle's per-occurrence share.

One thirty-second of the original target is divided among its actual indexed occurrences, preserving the differential,
cycle, stage floor and domain bank. -/
@[expose] def bCanonicalRequestType (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) (minimum : Nat) :=
  NewtonPeriodRequest prepared boundary.grid differential cycle minimum
    (Aggregate.perTerm (target / 32) (bCanonicalAssigned (cycle := cycle) prepared boundary).indexed.length)
      boundary.domains

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- The lifted source bank for the actual B-entries of the retained period request. -/
@[expose] def bCanonicalSourcesType {prepared : PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    (request : bCanonicalRequestType prepared boundary differential cycle target minimum) :=
  SheetEntries.LiftedSources boundary.lifted.mesh request.bEntries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- The route request on those retained B-source pieces at one thirty-second of the target. -/
@[expose] def bCanonicalRouteType {prepared : PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    {request : bCanonicalRequestType prepared boundary differential cycle target minimum}
    (sources : bCanonicalSourcesType request) :=
  RouteWords.RouteRequest (LiftedSources.pieces sources) (target / 32)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
/-- The stored B-route is the canonical builder's route on those exact source pieces. -/
@[expose] def bCanonicalRouteEq {prepared : PeriodPrograms.Prepared paired}
    {boundary : PeriodGeometry base.bank.toBranchCellBank}
    {request : bCanonicalRequestType prepared boundary differential cycle target minimum}
    {sources : bCanonicalSourcesType request} (route : bCanonicalRouteType sources) : Prop :=
  route = RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute (target / 32) route.positive

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Data in
/-- The chart request on the assigned B-cycle's original route spine.

It uses the selected standard differential, the retained domain bank and one thirty-second of the target. -/
@[expose] def bCanonicalChartsType (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) :=
  RouteChartRequests.RouteChartRequest
    (bCanonicalAssigned (cycle := cycle) prepared boundary).routeSpine
    (standardDifferential differential) boundary.domains (target / 32)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Data in
set_option genInjectivity false in
/-- Retained period, source, route and chart data for the canonical B-cycle comparison.

Every component uses the same original period geometry, differential, cycle and target. Dependent fields preserve the
actual source pieces and the canonical route's construction equation. -/
structure BCanonicalPreparation (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) (minimum : Nat) : Type 2 where
  /-- The exact B-cycle period request with its original floor and per-occurrence budget. -/ request :
    bCanonicalRequestType prepared boundary differential cycle target minimum
  /-- The retained lifted sources of that request's entries. -/ sources : bCanonicalSourcesType request
  /-- The actual route request on those retained source pieces. -/ route : bCanonicalRouteType sources
  /-- The retained route equals the canonical construction on the same pieces. -/ route_eq : bCanonicalRouteEq route
  /-- The retained standard-differential chart request on the assigned route spine. -/ charts : bCanonicalChartsType
    prepared boundary differential cycle target

constructive_injectivity BCanonicalPreparation

namespace BCanonicalPreparation

variable {prepared : Prepared paired}
  {boundary : PeriodGeometry base.bank.toBranchCellBank}

open Purelib.Approximation.Rational.Budget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment in
open
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries
  in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests in
open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
/-- Construct the canonical B-cycle preparation from a positive target and minimum stage.

Build the period request and retain its lifted source pieces, canonical route and chart request, all using the original
period geometry and the prescribed target shares. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired)
    (boundary : PeriodGeometry base.bank.toBranchCellBank)
    (differential cycle : Fin genus) (target : Rat.Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    BCanonicalPreparation prepared boundary differential cycle target minimum :=
  let partPositive := Field.div_pos_direct positive (by decide +kernel : (0 : Rat.Fraction.Rational) < 32)
  let request := NewtonPeriodRequest.build prepared boundary.grid differential cycle minimum
    (Aggregate.perTerm (target / 32) (bCanonicalAssigned (cycle := cycle) prepared boundary).indexed.length)
    (Aggregate.perTerm_positive partPositive _) boundary.domains
  let sources := LiftedSources.build boundary.lifted.mesh request.bEntries
  let route := RouteRequest.build (LiftedSources.pieces sources) RouteWords.canonicalRoute (target / 32) partPositive
  let charts := RouteChartRequest.build
    (bCanonicalAssigned (cycle := cycle) prepared boundary).routeSpine
    (standardDifferential differential) boundary.domains (target / 32) partPositive
  ⟨request, sources, route, rfl, charts⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank in
/-- The maximum of the retained scalar, route and chart refinement indices. -/
@[expose] def numericalIndex (data : BCanonicalPreparation prepared boundary differential cycle target minimum) : Nat :=
  max (FaceScalarBudgets.index data.request.scalars) (max data.route.index data.charts.index)

end BCanonicalPreparation

end Purelib.Riemann.Periods.NewtonCanonicalPeriodData

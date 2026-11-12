module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests.BasisSourceRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Riemann.Normalization

public section

/-! Basis source schedules on the original chart mesh, including its midpoint
tree. Polynomial and root-reading thresholds are separate. Evaluation
reuses the mesh's retained roots at both extremes and every midpoint. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Prepared Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Tree Mesh ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (TreeReadings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

set_option genInjectivity false in
/-- The retained basis source locations and request at one original prepared chart endpoint.

Each source row keeps its original owner and the source model floor separately from the chart root-reading stage. -/
structure EndpointSources (prepared : Prepared regular model parameter target floor)
    (covers : BasisSourceCovers parent) (sourceTarget : Coordinate) (sourceFloor :
      Nat) where
  /-- The original per-basis source locations joined to this exact prepared chart endpoint. -/ locations :
    BasisSourceLocations regular prepared.point covers
  /-- The positive basis source request on the exact retained source owners. -/ request :
    BasisSourceRequest locations.owners sourceTarget sourceFloor

constructive_injectivity EndpointSources

namespace EndpointSources

variable {prepared : Prepared regular model parameter
  target floor}

/-- Locate each original basis source at the retained chart endpoint and prepare its positive source request. -/
@[expose] def build (prepared : Prepared regular model parameter target floor) (covers :
  BasisSourceCovers parent)
    (sourceTarget : Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    EndpointSources prepared covers sourceTarget
      sourceFloor :=
  let locations := BasisSourceLocations.build regular prepared.point covers
  ⟨locations, BasisSourceRequest.build locations.owners sourceTarget positive sourceFloor⟩

variable {index stage minimum : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {comparison : ArcSamples.Data regular cell}
  {sample : ArcSamples.Sample comparison capSample}

set_option genInjectivity false in
/-- The actual source/chart comparison at the original retained endpoint reading.

The exact source-sample readback preserves the shared numerical bank and original root coordinate. -/
structure Evaluation (sources : EndpointSources
  prepared covers sourceTarget sourceFloor)
    (charts : ChartRequest sources.request polynomials minimum)
    (bank : BasisSourceLocations.SampleBank covers index)
    (reading : Reading regular model sample parameter target floor stage) where
  /-- The basis endpoint samples read from the supplied original shared polynomial bank. -/ samples :
    Samples sources.locations.owners polynomials
  /-- The retained endpoint samples are exactly the original locations' reads from that bank. -/ samples_eq : samples =
    sources.locations.samples bank polynomials
  /-- The source/chart comparison using the actual original endpoint root coordinate and reading stage. -/ evaluated :
    charts.Evaluation samples reading.root.coordinate stage

constructive_injectivity Evaluation

/-- Transport the original reading along its prepared-owner equality, then consume the existing numerical bank without
resampling its root or inverses. -/
@[expose] def evaluate (sources : EndpointSources
  prepared covers sourceTarget sourceFloor)
    (charts : ChartRequest sources.request polynomials minimum)
    (bank : BasisSourceLocations.SampleBank covers index)
    (reading : Reading regular model sample parameter target floor stage)
    (owner : reading.prepared = prepared) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : sources.request.index ≤ index) (later : charts.stage ≤ stage) :
      Evaluation sources charts bank
      reading := by
  have pointEq : reading.prepared.point = prepared.point := congrArg (fun value => value.point) owner
  let view := ReadingView.ofEqual pointEq reading.root
  let samples := sources.locations.samples bank polynomials
  let evaluated := charts.evaluate samples view.reading branch modelLater later
  have coordinateEq : view.reading.coordinate = reading.root.coordinate := ReadingView.coordinate_eq pointEq
    reading.root
  exact ⟨samples, rfl, coordinateEq ▸ evaluated⟩

end EndpointSources

/-- Source requests for every internal dyadic vertex, prepared before choosing any polynomial or reading stage. -/
@[expose] def BasisTreeSources (covers : BasisSourceCovers parent) (sourceTarget :
  Coordinate) (sourceFloor : Nat) :
    {depth : Nat} → {first last : Coordinate} → Tree regular model target floor depth
      first last → Type 2
  | _, _, _, .leaf _ _ => PUnit
  | _, _, _, .node middle left right =>
    EndpointSources middle covers sourceTarget
    sourceFloor ×
      EndpointSchedule.BasisTreeSources covers sourceTarget
        sourceFloor left × EndpointSchedule.BasisTreeSources
        covers sourceTarget sourceFloor right

namespace BasisTreeSources

/-- Prepare each actual original midpoint's basis source request, preserving the retained tree shape. -/
@[expose] def build (covers : BasisSourceCovers parent) (sourceTarget :
  Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    BasisTreeSources covers sourceTarget sourceFloor
      tree
  | _, _, _, .leaf _ _ => ⟨⟩
  | _, _, _, .node middle left right =>
      ⟨EndpointSources.build middle covers sourceTarget positive sourceFloor,
        BasisTreeSources.build covers
          sourceTarget positive sourceFloor left,
          BasisTreeSources.build covers
          sourceTarget positive sourceFloor right⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- The maximum source-polynomial stage of the original midpoint requests, retaining the supplied floor at leaves. -/
@[expose] def index : {depth : Nat} → {first last : Coordinate} → (tree : Tree regular
  model target floor depth first last) →
    BasisTreeSources covers sourceTarget sourceFloor
      tree → Nat
  | _, _, _, .leaf _ _, _ => sourceFloor
  | _, _, _, .node _ left right, sources => max sources.1.request.index
      (max (index left sources.2.1) (index right sources.2.2))

variable {index minimum : Nat} {box : Geometry.Rational.Box}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- The dependent basis source chart plans on every midpoint of the original retained dyadic tree. -/
@[expose] def Plans (polynomials : RegularBasisPolynomials cap index box) (minimum : Nat) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    BasisTreeSources covers sourceTarget sourceFloor
      tree → Type 2
  | _, _, _, .leaf _ _, _ => PUnit
  | _, _, _, .node _ left right, sources => ChartRequest sources.1.request polynomials minimum ×
      BasisTreeSources.Plans polynomials
        minimum left sources.2.1 ×
        BasisTreeSources.Plans polynomials
        minimum right sources.2.2

namespace Plans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- Prepare every original midpoint comparison on the same retained basis polynomial bank. -/
@[expose] def build (polynomials : RegularBasisPolynomials cap index box) (minimum : Nat) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    (sources : BasisTreeSources covers sourceTarget
      sourceFloor tree) → Plans
      polynomials minimum tree sources
  | _, _, _, .leaf _ _, _ => ⟨⟩
  | _, _, _, .node _ left right, sources =>
      ⟨ChartRequest.build sources.1.request polynomials minimum,
        Plans.build
          polynomials minimum left sources.2.1,
          Plans.build
          polynomials minimum right sources.2.2⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans in
/-- The maximum root-reading stage of the original midpoint plans, retaining the supplied minimum at leaves. -/
@[expose] def stage : {depth : Nat} → {first last : Coordinate} → (tree : Tree regular
  model target floor depth first last) →
    (sources : BasisTreeSources covers sourceTarget
      sourceFloor tree) → Plans
      polynomials minimum tree sources → Nat
  | _, _, _, .leaf _ _, _, _ => minimum
  | _, _, _, .node _ left right, sources, plans => max plans.1.stage
      (max (stage left sources.2.1 plans.2.1) (stage right sources.2.2 plans.2.2))

variable {capSample : Cap.Primitives.Sample cap differential index box}
  {comparison : ArcSamples.Data regular cell}
  {sample : ArcSamples.Sample comparison capSample} {readingStage :
    Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- Every midpoint comparison is tied to the reading retained by the original chart tree, and therefore to the very path
used by its area certificate. -/
@[expose] def Evaluation (bank : BasisSourceLocations.SampleBank covers index) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    (sources : BasisTreeSources covers sourceTarget
      sourceFloor tree) →
    Plans polynomials minimum tree
      sources → TreeReadings sample readingStage tree → Type 2
  | _, _, _, .leaf _ _, _, _, _ => PUnit
  | _, _, _, .node _ left right, sources, plans, readings =>
      EndpointSources.Evaluation sources.1 plans.1
        bank readings.1.reading ×
        Plans.Evaluation
          bank left sources.2.1 plans.2.1 readings.2.1 ×
        Plans.Evaluation
          bank right sources.2.2 plans.2.2 readings.2.2

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans in
/-- Evaluate each original midpoint comparison using its retained chart-tree reading and the common paid model and
reading stages. -/
@[expose] def evaluate (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    {depth : Nat} → {first last : Coordinate} → (tree : Tree regular model target floor
      depth first last) →
    (sources : BasisTreeSources covers sourceTarget
      sourceFloor tree) →
    (plans : Plans polynomials
      minimum tree sources) → (readings : TreeReadings sample readingStage tree) →
    BasisTreeSources.index tree sources ≤ index →
      stage tree sources plans ≤ readingStage →
    Evaluation bank tree
      sources plans readings
  | _, _, _, .leaf _ _, _, _, _, _, _ => ⟨⟩
  | _, _, _, .node _ left right, sources, plans, readings, modelLater, later =>
      ⟨sources.1.evaluate plans.1 bank readings.1.reading readings.1.owner branch
          ((Data.Nat.Order.le_max_left _ _).trans modelLater) ((Data.Nat.Order.le_max_left _ _).trans
            later),
        Plans.evaluate bank
          branch left sources.2.1 plans.2.1 readings.2.1
          ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans modelLater))
          ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)),
        Plans.evaluate bank
          branch right sources.2.2 plans.2.2 readings.2.2
          ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans modelLater))
          ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later))⟩

end Plans
end BasisTreeSources

namespace Mesh

variable {depth : Nat} {mesh : Mesh regular model depth
  target floor}

set_option genInjectivity false in
/-- Requests for both extreme vertices and every midpoint are selected before the shared polynomial stage, retaining the
original mesh owners. -/
structure BasisEndpoints (mesh : Mesh regular model depth target floor)
    (covers : BasisSourceCovers parent) (sourceTarget : Coordinate) (sourceFloor :
      Nat) where
  /-- The basis source requests at the exact original mesh's first prepared endpoint. -/ first :
    EndpointSources mesh.first covers sourceTarget
    sourceFloor
  /-- The basis source requests at the exact original mesh's last prepared endpoint. -/ last :
    EndpointSources mesh.last covers sourceTarget
    sourceFloor
  /-- The common cached source-polynomial stage for the original endpoint and midpoint requests. -/ index : Nat
  /-- The basis source requests on all actual midpoints of the retained original mesh tree. -/ tree :
    BasisTreeSources covers sourceTarget sourceFloor
    mesh.tree
  /-- The source stage is the maximum of all retained midpoint and extreme-vertex request stages. -/ index_eq : index =
    max (BasisTreeSources.index mesh.tree tree) (max
    first.request.index last.request.index)

constructive_injectivity BasisEndpoints

namespace BasisEndpoints

/-- Prepare both original extreme endpoints and every midpoint, then cache their common source-polynomial stage. -/
@[expose] def build (mesh : Mesh regular model depth target floor) (covers :
  BasisSourceCovers parent)
    (sourceTarget : Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    BasisEndpoints mesh covers sourceTarget
      sourceFloor :=
  let first := EndpointSources.build mesh.first
    covers sourceTarget positive sourceFloor
  let last := EndpointSources.build mesh.last covers
    sourceTarget positive sourceFloor
  let tree := BasisTreeSources.build covers
    sourceTarget positive sourceFloor mesh.tree
  ⟨first, last, max (BasisTreeSources.index mesh.tree
    tree) (max first.request.index last.request.index), tree, rfl⟩

variable {index stage minimum : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {comparison : ArcSamples.Data regular cell}
  {sample : ArcSamples.Sample comparison capSample}
  {charts : ChartMesh mesh capSample minimum}

set_option genInjectivity false in
/-- The original mesh's complete basis endpoint and midpoint chart schedule.

One shared polynomial bank supplies all plans, with a reading maximum also paying the original chart mesh. -/
structure Plan (sources : BasisEndpoints mesh
  covers sourceTarget sourceFloor)
    (charts : ChartMesh mesh capSample minimum) (polynomials : RegularBasisPolynomials cap
      index box) where
  /-- The basis comparison plans at the original mesh's first endpoint. -/ first : ChartRequest
    sources.first.request polynomials minimum
  /-- The basis comparison plans at the original mesh's last endpoint. -/ last : ChartRequest
    sources.last.request polynomials minimum
  /-- The common cached root-reading stage for the retained chart plans. -/ stage : Nat
  /-- The complete basis comparison plans on the original retained midpoint tree. -/ tree :
    BasisTreeSources.Plans polynomials minimum
    mesh.tree sources.tree
  /-- The reading stage pays the original chart mesh and every retained midpoint and extreme-vertex plan. -/ stage_eq :
    stage = max charts.stage (max
    (BasisTreeSources.Plans.stage mesh.tree
    sources.tree tree) (max first.stage last.stage))

constructive_injectivity Plan

namespace Plan

variable {sources : BasisEndpoints mesh
  covers sourceTarget sourceFloor}

/-- Prepare the retained extreme and midpoint comparison plans and cache their common original chart-reading stage. -/
@[expose] def build (sources : BasisEndpoints
  mesh covers sourceTarget sourceFloor) (charts : ChartMesh mesh capSample minimum)
    (polynomials : RegularBasisPolynomials cap index box) :
      Plan sources charts
      polynomials :=
  let first := ChartRequest.build sources.first.request polynomials minimum
  let last := ChartRequest.build sources.last.request polynomials minimum
  let tree := BasisTreeSources.Plans.build
    polynomials minimum mesh.tree sources.tree
  ⟨first, last, max charts.stage (max
    (BasisTreeSources.Plans.stage mesh.tree
    sources.tree tree) (max first.stage last.stage)), tree, rfl⟩

set_option genInjectivity false in
/-- The complete basis endpoint and midpoint comparisons bound to one exact original mesh evaluation. -/
structure Evaluation (plan : Plan
  sources charts polynomials)
    (bank : BasisSourceLocations.SampleBank covers index) (original : ChartMesh.Evaluation charts sample stage) where
  /-- The basis comparisons consuming the original mesh evaluation's actual first root reading. -/ first :
    EndpointSources.Evaluation sources.first
    plan.first bank original.first
  /-- The basis comparisons consuming the original mesh evaluation's actual last root reading. -/ last :
    EndpointSources.Evaluation sources.last plan.last
    bank original.last
  /-- The basis comparisons consuming all actual midpoint readings from that same original tree evaluation. -/ tree :
    BasisTreeSources.Plans.Evaluation bank mesh.tree
    sources.tree plan.tree original.readings

constructive_injectivity Evaluation

/-- Both evaluations consume the retained extreme readings of this exact mesh evaluation. All basis source rows use one
shared polynomial bank. -/
@[expose] def evaluate (plan :
  Plan sources charts
  polynomials)
    (bank : BasisSourceLocations.SampleBank covers index) (original : ChartMesh.Evaluation charts sample stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : sources.index ≤ index) (later : plan.stage ≤ stage) :
      Evaluation plan bank
      original := by
  have modelIndices := (Data.Nat.Order.le_max_right _ _).trans (sources.index_eq.symm.trans_le modelLater)
  have readingIndices := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _
    _).trans (plan.stage_eq.symm.trans_le later))
  exact ⟨sources.first.evaluate plan.first bank original.first original.first_prepared branch
      ((Data.Nat.Order.le_max_left _ _).trans modelIndices) ((Data.Nat.Order.le_max_left _ _).trans
        readingIndices),
    sources.last.evaluate plan.last bank original.last original.last_prepared branch
      ((Data.Nat.Order.le_max_right _ _).trans modelIndices) ((Data.Nat.Order.le_max_right _ _).trans
        readingIndices),
    BasisTreeSources.Plans.evaluate bank branch
      mesh.tree sources.tree plan.tree original.readings
      ((Data.Nat.Order.le_max_left _ _).trans (sources.index_eq.symm.trans_le modelLater))
      ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
        (plan.stage_eq.symm.trans_le later)))⟩

end Plan
end BasisEndpoints
end Mesh
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

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

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor :
    Nat}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

set_option genInjectivity false in
/-- The retained basis source locations and request at one original prepared chart endpoint.

Each source row keeps its original owner and the source model floor separately from the chart root-reading stage. -/
structure EndpointSources (prepared : VertexRequests.Prepared regular model parameter target floor)
    (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget : InverseRootPolynomial.Coordinate) (sourceFloor :
      Nat) where
  /-- The original per-basis source locations joined to this exact prepared chart endpoint. -/ locations :
    SourceLocations.BasisSourceLocations regular prepared.point covers
  /-- The positive basis source request on the exact retained source owners. -/ request :
    SourceRequests.BasisSourceRequest locations.owners sourceTarget sourceFloor

constructive_injectivity EndpointSources

namespace EndpointSources

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter
  target floor}

/-- Locate each original basis source at the retained chart endpoint and prepare its positive source request. -/
@[expose] def build (prepared : VertexRequests.Prepared regular model parameter target floor) (covers :
  SourceLocations.BasisSourceCovers parent)
    (sourceTarget : InverseRootPolynomial.Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources prepared covers sourceTarget
      sourceFloor :=
  let locations := BasisSourceLocations.build regular prepared.point covers
  ⟨locations, BasisSourceRequest.build locations.owners sourceTarget positive sourceFloor⟩

variable {index stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}

set_option genInjectivity false in
/-- The actual source/chart comparison at the original retained endpoint reading.

The exact source-sample readback preserves the shared numerical bank and original root coordinate. -/
structure Evaluation (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources
  prepared covers sourceTarget sourceFloor)
    (charts : BasisSourceRequest.ChartRequest sources.request polynomials minimum)
    (bank : BasisSourceLocations.SampleBank covers index)
    (reading : VertexRequests.Reading regular model sample parameter target floor stage) where
  /-- The basis endpoint samples read from the supplied original shared polynomial bank. -/ samples :
    BasisSourceRequest.Samples sources.locations.owners polynomials
  /-- The retained endpoint samples are exactly the original locations' reads from that bank. -/ samples_eq : samples =
    sources.locations.samples bank polynomials
  /-- The source/chart comparison using the actual original endpoint root coordinate and reading stage. -/ evaluated :
    charts.Evaluation samples reading.root.coordinate stage

constructive_injectivity Evaluation

/-- Transport the original reading along its prepared-owner equality, then consume the existing numerical bank without
resampling its root or inverses. -/
@[expose] def evaluate (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources
  prepared covers sourceTarget sourceFloor)
    (charts : BasisSourceRequest.ChartRequest sources.request polynomials minimum)
    (bank : BasisSourceLocations.SampleBank covers index)
    (reading : VertexRequests.Reading regular model sample parameter target floor stage)
    (owner : reading.prepared = prepared) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : sources.request.index ≤ index) (later : charts.stage ≤ stage) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources.Evaluation sources charts bank
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
@[expose] def BasisTreeSources (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget :
  InverseRootPolynomial.Coordinate) (sourceFloor : Nat) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → VertexTree.Tree regular model target floor depth
      first last → Type 2
  | _, _, _, .leaf _ _ => PUnit
  | _, _, _, .node middle left right =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources middle covers sourceTarget
    sourceFloor ×
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget
        sourceFloor left × Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources
        covers sourceTarget sourceFloor right

namespace BasisTreeSources

/-- Prepare each actual original midpoint's basis source request, preserving the retained tree shape. -/
@[expose] def build (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget :
  InverseRootPolynomial.Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular model target floor
      depth first last) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget sourceFloor
      tree
  | _, _, _, .leaf _ _ => ⟨⟩
  | _, _, _, .node middle left right =>
      ⟨EndpointSources.build middle covers sourceTarget positive sourceFloor,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.build covers
          sourceTarget positive sourceFloor left,
          Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.build covers
          sourceTarget positive sourceFloor right⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- The maximum source-polynomial stage of the original midpoint requests, retaining the supplied floor at leaves. -/
@[expose] def index : {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular
  model target floor depth first last) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget sourceFloor
      tree → Nat
  | _, _, _, .leaf _ _, _ => sourceFloor
  | _, _, _, .node _ left right, sources => max sources.1.request.index
      (max (index left sources.2.1) (index right sources.2.2))

variable {index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- The dependent basis source chart plans on every midpoint of the original retained dyadic tree. -/
@[expose] def Plans (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (minimum : Nat) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular model target floor
      depth first last) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget sourceFloor
      tree → Type 2
  | _, _, _, .leaf _ _, _ => PUnit
  | _, _, _, .node _ left right, sources => BasisSourceRequest.ChartRequest sources.1.request polynomials minimum ×
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans polynomials
        minimum left sources.2.1 ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans polynomials
        minimum right sources.2.2

namespace Plans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- Prepare every original midpoint comparison on the same retained basis polynomial bank. -/
@[expose] def build (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (minimum : Nat) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular model target floor
      depth first last) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget
      sourceFloor tree) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans
      polynomials minimum tree sources
  | _, _, _, .leaf _ _, _ => ⟨⟩
  | _, _, _, .node _ left right, sources =>
      ⟨BasisSourceRequest.ChartRequest.build sources.1.request polynomials minimum,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.build
          polynomials minimum left sources.2.1,
          Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.build
          polynomials minimum right sources.2.2⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans in
/-- The maximum root-reading stage of the original midpoint plans, retaining the supplied minimum at leaves. -/
@[expose] def stage : {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular
  model target floor depth first last) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget
      sourceFloor tree) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans
      polynomials minimum tree sources → Nat
  | _, _, _, .leaf _ _, _, _ => minimum
  | _, _, _, .node _ left right, sources, plans => max plans.1.stage
      (max (stage left sources.2.1 plans.2.1) (stage right sources.2.2 plans.2.2))

variable {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample} {readingStage :
    Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources in
/-- Every midpoint comparison is tied to the reading retained by the original chart tree, and therefore to the very path
used by its area certificate. -/
@[expose] def Evaluation (bank : BasisSourceLocations.SampleBank covers index) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular model target floor
      depth first last) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget
      sourceFloor tree) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans polynomials minimum tree
      sources → VertexPaths.TreeReadings sample readingStage tree → Type 2
  | _, _, _, .leaf _ _, _, _, _ => PUnit
  | _, _, _, .node _ left right, sources, plans, readings =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources.Evaluation sources.1 plans.1
        bank readings.1.reading ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.Evaluation
          bank left sources.2.1 plans.2.1 readings.2.1 ×
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.Evaluation
          bank right sources.2.2 plans.2.2 readings.2.2

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans in
/-- Evaluate each original midpoint comparison using its retained chart-tree reading and the common paid model and
reading stages. -/
@[expose] def evaluate (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular model target floor
      depth first last) →
    (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget
      sourceFloor tree) →
    (plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans polynomials
      minimum tree sources) → (readings : VertexPaths.TreeReadings sample readingStage tree) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.index tree sources ≤ index →
      stage tree sources plans ≤ readingStage →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.Evaluation bank tree
      sources plans readings
  | _, _, _, .leaf _ _, _, _, _, _, _ => ⟨⟩
  | _, _, _, .node _ left right, sources, plans, readings, modelLater, later =>
      ⟨sources.1.evaluate plans.1 bank readings.1.reading readings.1.owner branch
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans modelLater) ((Purelib.Data.Nat.Order.le_max_left _ _).trans
            later),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.evaluate bank
          branch left sources.2.1 plans.2.1 readings.2.1
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans modelLater))
          ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)),
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.evaluate bank
          branch right sources.2.2 plans.2.2 readings.2.2
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans modelLater))
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans later))⟩

end Plans
end BasisTreeSources

namespace Mesh

variable {depth : Nat} {mesh : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Mesh regular model depth
  target floor}

set_option genInjectivity false in
/-- Requests for both extreme vertices and every midpoint are selected before the shared polynomial stage, retaining the
original mesh owners. -/
structure BasisEndpoints (mesh : VertexTree.Mesh regular model depth target floor)
    (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget : InverseRootPolynomial.Coordinate) (sourceFloor :
      Nat) where
  /-- The basis source requests at the exact original mesh's first prepared endpoint. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources mesh.first covers sourceTarget
    sourceFloor
  /-- The basis source requests at the exact original mesh's last prepared endpoint. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources mesh.last covers sourceTarget
    sourceFloor
  /-- The common cached source-polynomial stage for the original endpoint and midpoint requests. -/ index : Nat
  /-- The basis source requests on all actual midpoints of the retained original mesh tree. -/ tree :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources covers sourceTarget sourceFloor
    mesh.tree
  /-- The source stage is the maximum of all retained midpoint and extreme-vertex request stages. -/ index_eq : index =
    max (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.index mesh.tree tree) (max
    first.request.index last.request.index)

constructive_injectivity BasisEndpoints

namespace BasisEndpoints

/-- Prepare both original extreme endpoints and every midpoint, then cache their common source-polynomial stage. -/
@[expose] def build (mesh : VertexTree.Mesh regular model depth target floor) (covers :
  SourceLocations.BasisSourceCovers parent)
    (sourceTarget : InverseRootPolynomial.Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints mesh covers sourceTarget
      sourceFloor :=
  let first := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources.build mesh.first
    covers sourceTarget positive sourceFloor
  let last := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources.build mesh.last covers
    sourceTarget positive sourceFloor
  let tree := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.build covers
    sourceTarget positive sourceFloor mesh.tree
  ⟨first, last, max (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.index mesh.tree
    tree) (max first.request.index last.request.index), tree, rfl⟩

variable {index stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {charts : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh mesh capSample minimum}

set_option genInjectivity false in
/-- The original mesh's complete basis endpoint and midpoint chart schedule.

One shared polynomial bank supplies all plans, with a reading maximum also paying the original chart mesh. -/
structure Plan (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints mesh
  covers sourceTarget sourceFloor)
    (charts : VertexTree.ChartMesh mesh capSample minimum) (polynomials : CapBasisEnergy.RegularBasisPolynomials cap
      index box) where
  /-- The basis comparison plans at the original mesh's first endpoint. -/ first : BasisSourceRequest.ChartRequest
    sources.first.request polynomials minimum
  /-- The basis comparison plans at the original mesh's last endpoint. -/ last : BasisSourceRequest.ChartRequest
    sources.last.request polynomials minimum
  /-- The common cached root-reading stage for the retained chart plans. -/ stage : Nat
  /-- The complete basis comparison plans on the original retained midpoint tree. -/ tree :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans polynomials minimum
    mesh.tree sources.tree
  /-- The reading stage pays the original chart mesh and every retained midpoint and extreme-vertex plan. -/ stage_eq :
    stage = max charts.stage (max
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.stage mesh.tree
    sources.tree tree) (max first.stage last.stage))

constructive_injectivity Plan

namespace Plan

variable {sources : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints mesh
  covers sourceTarget sourceFloor}

/-- Prepare the retained extreme and midpoint comparison plans and cache their common original chart-reading stage. -/
@[expose] def build (sources : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints
  mesh covers sourceTarget sourceFloor) (charts : VertexTree.ChartMesh mesh capSample minimum)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints.Plan sources charts
      polynomials :=
  let first := ChartRequest.build sources.first.request polynomials minimum
  let last := ChartRequest.build sources.last.request polynomials minimum
  let tree := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.build
    polynomials minimum mesh.tree sources.tree
  ⟨first, last, max charts.stage (max
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.stage mesh.tree
    sources.tree tree) (max first.stage last.stage)), tree, rfl⟩

set_option genInjectivity false in
/-- The complete basis endpoint and midpoint comparisons bound to one exact original mesh evaluation. -/
structure Evaluation (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints.Plan
  sources charts polynomials)
    (bank : BasisSourceLocations.SampleBank covers index) (original : ChartMesh.Evaluation charts sample stage) where
  /-- The basis comparisons consuming the original mesh evaluation's actual first root reading. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources.Evaluation sources.first
    plan.first bank original.first
  /-- The basis comparisons consuming the original mesh evaluation's actual last root reading. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.EndpointSources.Evaluation sources.last plan.last
    bank original.last
  /-- The basis comparisons consuming all actual midpoint readings from that same original tree evaluation. -/ tree :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.Evaluation bank mesh.tree
    sources.tree plan.tree original.readings

constructive_injectivity Evaluation

/-- Both evaluations consume the retained extreme readings of this exact mesh evaluation. All basis source rows use one
shared polynomial bank. -/
@[expose] def evaluate (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints.Plan sources charts
  polynomials)
    (bank : BasisSourceLocations.SampleBank covers index) (original : ChartMesh.Evaluation charts sample stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : sources.index ≤ index) (later : plan.stage ≤ stage) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints.Plan.Evaluation plan bank
      original := by
  have modelIndices := (Purelib.Data.Nat.Order.le_max_right _ _).trans (sources.index_eq.symm.trans_le modelLater)
  have readingIndices := (Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _
    _).trans (plan.stage_eq.symm.trans_le later))
  exact ⟨sources.first.evaluate plan.first bank original.first original.first_prepared branch
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans modelIndices) ((Purelib.Data.Nat.Order.le_max_left _ _).trans
        readingIndices),
    sources.last.evaluate plan.last bank original.last original.last_prepared branch
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans modelIndices) ((Purelib.Data.Nat.Order.le_max_right _ _).trans
        readingIndices),
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans.evaluate bank branch
      mesh.tree sources.tree plan.tree original.readings
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans (sources.index_eq.symm.trans_le modelLater))
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans
        (plan.stage_eq.symm.trans_le later)))⟩

end Plan
end BasisEndpoints
end Mesh
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

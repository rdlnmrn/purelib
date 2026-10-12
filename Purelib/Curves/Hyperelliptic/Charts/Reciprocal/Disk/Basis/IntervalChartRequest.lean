module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTree
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTree

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib.Riemann.Normalization

public section

/-! Prepare both endpoint and midpoint source owners before acquiring any
polynomial or root readings on one common interval. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Prepared)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Tree)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (EndpointSources BasisTreeSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)

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

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

namespace BasisIntervalChartRequest

variable (interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers) (regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

/-- The original reciprocal root model of the retained common interval's anchor cell. -/
@[expose] def Model := RootModel.build interval.anchor.cell

/-- The original chart request at the retained common interval's first parameter. -/
@[expose] def First (target : InverseRootPolynomial.Coordinate) (floor : Nat) := VertexRequests.Prepared regular
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.Model interval)
  interval.edge.left.parameter target floor
/-- The original chart request at the retained common interval's last parameter. -/
@[expose] def Last (target : InverseRootPolynomial.Coordinate) (floor : Nat) := VertexRequests.Prepared regular
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.Model interval)
  interval.edge.right.parameter target floor
/-- The original dyadic chart request tree between the retained interval endpoints. -/
@[expose] def Vertices (depth : Nat) (target : InverseRootPolynomial.Coordinate) (floor : Nat) :=
  VertexTree.Tree regular
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.Model interval)
    target floor depth interval.edge.left.parameter interval.edge.right.parameter

end BasisIntervalChartRequest

set_option genInjectivity false in
/-- The complete original chart and basis-source schedule for one retained common interval.

Both endpoint requests, the dyadic tree and every corresponding source owner are fixed before numerical acquisition. -/
structure BasisIntervalChartRequest (interval : CommonCover.BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap) (depth : Nat) (target sourceTarget : InverseRootPolynomial.Coordinate) (floor
      sourceFloor : Nat) where
  /-- The retained original basis-source tolerance is strictly positive. -/ source_positive : 0 < sourceTarget
  /-- The actual original chart request at the first retained interval endpoint. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.First interval
    regular target floor
  /-- The actual original chart request at the last retained interval endpoint. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.Last interval
    regular target floor
  /-- The complete original dyadic chart request tree on this retained interval. -/ tree :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.Vertices interval
    regular depth target floor
  /-- The actual original basis-source requests at the retained first chart endpoint. -/ firstSources :
    EndpointSchedule.EndpointSources first covers sourceTarget sourceFloor
  /-- The first source request is exactly the original interval-based endpoint selection. -/ firstSources_eq :
    firstSources = EndpointSources.onInterval first interval ⟨le_rfl, interval.ordered⟩ sourceTarget source_positive
    sourceFloor
  /-- The actual original basis-source requests at the retained last chart endpoint. -/ lastSources :
    EndpointSchedule.EndpointSources last covers sourceTarget sourceFloor
  /-- The last source request is exactly the original interval-based endpoint selection. -/ lastSources_eq : lastSources
    = EndpointSources.onInterval last interval ⟨interval.ordered, le_rfl⟩ sourceTarget source_positive sourceFloor
  /-- The complete original basis-source request tree on the retained chart vertices. -/ treeSources :
    EndpointSchedule.BasisTreeSources covers sourceTarget sourceFloor tree
  /-- The source tree is exactly the original interval-based selection on that same chart tree. -/ treeSources_eq :
    treeSources = BasisTreeSources.onInterval interval sourceTarget source_positive sourceFloor tree le_rfl le_rfl
    interval.ordered
  /-- The cached common stage paying all original chart and basis-source requests. -/ index : Nat
  /-- The common stage is exactly the maximum of all retained endpoint, vertex and source request stages. -/ index_eq :
    index = max (max first.request.index (max last.request.index tree.index))
    (max firstSources.request.index (max lastSources.request.index (BasisTreeSources.index tree treeSources)))

constructive_injectivity BasisIntervalChartRequest

namespace BasisIntervalChartRequest

/-- Prepare the original endpoint and dyadic chart owners with their matching basis-source requests, caching one common
paid stage. -/
@[expose] def build (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data cap)
    (depth : Nat) (target sourceTarget : InverseRootPolynomial.Coordinate) (positive : 0 < target) (sourcePositive : 0 <
      sourceTarget)
    (floor sourceFloor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
      depth target sourceTarget floor sourceFloor := by
  let model := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest.Model
    interval
  have firstInside := And.intro interval.anchor.lower (interval.ordered.trans interval.anchor.upper)
  have lastInside := And.intro (interval.anchor.lower.trans interval.ordered) interval.anchor.upper
  let first := Prepared.build regular model interval.edge.left.parameter firstInside target positive floor
  let last := Prepared.build regular model interval.edge.right.parameter lastInside target positive floor
  let tree := Tree.build regular model target positive floor depth _ _ firstInside lastInside interval.ordered
  let firstSources := EndpointSources.onInterval first interval ⟨le_rfl, interval.ordered⟩ sourceTarget sourcePositive
    sourceFloor
  let lastSources := EndpointSources.onInterval last interval ⟨interval.ordered, le_rfl⟩ sourceTarget sourcePositive
    sourceFloor
  let treeSources := BasisTreeSources.onInterval interval sourceTarget sourcePositive sourceFloor tree le_rfl le_rfl
    interval.ordered
  let index := max (max first.request.index (max last.request.index tree.index))
    (max firstSources.request.index (max lastSources.request.index (BasisTreeSources.index tree treeSources)))
  exact ⟨sourcePositive, first, last, tree, firstSources, rfl, lastSources, rfl, treeSources, rfl, index, rfl⟩

variable {interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers} {depth : Nat}

/-- The cached common stage pays the original retained first request stage. -/
theorem first_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
  depth target sourceTarget floor sourceFloor) :
    request.first.request.index ≤ request.index :=
  ((Purelib.Data.Nat.Order.le_max_left ..).trans (Purelib.Data.Nat.Order.le_max_left ..)).trans_eq request.index_eq.symm

/-- The cached common stage pays the original retained last request stage. -/
theorem last_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
  depth target sourceTarget floor sourceFloor) :
    request.last.request.index ≤ request.index :=
  ((Purelib.Data.Nat.Order.le_max_left ..).trans ((Purelib.Data.Nat.Order.le_max_right ..).trans
    (Purelib.Data.Nat.Order.le_max_left ..))).trans_eq request.index_eq.symm

/-- The cached common stage pays the original retained tree request stage. -/
theorem tree_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
  depth target sourceTarget floor sourceFloor) :
    request.tree.index ≤ request.index :=
  ((Purelib.Data.Nat.Order.le_max_right ..).trans ((Purelib.Data.Nat.Order.le_max_right ..).trans
    (Purelib.Data.Nat.Order.le_max_left ..))).trans_eq request.index_eq.symm

/-- The cached common stage pays the original retained firstSources request stage. -/
theorem firstSources_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
  depth target sourceTarget floor sourceFloor) :
    request.firstSources.request.index ≤ request.index :=
  ((Purelib.Data.Nat.Order.le_max_left ..).trans (Purelib.Data.Nat.Order.le_max_right ..)).trans_eq
    request.index_eq.symm

/-- The cached common stage pays the original retained lastSources request stage. -/
theorem lastSources_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
  depth target sourceTarget floor sourceFloor) :
    request.lastSources.request.index ≤ request.index :=
  ((Purelib.Data.Nat.Order.le_max_left ..).trans ((Purelib.Data.Nat.Order.le_max_right ..).trans
    (Purelib.Data.Nat.Order.le_max_right ..))).trans_eq request.index_eq.symm

/-- The cached common stage pays the original retained treeSources request stage. -/
theorem treeSources_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest interval regular
  depth target sourceTarget floor sourceFloor) :
    BasisTreeSources.index request.tree request.treeSources ≤ request.index :=
  ((Purelib.Data.Nat.Order.le_max_right ..).trans ((Purelib.Data.Nat.Order.le_max_right ..).trans
    (Purelib.Data.Nat.Order.le_max_right ..))).trans_eq request.index_eq.symm

end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest

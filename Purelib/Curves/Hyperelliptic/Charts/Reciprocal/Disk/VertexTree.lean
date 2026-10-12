module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Normalization

/-!
# A shared dyadic tree of original reciprocal arc vertices

Each midpoint has one original owner and one source-stage request. After
selecting the common polynomial, chart requests select one common reading
stage. Evaluation will pass each midpoint reading to both adjacent branches.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint midpoint_between)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Prepared Chart)

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
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- A finite dyadic tree with one original prepared root owner at every interior midpoint. -/
inductive Tree (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) : Nat → InverseRootPolynomial.Coordinate →
      InverseRootPolynomial.Coordinate → Type 1
  /-- A depth-zero original dyadic interval has no interior prepared midpoint. -/ | leaf (first last :
    InverseRootPolynomial.Coordinate) : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular
    model target floor 0 first last
  /-- Retain one actual midpoint owner and the two original adjacent dyadic subtrees. -/ | node {depth : Nat} {first
    last : InverseRootPolynomial.Coordinate}
      (middle : VertexRequests.Prepared regular model (PreparedBoxPartitions.midpoint first last) target floor)
      (left : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first
        (PreparedBoxPartitions.midpoint first last))
      (right : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth
        (PreparedBoxPartitions.midpoint first last) last) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor (depth + 1) first
        last

constructive_injectivity Tree

namespace Tree

/-- Prepare the original dyadic vertex tree or its chart requests while sharing each cached midpoint between adjacent
branches. -/
@[expose] def build (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    (depth : Nat) → (first last : InverseRootPolynomial.Coordinate) →
    (edge.left.parameter ≤ first ∧ first ≤ edge.right.parameter) →
    (edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) → first ≤ last →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first last
  | 0, first, last, _, _, _ => .leaf first last
  | depth + 1, first, last, firstInside, lastInside, ordered =>
      let between := PreparedBoxPartitions.midpoint_between ordered
      let middleInside := ⟨firstInside.1.trans between.1, between.2.trans lastInside.2⟩
      .node (Prepared.build regular model _ middleInside target positive floor)
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree.build regular model target positive floor
          depth first _ firstInside middleInside between.1)
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree.build regular model target positive floor
          depth _ last middleInside lastInside between.2)

/-- Compute a common polynomial stage above the actual original endpoint and midpoint requests. -/
@[expose] def index : {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} →
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first last → Nat
  | _, _, _, .leaf _ _ => 0
  | _, _, _, .node middle left right => max middle.request.index (max left.index right.index)

end Tree

variable {index : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {minimum
    : Nat}

set_option genInjectivity false in
/-- A dependent tree of chart requests on the exact original prepared midpoint owners. -/
inductive ChartTree (capSample : Primitives.Sample cap differential index box) (minimum : Nat) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first last → Type 1
  /-- The original depth-zero interval has no midpoint chart request. -/ | leaf (first last :
    InverseRootPolynomial.Coordinate) : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree
    capSample minimum (.leaf first last)
  /-- Attach the actual midpoint chart request to its two original retained subtrees. -/ | node {depth : Nat} {first
    last : InverseRootPolynomial.Coordinate}
      {middle : VertexRequests.Prepared regular model (PreparedBoxPartitions.midpoint first last) target floor}
      {left : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first
        (PreparedBoxPartitions.midpoint first last)}
      {right : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth
        (PreparedBoxPartitions.midpoint first last) last}
      (chart : VertexRequests.Chart middle capSample minimum)
      (before : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree capSample minimum left) (after
        : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree capSample minimum right) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree capSample minimum (.node middle left
        right)

constructive_injectivity ChartTree

namespace ChartTree

/-- Prepare the original dyadic vertex tree or its chart requests while sharing each cached midpoint between adjacent
branches. -/
@[expose] def build (capSample : Primitives.Sample cap differential index box) (minimum : Nat) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first last) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree capSample minimum tree
  | _, _, _, .leaf first last => .leaf first last
  | _, _, _, .node middle left right => .node (Chart.build middle capSample minimum)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree.build capSample minimum left)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree.build capSample minimum right)

/-- Compute a common root-reading stage above the actual retained chart requests. -/
@[expose] def stage : {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → {tree :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth first last} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree capSample minimum tree → Nat
  | _, _, _, _, .leaf _ _ => 0
  | _, _, _, _, .node middle left right => max middle.stage (max left.stage right.stage)

end ChartTree

set_option genInjectivity false in
/-- Endpoints are prepared once outside the midpoint tree. -/
structure Mesh (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    (depth : Nat) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached request at the original cell's first retained endpoint. -/ first : VertexRequests.Prepared regular
    model edge.left.parameter target floor
  /-- The cached request at the original cell's last retained endpoint. -/ last : VertexRequests.Prepared regular model
    edge.right.parameter target floor
  /-- The retained dyadic midpoint tree indexed by these exact original endpoint owners. -/ tree :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree regular model target floor depth edge.left.parameter
    edge.right.parameter
  /-- Compute a common polynomial stage above the actual original endpoint and midpoint requests. -/ index : Nat
  /-- The common polynomial stage is the maximum of both original endpoint requests and the retained midpoint tree. -/
    index_eq : index = max first.request.index (max last.request.index tree.index)

constructive_injectivity Mesh

namespace Mesh

/-- Prepare the original dyadic vertex tree or its chart requests while sharing each cached midpoint between adjacent
branches. -/
@[expose] def build (owners : ParentOwners.OwnedEndpoints regular cell)
    (depth : Nat) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Mesh regular owners.model depth target floor :=
  let first := Prepared.ofPoint owners.first owners.bounds.first target positive floor
  let last := Prepared.ofPoint owners.last owners.bounds.last target positive floor
  let tree := Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Tree.build regular owners.model target positive
    floor depth _ _ ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩ cell.ordered.le
  ⟨first, last, tree, max first.request.index (max last.request.index tree.index), rfl⟩

end Mesh

set_option genInjectivity false in
/-- Chart requests for the exact original endpoint and midpoint preparation.

The cached common reading stage is separate from the source polynomial stage and pays every original retained vertex
request. -/
structure ChartMesh {depth : Nat} (mesh : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Mesh regular model
  depth target floor)
    (capSample : Primitives.Sample cap differential index box) (minimum : Nat) where
  /-- The paid chart request on the exact original first prepared endpoint. -/ first : VertexRequests.Chart mesh.first
    capSample minimum
  /-- The paid chart request on the exact original last prepared endpoint. -/ last : VertexRequests.Chart mesh.last
    capSample minimum
  /-- The chart-request tree indexed by the actual original retained midpoint preparation. -/ tree :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree capSample minimum mesh.tree
  /-- Compute a common root-reading stage above the actual retained chart requests. -/ stage : Nat
  /-- The retained common reading stage is the maximum of both original endpoint stages and the chart tree. -/ stage_eq
    : stage = max first.stage (max last.stage tree.stage)

constructive_injectivity ChartMesh

namespace ChartMesh

/-- Prepare the original dyadic vertex tree or its chart requests while sharing each cached midpoint between adjacent
branches. -/
@[expose] def build {depth : Nat} (mesh : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.Mesh regular model
  depth target floor)
    (capSample : Primitives.Sample cap differential index box) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh mesh capSample minimum :=
  let first := Chart.build mesh.first capSample minimum
  let last := Chart.build mesh.last capSample minimum
  let tree := Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartTree.build capSample minimum mesh.tree
  ⟨first, last, tree, max first.stage (max last.stage tree.stage), rfl⟩

end ChartMesh
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree

module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

/-!
# Retained cap-coordinate joins over a complete exterior parent

Every cell in the existing comparison bank gets one shared endpoint model.
The complete dyadic mesh certifies all consecutive parameter equalities;
the retained source sheet supplies the operational coordinate comparisons.
These comparisons are cached before any later primitive sample is selected.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs

open Purelib.Geometry

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge Endpoint dyadicEdges)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Endpoints Join)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- The endpoint root caches and their stage-independent numerical budgets are retained together, before any requested
accuracy is selected.

The two endpoint owners retain the supplied cell, and the cached numerical
bounds refer to these exact coordinate owners before any accuracy request. -/
structure OwnedEndpoints (regular : RegularBounds.Data cap)
    {edge : ClearSheetContinuation.Subdivision.ParameterEdge} (cell : UniformReciprocalCover.Cell data edge) extends
      Endpoints cap cell where
  /-- The cached numerical endpoint bounds tied to these exact original coordinate owners. -/ bounds :
    EndpointPairs.PairData regular toEndpoints

constructive_injectivity OwnedEndpoints

/-- Acquire the original cell's two root endpoints once and cache their stage-independent pair bounds. -/
@[expose] def OwnedEndpoints.build (regular : RegularBounds.Data cap)
    {edge : ClearSheetContinuation.Subdivision.ParameterEdge} (cell : UniformReciprocalCover.Cell data edge) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell :=
  let endpoints := Endpoints.build cap cell
  ⟨endpoints, PairData.build regular endpoints⟩

set_option genInjectivity false in
/-- A dependent spine of original endpoint owners indexed by the exact retained comparison bank.

Each constructor follows the comparison bank's original cell and tail.
The type index preserves that exact bank and its ordered parameter edges. -/
inductive Owners : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → ParentBank.Bank regular data edges
  → Type 1
  /-- The empty original comparison bank has no endpoint owners. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners .nil
  /-- Prepend one original cell's endpoint owners to the retained tail bank. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
      (head : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell) (tail :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners (.cons comparison bank)

constructive_injectivity Owners

namespace Owners

/-- Cache the original endpoint owners along the retained comparison bank without replacing its source cells. -/
@[expose] def build : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → (bank : ParentBank.Bank regular
  data edges) → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank
  | _, .nil => .nil
  | _, .cons _ tail => .cons (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints.build regular _)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.build tail)

/-- The exact endpoint adjacency relation for an original parameter-edge chain. -/
@[expose] def From (first : InverseRootPolynomial.Coordinate) : List ClearSheetContinuation.Subdivision.ParameterEdge →
  InverseRootPolynomial.Coordinate → Prop
  | [], last => first = last
  | edge :: rest, last => first = edge.left.parameter ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From edge.right.parameter rest last

/-- Concatenate parameter chains through their shared endpoint.

The endpoint relation retains the supplied edge order and the middle
parameter while composing the two outer endpoints. -/
theorem from_append {first middle last : InverseRootPolynomial.Coordinate} {left right : List
  ClearSheetContinuation.Subdivision.ParameterEdge}
    (before : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first left middle) (after :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From middle right last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first (left ++ right) last := by
  induction left generalizing first with
  | nil => exact before ▸ after
  | cons edge rest ih => exact ⟨before.1, ih before.2⟩

/-- The dyadic edge list connects its supplied endpoints.

Each recursive split joins the two retained sublists through their midpoint
and preserves the original outer parameters. -/
theorem dyadic_from (depth : Nat) (first last : ClearSheetContinuation.Subdivision.Endpoint) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first.parameter
      (ClearSheetContinuation.Subdivision.dyadicEdges depth first last) last.parameter := by
  induction depth generalizing first last with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth ih => exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.from_append (ih _ _) (ih _ _)

/-- Consecutive parameter edges share their joining parameter.

The finite relation checks the head junction and follows the original
remaining edge spine, with empty and singleton lists requiring no junction. -/
@[expose] def Junctions : List ClearSheetContinuation.Subdivision.ParameterEdge → Prop
  | [] => True
  | [_] => True
  | first :: next :: remaining => first.right.parameter = next.left.parameter ∧
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Junctions (next :: remaining)

/-- The endpoint relation supplies every consecutive edge junction.

The head endpoint identity supplies the next joining parameter, and the
retained tail relation supplies the remaining finite junctions. -/
theorem junctions_of_from {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {first last :
  InverseRootPolynomial.Coordinate}
    (chain : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first edges last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Junctions edges := by
  induction edges generalizing first with
  | nil => trivial
  | cons edge rest ih =>
      cases rest with
      | nil => trivial
      | cons next remaining => exact ⟨chain.2.1, ih chain.2⟩

/-- Retain an operational join at each consecutive cell boundary.

The dependent product follows the supplied owner spine and retains both
actual endpoint owners of every junction. -/
@[expose] def LinkData : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank → Type
  | _, _, .nil => PUnit
  | _, _, .cons _ .nil => PUnit
  | _, _, .cons first (@Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _
    nextComparison _ next remaining) =>
      Join first.last next.first × Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.LinkData
        (.cons (comparison := nextComparison) next remaining)

set_option genInjectivity false in
/-- Cached operational joins indexed by the original endpoint-owner spine.

The cached dependent product contains the joins of adjacent supplied cell
owners, allowing readback and primitive comparisons without rebuilding them. -/
structure Links {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} (owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) where
  /-- The cached operational joins for this exact original owner spine. -/ retained :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.LinkData owners

constructive_injectivity Links

/-- Every consecutive pair names the same supplied cap primitive. -/
@[expose] def PrimitiveLinks {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank → Type
  | _, _, .nil => PUnit
  | _, _, .cons _ .nil => PUnit
  | _, _, .cons first (@Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _
    nextComparison _ next remaining) =>
      Gaussian.Equivalence.NamedEquivalent
        (first.last.coordinates.chartPrimitive sample).name (next.first.coordinates.chartPrimitive sample).name ×
          Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.PrimitiveLinks sample (.cons
            (comparison := nextComparison) next remaining)

namespace Links

/-- Construct owner joins from the retained parameter junctions.

Each head join uses the two supplied endpoint owners; recursion retains the
original tail spine and its remaining junction evidence. -/
@[expose] def ofJunctions : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} →
    (owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Junctions edges →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.LinkData owners
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons _ .nil, _ => ⟨⟩
  | _, _, .cons first (@Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _
    nextComparison _ next remaining), junctions =>
      ⟨Join.ofSameParent first.last next.first junctions.1,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links.ofJunctions (.cons (comparison :=
          nextComparison) next remaining) junctions.2⟩

/-- Cache the original endpoint owners along the retained comparison bank without replacing its source cells. -/
@[expose] def build (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    (owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links owners :=
  ⟨ofJunctions owners (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.junctions_of_from
    (mesh.edges_eq.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.dyadic_from mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint))⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links in
/-- Read the cached original first boundary join from the retained owner-link bank. -/
@[expose] def head {edge nextEdge : ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
  ClearSheetContinuation.Subdivision.ParameterEdge}
    {cell : UniformReciprocalCover.Cell data edge} {nextCell : UniformReciprocalCover.Cell data nextEdge}
    {comparison : ArcSamples.Data regular cell} {nextComparison : ArcSamples.Data regular nextCell}
    {bank : ParentBank.Bank regular data remaining} {first :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell} {next :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular nextCell} {tail :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
    (links : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links (.cons (comparison := comparison)
      first (.cons (comparison := nextComparison) next tail))) :
    Join first.last next.first := links.retained.1

/-- Read the cached original tail joins without rebuilding any endpoint owner. -/
@[expose] def tail {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
  ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
    {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
    {first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell} {rest :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} (links :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links (.cons (comparison := comparison) first
      rest)) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links rest := by
  cases rest with
  | nil => exact ⟨⟨⟩⟩
  | cons next remaining => exact ⟨links.retained.2⟩

/-- Reuse all cached joins; no root model or ownership comparison is rebuilt. -/
@[expose] def primitives {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links owners →
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.PrimitiveLinks sample owners
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons _ .nil, _ => ⟨⟩
  | _, _, .cons _ (@Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _), links =>
      ⟨links.head.primitiveEquivalent sample,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Links.primitives sample links.tail⟩

end Links
set_option genInjectivity false in
/-- A view of an already retained endpoint. Its model and point are copied from the owner spine; reading a boundary
never acquires another root.

The supplied cell and root model determine the retained point at the stated
parameter; its cached numerical bounds travel with that same point. -/
structure EndpointView (regular : RegularBounds.Data cap) (data : UniformReciprocalModels.Data patch count) (parameter :
  InverseRootPolynomial.Coordinate) where
  /-- The original parameter edge containing the retained endpoint. -/ edge :
    ClearSheetContinuation.Subdivision.ParameterEdge
  /-- The original source cell on the retained parameter edge. -/ cell : UniformReciprocalCover.Cell data edge
  /-- The retained root model owned by this exact original source cell. -/ model :
    UniformReciprocalRootChannels.RootModel cell
  /-- The original endpoint occurrence at the retained boundary parameter. -/ point : ArcOwners.Point cap model
    parameter
  /-- The cached numerical endpoint bounds tied to these exact original coordinate owners. -/ bounds :
    EndpointComparison.Data regular point

constructive_injectivity EndpointView

/-- Transport a retained point and its cached numerical bounds together. -/
@[expose] def EndpointView.ofPoint {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  UniformReciprocalCover.Cell data edge}
    {model : UniformReciprocalRootChannels.RootModel cell} {parameter target : InverseRootPolynomial.Coordinate}
    (point : ArcOwners.Point cap model parameter)
    (bounds : EndpointComparison.Data regular point) (equal : parameter = target) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular data target := by
  cases equal
  exact ⟨edge, cell, model, point, bounds⟩

set_option genInjectivity false in
/-- A boundary view retains the already sampled root and primitive value.

The endpoint and its cached rational reading retain the supplied primitive
sample and stage, so boundary transport does not sample the root again. -/
structure EndpointView.RootReading (view : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView
  regular data parameter)
    {index : Nat} {box : Rational.Box} (sample : Primitives.Sample cap differential index box) (stage :
      Nat) where
  /-- The original chart endpoint used by the cached boundary reading. -/ endpoint : Coordinates.Overlap.Endpoint
    view.point.coordinates sample
  /-- The already sampled root and primitive reading at the original retained stage. -/ reading :
    ChartReadings.Endpoint.Reading endpoint stage

constructive_injectivity EndpointView.RootReading

/-- Transport the retained original endpoint reading into its exact boundary view. -/
@[expose] def EndpointView.rootReading {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  UniformReciprocalCover.Cell data edge}
    {model : UniformReciprocalRootChannels.RootModel cell} {parameter target : InverseRootPolynomial.Coordinate}
    {point : ArcOwners.Point cap model parameter}
    (bounds : EndpointComparison.Data regular point) (equal : parameter = target)
    {index stage : Nat} {box : Rational.Box} {sample : Primitives.Sample cap differential index box}
    {endpoint : Coordinates.Overlap.Endpoint point.coordinates sample}
    (reading : ChartReadings.Endpoint.Reading endpoint stage) :
    RootReading (ofPoint point bounds equal) sample stage := by
  cases equal
  exact ⟨endpoint, reading⟩

/-- Transport to the retained boundary view preserves the original sampled primitive value. -/
theorem EndpointView.rootReading_value {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  UniformReciprocalCover.Cell data edge}
    {model : UniformReciprocalRootChannels.RootModel cell} {parameter target : InverseRootPolynomial.Coordinate}
    {point : ArcOwners.Point cap model parameter}
    (bounds : EndpointComparison.Data regular point) (equal : parameter = target)
    {index stage : Nat} {box : Rational.Box} {sample : Primitives.Sample cap differential index box}
    {endpoint : Coordinates.Overlap.Endpoint point.coordinates sample}
    (reading : ChartReadings.Endpoint.Reading endpoint stage) :
    (rootReading bounds equal reading).reading.value = reading.value := by
  cases equal
  rfl

/-- Transport to the retained boundary view preserves the original sampled root coordinate. -/
theorem EndpointView.rootReading_coordinate {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  UniformReciprocalCover.Cell data edge}
    {model : UniformReciprocalRootChannels.RootModel cell} {parameter target : InverseRootPolynomial.Coordinate}
    {point : ArcOwners.Point cap model parameter}
    (bounds : EndpointComparison.Data regular point) (equal : parameter = target)
    {index stage : Nat} {box : Rational.Box} {sample : Primitives.Sample cap differential index box}
    {endpoint : Coordinates.Overlap.Endpoint point.coordinates sample}
    (reading : ChartReadings.Endpoint.Reading endpoint stage) :
    (rootReading bounds equal reading).reading.coordinate = reading.coordinate := by
  cases equal
  rfl

/-- Read the original first endpoint owner and bounds from a nonempty retained chain. -/
@[expose] def firstView : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} →
    (owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) → {first last :
      InverseRootPolynomial.Coordinate} → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first
      edges last → edges ≠ [] → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular
      data first
  | _, _, .nil, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, _, .cons first _, _, _, chain, _ =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.ofPoint first.first
        first.bounds.first chain.1.symm

/-- Read the original last endpoint owner and bounds from a nonempty retained chain. -/
@[expose] def lastView : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} →
    (owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) → {first last :
      InverseRootPolynomial.Coordinate} → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first
      edges last → edges ≠ [] → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular
      data last
  | _, _, .nil, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, _, .cons first .nil, _, _, chain, _ =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.ofPoint first.last first.bounds.last
    chain.2
  | _, _, .cons _ (@Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.cons _ _ _ _ _ _ _ _ _ _ _ _ _
    nextComparison _ next remaining), _, _, chain, _ =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.lastView (.cons (comparison :=
        nextComparison) next remaining) chain.2 (by intro equal; cases equal)

/-- The original complete dyadic mesh contains at least one edge. -/
theorem mesh_nonempty (mesh : UniformReciprocalCover.Mesh data) : mesh.edges ≠ [] := by
  intro empty
  have zero : 2 ^ mesh.depth = 0 := by rw [← mesh.edgeCount_eq, ← mesh.edges_length, empty]; rfl
  exact (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))) zero

/-- The original complete retained mesh connects parameter zero to parameter one. -/
theorem mesh_from (mesh : UniformReciprocalCover.Mesh data) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From 0 mesh.edges 1 :=
  mesh.edges_eq.symm ▸ Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.dyadic_from mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint

set_option genInjectivity false in
/-- Both exposed points are certified views of this exact complete owner bank, including its retained endpoint models
and root occurrences.

The first and last views retain the owner spine's endpoint models. Their
readback equalities identify the same complete mesh's parameter-zero and
parameter-one occurrences. -/
structure Boundary (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges} (owners :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) where
  /-- The retained view of this exact original bank's parameter-zero endpoint. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular data 0
  /-- The first boundary view is exactly the original owner spine's first endpoint. -/ first_eq : first =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.firstView owners
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_from mesh)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_nonempty mesh)
  /-- The retained view of this exact original bank's parameter-one endpoint. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular data 1
  /-- The last boundary view is exactly the original owner spine's last endpoint. -/ last_eq : last =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.lastView owners
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_from mesh)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_nonempty mesh)

constructive_injectivity Boundary

/-- Expose the original complete owner bank's first and last endpoint views with exact readback identities. -/
@[expose] def Boundary.build (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
  (owners : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.Boundary mesh owners :=
  ⟨firstView owners (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_from mesh)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_nonempty mesh), rfl,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.lastView owners
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_from mesh)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.mesh_nonempty mesh), rfl⟩

end Owners
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

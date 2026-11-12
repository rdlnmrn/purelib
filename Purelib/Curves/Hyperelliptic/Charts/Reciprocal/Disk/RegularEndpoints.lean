module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedSigns

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# The shared regular primitive at retained parent endpoint owners

Select the existing first and last cell alignments through the certified
owner views. Their polynomial is the common parent primitive. The join
proof uses the retained roots even when shared samples have transported
index presentations.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)

variable {genus count index depth : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Geometry.Rational.Box} {capSample :
    Primitives.Sample cap differential index box}
  {edge : ParameterEdge} {cell :
    Cell data edge} {model :
    RootModel cell} {parameter :
    Coordinate}

set_option genInjectivity false in
/-- The retained cell alignment exhibiting the shared regular primitive at an actual parent endpoint owner. -/
structure RegularEndpoint (regular : RegularBounds.Data cap)
    (capSample : Primitives.Sample cap differential index box)
    (_point : ArcOwners.Point cap model parameter) (value : Polynomial) where
  /-- The original retained arc comparison for this endpoint's cell. -/ comparison : ArcSamples.Data regular cell
  /-- The cached arc sample on the supplied cap primitive sample. -/ sample : ArcSamples.Sample comparison capSample
  /-- The retained regular-sheet alignment of that exact arc sample. -/ alignment : SheetAlignment.RegularAlignment
    sample
  /-- The retained alignment uses exactly the specified common polynomial. -/ primitive_eq : alignment.primitive = value

constructive_injectivity RegularEndpoint

/-- Transport the original cell alignment to its certified endpoint view without changing the sample. -/
def RegularEndpoint.ofPoint {target : Coordinate} {value : Polynomial}
    (point : ArcOwners.Point cap model parameter)
    (bounds : EndpointComparison.Data regular point) (same : parameter = target)
    {comparison : ArcSamples.Data regular cell} {sample : ArcSamples.Sample comparison capSample}
    (alignment : SheetAlignment.RegularAlignment sample) (primitive_eq : alignment.primitive = value) :
    RegularEndpoint regular capSample (EndpointView.ofPoint
      point bounds same).point value := by
  cases same
  exact ⟨comparison, sample, alignment, primitive_eq⟩

namespace RegularCells

/-- Read the first retained cell's alignment through the actual first endpoint owner view. -/
def firstEndpoint (value : Polynomial) : {edges : List
  ParameterEdge} → {bank : Bank regular data edges} →
    {retained : ComparedCells source capSample depth bank} → (cells : RegularCells retained) →
    (owners : Owners bank) → {first last : Coordinate} → (chain : From first
      edges last) →
    (nonempty : edges ≠ []) → RegularCells.WithPrimitive value cells →
    RegularEndpoint regular capSample (owners.firstView
      chain nonempty).point value
  | _, _, _, .nil, .nil, _, _, _, nonempty, _ => False.elim (nonempty rfl)
  | _, _, _, .cons head _, .cons owner _, _, _, chain, _, shared =>
      RegularEndpoint.ofPoint owner.first
        owner.bounds.first chain.1.symm head.alignment shared.1

/-- Read the last retained cell's alignment through the actual last endpoint owner view. -/
def lastEndpoint (value : Polynomial) : {edges : List
  ParameterEdge} → {bank : Bank regular data edges} →
    {retained : ComparedCells source capSample depth bank} → (cells : RegularCells retained) →
    (owners : Owners bank) → {first last : Coordinate} → (chain : From first
      edges last) →
    (nonempty : edges ≠ []) → RegularCells.WithPrimitive value cells →
    RegularEndpoint regular capSample (owners.lastView
      chain nonempty).point value
  | _, _, _, .nil, .nil, _, _, _, nonempty, _ => False.elim (nonempty rfl)
  | _, _, _, .cons head .nil, .cons owner .nil, _, _, chain, _, shared =>
      RegularEndpoint.ofPoint owner.last owner.bounds.last
        chain.2 head.alignment shared.1
  | _, _, _, .cons _ (.cons next rest), .cons _ (.cons owner owners), _, _, chain, _, shared =>
      RegularCells.lastEndpoint value (.cons next
        rest) (.cons owner owners) chain.2 (by intro empty; cases empty) shared.2

/-- Read the common regular primitive at the exact retained whole-parent first endpoint. -/
def boundaryFirst (mesh : Mesh data) {bank : Bank regular data mesh.edges}
    {retained : ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : Owners bank) (links : Links owners) (boundary : Boundary mesh owners) (later :
      2 ≤ index) :
    RegularEndpoint regular capSample boundary.first.point
      (RegularCells.primitive cells) := by
  rw [boundary.first_eq]
  exact firstEndpoint (RegularCells.primitive
    cells) cells owners (mesh_from mesh) (mesh_nonempty mesh) (RegularCells.shared cells owners links
    later)

/-- Read the common regular primitive at the exact retained whole-parent last endpoint. -/
def boundaryLast (mesh : Mesh data) {bank : Bank regular data mesh.edges}
    {retained : ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : Owners bank) (links : Links owners) (boundary : Boundary mesh owners) (later :
      2 ≤ index) :
    RegularEndpoint regular capSample boundary.last.point
      (RegularCells.primitive cells) := by
  rw [boundary.last_eq]
  exact lastEndpoint (RegularCells.primitive
    cells) cells owners (mesh_from mesh) (mesh_nonempty mesh) (RegularCells.shared cells owners links
    later)

end RegularCells

variable {otherCount otherIndex : Nat} {otherParent :
  Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherPatch : UniformPrimitiveSheetCompatibility.PreparedPatch otherParent} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {otherEdge : ParameterEdge} {otherCell :
    Cell otherData otherEdge} {otherModel :
    RootModel otherCell} {otherParameter :
    Coordinate}
  {first : ArcOwners.Point cap model parameter} {last :
    ArcOwners.Point cap otherModel otherParameter}
  {otherSample : Primitives.Sample cap differential otherIndex box}
    {firstValue lastValue : Polynomial}

/-- An operational join between retained endpoint owners identifies their common polynomials when the original cap
samples and stages agree. -/
theorem RegularEndpoint.join (left : RegularEndpoint
  regular capSample first firstValue)
    (right : RegularEndpoint regular otherSample last
      lastValue) (joined : ArcOwners.Join first last)
    (indices : index = otherIndex) (samples : HEq capSample otherSample) (later : 2 ≤ index) : firstValue = lastValue :=
      by
  cases indices
  have same : capSample = otherSample := eq_of_heq samples
  cases same
  exact left.primitive_eq.symm.trans ((Join.primitive_eq joined left.alignment right.alignment later).trans
    right.primitive_eq)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints

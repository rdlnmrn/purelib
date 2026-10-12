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

variable {genus count index depth : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell} {parameter :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

set_option genInjectivity false in
/-- The retained cell alignment exhibiting the shared regular primitive at an actual parent endpoint owner. -/
structure RegularEndpoint (regular : RegularBounds.Data cap)
    (capSample : Primitives.Sample cap differential index box)
    (_point : ArcOwners.Point cap model parameter) (value : InverseRootPolynomial.Polynomial) where
  /-- The original retained arc comparison for this endpoint's cell. -/ comparison : ArcSamples.Data regular cell
  /-- The cached arc sample on the supplied cap primitive sample. -/ sample : ArcSamples.Sample comparison capSample
  /-- The retained regular-sheet alignment of that exact arc sample. -/ alignment : SheetAlignment.RegularAlignment
    sample
  /-- The retained alignment uses exactly the specified common polynomial. -/ primitive_eq : alignment.primitive = value

constructive_injectivity RegularEndpoint

/-- Transport the original cell alignment to its certified endpoint view without changing the sample. -/
def RegularEndpoint.ofPoint {target : InverseRootPolynomial.Coordinate} {value : InverseRootPolynomial.Polynomial}
    (point : ArcOwners.Point cap model parameter)
    (bounds : EndpointComparison.Data regular point) (same : parameter = target)
    {comparison : ArcSamples.Data regular cell} {sample : ArcSamples.Sample comparison capSample}
    (alignment : SheetAlignment.RegularAlignment sample) (primitive_eq : alignment.primitive = value) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint regular capSample (EndpointView.ofPoint
      point bounds same).point value := by
  cases same
  exact ⟨comparison, sample, alignment, primitive_eq⟩

namespace RegularCells

/-- Read the first retained cell's alignment through the actual first endpoint owner view. -/
def firstEndpoint (value : InverseRootPolynomial.Polynomial) : {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
    {retained : ParentPaths.ComparedCells source capSample depth bank} → (cells : RegularCells retained) →
    (owners : ParentOwners.Owners bank) → {first last : InverseRootPolynomial.Coordinate} → (chain : Owners.From first
      edges last) →
    (nonempty : edges ≠ []) → RegularCells.WithPrimitive value cells →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint regular capSample (owners.firstView
      chain nonempty).point value
  | _, _, _, .nil, .nil, _, _, _, nonempty, _ => False.elim (nonempty rfl)
  | _, _, _, .cons head _, .cons owner _, _, _, chain, _, shared =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint.ofPoint owner.first
        owner.bounds.first chain.1.symm head.alignment shared.1

/-- Read the last retained cell's alignment through the actual last endpoint owner view. -/
def lastEndpoint (value : InverseRootPolynomial.Polynomial) : {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
    {retained : ParentPaths.ComparedCells source capSample depth bank} → (cells : RegularCells retained) →
    (owners : ParentOwners.Owners bank) → {first last : InverseRootPolynomial.Coordinate} → (chain : Owners.From first
      edges last) →
    (nonempty : edges ≠ []) → RegularCells.WithPrimitive value cells →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint regular capSample (owners.lastView
      chain nonempty).point value
  | _, _, _, .nil, .nil, _, _, _, nonempty, _ => False.elim (nonempty rfl)
  | _, _, _, .cons head .nil, .cons owner .nil, _, _, chain, _, shared =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint.ofPoint owner.last owner.bounds.last
        chain.2 head.alignment shared.1
  | _, _, _, .cons _ (.cons next rest), .cons _ (.cons owner owners), _, _, chain, _, shared =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularCells.lastEndpoint value (.cons next
        rest) (.cons owner owners) chain.2 (by intro empty; cases empty) shared.2

/-- Read the common regular primitive at the exact retained whole-parent first endpoint. -/
def boundaryFirst (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (boundary : Owners.Boundary mesh owners) (later :
      2 ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint regular capSample boundary.first.point
      (RegularCells.primitive cells) := by
  rw [boundary.first_eq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularCells.firstEndpoint (RegularCells.primitive
    cells) cells owners (Owners.mesh_from mesh) (Owners.mesh_nonempty mesh) (RegularCells.shared cells owners links
    later)

/-- Read the common regular primitive at the exact retained whole-parent last endpoint. -/
def boundaryLast (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
    {retained : ParentPaths.ComparedCells source capSample depth bank} (cells : RegularCells retained)
    (owners : ParentOwners.Owners bank) (links : Owners.Links owners) (boundary : Owners.Boundary mesh owners) (later :
      2 ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint regular capSample boundary.last.point
      (RegularCells.primitive cells) := by
  rw [boundary.last_eq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularCells.lastEndpoint (RegularCells.primitive
    cells) cells owners (Owners.mesh_from mesh) (Owners.mesh_nonempty mesh) (RegularCells.shared cells owners links
    later)

end RegularCells

variable {otherCount otherIndex : Nat} {otherParent :
  Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {otherCell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge} {otherModel :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell} {otherParameter :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {first : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter} {last :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel otherParameter}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential otherIndex box}
    {firstValue lastValue : Purelib.Riemann.Normalization.InverseRootPolynomial.Polynomial}

/-- An operational join between retained endpoint owners identifies their common polynomials when the original cap
samples and stages agree. -/
theorem RegularEndpoint.join (left : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint
  regular capSample first firstValue)
    (right : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints.RegularEndpoint regular otherSample last
      lastValue) (joined : ArcOwners.Join first last)
    (indices : index = otherIndex) (samples : HEq capSample otherSample) (later : 2 ≤ index) : firstValue = lastValue :=
      by
  cases indices
  have same : capSample = otherSample := eq_of_heq samples
  cases same
  exact left.primitive_eq.symm.trans ((Join.primitive_eq joined left.alignment right.alignment later).trans
    right.primitive_eq)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints

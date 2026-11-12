module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns

@[expose] public section

/-! The same-differential primitive equality consumes the shared root-sign
comparison, which also applies across differentials. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedSigns

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {model : RootModel cell} {parameter :
    Coordinate}
  {otherCount : Nat} {otherParent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve
    differential}
  {otherPatch : PreparedPatch otherParent} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {otherEdge : ParameterEdge} {otherCell :
    Cell otherData otherEdge}
  {otherModel : RootModel otherCell}
    {otherParameter : Coordinate}
  {first : Point cap model parameter} {last :
    Point cap otherModel otherParameter}

variable {regular : RegularBounds.Data cap}
  {comparison : ArcSamples.Data regular cell}
  {otherComparison : ArcSamples.Data regular otherCell}
  {index : Nat} {box : Geometry.Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}
  {before : ArcSamples.Sample comparison capSample}
  {after : ArcSamples.Sample otherComparison capSample}

/-- The join identifies the actual cached signed polynomials, so later boundary evaluation can reuse one primitive
across the joined parents. -/
theorem Join.primitive_eq (joined : Join first last)
    (left : SheetAlignment.RegularAlignment before)
    (right : SheetAlignment.RegularAlignment after) (later : 2 ≤ index) :
    left.primitive = right.primitive := by
  rw [left.primitive_eq, right.primitive_eq, Join.paired_same_sign joined left right later]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedSigns

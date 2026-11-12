module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
import Init.Prelude
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation

public section

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
open Purelib.Riemann.Normalization

/-! Paired ribbon evaluation consumes the complete common reciprocal mesh.
Both interval-containment obligations come from its retained cell owners. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon (PairedRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.PairedRibbonRequest (Evaluation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {otherPatch : PreparedPatch
    (recastCenteredEdge other parent)}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Cover data} {secondCover :
    Cover otherData}
  {regular : RegularBounds.Data cap}
  {index : Nat} {box otherBox : Geometry.Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box}
  {otherSample : Cap.Primitives.Sample cap other index otherBox}

/-- No caller-supplied intersection, endpoint order or interval-ownership proof remains: the executable common cover
supplies the geometric obligations. -/
@[expose] def evaluateCommon (interval : CommonInterval firstCover secondCover)
    {comparison : Data regular interval.first.cell} {otherComparison : Data regular
      interval.second.cell}
    {retained : Sample comparison sample} {otherRetained : Sample otherComparison otherSample}
    {target : Coordinate} {minimum : Nat}
    (request : PairedRibbonRequest comparison otherComparison target minimum)
    (source : SourcePrimitive data index) (otherSource :
      SourcePrimitive otherData index)
    (left : RegularAlignment retained) (right : RegularAlignment otherRetained)
    (later : request.index ≤ index) (depth : Nat) :
    Evaluation request source otherSource left right interval.edge.left.parameter
      interval.edge.right.parameter depth :=
  request.evaluate source otherSource left right later interval.edge.left.parameter interval.edge.right.parameter
    interval.first.lower interval.first.upper interval.second.lower interval.second.upper interval.ordered depth

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbon

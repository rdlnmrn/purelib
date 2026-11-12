module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSigns

@[expose] public section

/-! The actual endpoint certificates of two differentials retain a single
sheet bit when their reciprocal root owners are joined. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedEndpoints
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Polynomial)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints (RegularEndpoint)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
variable {genus count otherCount index : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {parent : CenteredEdge curve differential} {otherParent :
    CenteredEdge curve other}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {otherPatch :
    Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : ParameterEdge} {cell :
    Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {model : RootModel cell} {otherModel :
    RootModel otherCell} {parameter
    otherParameter : Coordinate}
  {first : ArcOwners.Point cap model parameter} {last :
    ArcOwners.Point cap otherModel otherParameter}
  {box otherBox : Geometry.Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box}
  {otherSample : Cap.Primitives.Sample cap other index otherBox}
    {firstValue lastValue : Polynomial}

/-- Different numerators do not choose independent sheet signs. This reads the two cached signed primitives and the
actual retained root join. -/
theorem RegularEndpoint.paired_primitive_signed (left : RegularEndpoint regular sample first
  firstValue)
    (right : RegularEndpoint regular otherSample last lastValue) (joined : ArcOwners.Join first last)
    (later : 2 ≤ index) :
    (firstValue, lastValue) =
      (if left.alignment.first.flip then -sample.primitive.value else sample.primitive.value,
       if left.alignment.first.flip then -otherSample.primitive.value else otherSample.primitive.value) := by
  have sign := Join.paired_same_sign joined left.alignment right.alignment later
  have firstEq := left.primitive_eq.symm.trans left.alignment.primitive_eq
  have lastEq := right.primitive_eq.symm.trans right.alignment.primitive_eq
  rw [← sign] at lastEq
  exact congrArg₂ Prod.mk firstEq lastEq

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedEndpoints

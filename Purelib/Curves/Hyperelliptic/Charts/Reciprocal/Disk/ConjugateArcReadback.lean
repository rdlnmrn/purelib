module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Conjugate whole-parent area reads the unsigned inverse arc while retaining
the endpoint chord needed by the exterior energy comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateArcReadback

open Purelib.Riemann.Normalization

variable {genus count otherCount : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential other :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {firstCover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {secondCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover firstCover secondCover}
  {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage depth : Nat} {box otherBox :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {source : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data stage} {otherSource :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive otherData stage}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest regular common target minimum}
  {evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.Evaluation request sample
    otherSample source otherSource depth}

open Purelib.Data.Rat.Fraction.Compatibility

/-- The complete cap increment path is the actual inverse arc minus its
endpoint chord. The endpoints are those of the retained source parent. -/
theorem cap_conjugate_area_arc (fine : Nat) :
    Path.PairedIncrementArea.area (Path.Dyadic.DyadicPairedPrimitivePaths.increments (fun parameter =>
      Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
        otherSample parameter)) fine 0 1) =
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
      (fun point => Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
        otherSample.primitive.value.eval point⟩)
      fine (parent.edge.point 0) (parent.edge.point 1) -
    Topology.Polygon.Stokes.edgeArea (Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
      otherSample 0))
      (Path.ConjugateIncrementComparison.conjugateFirst
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
        otherSample 1)) := open Purelib.Polynomial in by
  rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_area]
  have interpolate (parameter : Normalization.InverseRootPolynomial.Coordinate) : parent.edge.point parameter =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source (parent.edge.point 0) (parent.edge.point 1)
        parameter := by
    change parent.edge.localSegment.pointAt parameter =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source (parent.edge.localSegment.pointAt 0)
        (parent.edge.localSegment.pointAt 1) parameter
    rw [Geometry.ClearPath.ClearSegment.pointAt_zero, Geometry.ClearPath.ClearSegment.pointAt_one]
    rfl
  have points (parameter : Normalization.InverseRootPolynomial.Coordinate) :
    Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
        otherSample parameter) =
      Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source (parent.edge.point 0) (parent.edge.point 1)
          parameter)⁻¹,
        otherSample.primitive.value.eval
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source (parent.edge.point 0) (parent.edge.point 1)
          parameter)⁻¹⟩ := by
    dsimp only [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues]
    rw [interpolate]
  exact congrArg (fun value => value -
    Topology.Polygon.Stokes.edgeArea (Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
      otherSample 0))
      (Path.ConjugateIncrementComparison.conjugateFirst
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
        otherSample 1)))
    (Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr points fine 0 1)

/-- Requested comparison with the literal inverse arc, keeping the exact
endpoint chord until the exterior assembly accounts for it. -/
theorem AreaRequest.Certified.conjugate_arc_error
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest request} {fine : Nat}
    (certified : Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest.AreaRequest.Certified prepared sample
      otherSample fine) (later : prepared.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (Path.Dyadic.DyadicPairedPrimitivePaths.increments (fun parameter =>
      Path.ConjugateIncrementComparison.conjugateFirst
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues certified.source
          certified.otherSource parameter)) (common.depth + fine) 0 1) -
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => Path.ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (common.depth + fine) (parent.edge.point 0) (parent.edge.point 1) -
      Topology.Polygon.Stokes.edgeArea (Path.ConjugateIncrementComparison.conjugateFirst
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent) sample
        otherSample 0))
        (Path.ConjugateIncrementComparison.conjugateFirst
          (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues (parent := parent)
          sample otherSample 1)))) < target := by
  have bound :=
    Hyperelliptic.Charts.Reciprocal.Disk.ConjugateAreaRequest.AreaRequest.Certified.conjugate_unsigned_area_error
    certified later
  rw [Hyperelliptic.Charts.Reciprocal.Disk.ConjugateArcReadback.cap_conjugate_area_arc] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateArcReadback

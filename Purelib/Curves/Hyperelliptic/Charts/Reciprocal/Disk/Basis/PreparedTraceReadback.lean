module
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.UniformPreparedRequests

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Integration

open Purelib.Riemann.Readings.UniformPreparedRequests

@[expose] public section

/-! Trace resampling reads the actual common-parent polynomial, child mesh
and retained depth bounds, without acquiring another bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedTraceReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest
  (Acquisition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling (PrimitiveSlopeBound)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent} {data :
    Data patch count}
  {cover : Cover data} {covers :
    BasisSourceCovers parent}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {minimum : Nat} {common :
    BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate} {floor
    index depth : Nat} {box : Geometry.Rational.Box}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {polynomials : RegularBasisPolynomials cap
    index box} {originals :
    CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : BasisSourceLocations.SampleBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- Supply the resampling hypothesis from the cached source cover and the acquisition's exact polynomial readback. -/
theorem row_slope (acquired : Acquisition request polynomials originals cells coefficients
  depth) (row : Fin genus) :
    PrimitiveSlopeBound (covers.get row).data.sourceSlope
      (RequestedParents.cons (acquired.prepared.get row).localRequest .nil) := by
  constructor
  · intro first last firstInside lastInside
    rw [acquired.primitive_eq row]
    have scalar := (originals.get row).increment_bound firstInside lastInside
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  · trivial

/-- Read the retained nonuniform depth bounds from this exact acquisition. -/
theorem row_depths (acquired : Acquisition request polynomials originals cells coefficients
  depth)
    (row : Fin genus) {scheduled : Nat} (later : common.depth + acquired.extraDepth ≤ scheduled) :
    PreparedDyadicPrimitiveResampling.PreparedDepthBounds depth scheduled
      (RequestedParents.cons (acquired.prepared.get row).localRequest .nil) := by
  constructor
  · rw [acquired.depths_eq row]
    exact ⟨acquired.minimum_le.trans (Nat.le_add_left _ _), later⟩
  · trivial

/-- Identify the polynomial path with the acquisition's actual child mesh, without identifying its polynomial increments
with model integral samples. -/
theorem row_path (acquired : Acquisition request polynomials originals cells coefficients
  depth) (row : Fin genus) :
    PreparedDyadicPrimitiveResampling.preparedPrimitivePath
      (RequestedParents.cons (acquired.prepared.get row).localRequest .nil) =
    (acquired.prepared.get row).localRequest.request.block.children.map (fun child =>
      (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (child.edge.point 1) -
        (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (child.edge.point 0)) := by
  change DyadicPrimitivePaths.dyadicIncrements _ _ 0 1 ++ [] = _
  rw [Append.append_nil]
  exact (acquired.paths row (acquired.prepared.get row).localRequest.request.model.primitive.value.eval).symm

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedTraceReadback

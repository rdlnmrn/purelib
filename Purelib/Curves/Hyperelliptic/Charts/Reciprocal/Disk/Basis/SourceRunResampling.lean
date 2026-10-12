module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Integration.Path.Dyadic.SourceDyadicResampling
public import Purelib.Integration.Path.ConjugatePathReadback
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback.BasisPreparedCommonRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback.BasisPreparedCommonRequest

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  Acquisition.ChildPairs

open
  Acquisition.ChildPairs

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.Dyadic.SourceListResampling

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Resample physical source runs onto the exact cached common-parent polygon. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRunResampling

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {index : Nat}

variable {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {minimum floor depth : Nat}
  {common : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
    {areaAllowance sourceTarget coefficientTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {box : Purelib.Geometry.Rational.Box} {polynomials :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {acquired :
    PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition
    request polynomials originals cells coefficients depth}

open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal conjugateDiagonal_sub conjugateDiagonal_area
  conjugateDiagonal_dyadic)

/-- The actual conjugate physical source run approximates the retained common-parent source polygon.

The homogeneous area bound uses the maximum of the supplied run width and the original dyadic width, retaining the exact
source primitive and coefficient vector. -/
theorem BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.source_run_bound
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs)
    {points : List InverseRootPolynomial.Coordinate} {width : InverseRootPolynomial.Coordinate}
    (chain : SourceResampling.Chain 0 points 1)
    (steps : SourceResampling.widths 0 points width) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
      (SourceListResampling.increments (fun t => ConjugatePathReadback.conjugateDiagonal (PrimitiveBank.value originals
        coefficients t)) 0 points) -
      weighted.source.area) ≤
      16 * (BasisSourceCovers.primitiveSlope covers)^2 *
        (max width ((1 / 2 : InverseRootPolynomial.Coordinate)^(common.depth + acquired.extraDepth)))^2 *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have bounded := SourceDyadicResampling.dyadic_resampling_bound
    (fun t => ConjugatePathReadback.conjugateDiagonal (PrimitiveBank.value originals coefficients t))
    (density := BasisSourceCovers.primitiveSlope covers * PreparedObservationCoercivity.coefficientNormSq coefficients)
    (fun a b al au bl bu => by
      rw [← ConjugatePathReadback.conjugateDiagonal_sub]
      have bound := ReciprocalDiskArcOwners.increment_bound
        originals coefficients (first := a) (last := b) ⟨al, au⟩ ⟨bl, bu⟩
      constructor
      · change Data.Gaussian.Basic.Canonical.normSq
          (Data.Gaussian.Basic.conj
            (PrimitiveBank.value originals coefficients b -
              PrimitiveBank.value originals coefficients a)) ≤ _
        rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
        exact (Data.Gaussian.Norm.Basic.normSq_conj _).trans_le bound
      · change Data.Gaussian.Basic.Canonical.normSq
          (PrimitiveBank.value originals coefficients b -
            PrimitiveBank.value originals coefficients a) ≤ _
        rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
        exact bound)
    chain steps (common.depth + acquired.extraDepth)
  rw [ConjugatePathReadback.conjugateDiagonal_dyadic, ConjugatePathReadback.conjugateDiagonal_area, ←
    Weighted.source_path weighted, ← weighted.source.area_eq] at bounded
  exact bounded.trans_eq (by ring1)

/-- Endpoint equality is separate from the area estimate and retains the actual common-parent source total. -/
theorem BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.source_run_total
    {pairs : Acquisition.ChildPairs acquired} (weighted : ChildPairs.Weighted pairs)
    {points : List InverseRootPolynomial.Coordinate} (chain : SourceResampling.Chain 0 points 1) :
    PairedIncrementArea.total
      (SourceListResampling.increments (fun t => ConjugatePathReadback.conjugateDiagonal (PrimitiveBank.value originals
        coefficients t)) 0 points) =
      ConjugatePathReadback.conjugateDiagonal weighted.source.total := by
  rw [SourceListResampling.increments_total, Chain.terminal_eq chain, ← ConjugatePathReadback.conjugateDiagonal_sub,
    Weighted.source_total weighted]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRunResampling

module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Vector

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

@[expose] public section

/-! Common-interval vertex readings retain the very same pullback polynomial
as the interval path, even when the anchor point changes. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations (SampleBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceOwner)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (comparisonLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

namespace BasisSourceLocations

variable {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {model :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {anchor :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter}

/-- Transporting a retained reciprocal sample across an exact source-owner equality preserves every scalar pullback
polynomial evaluation. -/
private theorem cast_sample_value {row : Fin genus}
    (first last : SourceRequests.BasisSourceOwner regular anchor row) (equal : first = last)
    (polynomial : Primitives.Sample cap (PeriodMatrix.standardDifferential row) index box)
    (sample : ArcSamples.Sample last.comparison polynomial) (point : InverseRootPolynomial.Gaussian) :
    ((congrArg (fun owner : SourceRequests.BasisSourceOwner regular anchor row =>
      ArcSamples.Sample owner.comparison polynomial) equal).mpr sample).pullback.value.eval point =
      sample.pullback.value.eval point := by
  cases equal
  rfl

/-- The retained row of a located sample bank evaluates exactly the original source location's cached pullback
polynomial. -/
theorem samples_value (locations : SourceLocations.BasisSourceLocations regular anchor covers)
    (bank : BasisSourceLocations.SampleBank covers index) (polynomials : CapBasisEnergy.RegularBasisPolynomials cap
      index box)
    (row : Fin genus) (point : InverseRootPolynomial.Gaussian) :
    ((locations.samples bank polynomials).get row).pullback.value.eval point =
      ((locations.get row).sample (bank.get row) (polynomials.get row)).pullback.value.eval point := by
  unfold BasisSourceLocations.samples
  rw [DependentVector.ofFn_get]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback.BasisSourceLocations.cast_sample_value
    _ _ (locations.owners_get row) _ _ point

end BasisSourceLocations

namespace BasisCommonInterval

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {edge :
  Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {model :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Changing the root-reading anchor does not resample the interval's retained source cells or change their pullback
polynomial values. -/
theorem locations_sample_value (interval : CommonCover.BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap) (anchor : ArcOwners.Point cap model parameter)
    (between : interval.edge.left.parameter ≤ parameter ∧ parameter ≤ interval.edge.right.parameter)
    (bank : BasisSourceLocations.SampleBank covers index) (polynomials : CapBasisEnergy.RegularBasisPolynomials cap
      index box)
    (row : Fin genus) (point : InverseRootPolynomial.Gaussian) :
    (((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.locations interval
      regular anchor between).samples bank polynomials).get row).pullback.value.eval point =

        (((CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
        interval regular).samples bank polynomials).get row).pullback.value.eval point := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback.BasisSourceLocations.samples_value,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback.BasisSourceLocations.samples_value]
  unfold BasisCommonInterval.locations BasisCommonInterval.comparisonLocations
  rw [DependentVector.ofFn_get]
  unfold BasisCommonInterval.locations
  rw [DependentVector.ofFn_get]
  rfl

end BasisCommonInterval
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback

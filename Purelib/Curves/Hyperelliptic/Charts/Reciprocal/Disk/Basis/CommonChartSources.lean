module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
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
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackReadback

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests

open Purelib.Data.Vector

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Chart vertex requests on the fixed owners of one common interval. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Prepared Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (EndpointSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

namespace EndpointSources

/-- Keep the common interval's source cells at boundary vertices as well as internal vertices, instead of performing
another pointwise cover lookup. -/
def onInterval (prepared : Prepared regular model parameter target floor)
    (interval : BasisCommonInterval cover covers)
    (inside : interval.edge.left.parameter ≤ parameter ∧ parameter ≤ interval.edge.right.parameter)
    (sourceTarget : Coordinate) (positive : 0 < sourceTarget) (sourceFloor : Nat) :
    EndpointSources prepared covers sourceTarget sourceFloor :=
  let locations := interval.locations regular prepared.point inside
  ⟨locations, BasisSourceRequest.build locations.owners sourceTarget positive sourceFloor⟩

variable {prepared : Prepared regular model parameter
  target floor}
  {interval : BasisCommonInterval cover covers}
  {inside : interval.edge.left.parameter ≤ parameter ∧ parameter ≤ interval.edge.right.parameter}
  {positive : 0 < sourceTarget}
  {index stage minimum : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {comparison : ArcSamples.Data regular cell}
  {sample : ArcSamples.Sample comparison capSample}
  {charts : BasisSourceRequest.ChartRequest
    (onInterval prepared
      interval inside sourceTarget positive sourceFloor).request polynomials minimum}
  {bank : BasisSourceLocations.SampleBank
    covers index}
  {reading : Reading regular model sample parameter
    target floor stage}

/-- The chart endpoint certificate reads precisely the polynomial used by the common interval's pullback path. -/
theorem onInterval_value
    (evaluated : EndpointSources.Evaluation
      (onInterval prepared interval
      inside sourceTarget positive sourceFloor) charts bank reading)
    (originals : PrimitiveBank covers index)
    (coefficients : GaussianVector genus) :
    sumFin (fun row => coefficients row * evaluated.evaluated.sources row) =
      (BasisCommonInterval.primitiveSample interval regular polynomials originals bank).pullbackValue coefficients
        parameter := by
  unfold BasisCommonInterval.PrimitiveSample.pullbackValue
  apply sumFin_congr
  intro row
  apply congrArg (fun value => coefficients row * value)
  rw [evaluated.evaluated.sources_eq row, evaluated.samples_eq]
  have pointEq :
      (((interval.locations regular prepared.point inside).owners.get row).parent.edge.point
        ((interval.locations regular prepared.point inside).owners.get row).parameter) = parent.edge.point parameter :=
          by
    rw [BasisSourceLocations.owners_get]
    unfold BasisCommonInterval.locations
    rw [DependentVector.ofFn_get]
    rfl
  change (((interval.locations regular prepared.point inside).samples bank polynomials).get row).pullback.value.eval
    (((interval.locations regular prepared.point inside).owners.get row).parent.edge.point
      ((interval.locations regular prepared.point inside).owners.get row).parameter)⁻¹ = _
  rw [pointEq, BasisCommonInterval.locations_sample_value interval]
  have comparisonPoint :
      (((BasisCommonInterval.comparisonLocations interval regular).owners.get row).parent.edge.point parameter) =
        parent.edge.point parameter := by
    rw [BasisSourceLocations.owners_get]
    unfold BasisCommonInterval.comparisonLocations
      BasisCommonInterval.locations
    rw [DependentVector.ofFn_get]
    rfl
  rw [comparisonPoint]
  rfl

/-- The original common-interval pullback value and actual chart root reading satisfy the retained homogeneous basis
comparison bound. -/
theorem onInterval_accurate
    (evaluated : EndpointSources.Evaluation
      (onInterval prepared interval
      inside sourceTarget positive sourceFloor) charts bank reading)
    (originals : PrimitiveBank covers index)
    (coefficients : GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq
      ((BasisCommonInterval.primitiveSample interval regular polynomials originals bank).pullbackValue coefficients
        parameter -
        polynomials.value coefficients reading.root.coordinate) ≤
      10 * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  rw [← onInterval_value evaluated
    originals coefficients]
  exact evaluated.evaluated.accurate coefficients

end EndpointSources
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSources

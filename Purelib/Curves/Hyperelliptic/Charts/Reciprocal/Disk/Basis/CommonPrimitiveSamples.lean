module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Vector

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Sample common intervals from the retained original and reciprocal banks.
The certified comparison uses the same original polynomial on every interval. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceCover
  BasisSourceLocations BasisSourceLocation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceOwner BasisSourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison (BasisPrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point)

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

/-- Original source primitives shared by all common intervals of this parent. -/
@[expose] def PrimitiveBank (covers : SourceLocations.BasisSourceCovers parent) (index : Nat) :=
  Data.Vector.DependentVector (fun row => UniformReciprocalPrimitives.SourcePrimitive (covers.get row).data index)

variable {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {model :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {anchor :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter}

/-- Transport the original cached source primitive along the retained exact source-owner equality.

The equality transports the complete original primitive to the requested
source owner without acquiring or reconstructing its cached polynomial. -/
@[expose] def attach {row : Fin genus} {source : SourceLocations.BasisSourceCover parent row}
    (location : SourceLocations.BasisSourceLocation regular anchor source) (owner : SourceRequests.BasisSourceOwner
      regular anchor row)
    (equal : location.owner = owner) (primitive : UniformReciprocalPrimitives.SourcePrimitive source.data index) :
    UniformReciprocalPrimitives.SourcePrimitive owner.data index :=
  equal ▸ primitive

/-- Transporting the retained primitive to its exact source owner preserves every scalar polynomial evaluation. -/
private theorem attach_value {row : Fin genus} {source : SourceLocations.BasisSourceCover parent row}
    (location : SourceLocations.BasisSourceLocation regular anchor source) (owner : SourceRequests.BasisSourceOwner
      regular anchor row)
    (equal : location.owner = owner) (primitive : UniformReciprocalPrimitives.SourcePrimitive source.data index)
    (point : InverseRootPolynomial.Gaussian) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.attach location owner
      equal primitive).primitive.value.eval point = primitive.primitive.value.eval point := by
  cases equal
  rfl

/-- Reattach the original cached primitives to the located source owners. -/
@[expose] def originals (locations : SourceLocations.BasisSourceLocations regular anchor covers) (bank :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers
  index) :
    BasisPrimitiveRequest.Sources locations.owners index :=
  DependentVector.ofFn fun row =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.attach (locations.get
      row) (locations.owners.get row) (locations.owners_get row).symm (bank.get row)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations in
/-- Scalar readback avoids an equality between vector-producing functions. -/
theorem originals_value (locations : SourceLocations.BasisSourceLocations regular anchor covers) (bank :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers
  index)
    (row : Fin genus) (point : InverseRootPolynomial.Gaussian) :
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.originals locations
      bank).get row).primitive.value.eval point = (bank.get row).primitive.value.eval point := by
  unfold originals
  rw [DependentVector.ofFn_get]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.attach_value ..

end BasisSourceLocations

namespace BasisCommonInterval

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

/-- The first point fixes one set of owners for the entire common interval. -/
@[expose] def comparisonLocations (interval : CommonCover.BasisCommonInterval cover covers) (regular :
  RegularBounds.Data cap) :=
  let model := RootModel.build interval.anchor.cell
  let point := ArcOwners.Point.build cap model interval.edge.left.parameter
    ⟨interval.anchor.lower, interval.ordered.trans interval.anchor.upper⟩
  BasisCommonInterval.locations interval regular point ⟨le_rfl, interval.ordered⟩

/-- The basis primitive comparison request on the original owners retained for one complete common interval. -/
@[expose] def PrimitiveRequest (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (target : InverseRootPolynomial.Coordinate) (floor : Nat) :=
  PrimitiveComparison.BasisPrimitiveRequest
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
    interval regular).owners target floor

/-- Prepare the original common interval's basis primitive comparison at the positive target and retained stage floor.
-/
@[expose] def primitiveRequest (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveRequest
      interval regular target floor :=
  BasisPrimitiveRequest.build
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
    interval regular).owners target positive floor

set_option genInjectivity false in
/-- The interval retains its numerical pullbacks and reuses the original bank. No inverse refinement or original source
polynomial is rebuilt. -/
structure PrimitiveSample (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data cap)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) where
  /-- The original cached basis primitives transported to this interval's exact retained source owners. -/ originals :
    BasisPrimitiveRequest.Sources
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
    interval regular).owners index
  /-- The actual reciprocal basis samples on the same retained original source owners. -/ pullbacks :
    BasisSourceRequest.Samples
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
    interval regular).owners polynomials

constructive_injectivity PrimitiveSample

/-- Read each retained reciprocal cell once, using its existing inverse. -/
@[expose] def primitiveSample (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers
      index) (cells : BasisSourceLocations.SampleBank covers index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample
      interval regular polynomials :=
  let locations :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
    interval regular
  ⟨BasisSourceLocations.originals locations originals, locations.samples cells polynomials⟩

namespace PrimitiveSample

variable {interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers} {polynomials :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

/-- The coefficient-weighted original primitive value at the supplied parameter of the retained parent interval. -/
@[expose] def sourceValue (sample :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample interval
  regular polynomials) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row * (sample.originals.get row).primitive.value.eval
    (((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
      interval regular).owners.get row).parent.edge.point parameter)

/-- The coefficient-weighted reciprocal pullback value at the inverse physical point of the retained parent parameter.
-/
@[expose] def pullbackValue (sample :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample interval
  regular polynomials) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row * (sample.pullbacks.get row).pullback.value.eval
    (((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
      interval regular).owners.get row).parent.edge.point parameter)⁻¹

/-- Every interval reads the same original primitive function on the physical parent, including when adjacent intervals
have different reciprocal owners. -/
theorem sourceValue_readback (interval : CommonCover.BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap) (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers
      index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (parameter : InverseRootPolynomial.Coordinate) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.primitiveSample
      interval regular polynomials originals cells).sourceValue coefficients parameter =
      FiniteSum.Fin.sumFin (fun row => coefficients row * (originals.get row).primitive.value.eval (parent.edge.point
        parameter)) := by
  unfold CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample.sourceValue
  apply FiniteSum.Fin.sumFin_congr
  intro row
  change coefficients row *
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.originals
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
    interval regular) originals).get row).primitive.value.eval
    (((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.comparisonLocations
      interval regular).owners.get row).parent.edge.point parameter) = _
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.originals_value,
    BasisSourceLocations.owners_get]
  rfl

/-- Both endpoint differences use the same retained owners and original bank. -/
theorem accurate (sample :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample interval
  regular polynomials) {target : InverseRootPolynomial.Coordinate} {floor : Nat}
    (request :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveRequest
      interval regular target floor) (later : request.index ≤ index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {first last : InverseRootPolynomial.Coordinate}
    (firstInside : interval.edge.left.parameter ≤ first ∧ first ≤ interval.edge.right.parameter)
    (lastInside : interval.edge.left.parameter ≤ last ∧ last ≤ interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((sample.sourceValue coefficients last - sample.sourceValue coefficients
      first) -
      (sample.pullbackValue coefficients last - sample.pullbackValue coefficients first)) ≤
      target * (last - first)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := request.accurate sample.originals sample.pullbacks later coefficients
    (fun row => BasisCommonInterval.locations_contains interval regular _ ⟨le_rfl, interval.ordered⟩ firstInside row)
    (fun row => BasisCommonInterval.locations_contains interval regular _ ⟨le_rfl, interval.ordered⟩ lastInside row)
  have sourceEq : sample.sourceValue coefficients last - sample.sourceValue coefficients first =
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        ((sample.originals.get row).primitive.value.eval
          (((comparisonLocations
          interval regular).owners.get row).parent.edge.point last) -
          (sample.originals.get row).primitive.value.eval
            (((comparisonLocations
            interval regular).owners.get row).parent.edge.point first))) := by
    unfold CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample.sourceValue
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun _ => by ring1)
  have pullbackEq : sample.pullbackValue coefficients last - sample.pullbackValue coefficients first =
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        ((sample.pullbacks.get row).pullback.value.eval
          (((comparisonLocations
          interval regular).owners.get row).parent.edge.point last)⁻¹ -
          (sample.pullbacks.get row).pullback.value.eval
            (((comparisonLocations
            interval regular).owners.get row).parent.edge.point first)⁻¹)) := by
    unfold CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample.pullbackValue
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun _ => by ring1)
  rw [sourceEq, pullbackEq]
  exact bound

end PrimitiveSample
end BasisCommonInterval
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

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

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {covers :
    BasisSourceCovers parent}
  {index : Nat} {box : Geometry.Rational.Box}

namespace BasisSourceLocations

/-- Original source primitives shared by all common intervals of this parent. -/
@[expose] def PrimitiveBank (covers : BasisSourceCovers parent) (index : Nat) :=
  DependentVector (fun row => SourcePrimitive (covers.get row).data index)

variable {edge : ParameterEdge} {cell :
  Cell data edge} {model :
  RootModel cell}
  {parameter : Coordinate} {anchor :
    Point cap model parameter}

/-- Transport the original cached source primitive along the retained exact source-owner equality.

The equality transports the complete original primitive to the requested
source owner without acquiring or reconstructing its cached polynomial. -/
@[expose] def attach {row : Fin genus} {source : BasisSourceCover parent row}
    (location : BasisSourceLocation regular anchor source) (owner : BasisSourceOwner
      regular anchor row)
    (equal : location.owner = owner) (primitive : SourcePrimitive source.data index) :
    SourcePrimitive owner.data index :=
  equal ▸ primitive

/-- Transporting the retained primitive to its exact source owner preserves every scalar polynomial evaluation. -/
private theorem attach_value {row : Fin genus} {source : BasisSourceCover parent row}
    (location : BasisSourceLocation regular anchor source) (owner : BasisSourceOwner
      regular anchor row)
    (equal : location.owner = owner) (primitive : SourcePrimitive source.data index)
    (point : Gaussian) :
    (attach location owner
      equal primitive).primitive.value.eval point = primitive.primitive.value.eval point := by
  cases equal
  rfl

/-- Reattach the original cached primitives to the located source owners. -/
@[expose] def originals (locations : BasisSourceLocations regular anchor covers) (bank :
  PrimitiveBank covers
  index) :
    BasisPrimitiveRequest.Sources locations.owners index :=
  DependentVector.ofFn fun row =>
    attach (locations.get
      row) (locations.owners.get row) (locations.owners_get row).symm (bank.get row)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations in
/-- Scalar readback avoids an equality between vector-producing functions. -/
theorem originals_value (locations : BasisSourceLocations regular anchor covers) (bank :
  PrimitiveBank covers
  index)
    (row : Fin genus) (point : Gaussian) :
    ((BasisSourceLocations.originals locations
      bank).get row).primitive.value.eval point = (bank.get row).primitive.value.eval point := by
  unfold originals
  rw [DependentVector.ofFn_get]
  exact attach_value ..

end BasisSourceLocations

namespace BasisCommonInterval

variable {cover : Cover data}

/-- The first point fixes one set of owners for the entire common interval. -/
@[expose] def comparisonLocations (interval : BasisCommonInterval cover covers) (regular :
  RegularBounds.Data cap) :=
  let model := RootModel.build interval.anchor.cell
  let point := Point.build cap model interval.edge.left.parameter
    ⟨interval.anchor.lower, interval.ordered.trans interval.anchor.upper⟩
  BasisCommonInterval.locations interval regular point ⟨le_rfl, interval.ordered⟩

/-- The basis primitive comparison request on the original owners retained for one complete common interval. -/
@[expose] def PrimitiveRequest (interval : BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (target : Coordinate) (floor : Nat) :=
  BasisPrimitiveRequest
    (comparisonLocations
    interval regular).owners target floor

/-- Prepare the original common interval's basis primitive comparison at the positive target and retained stage floor.
-/
@[expose] def primitiveRequest (interval : BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
      PrimitiveRequest
      interval regular target floor :=
  BasisPrimitiveRequest.build
    (comparisonLocations
    interval regular).owners target positive floor

set_option genInjectivity false in
/-- The interval retains its numerical pullbacks and reuses the original bank. No inverse refinement or original source
polynomial is rebuilt. -/
structure PrimitiveSample (interval : BasisCommonInterval cover covers) (regular : RegularBounds.Data cap)
    (polynomials : RegularBasisPolynomials cap index box) where
  /-- The original cached basis primitives transported to this interval's exact retained source owners. -/ originals :
    BasisPrimitiveRequest.Sources
    (comparisonLocations
    interval regular).owners index
  /-- The actual reciprocal basis samples on the same retained original source owners. -/ pullbacks :
    BasisSourceRequest.Samples
    (comparisonLocations
    interval regular).owners polynomials

constructive_injectivity PrimitiveSample

/-- Read each retained reciprocal cell once, using its existing inverse. -/
@[expose] def primitiveSample (interval : BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (polynomials : RegularBasisPolynomials cap index box)
    (originals :
      BasisSourceLocations.PrimitiveBank covers
      index) (cells : BasisSourceLocations.SampleBank covers index) :
    PrimitiveSample
      interval regular polynomials :=
  let locations :=
    comparisonLocations
    interval regular
  ⟨BasisSourceLocations.originals locations originals, locations.samples cells polynomials⟩

namespace PrimitiveSample

variable {interval : BasisCommonInterval cover
  covers} {polynomials :
  RegularBasisPolynomials cap index box}

/-- The coefficient-weighted original primitive value at the supplied parameter of the retained parent interval. -/
@[expose] def sourceValue (sample :
  PrimitiveSample interval
  regular polynomials) (coefficients : GaussianVector genus)
    (parameter : Coordinate) : Gaussian :=
  sumFin fun row => coefficients row * (sample.originals.get row).primitive.value.eval
    (((comparisonLocations
      interval regular).owners.get row).parent.edge.point parameter)

/-- The coefficient-weighted reciprocal pullback value at the inverse physical point of the retained parent parameter.
-/
@[expose] def pullbackValue (sample :
  PrimitiveSample interval
  regular polynomials) (coefficients : GaussianVector genus)
    (parameter : Coordinate) : Gaussian :=
  sumFin fun row => coefficients row * (sample.pullbacks.get row).pullback.value.eval
    (((comparisonLocations
      interval regular).owners.get row).parent.edge.point parameter)⁻¹

/-- Every interval reads the same original primitive function on the physical parent, including when adjacent intervals
have different reciprocal owners. -/
theorem sourceValue_readback (interval : BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap) (polynomials : RegularBasisPolynomials cap index box)
    (originals :
      BasisSourceLocations.PrimitiveBank covers
      index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : GaussianVector genus) (parameter : Coordinate) :
    (primitiveSample
      interval regular polynomials originals cells).sourceValue coefficients parameter =
      sumFin (fun row => coefficients row * (originals.get row).primitive.value.eval (parent.edge.point
        parameter)) := by
  unfold sourceValue
  apply sumFin_congr
  intro row
  change coefficients row *
    ((BasisSourceLocations.originals
    (comparisonLocations
    interval regular) originals).get row).primitive.value.eval
    (((comparisonLocations
      interval regular).owners.get row).parent.edge.point parameter) = _
  rw [BasisSourceLocations.originals_value,
    BasisSourceLocations.owners_get]
  rfl

/-- Both endpoint differences use the same retained owners and original bank. -/
theorem accurate (sample :
  PrimitiveSample interval
  regular polynomials) {target : Coordinate} {floor : Nat}
    (request :
      PrimitiveRequest
      interval regular target floor) (later : request.index ≤ index)
    (coefficients : GaussianVector genus) {first last : Coordinate}
    (firstInside : interval.edge.left.parameter ≤ first ∧ first ≤ interval.edge.right.parameter)
    (lastInside : interval.edge.left.parameter ≤ last ∧ last ≤ interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((sample.sourceValue coefficients last - sample.sourceValue coefficients
      first) -
      (sample.pullbackValue coefficients last - sample.pullbackValue coefficients first)) ≤
      target * (last - first)^2 * coefficientNormSq coefficients := by
  have bound := request.accurate sample.originals sample.pullbacks later coefficients
    (fun row => BasisCommonInterval.locations_contains interval regular _ ⟨le_rfl, interval.ordered⟩ firstInside row)
    (fun row => BasisCommonInterval.locations_contains interval regular _ ⟨le_rfl, interval.ordered⟩ lastInside row)
  have sourceEq : sample.sourceValue coefficients last - sample.sourceValue coefficients first =
      sumFin (fun row => coefficients row *
        ((sample.originals.get row).primitive.value.eval
          (((comparisonLocations
          interval regular).owners.get row).parent.edge.point last) -
          (sample.originals.get row).primitive.value.eval
            (((comparisonLocations
            interval regular).owners.get row).parent.edge.point first))) := by
    unfold sourceValue
    rw [← sumFin_sub]
    exact sumFin_congr (fun _ => by ring1)
  have pullbackEq : sample.pullbackValue coefficients last - sample.pullbackValue coefficients first =
      sumFin (fun row => coefficients row *
        ((sample.pullbacks.get row).pullback.value.eval
          (((comparisonLocations
          interval regular).owners.get row).parent.edge.point last)⁻¹ -
          (sample.pullbacks.get row).pullback.value.eval
            (((comparisonLocations
            interval regular).owners.get row).parent.edge.point first)⁻¹)) := by
    unfold pullbackValue
    rw [← sumFin_sub]
    exact sumFin_congr (fun _ => by ring1)
  rw [sourceEq, pullbackEq]
  exact bound

end PrimitiveSample
end BasisCommonInterval
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

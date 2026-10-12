module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseModelRootAgreement
public import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Init.ByCases
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Cap coordinates on the retained inverse arcs

Each endpoint uses the root program supplied by its cell's inverse model.
Neighboring cells share the source model's sheet, so their quotient cap
coordinates and their actual shared polynomial primitives agree at a common
parameter. The two-step root preparation is retained once per cell.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib.Geometry

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel RootPoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}

set_option genInjectivity false in
/-- A retained reciprocal root occurrence with its original regular-cap coordinate overlap.

The coordinate owner is indexed by the actual inverse source point and the exact retained root-channel attachment. -/
structure Point (cap : ReciprocalInnerInverse.Data curve collar) (model : UniformReciprocalRootChannels.RootModel cell)
  (parameter : InverseRootPolynomial.Coordinate) where
  /-- The original retained reciprocal root channel at this exact source parameter. -/ root :
    UniformReciprocalRootChannels.RootPoint model parameter
  /-- The original cap coordinate overlap for this retained root attachment at the actual inverse source point. -/
    coordinates : Coordinates.Overlap cap (parent.edge.point parameter)⁻¹ root.channel.attachment.owner

constructive_injectivity Point

namespace Point

/-- Consume a retained disk root when another endpoint consumer already owns it. -/
@[expose] def ofRegular (model : UniformReciprocalRootChannels.RootModel cell) (parameter :
  InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter)
    (regular : Owners.DiskPoint cap (parent.edge.point parameter)⁻¹) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter :=
  let root := RootPoint.build model parameter between
  ⟨root, Coordinates.Overlap.ofPoint regular root.channel.attachment.owner⟩

/-- Acquire one original regular cap root at the inverse boundary point and retain its overlap with the supplied
reciprocal cell root. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) (model : UniformReciprocalRootChannels.RootModel
  cell) (parameter : InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point.ofRegular model parameter between
    (Owners.atInverseBoundary cap
    (data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩))

variable {model : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {otherCell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data otherEdge} {otherModel :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell}

/-- No sign or equality of prepared paths is supplied by the caller. -/
@[expose] def coordinateEquivalent (first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model
  parameter) (last : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel parameter) :
    Gaussian.Equivalence.NamedEquivalent first.coordinates.coordinate.prepared.denominator.name
      last.coordinates.coordinate.prepared.denominator.name :=
  first.coordinates.coordinate.equivalent last.coordinates.coordinate (by
    rw [first.coordinates.reciprocal_eq, last.coordinates.reciprocal_eq]
    exact first.root.ownerEquivalent last.root)
    (InverseModelRootAgreement.equivalent_of_value first.coordinates.regular.channel last.coordinates.regular.channel
      rfl)

/-- Read the inverse polynomial already retained by the actual arc sample. The offset accounts for the two initial
root-channel preparation steps. -/
theorem inverse_accurate (owned : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter)
    {regular : RegularBounds.Data cap} {comparison : ArcSamples.Data regular cell}
    {index : Nat} {box : Rational.Box} {capSample : Primitives.Sample cap differential index box}
    (sample : ArcSamples.Sample comparison capSample) {target : InverseRootPolynomial.Coordinate} {floor rootIndex :
      Nat}
    (request : InverseModelRootRequests.InverseRequest owned.root.channel target floor)
    (later : 2 + request.index ≤ index) (rootLater : request.comparison.rightIndex ≤ rootIndex) :
    Data.Gaussian.Norm.Basic.normSq (sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹ -
      Data.Gaussian.Field.inv ((Sampling.approximation owned.root.channel.certificate.value.name).sample
        rootIndex)) < target := by
  have shifted : 2 + (index - 2) = index := by omega0
  have accurate := request.accurate (index := index - 2) (by omega0) rootLater
  rw [model.refine_eq, shifted] at accurate
  let reading := (Sampling.approximation owned.root.channel.certificate.value.name).sample rootIndex
  have inverseEq : Data.Gaussian.Basic.Canonical.inv reading = Data.Gaussian.Field.inv reading := by
    change reading⁻¹ = Data.Gaussian.Field.inv reading
    exact Data.Gaussian.Field.inv_eq reading
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, inverseEq] at accurate
  rw [sample.retained.inverse_eq, sample.cell_eq]
  exact accurate

end Point

variable {model : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {otherCount : Nat} {otherDifferential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve otherDifferential}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {otherCell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge}
  {otherModel : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell}
    {otherParameter : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

set_option genInjectivity false in
/-- Retain physical endpoint equality and the root-coordinate comparison for two original endpoints.

The two indexed root occurrences may belong to different source parents.
Their actual endpoint equality and operational coordinate witness are retained. -/
structure Join (first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter) (last :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel otherParameter) where
  /-- The original source parents reach exactly the same retained physical endpoint. -/ point_eq : parent.edge.point
    parameter = otherParent.edge.point otherParameter
  /-- The two retained cap coordinate names are operationally equivalent. -/ coordinate :
    Gaussian.Equivalence.NamedEquivalent first.coordinates.coordinate.prepared.denominator.name
    last.coordinates.coordinate.prepared.denominator.name

constructive_injectivity Join

namespace Join

/-- Retain the endpoint and coordinate comparison of two original cells at an equal parameter of the same source parent.
-/
@[expose] def ofSameParent {nextEdge : ClearSheetContinuation.Subdivision.ParameterEdge} {nextCell :
  UniformReciprocalCover.Cell data nextEdge}
    {nextModel : UniformReciprocalRootChannels.RootModel nextCell} {nextParameter : InverseRootPolynomial.Coordinate}
    (first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter) (last :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap nextModel nextParameter)
    (same : parameter = nextParameter) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last :=
  ⟨congrArg parent.edge.point same, by subst nextParameter; exact first.coordinateEquivalent last⟩

/-- Transport an operational reciprocal-root comparison at equal points to the retained cap coordinate names.

The supplied physical equality identifies both retained points. The root
comparison then determines the corresponding regular-model quotient names. -/
@[expose] def coordinateEquivalent {firstPoint lastPoint : InverseRootPolynomial.Gaussian}
    {firstOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    (first : Coordinates.Overlap cap firstPoint firstOwner)
    (last : Coordinates.Overlap cap lastPoint lastOwner) (same : firstPoint = lastPoint)
    (roots : Gaussian.Equivalence.NamedEquivalent first.reciprocal.value.name last.reciprocal.value.name) :
    Gaussian.Equivalence.NamedEquivalent first.coordinate.prepared.denominator.name
      last.coordinate.prepared.denominator.name := by
  cases same
  exact first.coordinate.equivalent last.coordinate roots
    (InverseModelRootAgreement.equivalent_of_value first.regular.channel last.regular.channel rfl)

/-- Transport the already retained reciprocal root certificates into the common cap coordinate; the regular cap root is
determined by its model. -/
@[expose] def ofRoots (first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter) (last :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel otherParameter)
    (same : parent.edge.point parameter = otherParent.edge.point otherParameter)
    (roots : Gaussian.Equivalence.NamedEquivalent first.root.channel.certificate.value.name
      last.root.channel.certificate.value.name) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last
      :=
  ⟨same, Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join.coordinateEquivalent first.coordinates
    last.coordinates (congrArg Inv.inv same) (by
    rw [first.coordinates.reciprocal_eq, last.coordinates.reciprocal_eq]
    exact first.root.channel.owner_equivalent.trans (roots.trans last.root.channel.owner_equivalent.symm))⟩

/-- Reuse the stored coordinate comparison for every shared primitive stage.

The retained endpoint equality and coordinate comparison apply to the same
finite polynomial sample, in either branch of the reciprocal origin. -/
@[expose] def primitiveEquivalent {first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model
  parameter} {last : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel otherParameter}
    (joined : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last) {index : Nat} {box :
      Rational.Box} {numerator : Differentials.Basic.Differential genus}
    (sample : Primitives.Sample cap numerator index box) :
    Gaussian.Equivalence.NamedEquivalent (first.coordinates.chartPrimitive sample).name (last.coordinates.chartPrimitive
      sample).name := by
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · rw [Coordinates.Overlap.chartPrimitive, Coordinates.Overlap.chartPrimitive, if_pos regular, if_pos regular]
    apply Congruence.coherentMul_respects _ _ _ _ joined.coordinate
    rw [joined.point_eq]
    exact NamedEquivalent.refl _
  · rw [Coordinates.Overlap.chartPrimitive, Coordinates.Overlap.chartPrimitive, if_neg regular, if_neg regular]
    exact Horner.horner_respects _ _
      (Coherence.exact 0) (Coherence.exact 0)
      joined.coordinate (NamedEquivalent.refl _) sample.primitive.value.coeffs

end Join

set_option genInjectivity false in
/-- Both endpoint channels reuse the same small reciprocal model.

The indexed fields retain the supplied owners, channels and exact cached
data. Their identities bind each displayed field to those same inputs. -/
structure Endpoints (cap : ReciprocalInnerInverse.Data curve collar) (cell : UniformReciprocalCover.Cell data edge)
  where
  /-- The small reciprocal root model shared by both original cell endpoints. -/ model :
    UniformReciprocalRootChannels.RootModel cell
  /-- The retained root and cap coordinate occurrence at the original left parameter. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model edge.left.parameter
  /-- The retained root and cap coordinate occurrence at the original right parameter. -/ last :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model edge.right.parameter

constructive_injectivity Endpoints

/-- Build one small reciprocal root model and retain both endpoint coordinate occurrences on that exact model. -/
@[expose] def Endpoints.build (cap : ReciprocalInnerInverse.Data curve collar) (cell : UniformReciprocalCover.Cell data
  edge) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Endpoints cap cell :=
  let model := RootModel.build cell
  ⟨model, Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point.build cap model _ ⟨le_rfl, cell.ordered.le⟩,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point.build cap model _ ⟨cell.ordered.le, le_rfl⟩⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Transport
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Transport
import Purelib.Data.List.DependentProduct
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Actual chart owners of the same retained circle quadrature

Each stored reading supplies one attached chart view and its identical paid
request. The saved original path integral sample is the ordered weighted
sum of those same actual chart readings on its original rational circle.
This finite correspondence does not assert a cyclic continuation seam.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

open Purelib
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {actual : { value : RationalCurve // value = circle base }}
    {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}
    {factors : Canonical → Canonical}

namespace Readings

/-- Actual attached chart views indexed by the literal complete readings of the original retained bank.

The original dependent product preserves each bounded dyadic occurrence.
Every entry retains the actual point, signed overlap, affine certificate
and whole already paid request of that exact original reading.
-/
abbrev Attached
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual
      depth left right target) :=
  DependentProduct (dyadicEdges depth left right) fun index => Reading.Attached (stored.get index)

/-- Attach each actual stored reading once by a structural traversal of its original complete bank.

The mapper consumes each supplied whole head and literal tail with the
supplied actual edge cache. It never calls a reading, numerical preparation,
coefficient or request producer.
-/
def attach
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual
      depth left right target)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :
    Attached stored := by
  let kind := fun edge : ParameterEdge => Reading differential cap (actual.val.point edge.left.parameter)
    (point_inside base unitBound collarBound actual edge.left.parameter) target
    (factors (actual.val.point edge.left.parameter))
  let entries := cast (congrArg (fun items : List ParameterEdge =>
    DependentProduct items (fun index => kind (items[index.val]'index.isLt))) cachedEdges.property.symm) stored
  let attached := DependentProduct.map cachedEdges.val entries
    (fun _ source => Reading.Attached source) (fun _ source => Reading.attach source)
  have same : (DependentProduct cachedEdges.val fun index =>
      Reading.Attached (DependentProduct.get cachedEdges.val entries index)) = Attached stored := by
    cases cachedEdges with
    | mk edges equal => cases equal; rfl
  exact Eq.mp same attached

/-- The attached bank's whole original occurrence is the same attachment of that literal retained reading. -/
theorem get_attach
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (index : Fin (dyadicEdges depth left right).length) :
    DependentProduct.get (dyadicEdges depth left right) (attach stored) index = Reading.attach (stored.get index) := by
  unfold attach
  exact DependentProduct.get_map (dyadicEdges depth left right) stored _ _ index

/-- Supplying the original equal edge cache preserves the complete attached bank and every retained chart request. -/
theorem attach_cachedEdges
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual
      depth left right target) (cachedEdges : DyadicEdges depth left right) :
    attach stored cachedEdges = attach stored := by
  cases cachedEdges with
  | mk edges equal => cases equal; rfl

end Readings

namespace Stage

variable {allowance : Option { value : Fraction.Rational // 0 ≤ value }}

/-- Attach the actual saved stage bank without reconstructing its path, cells or numerical observations. -/
def attach
    (retained : Stage differential cap base unitBound collarBound actual depth left right target allowance factors) :
    Readings.Attached retained.1 :=
  Readings.attach retained.1 retained.2.1

/-- The saved original stage integral is the ordered quadrature of its same actual attached-chart paid readings.

The original cell-integral and path-sum laws supply the exact circle
velocity and rational parameter increments. Only the attached request's
identical retained Gaussian value is transported; no new mesh, observation,
source path or integral programme is constructed.
-/
theorem attached_integralSample
    (retained : Stage differential cap base unitBound collarBound actual depth left right target allowance factors)
    (attached : Readings.Attached retained.1) :
    retained.2.2.val.integralSample = Norm.Sum.Basic.gaussianSum
      (DependentProduct.mapToList (dyadicEdges depth left right) attached fun index entry =>
        let edge := (dyadicEdges depth left right)[index.val]'index.isLt
        Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) *
          (velocity base edge.left.parameter * entry.2.val.reading.value)) := by
  apply Eq.trans retained.2.2.val.integralSample_eq_gaussianSum
  apply congrArg Norm.Sum.Basic.gaussianSum
  rewrite [retained.cells, Readings.cells_eq, DependentProduct.map_mapToList]
  apply DependentProduct.mapToList_eq_of_get
  intro index
  let edge := (dyadicEdges depth left right)[index.val]'index.isLt
  have value := (DependentProduct.get (dyadicEdges depth left right) attached index).value_eq
  change (DependentProduct.get (dyadicEdges depth left right) attached index).2.val.reading.value =
    (DependentProduct.get (dyadicEdges depth left right) retained.1 index).2.2.reading.value at value
  exact (readingCell.integralSample differential base unitBound collarBound actual target edge
    (DependentProduct.get (dyadicEdges depth left right) retained.1 index) none allowance).trans
      (congrArg (fun observed : Canonical =>
        Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) *
          (velocity base edge.left.parameter * observed)) value.symm)

end Stage

namespace Model.EvenNegative

variable {reference : OddPowerDifferential curve.polynomial}
    {referenceBudget : { value : Fraction.Rational // 0 ≤ value }}
    (retained : CertifiedProgram.CachedModel (operations
      (differential := differential) (reference := reference) (cap := cap) (base := base)
      (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      (left := left) (right := right) (referenceBudget := referenceBudget)))

/-- Attach the actual signed programme cache's saved target bank, retaining its path and cached sample unchanged. -/
def attach : Readings.Attached retained.model.2.2.val.1 :=
  Stage.attach retained.model.2.2.val

/-- The programme's actual cached sample is the same ordered attached affine-chart quadrature.

The original cache equation and signed path projection are composed with
the whole saved stage's chart identity. The supplied stage, original
numerical bank and cached sample are consumed directly.
-/
theorem attached_sample (attached : Readings.Attached retained.model.2.2.val.1) :
    retained.sample = Norm.Sum.Basic.gaussianSum
      (DependentProduct.mapToList (dyadicEdges retained.model.1.model.1 left right) attached fun index entry =>
        let edge := (dyadicEdges retained.model.1.model.1 left right)[index.val]'index.isLt
        Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) *
          (velocity base edge.left.parameter * entry.2.val.reading.value)) :=
  retained.sample_eq.trans ((sample_path retained.model).trans
    (Stage.attached_integralSample retained.model.2.2.val attached))

end Model.EvenNegative

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end

module

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Transport
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Comparison
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Primitive
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Bounds
public import Purelib.Data.List.DependentProduct
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Bounds
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Retained whole-form observations on the original rational circle

The original circle cache and dyadic edges determine each actual numerical
reading once. The same original dependent product then supplies both the
sampled form cells and their differences from a supplied finite coefficient.
These stage models alone assert no Cauchy estimate or residue formula.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Geometry.Rational.Box.Square.Centered
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelRootChannels
open Purelib.Approximation.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}

/-- The actual circle's cap power coordinates lie in the original collar under explicit scalar radius bounds.

The original circle keeps its base quadrance at every parameter. The cap
power is one or two, and the unit quadrance bound makes its second power
no larger. Coordinate bounds then place that same point in the retained
original symmetric collar square.
-/
theorem point_inside (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (time : Fraction.Rational) :
    collar.box.Contains (Primitives.point curve (actual.val.point time)) := by
  have norm : Norm.Basic.normSq (actual.val.point time) = Norm.Basic.normSq base := by
    rewrite [actual.property]
    exact point_normSq base time
  have parameterUnit := norm.trans_le unitBound
  have parameterRadius := norm.trans_le collarBound
  rewrite [collar.box_eq]
  exact Primitives.point_in_square curve (actual.val.point time) parameterUnit
    (ReciprocalExteriorCollar.innerRadius curve) (ReciprocalExteriorCollar.innerRadius_positive curve).le
    parameterRadius

/-- The same supplied nonzero circle base keeps the original retained curve point away from zero. -/
theorem point_nonzero (base : Canonical) (nonzero : base ≠ 0)
    (actual : { value : RationalCurve // value = circle base }) (time : Fraction.Rational) :
    actual.val.point time ≠ 0 := by
  rewrite [actual.property]
  exact point_ne_zero base nonzero time

/-- Whole original form readings indexed by the same original dyadic edge occurrences and actual circle cache.

The supplied factor function indexes each retained scaled root. Its default
is the original cap power at the same actual parameter.
-/
abbrev Readings (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational)
    (factors : Canonical → Canonical :=
      fun parameter => parameter ^ HyperellipticReciprocal.originOrder curve) :=
  DependentProduct (dyadicEdges depth left right) fun index =>
    let edge := (dyadicEdges depth left right)[index.val]'index.isLt
    Reading differential cap (actual.val.point edge.left.parameter)
      (point_inside base unitBound collarBound actual edge.left.parameter) target
      (factors (actual.val.point edge.left.parameter))

/-- Prepare and observe the actual whole cap form once at the supplied original edge's left endpoint.

The original radius bounds place that same point in the retained collar.
One numerical preparation, both root scales and the complete original
coefficient are retained before paying the supplied positive target.
-/
def readEdge (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (target : Fraction.Rational)
    (positive : 0 < target) (edge : ParameterEdge) :
    Reading differential cap (actual.val.point edge.left.parameter)
      (point_inside base unitBound collarBound actual edge.left.parameter) target :=
  let parameter := actual.val.point edge.left.parameter
  have parameterNonzero : parameter ≠ 0 := point_nonzero base nonzero actual edge.left.parameter
  let inside := point_inside base unitBound collarBound actual edge.left.parameter
  let regular := RootChannel.prepare cap.model cap.model_small (Primitives.point curve parameter) inside
  let prepared := prepare cap parameter parameterNonzero inside regular
  let cached := coefficient differential prepared
  read differential cap parameter parameterNonzero inside target positive prepared cached

/-- Observe the complete actual form once at every retained dyadic left endpoint.

Each entry computes one numerical preparation, both exact root scales and
one complete original coefficient before paying its actual observation.
The original bounded occurrence and both endpoint records stay unchanged.
-/
def readings (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :
    Readings differential cap base unitBound collarBound actual depth left right target :=
  let kind := fun edge : ParameterEdge => Reading differential cap (actual.val.point edge.left.parameter)
    (point_inside base unitBound collarBound actual edge.left.parameter) target
  let retained := DependentProduct.ofFn cachedEdges.val fun index =>
    readEdge differential cap base nonzero unitBound collarBound actual target positive
      (cachedEdges.val[index.val]'index.isLt)
  cast (congrArg (fun items : List ParameterEdge =>
    DependentProduct items (fun index => kind (items[index.val]'index.isLt))) cachedEdges.property) retained

/-- Form the original constant circle cell from the actual supplied whole reading and optional scalar reference.

The same original request supplies its observed coefficient. A supplied
reference is subtracted at that same original edge point; neither branch
rebuilds a channel, numerical preparation or observation request.
-/
@[expose] def readingCell (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (target : Fraction.Rational)
    (edge : ParameterEdge) {factor : Canonical}
    (reading : Reading differential cap (actual.val.point edge.left.parameter)
      (point_inside base unitBound collarBound actual edge.left.parameter) target factor)
    (reference : Option (Canonical → Canonical) := none)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none) :=
  let value := match reference with
    | none => reading.request.reading.value
    | some evaluate => reading.request.reading.value - evaluate (actual.val.point edge.left.parameter)
  let cell := coefficientCell base actual (fun _ => value)
    edge.left.parameter (edge.right.parameter - edge.left.parameter)
  match allowance with
  | none => cell
  | some retained => cell.weakenAllowance retained.val (by change 0 ≤ retained.val; exact retained.property)

namespace readingCell

open Purelib.Polynomial
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable (differential : OddPowerDifferential curve.polynomial) (base : Canonical)
  (unitBound : Norm.Basic.normSq base ≤ 1)
  (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
  (actual : { value : RationalCurve // value = circle base }) (target : Fraction.Rational)
  (edge : ParameterEdge) {factor : Canonical}
  (reading : Reading differential cap (actual.val.point edge.left.parameter)
    (point_inside base unitBound collarBound actual edge.left.parameter) target factor)
  (reference : Option (Canonical → Canonical))
  (allowance : Option { value : Fraction.Rational // 0 ≤ value })

/-- Omitting the allowance retains the complete original constant circle cell and all its actual observations. -/
theorem default :
    readingCell differential cap base unitBound collarBound actual target edge reading reference none =
      coefficientCell base actual
        (fun _ => match reference with
          | none => reading.request.reading.value
          | some evaluate => reading.request.reading.value - evaluate (actual.val.point edge.left.parameter))
        edge.left.parameter (edge.right.parameter - edge.left.parameter) := rfl

/-- A supplied allowance changes only the original cell allowance and transports the same actual observations. -/
theorem with_allowance (retained : { value : Fraction.Rational // 0 ≤ value }) :
    readingCell differential cap base unitBound collarBound actual target edge reading reference (some retained) =
      (readingCell differential cap base unitBound collarBound actual target edge reading
        reference none).weakenAllowance
        retained.val (by change 0 ≤ retained.val; exact retained.property) := rfl

/-- The actual cell polynomial is its original tangent times the same retained observation or reference difference. -/
theorem polynomial :
    (readingCell differential cap base unitBound collarBound actual target edge reading
      reference allowance).polynomial =
      Ascending.Gaussian.Basic.constant
        (velocity base edge.left.parameter *
          (match reference with
            | none => reading.request.reading.value
            | some evaluate => reading.request.reading.value - evaluate (actual.val.point edge.left.parameter))) := by
  cases allowance <;> rfl

/-- The actual cell retains its original parameter displacement when its observation allowance is widened. -/
theorem displacement :
    (readingCell differential cap base unitBound collarBound actual target edge reading
      reference allowance).displacement =
      Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) := by
  cases allowance with
  | none =>
      rewrite [default]
      exact coefficientCell_displacement base actual _ edge.left.parameter
        (edge.right.parameter - edge.left.parameter)
  | some retained =>
      rewrite [with_allowance, CellModel.weakenAllowance_displacement, default]
      exact coefficientCell_displacement base actual _ edge.left.parameter
        (edge.right.parameter - edge.left.parameter)

/-- The actual cell's local allowance is precisely its supplied nonnegative value, with the former zero as default. -/
theorem allowance_value :
    (readingCell differential cap base unitBound collarBound actual target edge reading
      reference allowance).localAllowance =
      match allowance with
      | none => 0
      | some retained => retained.val := by
  cases allowance <;> rfl

/-- Widening the allowance preserves the same complete actual finite cell integral sample. -/
theorem integralSample :
    (readingCell differential cap base unitBound collarBound actual target edge reading
      reference allowance).integralSample =
      Stereographic.Tangent.increment (edge.right.parameter - edge.left.parameter) *
        (velocity base edge.left.parameter *
          (match reference with
            | none => reading.request.reading.value
            | some evaluate => reading.request.reading.value - evaluate (actual.val.point edge.left.parameter))) := by
  cases allowance with
  | none =>
      rewrite [default]
      exact coefficientCell_integralSample base actual _ edge.left.parameter
        (edge.right.parameter - edge.left.parameter)
  | some retained =>
      rewrite [with_allowance, CellModel.weakenAllowance_integralSample, default]
      exact coefficientCell_integralSample base actual _ edge.left.parameter
        (edge.right.parameter - edge.left.parameter)

end readingCell

namespace Readings

variable {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}
  {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}
  {factors : Canonical → Canonical}

/-- Read the same complete stored observation at its original bounded dyadic occurrence.

A supplied actual edge cache controls the original product traversal.
Exact list and occurrence identities transport that same whole entry to
its original public index; the canonical original list remains the default.
-/
@[expose] def get
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (index : Fin (dyadicEdges depth left right).length)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :
    Reading differential cap (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      (point_inside base unitBound collarBound actual
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) target
      (factors (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)) :=
  let kind := fun edge : ParameterEdge => Reading differential cap (actual.val.point edge.left.parameter)
    (point_inside base unitBound collarBound actual edge.left.parameter) target
    (factors (actual.val.point edge.left.parameter))
  let entries := cast (congrArg (fun items : List ParameterEdge =>
    DependentProduct items (fun index => kind (items[index.val]'index.isLt))) cachedEdges.property.symm) stored
  let actualIndex : Fin cachedEdges.val.length := ⟨index.val, cachedEdges.property.symm ▸ index.isLt⟩
  let retained := DependentProduct.get cachedEdges.val entries actualIndex
  have same : cachedEdges.val[actualIndex.val]'actualIndex.isLt =
      (dyadicEdges depth left right)[index.val]'index.isLt :=
    getElem_congr cachedEdges.property (show actualIndex.val = index.val from rfl) actualIndex.isLt
  cast (congrArg kind same) retained

/-- The default cached lookup is the original whole dependent-product lookup at the unchanged bounded occurrence. -/
theorem get_eq
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (index : Fin (dyadicEdges depth left right).length) :
    stored.get index = DependentProduct.get (dyadicEdges depth left right) stored index := rfl

/-- Agreement of the complete actual stored entries identifies both whole original banks. -/
theorem eq_of_get
    (first second :
      Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (same : ∀ index, first.get index = second.get index) : first = second := by
  apply DependentProduct.eq_of_get (dyadicEdges depth left right)
  intro index
  exact ((get_eq first index).symm.trans (same index)).trans (get_eq second index)

/-- Transport the same whole original reading bank along an exact observation-target identity.

Only the correctness-bearing target index changes by equality. The
complete retained preparations, channels and paid requests are the same
supplied product; no entry or producer is traversed again.
-/
def transportTarget {lastTarget : Fraction.Rational}
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (same : target = lastTarget) :
    Readings (factors := factors) differential cap base unitBound collarBound actual depth left right lastTarget :=
  cast (congrArg
    (Readings (factors := factors) differential cap base unitBound collarBound actual depth left right) same) stored

/-- Exact target transport retains the same whole original supplied bank as a heterogeneous equality. -/
theorem transportTarget_heq {lastTarget : Fraction.Rational}
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (same : target = lastTarget) : HEq (stored.transportTarget same) stored := by
  unfold transportTarget
  exact cast_heq _ _

/-- Exact target transport preserves the complete supplied canonical bank, including its original paid procedures. -/
theorem transportTarget_readings (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (depth : Nat) (left right : Endpoint)
    (firstTarget lastTarget : Fraction.Rational) (firstPositive : 0 < firstTarget) (lastPositive : 0 < lastTarget)
    (same : firstTarget = lastTarget)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :
    (readings differential cap base nonzero unitBound collarBound actual depth left right
      firstTarget firstPositive cachedEdges).transportTarget same =
      readings differential cap base nonzero unitBound collarBound actual depth left right
        lastTarget lastPositive cachedEdges := by
  cases same
  unfold transportTarget
  rfl

/-- Reading through the supplied exact edge-cache view preserves the complete actual original stored entry. -/
theorem get_cachedEdges
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (index : Fin (dyadicEdges depth left right).length) (cachedEdges : DyadicEdges depth left right) :
    stored.get index cachedEdges = stored.get index := by
  cases cachedEdges with
  | mk edges same => cases same; rfl

/-- Materializing through the supplied exact edge cache preserves the complete original reading bank. -/
theorem readings_cachedEdges (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (cachedEdges : DyadicEdges depth left right) :
    readings differential cap base nonzero unitBound collarBound actual depth left right target positive cachedEdges =
      readings differential cap base nonzero unitBound collarBound actual depth left right target positive := by
  cases cachedEdges with
  | mk edges same => cases same; rfl

/-- Reading the original bank returns the same complete original edge observation at its retained bounded occurrence. -/
theorem get_readEdge (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (index : Fin (dyadicEdges depth left right).length) :
    (readings differential cap base nonzero unitBound collarBound actual depth left right target positive).get index =
      readEdge differential cap base nonzero unitBound collarBound actual target positive
        ((dyadicEdges depth left right)[index.val]'index.isLt) := by
  unfold readings get
  exact DependentProduct.get_ofFn _ _ _

/-- Materializing the original bank returns the whole supplied numerical caches and their actual channel request.

The original dependent-product lookup law selects the complete stored
entry. The opaque reading constructor's own equation then identifies its
actual preparation, coefficient and once-paid request without exposing or
rebuilding either producer in external clients.
-/
theorem get_readings (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (index : Fin (dyadicEdges depth left right).length) :
    (readings differential cap base nonzero unitBound collarBound actual depth left right target positive).get index =
      (let edge := (dyadicEdges depth left right)[index.val]'index.isLt
       let parameter := actual.val.point edge.left.parameter
       let inside := point_inside base unitBound collarBound actual edge.left.parameter
       let regular := RootChannel.prepare
         cap.model cap.model_small (Primitives.point curve parameter) inside
       let prepared := prepare cap parameter (point_nonzero base nonzero actual edge.left.parameter) inside regular
       let cached := coefficient differential prepared
       ⟨prepared, cached,
         Approximation.Gaussian.Equivalence.Observation.Request.build cached.channel target positive⟩) := by
  rewrite [get_readEdge]
  unfold readEdge
  exact read_eq _ _ _ _ _ _ _ _ _

/-- Every canonical bank occurrence retains the same complete original numerical preparation produced at that point. -/
theorem get_regular (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (index : Fin (dyadicEdges depth left right).length) :
    ((readings differential cap base nonzero unitBound collarBound actual depth left right target positive).get
      index).1.1 =
      (let edge := (dyadicEdges depth left right)[index.val]'index.isLt
       RootChannel.prepare
         cap.model cap.model_small (Primitives.point curve (actual.val.point edge.left.parameter))
           (point_inside base unitBound collarBound actual edge.left.parameter)) := by
  rewrite [get_readings]
  exact prepare_regular _ _ _ _ _

/-- Map the actual whole bank into its original ordered circle cells using the supplied exact edge-list cache. -/
@[expose] def cells
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (reference : Option (Canonical → Canonical) := none)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :=
  let kind := fun edge : ParameterEdge => Reading differential cap (actual.val.point edge.left.parameter)
    (point_inside base unitBound collarBound actual edge.left.parameter) target
    (factors (actual.val.point edge.left.parameter))
  let entries := cast (congrArg (fun items : List ParameterEdge =>
    DependentProduct items (fun index => kind (items[index.val]'index.isLt))) cachedEdges.property.symm) stored
  DependentProduct.mapToList cachedEdges.val entries fun index reading =>
    readingCell differential cap base unitBound collarBound actual target
      (cachedEdges.val[index.val]'index.isLt) reading reference allowance

/-- The default edge-cache view maps the same original product entries and original indices directly. -/
theorem cells_eq
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (reference : Option (Canonical → Canonical)) (allowance : Option { value : Fraction.Rational // 0 ≤ value }) :
    stored.cells reference allowance =
      DependentProduct.mapToList (dyadicEdges depth left right) stored fun index reading =>
        readingCell differential cap base unitBound collarBound actual target
          ((dyadicEdges depth left right)[index.val]'index.isLt) reading reference allowance := rfl

/-- Exact target transport preserves the same complete ordered original cell list. -/
theorem cells_transportTarget {lastTarget : Fraction.Rational}
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (same : target = lastTarget) (reference : Option (Canonical → Canonical))
    (allowance : Option { value : Fraction.Rational // 0 ≤ value }) :
    (stored.transportTarget same).cells reference allowance = stored.cells reference allowance := by
  cases same
  unfold transportTarget
  rfl

/-- A retained depth-zero bank maps its actual whole entry to the same single original cell. -/
theorem cells_zero
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual 0 left right target)
    (reference : Option (Canonical → Canonical)) (allowance : Option { value : Fraction.Rational // 0 ≤ value }) :
    stored.cells reference allowance =
      [readingCell differential cap base unitBound collarBound actual target ⟨left, right⟩
        (stored.get ⟨0, Nat.zero_lt_succ 0⟩) reference allowance] := by
  rewrite [cells_eq, get_eq]
  rfl

/-- A retained depth-one bank maps its two actual whole entries in their original midpoint order. -/
theorem cells_one
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual 1 left right target)
    (reference : Option (Canonical → Canonical)) (allowance : Option { value : Fraction.Rational // 0 ≤ value }) :
    let middle : Endpoint :=
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    stored.cells reference allowance =
      [readingCell differential cap base unitBound collarBound actual target ⟨left, middle⟩
          (stored.get ⟨0, Nat.zero_lt_succ 1⟩) reference allowance,
        readingCell differential cap base unitBound collarBound actual target ⟨middle, right⟩
          (stored.get ⟨1, Nat.lt_succ_self 1⟩) reference allowance] := by
  rewrite [cells_eq, get_eq, get_eq]
  rfl

/-- Mapping through the supplied exact edge-cache view preserves the complete original ordered actual cells. -/
theorem cells_cachedEdges
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (reference : Option (Canonical → Canonical)) (allowance : Option { value : Fraction.Rational // 0 ≤ value })
    (cachedEdges : DyadicEdges depth left right) :
    stored.cells reference allowance cachedEdges = stored.cells reference allowance := by
  cases cachedEdges with
  | mk edges same => cases same; rfl

/-- Map the retained whole readings into actual same-curve constant cells in their original order. -/
@[expose] def model
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) : PathModel :=
  ⟨stored.cells none allowance cachedEdges⟩

/-- Map the same retained observations into coefficient-error cells without paying any new observation request. -/
@[expose] def differenceModel
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (reference : Canonical → Canonical)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) : PathModel :=
  ⟨stored.cells (some reference) allowance cachedEdges⟩

/-- The retained model has exactly the original dyadic occurrence count. -/
theorem model_count
    (stored : Readings (factors := factors) differential cap base unitBound collarBound actual depth left right target)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :
    (stored.model allowance cachedEdges).cells.length = 2 ^ depth := by
  cases cachedEdges with
  | mk edges same =>
      cases same
      exact (DependentProduct.length_mapToList (dyadicEdges depth left right) stored _).trans
        (dyadicEdges_length depth left right)

/-- The actual two stored original observations obey the same model's derived whole-form separation bound.

Their canonical dyadic indices may belong to different meshes and requests.
The same actual coefficient caches feed the original full-channel spatial
comparison, then both actual requested semantic allowances are paid by the
original observation theorem. A visible radius alone is not used as a
semantic allowance or a derivative comparison.
-/
theorem distance_le
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    {firstLeft firstRight lastLeft lastRight : Endpoint}
    {firstDepth lastDepth : Nat} {firstTarget lastTarget : Fraction.Rational}
    (first : Readings (factors := factors) differential cap base unitBound collarBound actual
      firstDepth firstLeft firstRight firstTarget)
    (last : Readings (factors := factors) differential cap base unitBound collarBound actual
      lastDepth lastLeft lastRight lastTarget)
    (firstIndex : Fin (dyadicEdges firstDepth firstLeft firstRight).length)
    (lastIndex : Fin (dyadicEdges lastDepth lastLeft lastRight).length)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Norm.Basic.normSq ((last.get lastIndex).request.reading.value - (first.get firstIndex).request.reading.value) ≤
      32 * (lastTarget + firstTarget) +
        4 * Coefficient.separationBound bounds (first.get firstIndex).2.1 (last.get lastIndex).2.1 accuracy := by
  let firstReading := first.get firstIndex
  let lastReading := last.get lastIndex
  let firstEdge := (dyadicEdges firstDepth firstLeft firstRight)[firstIndex.val]'firstIndex.isLt
  let lastEdge := (dyadicEdges lastDepth lastLeft lastRight)[lastIndex.val]'lastIndex.isLt
  have firstNonzero := point_nonzero base nonzero actual firstEdge.left.parameter
  have lastNonzero := point_nonzero base nonzero actual lastEdge.left.parameter
  let compared := firstReading.2.1.comparePoints bounds lastReading.2.1 pairs firstNonzero lastNonzero
    0 0 accuracy positive
  exact Equivalence.Observation.Request.distance_le lastReading.request firstReading.request compared

/-- Every canonical stored root guard retains the same uniform floor from the original collar clearance. -/
theorem get_lower_bound (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (index : Fin (dyadicEdges depth left right).length) :
    min 1 (cap.clearance.bound / 4) / 8 ≤
      ((readings differential cap base nonzero unitBound collarBound actual depth left right target positive).get
        index).1.1.prepared.apart.certificate.lowerSq := by
  rewrite [get_regular]
  exact RootChannel.prepare_lower_bound cap.model cap.model_small cap.clearance _ _

/-- Every canonical stored root sampler obeys the original polynomial's same finite box ceiling. -/
theorem get_samplerBound (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (index : Fin (dyadicEdges depth left right).length) :
    (Name.Sampling.approximation
      ((readings differential cap base nonzero unitBound collarBound actual depth left right target positive).get
        index).1.1.certificate.value.name).centerBound ≤
      2 * (1 + 2 * (1 + (4 + Polynomial.Dense.Gaussian.Bounds.Box.denseEvalNormBound cap.polynomial collar.box))) := by
  rewrite [get_regular]
  apply RootChannel.prepare_samplerBound_le
  exact Polynomial.Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound cap.polynomial
    (point_inside base unitBound collarBound actual _)

/-- Actual negative-sheet readings and their retained coefficient comparisons at the original bank's exact occurrences.

The original dependent product indexes each comparison by the literal
source reading. The actual negative observation and its comparison are
constructed together, retaining their same numerical root and scalar cache.
-/
abbrev EvenNegative (differential reference : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational)
    (original : Readings reference cap base unitBound collarBound actual depth left right target) :=
  DependentProduct (dyadicEdges depth left right) fun index =>
    let edge := (dyadicEdges depth left right)[index.val]'index.isLt
    (negative : Reading differential cap (actual.val.point edge.left.parameter)
      (point_inside base unitBound collarBound actual edge.left.parameter) target (-1)) ×
        Equivalence.NamedEquivalent negative.2.1.channel.name (original.get index).2.1.channel.name

/-- Observe the actual negative even sheet at each original stored source reading in one structural traversal.

The same original regular preparation and scalar numerator feed each
negative-sheet constructor. Its actual coefficient comparison is retained
beside that observation, without another source lookup or factory call.
-/
def evenNegative (differential reference : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (original : Readings reference cap base unitBound collarBound actual depth left right target) :
    EvenNegative differential reference cap base unitBound collarBound actual depth left right target original :=
  DependentProduct.map (dyadicEdges depth left right) original
    (fun index source =>
      let edge := (dyadicEdges depth left right)[index.val]'index.isLt
      (negative : Reading differential cap (actual.val.point edge.left.parameter)
        (point_inside base unitBound collarBound actual edge.left.parameter) target (-1)) ×
          Equivalence.NamedEquivalent negative.2.1.channel.name source.2.1.channel.name)
    (fun index source =>
      let edge := (dyadicEdges depth left right)[index.val]'index.isLt
      Reading.evenNegative differential reference pairs referencePairs sameNumerator oppositeScale
        (actual.val.point edge.left.parameter) (point_nonzero base nonzero actual edge.left.parameter)
        (point_inside base unitBound collarBound actual edge.left.parameter) parity target positive source)

namespace EvenNegative

variable {differential reference : OddPowerDifferential curve.polynomial}
  {original : Readings reference cap base unitBound collarBound actual depth left right target}

/-- Read one complete retained negative observation and its original same-root coefficient comparison. -/
def get
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (index : Fin (dyadicEdges depth left right).length) :=
  DependentProduct.get (dyadicEdges depth left right) retained index

/-- The complete paired lookup is the original dependent-product lookup on the same retained bank. -/
theorem get_eq
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (index : Fin (dyadicEdges depth left right).length) :
    get retained index = DependentProduct.get (dyadicEdges depth left right) retained index := (rfl)

/-- Project the actual retained negative observations into the original whole-reading bank. -/
def readings
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original) :
    Readings differential cap base unitBound collarBound actual depth left right target (fun _ => -1) :=
  DependentProduct.map (dyadicEdges depth left right) retained
    (fun index _ =>
      let edge := (dyadicEdges depth left right)[index.val]'index.isLt
      Reading differential cap (actual.val.point edge.left.parameter)
        (point_inside base unitBound collarBound actual edge.left.parameter) target (-1))
    (fun _ entry => entry.1)

/-- Projecting the bank preserves the same complete retained negative observation at its original bounded occurrence. -/
theorem get_readings
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (index : Fin (dyadicEdges depth left right).length) :
    (readings retained).get index = (get retained index).1 := by
  unfold readings get
  exact DependentProduct.get_map (dyadicEdges depth left right) retained _ _ index

end EvenNegative

end Readings

/-- One original observation bank paired with its once-built actual same-curve path model. -/
abbrev Stage (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none)
    (factors : Canonical → Canonical :=
      fun parameter => parameter ^ HyperellipticReciprocal.originOrder curve) :=
  (stored : Readings differential cap base unitBound collarBound actual depth left right target factors) ×
  (cachedEdges : DyadicEdges depth left right) ×
    { path : PathModel // path = stored.model allowance cachedEdges }

namespace Stage

/-- Retain a supplied whole reading bank and build its same-curve path once from the supplied exact edge cache.

The factor index and all original observations are unchanged. The original
stage factory and signed bank projections share this same constructor.
-/
@[expose] def ofReadings {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {actual : { value : RationalCurve // value = circle base }} {depth : Nat} {left right : Endpoint}
    {target : Fraction.Rational} {factors : Canonical → Canonical}
    (stored : Readings differential cap base unitBound collarBound actual depth left right target factors)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none)
    (cachedEdges : DyadicEdges depth left right := ⟨dyadicEdges depth left right, rfl⟩) :
    Stage differential cap base unitBound collarBound actual depth left right target allowance factors :=
  let path := stored.model allowance cachedEdges
  ⟨stored, cachedEdges, ⟨path, rfl⟩⟩

/-- The constructor retains the complete supplied bank, exact edge cache and once-built original path. -/
theorem ofReadings_eq {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {actual : { value : RationalCurve // value = circle base }} {depth : Nat} {left right : Endpoint}
    {target : Fraction.Rational} {factors : Canonical → Canonical}
    (stored : Readings differential cap base unitBound collarBound actual depth left right target factors)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value }) (cachedEdges : DyadicEdges depth left right) :
    ofReadings stored allowance cachedEdges =
      ⟨stored, cachedEdges, ⟨stored.model allowance cachedEdges, rfl⟩⟩ := (rfl)

end Stage

/-- Retain the actual observation bank and form its original constant-cell path once. -/
@[expose] def stage (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none) :
    Stage differential cap base unitBound collarBound actual depth left right target allowance :=
  let edges := dyadicEdges depth left right
  let cachedEdges : DyadicEdges depth left right := ⟨edges, rfl⟩
  let stored := readings differential cap base nonzero unitBound collarBound actual
    depth left right target positive cachedEdges
  Stage.ofReadings stored allowance cachedEdges

/-- The retained stage path has exactly the cells mapped from its same whole stored bank. -/
theorem Stage.cells {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {actual : { value : RationalCurve // value = circle base }} {depth : Nat} {left right : Endpoint}
    {target : Fraction.Rational} {allowance : Option { value : Fraction.Rational // 0 ≤ value }}
    {factors : Canonical → Canonical}
    (retained : Stage differential cap base unitBound collarBound actual depth left right target allowance factors) :
    retained.2.2.val.cells = retained.1.cells none allowance := by
  rewrite [retained.2.2.property]
  exact Readings.cells_cachedEdges retained.1 none allowance retained.2.1

/-- The same retained stage path reads the integral sample of its original complete observation bank. -/
theorem Stage.sample {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {actual : { value : RationalCurve // value = circle base }} {depth : Nat} {left right : Endpoint}
    {target : Fraction.Rational} {allowance : Option { value : Fraction.Rational // 0 ≤ value }}
    {factors : Canonical → Canonical}
    (retained : Stage differential cap base unitBound collarBound actual depth left right target allowance factors) :
    retained.2.2.val.integralSample = (retained.1.model allowance).integralSample :=
  congrArg (fun cells => (PathModel.mk cells).integralSample) retained.cells

/-- The original stage builder retains the complete canonical bank from its supplied numerical producer. -/
theorem stage_readings (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Fraction.Rational) (positive : 0 < target)
    (allowance : Option { value : Fraction.Rational // 0 ≤ value } := none) :
    (stage differential cap base nonzero unitBound collarBound actual depth left right target positive allowance).1 =
      readings differential cap base nonzero unitBound collarBound actual depth left right target positive := by
  unfold stage
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end

module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial.Bounds
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Paid selection before the original polynomial cap sample

The actual retained scalar equals the fixed residual scale times a
nonnegative multiplier. That same scalar feeds one original Selection. Only then is the original PolynomialSample
constructed at that actual retained stage, with both complete factory values
and their exact readbacks kept together.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample.ResidualBounds

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Polynomial Box Coordinate)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Data.Rat.Fraction.Order

/-- Retain one original paid selection and the original whole sample built at its selected stage.

Both subtypes identify complete factory values. The original residual cache,
multiplier, actual scale, starting floor, target and primitive box remain the same
indices; no pre-existing sample is changed or assigned another stage.
-/
@[expose] def SelectedSample {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    (bounds : ResidualBounds cap numerator) (multiplier : Coordinate) (nonnegative : 0 ≤ multiplier)
    (cachedScale : { value : Coordinate // value = multiplier * bounds.scale })
    (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :=
  (selection : { actual : Selection cachedScale.val floor target //
    actual = Selection.build cachedScale.val
      ((Arithmetic.mul_nonneg_direct nonnegative bounds.scale_nonnegative).trans_eq cachedScale.property.symm)
      floor target positive }) ×
  { actual : PolynomialSample cap numerator selection.val.stage box //
    actual = PolynomialSample.build cap numerator selection.val.stage box }

/-- Select the original paid stage once, then construct one whole original sample at that actual stage. -/
def select {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    (bounds : ResidualBounds cap numerator) (multiplier : Coordinate) (nonnegative : 0 ≤ multiplier)
    (cachedScale : { value : Coordinate // value = multiplier * bounds.scale })
    (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :
    SelectedSample bounds multiplier nonnegative cachedScale floor target positive box :=
  let selection := Selection.build cachedScale.val
    ((Arithmetic.mul_nonneg_direct nonnegative bounds.scale_nonnegative).trans_eq cachedScale.property.symm)
    floor target positive
  let sample := PolynomialSample.build cap numerator selection.stage box
  ⟨⟨selection, rfl⟩, ⟨sample, rfl⟩⟩

/-- The complete selected sample is the same ordered original selection and sample factory value. -/
private theorem packaged_select_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    (bounds : ResidualBounds cap numerator) (multiplier : Coordinate) (nonnegative : 0 ≤ multiplier)
    (cachedScale : { value : Coordinate // value = multiplier * bounds.scale })
    (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :
    select bounds multiplier nonnegative cachedScale floor target positive box =
    let selection := Selection.build cachedScale.val
      ((Arithmetic.mul_nonneg_direct nonnegative bounds.scale_nonnegative).trans_eq cachedScale.property.symm)
      floor target positive
    let sample := PolynomialSample.build cap numerator selection.stage box
    ⟨⟨selection, rfl⟩, ⟨sample, rfl⟩⟩ := by rfl

/-- The complete selected sample is the same ordered original selection and sample factory value. -/
theorem select_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    (bounds : ResidualBounds cap numerator) (multiplier : Coordinate) (nonnegative : 0 ≤ multiplier)
    (cachedScale : { value : Coordinate // value = multiplier * bounds.scale })
    (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :
    select bounds multiplier nonnegative cachedScale floor target positive box =
    let selection := Selection.build cachedScale.val
      ((Arithmetic.mul_nonneg_direct nonnegative bounds.scale_nonnegative).trans_eq cachedScale.property.symm)
      floor target positive
    let sample := PolynomialSample.build cap numerator selection.stage box
    ⟨⟨selection, rfl⟩, ⟨sample, rfl⟩⟩ :=
  packaged_select_factory bounds multiplier nonnegative cachedScale floor target positive box

namespace SelectedSample

/-- Read the same whole original finite Selection, including its fuel, stage and attained allowance. -/
def selection {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :
    Selection cachedScale.val floor target := retained.1.val

/-- Read the same complete original PolynomialSample at the retained selection's own stage. -/
def sample {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :
    PolynomialSample cap numerator retained.selection.stage box := retained.2.val

/-- The retained selection is exactly its original whole finite-search factory value. -/
private theorem packaged_selection_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    retained.selection = Selection.build cachedScale.val
      ((Arithmetic.mul_nonneg_direct nonnegative bounds.scale_nonnegative).trans_eq cachedScale.property.symm)
      floor target positive := retained.1.property

/-- The retained selection is exactly its original whole finite-search factory value. -/
theorem selection_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    retained.selection = Selection.build cachedScale.val
      ((Arithmetic.mul_nonneg_direct nonnegative bounds.scale_nonnegative).trans_eq cachedScale.property.symm)
      floor target positive :=
  packaged_selection_eq retained

/-- The retained sample is exactly the original whole factory at that same selected stage and box. -/
private theorem packaged_sample_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    retained.sample = PolynomialSample.build cap numerator retained.selection.stage box := retained.2.property

/-- The retained sample is exactly the original whole factory at that same selected stage and box. -/
theorem sample_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    retained.sample = PolynomialSample.build cap numerator retained.selection.stage box :=
  packaged_sample_eq retained

/-- The original selected stage is at least its supplied starting floor. -/
theorem lower {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :
    floor ≤ retained.selection.stage := retained.selection.lower

/-- The stored original allowance uses the same multiplied scale and actual selected stage. -/
theorem allowance_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    retained.selection.allowance = quarterRadius cachedScale.val retained.selection.stage :=
  retained.selection.allowance_eq

/-- The stored original allowance strictly pays the supplied positive target. -/
theorem paid {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :
    retained.selection.allowance < target := retained.selection.accurate

/-- The same selected sample stage strictly pays its multiplied quarter-radius request. -/
theorem accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    quarterRadius cachedScale.val retained.selection.stage < target :=
  retained.allowance_eq.symm.trans_lt retained.paid

/-- The fixed multiplier times the original residual allowance is paid at the same selected sample stage. -/
theorem scaled_accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial}
    {bounds : ResidualBounds cap numerator} {multiplier : Coordinate} {nonnegative : 0 ≤ multiplier}
    {cachedScale : { value : Coordinate // value = multiplier * bounds.scale }}
    {floor : Nat} {target : Coordinate} {positive : 0 < target} {box : Box}
    (retained : SelectedSample bounds multiplier nonnegative cachedScale floor target positive box) :

    multiplier * quarterRadius bounds.scale retained.selection.stage < target := by
  have scalar : multiplier * quarterRadius bounds.scale retained.selection.stage =
      quarterRadius (multiplier * bounds.scale) retained.selection.stage := by
    rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1
  have readback := congrArg (fun value : Coordinate => quarterRadius value retained.selection.stage)
    cachedScale.property.symm
  exact (scalar.trans readback).trans_lt retained.accurate

end SelectedSample

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample.ResidualBounds

end

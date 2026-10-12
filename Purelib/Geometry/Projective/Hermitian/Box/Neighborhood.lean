module

public import Purelib.Geometry.Projective.Hermitian.Box.Sample
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Rat.List.Minimum
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Proper neighbourhoods with retained Hermitian signs

An interior sample avoiding every non-universal form gives a positive finite
clearance payment. The original neighbourhood constructor then returns a
proper strictly nested box with a certified uniform sign for every form.
-/

public section

namespace Purelib.Geometry.Projective.Hermitian.Box

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry

/-- Compute a squared-distance payment from the original sample value and bounding-box variation coefficient. -/
@[expose] def signDistanceSq (form : HermitianForm) (bounding : Rational.Box)
    (point : Gaussian.Basic.Canonical) : Fraction.Rational :=
  form.eval point ^ 2 / (4 * (1 + variationCoefficient form bounding))

/-- A nonzero form value gives a strictly positive sign-clearance payment. -/
theorem signDistanceSq_pos (form : HermitianForm) (bounding : Rational.Box)
    (point : Gaussian.Basic.Canonical) (nonzero : form.eval point ≠ 0) :
    0 < signDistanceSq form bounding point := by
  have coefficientPositive : 0 < 1 + variationCoefficient form bounding :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (variationCoefficient_nonneg form bounding)
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.exact_rational_sq_pos nonzero)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) coefficientPositive)

/-- A squared diagonal paying the original clearance gives the strict Hermitian variation margin. -/
theorem variationSqBound_lt_of_signDistanceSq (form : HermitianForm)
    (bounding current : Rational.Box) (point : Gaussian.Basic.Canonical)
    (diagonal : current.diagonalSq < 4 * signDistanceSq form bounding point) :
    variationSqBound form bounding current < form.eval point ^ 2 := by
  have coefficientPositive : 0 < 1 + variationCoefficient form bounding :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (variationCoefficient_nonneg form bounding)
  have coefficientBound : variationCoefficient form bounding ≤ 1 + variationCoefficient form bounding := by
    calc
      variationCoefficient form bounding = 0 + variationCoefficient form bounding := by ring1
      _ ≤ 1 + variationCoefficient form bounding :=
        Fraction.Order.Arithmetic.add_le_add_direct (by decide) (Fraction.Order.Basic.le_refl _)
  calc
    variationSqBound form bounding current ≤
        (1 + variationCoefficient form bounding) * current.diagonalSq :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientBound current.diagonalSq_nonneg
    _ < (1 + variationCoefficient form bounding) * (4 * signDistanceSq form bounding point) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct coefficientPositive diagonal
    _ = (form.eval point ^ 2 / (4 * (1 + variationCoefficient form bounding))) *
        (4 * (1 + variationCoefficient form bounding)) := by unfold signDistanceSq; ring1
    _ = form.eval point ^ 2 := Fraction.Field.div_mul_cancel_of_ne _ _
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide) coefficientPositive).ne'

/-- Use unit clearance for universal zero forms and the original sign clearance for every other form. -/
@[expose] def guardedSignDistanceSq (form : HermitianForm) (bounding : Rational.Box)
    (point : Gaussian.Basic.Canonical) : Fraction.Rational :=
  if form.IsZero then 1 else signDistanceSq form bounding point

set_option genInjectivity false in
/-- Retain one proper neighbourhood with simultaneous certified signs for an original finite form family.

The original sample owner, form-clearance cache and its minimum determine
the exact returned box. Every non-universal form retains a strict margin
certificate using this same sample and box; universal zero forms keep their
separate coefficientwise interpretation.
-/
structure SignNeighborhood (forms : List HermitianForm) (outer : Rational.Box) where
  /-- The exact retained interior sample and its original finite-search caches. -/ sample : Sample forms outer
  /-- The computed clearance list in original form order. -/ clearances : List Fraction.Rational
  /-- Every clearance uses this same retained sample and original bounding box. -/ clearancesSpec :
    clearances = forms.map (fun form => guardedSignDistanceSq form outer sample.point)
  /-- The minimum of the cached finite clearances. -/ distanceSq : Fraction.Rational
  /-- The distance request consumes the exact original clearance cache. -/ distanceSpec :
    distanceSq = Rat.List.Minimum.positiveMinimum clearances
  /-- The retained minimum is strictly positive. -/ distancePositive : 0 < distanceSq
  /-- The actual computed rational neighbourhood box. -/ box : Rational.Box
  /-- The box uses the retained sample and computed minimum without replacing either owner. -/ boxSpec :
    box = Rational.Box.Neighborhood.innerBox outer sample.point sample.inside distanceSq distancePositive
  /-- The returned box has strictly positive coordinate widths. -/ proper : box.Proper
  /-- The returned box lies strictly inside its original parent. -/ nested : box.StrictInterior outer
  /-- The original sample remains strictly inside the returned box. -/ sampleInside : box.StrictContains sample.point
  /-- Every non-universal original form has a strict margin on the same actual box. -/ certificate :
    ∀ form ∈ forms, ¬form.IsZero → Certificate form outer box

/-- Compute a proper uniformly signed neighbourhood from one exact retained regular sample.

The builder computes the clearance list once, folds that cache once and
passes its positive minimum to the original box-neighbourhood constructor.
The returned strict margin certificates consume those same cached payments.
-/
def signNeighborhoodOfSample {forms : List HermitianForm} {outer : Rational.Box}
    (sample : Sample forms outer) :
    { neighborhood : SignNeighborhood forms outer // neighborhood.sample = sample } := by
  let clearances := forms.map (fun form => guardedSignDistanceSq form outer sample.point)
  have allPositive : ∀ clearance ∈ clearances, 0 < clearance := by
    intro clearance member
    rcases List.Map.mem_map.mp member with ⟨form, formMember, equal⟩
    rewrite [← equal]
    by_cases zero : form.IsZero
    · rewrite [guardedSignDistanceSq, if_pos zero]
      decide
    · rewrite [guardedSignDistanceSq, if_neg zero]
      exact signDistanceSq_pos form outer sample.point (sample.regular form formMember zero)
  let distanceSq := Rat.List.Minimum.positiveMinimum clearances
  have distancePositive : 0 < distanceSq := Rat.List.Minimum.positiveMinimum_pos clearances allPositive
  let box := Rational.Box.Neighborhood.innerBox outer sample.point sample.inside distanceSq distancePositive
  have nested := Rational.Box.Neighborhood.innerBox_strictInterior sample.inside distancePositive
  have sampleInside := Rational.Box.Neighborhood.innerBox_strictContains_center sample.inside distancePositive
  refine ⟨
    { sample := sample
      clearances := clearances
      clearancesSpec := rfl
      distanceSq := distanceSq
      distanceSpec := rfl
      distancePositive := distancePositive
      box := box
      boxSpec := rfl
      proper := Rational.Box.Neighborhood.innerBox_proper sample.inside distancePositive
      nested := nested
      sampleInside := sampleInside
      certificate := ?_ }, rfl⟩
  intro form member nonzero
  have clearanceMember : guardedSignDistanceSq form outer sample.point ∈ clearances :=
    List.Map.mem_map_of_mem (f := fun retained => guardedSignDistanceSq retained outer sample.point) member
  have payment := Rat.List.Minimum.positiveMinimum_le_of_mem clearanceMember
  rewrite [guardedSignDistanceSq, if_neg nonzero] at payment
  have diagonal : box.diagonalSq < 4 * signDistanceSq form outer sample.point :=
    (Rational.Box.Neighborhood.innerBox_diagonalSq_lt sample.inside distancePositive).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct payment (by decide))
  exact
    { refines := Rational.Box.Refinement.StrictInterior.refines nested
      sample := sample.point
      sampleInside := ⟨sampleInside.1.le, sampleInside.2.1.le, sampleInside.2.2.1.le, sampleInside.2.2.2.le⟩
      margin := variationSqBound_lt_of_signDistanceSq form outer box sample.point diagonal }

/-- The neighbourhood builder retains the exact supplied sample owner and all of its finite-search caches. -/
theorem signNeighborhoodOfSample_sample {forms : List HermitianForm} {outer : Rational.Box}
    (sample : Sample forms outer) : (signNeighborhoodOfSample sample).1.sample = sample :=
  (signNeighborhoodOfSample sample).2

namespace SignNeighborhood

/-- Read a uniform form sign from the exact retained family neighbourhood and its original certificate. -/
def formStability {forms : List HermitianForm} {outer : Rational.Box}
    (neighborhood : SignNeighborhood forms outer) (form : HermitianForm) (member : form ∈ forms) :
    Formula.Box.FormStability form neighborhood.box := by
  by_cases zero : form.IsZero
  · exact .zero fun point _ => form.eval_of_isZero zero point
  · cases (neighborhood.certificate form member zero).strictSign with
    | negative holds => exact .negative holds
    | positive holds => exact .positive holds

/-- A retained squared-distance guard excludes its original centre throughout the exact signed neighbourhood. -/
theorem ne_center {forms : List HermitianForm} {outer : Rational.Box}
    (neighborhood : SignNeighborhood forms outer) (center : Gaussian.Basic.Canonical)
    (member : distanceSqForm center ∈ forms) {point : Gaussian.Basic.Canonical}
    (inside : neighborhood.box.Contains point) : point ≠ center := by
  let atom : Atom := ⟨distanceSqForm center, .nonzero⟩
  have stability : Formula.Box.AtomStability atom outer neighborhood.box :=
    (neighborhood.formStability (distanceSqForm center) member).toAtom
  have sampleInside : neighborhood.box.Contains neighborhood.sample.point :=
    ⟨neighborhood.sampleInside.1.le, neighborhood.sampleInside.2.1.le,
      neighborhood.sampleInside.2.2.1.le, neighborhood.sampleInside.2.2.2.le⟩
  have nonzero := (Formula.Box.atom_holds_iff stability inside sampleInside).mpr
    (neighborhood.sample.regular (distanceSqForm center) member (distanceSqForm_nonzero center))
  change (distanceSqForm center).eval point ≠ 0 at nonzero
  rewrite [eval_distanceSqForm] at nonzero
  intro equal
  rewrite [equal, Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero] at nonzero
  exact nonzero rfl

end SignNeighborhood

end Purelib.Geometry.Projective.Hermitian.Box

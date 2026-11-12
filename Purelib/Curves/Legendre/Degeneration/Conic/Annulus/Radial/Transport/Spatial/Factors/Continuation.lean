module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original factor preparations along a paid physical point function

A physical rational point function remains in the original sharp source
square and carries an explicit finite squared-distance variation ceiling.
Those two geometric laws construct original normalized/cofactor PathData and
finite Preparation.Results on the unchanged source budgets. Both actual
point functions below use this same constructor, without replacing an
original ClearPath, quarter Reading or root Owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Geometry.Rational

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}

/-- Construct normalized root PathData on the supplied SAME physical point function and source Seed budget. -/
def normalAlong (budgets : Budgets anchor) (point : Fraction.Rational → Canonical)
    (contained : ∀ time, FixedRootBoxPath.Inside time → (sourceBox anchor).Contains (point time))
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (variation : ∀ left right, FixedRootBoxPath.Inside left → FixedRootBoxPath.Inside right →
      Norm.Basic.normSq (point left - point right) ≤ scale * (right - left) ^ 2) : NormalPath budgets :=
  { point := fun time => Clearance.normalizedRadicand site parameter (point time)
    nonzero := fun time inside => budgets.normalized_nonzero (contained time inside)
    firstMovement := fun time inside => by
      have paid := budgets.normalized_movement (contained time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := fun time inside => by
      have paid := budgets.normalized_movement (contained time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)) * scale
    scale_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 801 / 64)
        (Norm.Basic.normSq_nonneg _)) nonnegative
    variation := by
      intro left right leftInside rightInside
      have polynomial := Clearance.normalized_distance_le site parameter (Waist.direction quarter first)
        anchor.regular (contained left leftInside) (contained right rightInside)
      have geometric := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (variation left right leftInside rightInside)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 801 / 64)
          (Norm.Basic.normSq_nonneg (halfGap site parameter)))
      rewrite [Norm.Basic.normSq_eq_canonical
        (Clearance.normalizedRadicand site parameter (point left) -
          Clearance.normalizedRadicand site parameter (point right))] at polynomial
      exact polynomial.trans (geometric.trans_eq (by ring1)) }

/-- Construct cofactor root PathData on that SAME supplied point function and unchanged quarter reference budget. -/
def unitAlong (budgets : Budgets anchor) (point : Fraction.Rational → Canonical)
    (contained : ∀ time, FixedRootBoxPath.Inside time → (sourceBox anchor).Contains (point time))
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (variation : ∀ left right, FixedRootBoxPath.Inside left → FixedRootBoxPath.Inside right →
      Norm.Basic.normSq (point left - point right) ≤ scale * (right - left) ^ 2) : UnitPath budgets :=
  { point := fun time => (unitPolynomial site).eval (point time)
    nonzero := fun time inside => budgets.unit_nonzero (contained time inside)
    firstMovement := fun time inside => by
      have paid := budgets.unit_movement (contained time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := fun time inside => by
      have paid := budgets.unit_movement (contained time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := scale
    scale_nonnegative := nonnegative
    variation := by
      intro left right leftInside rightInside
      have distance := Clearance.cofactor_distance site (point left) (point right)
      rewrite [Norm.Basic.normSq_eq_canonical
        ((unitPolynomial site).eval (point left) - (unitPolynomial site).eval (point right))] at distance
      exact distance.le.trans (variation left right leftInside rightInside) }

/-- Both original factor paths and their complete finite preparation results on one supplied physical function.

The function, containment and variation certificates remain exact indices.
Whole factory identities retain both original PathData values and each actual
Preparation.Result, including the computed finite depth, cached endpoint
Owners and accepted advances. This is a preparation cache, not a replacement
spatial trace or a statement of period transport.
-/
@[expose] def Continuation (budgets : Budgets anchor) (point : Fraction.Rational → Canonical)
    (contained : ∀ time, FixedRootBoxPath.Inside time → (sourceBox anchor).Contains (point time))
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (variation : ∀ left right, FixedRootBoxPath.Inside left → FixedRootBoxPath.Inside right →
      Norm.Basic.normSq (point left - point right) ≤ scale * (right - left) ^ 2) :=
  Σ normal : { path : NormalPath budgets // path = normalAlong budgets point contained scale nonnegative variation },
    Σ unit : { path : UnitPath budgets // path = unitAlong budgets point contained scale nonnegative variation },
      { retained : FixedRootBoxPath.Preparation.Result normal.val × FixedRootBoxPath.Preparation.Result unit.val //
          PreparationCache normal.val retained.1 ∧ PreparationCache unit.val retained.2 }

namespace Continuation

/-- Construct each original factor path once, then prepare it once on the SAME physical function and source budgets. -/
def build (budgets : Budgets anchor) (point : Fraction.Rational → Canonical)
    (contained : ∀ time, FixedRootBoxPath.Inside time → (sourceBox anchor).Contains (point time))
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (variation : ∀ left right, FixedRootBoxPath.Inside left → FixedRootBoxPath.Inside right →
      Norm.Basic.normSq (point left - point right) ≤ scale * (right - left) ^ 2) :
    Continuation budgets point contained scale nonnegative variation :=
  let normal := normalAlong budgets point contained scale nonnegative variation
  let unit := unitAlong budgets point contained scale nonnegative variation
  let preparedNormal := FixedRootBoxPath.Preparation.Result.build normal
  let preparedUnit := FixedRootBoxPath.Preparation.Result.build unit
  ⟨⟨normal, rfl⟩, ⟨⟨unit, rfl⟩, ⟨⟨preparedNormal, preparedUnit⟩,
    (by unfold PreparationCache; rfl), (by unfold PreparationCache; rfl)⟩⟩⟩

variable {budgets : Budgets anchor} {point : Fraction.Rational → Canonical}
variable {contained : ∀ time, FixedRootBoxPath.Inside time → (sourceBox anchor).Contains (point time)}
variable {scale : Fraction.Rational} {nonnegative : 0 ≤ scale}
variable {variation : ∀ left right, FixedRootBoxPath.Inside left → FixedRootBoxPath.Inside right →
  Norm.Basic.normSq (point left - point right) ≤ scale * (right - left) ^ 2}

/-- Read the SAME whole original normalized PathData cache. -/
@[expose] def normal (completed : Continuation budgets point contained scale nonnegative variation) := completed.1.val

/-- Read the SAME whole original cofactor PathData cache. -/
@[expose] def unit (completed : Continuation budgets point contained scale nonnegative variation) := completed.2.1.val

/-- Read the complete original normalized finite preparation without recomputing its depth or advances. -/
@[expose] def preparedNormal (completed : Continuation budgets point contained scale nonnegative variation) :=
  completed.2.2.val.1

/-- Read the complete original cofactor finite preparation without recomputing its depth or advances. -/
@[expose] def preparedUnit (completed : Continuation budgets point contained scale nonnegative variation) :=
  completed.2.2.val.2

/-- The normalized PathData is its entire original factory on the SAME physical function and geometric certificates. -/
theorem normal_eq (completed : Continuation budgets point contained scale nonnegative variation) :
    completed.normal = normalAlong budgets point contained scale nonnegative variation := completed.1.property

/-- The cofactor PathData is its entire original factory on the SAME physical function and geometric certificates. -/
theorem unit_eq (completed : Continuation budgets point contained scale nonnegative variation) :
    completed.unit = unitAlong budgets point contained scale nonnegative variation := completed.2.1.property

/-- The normalized point reads its original factor at the identical supplied physical point. -/
theorem normal_point (completed : Continuation budgets point contained scale nonnegative variation)
    (time : Fraction.Rational) :
    completed.normal.point time = Clearance.normalizedRadicand site parameter (point time) := by
  have points := congrArg (fun path : NormalPath budgets => path.point time) completed.normal_eq
  exact points

/-- The cofactor point reads its original affine factor at the identical supplied physical point. -/
theorem unit_point (completed : Continuation budgets point contained scale nonnegative variation)
    (time : Fraction.Rational) : completed.unit.point time = (unitPolynomial site).eval (point time) := by
  have points := congrArg (fun path : UnitPath budgets => path.point time) completed.unit_eq
  exact points

/-- The normalized preparation is the original whole factory on its SAME cached PathData. -/
theorem preparedNormal_eq (completed : Continuation budgets point contained scale nonnegative variation) :
    completed.preparedNormal = FixedRootBoxPath.Preparation.Result.build completed.normal := by
  have retained := completed.2.2.property.1
  unfold PreparationCache at retained
  exact retained

/-- The cofactor preparation is the original whole factory on its SAME separately cached PathData. -/
theorem preparedUnit_eq (completed : Continuation budgets point contained scale nonnegative variation) :
    completed.preparedUnit = FixedRootBoxPath.Preparation.Result.build completed.unit := by
  have retained := completed.2.2.property.2
  unfold PreparationCache at retained
  exact retained

variable {followingPoint : Fraction.Rational → Canonical}
variable {followingContained : ∀ time, FixedRootBoxPath.Inside time →
  (sourceBox anchor).Contains (followingPoint time)}
variable {followingScale : Fraction.Rational} {followingNonnegative : 0 ≤ followingScale}
variable {followingVariation : ∀ left right, FixedRootBoxPath.Inside left → FixedRootBoxPath.Inside right →
  Norm.Basic.normSq (followingPoint left - followingPoint right) ≤ followingScale * (right - left) ^ 2}

/-- Compare the literal normalized finish and following source Owners at a geometrically proved common point.

The two actual finite preparations remain distinct inputs. Their retained
finish refinement and original cached source-box readback supply the signed
comparison through the SAME source Seed Budget. No source or finish Owner
is replaced, and no agreement is admitted as a caller field.
-/
def normal_join (completed : Continuation budgets point contained scale nonnegative variation)
    (following : Continuation budgets followingPoint followingContained
      followingScale followingNonnegative followingVariation)
    (point_eq : point 1 = followingPoint 0) :
    NamedEquivalent (ownerRootName completed.preparedNormal.finishOwner.parameterNonzero
      completed.preparedNormal.finishOwner)
      (ownerRootName following.preparedNormal.source.parameterNonzero following.preparedNormal.source) := by
  have parameter_eq := (completed.normal_point 1).trans
    ((congrArg (Clearance.normalizedRadicand site parameter) point_eq).trans (following.normal_point 0).symm)
  have movement := budgets.normalized_movement (contained 1 (of_decide_eq_true rfl))
  rewrite [← completed.normal_point 1, Norm.Basic.normSq_eq_canonical] at movement
  have followingRefines : following.preparedNormal.source.track.initial.box.Refines
      anchor.seed.owner.track.initial.box := by
    have sourceBox := congrArg (fun owner => owner.track.initial.box) following.preparedNormal.source_eq
    have firstBox := following.normal.first_box 0 (by decide +kernel)
    have equal := sourceBox.trans firstBox
    exact Eq.mpr (congrArg (fun current : Box => current.Refines anchor.seed.owner.track.initial.box) equal)
      (Box.refines_refl _)
  exact budgets.normalized.retainedOwnersEquivalentOfEq parameter_eq
    completed.preparedNormal.finishOwner.parameterNonzero movement
    completed.preparedNormal.finishOwner following.preparedNormal.source
    completed.preparedNormal.prepared.finishOwner_refines followingRefines

/-- Compare the literal cofactor finish and following source Owners through their SAME original quarter Budget.

The actual endpoint equality is transported only through the original affine
factor. Both full preparation caches and the exact stored finish/source
Owners are retained, including their separate refinement certificates.
-/
def unit_join (completed : Continuation budgets point contained scale nonnegative variation)
    (following : Continuation budgets followingPoint followingContained
      followingScale followingNonnegative followingVariation)
    (point_eq : point 1 = followingPoint 0) :
    NamedEquivalent (ownerRootName completed.preparedUnit.finishOwner.parameterNonzero
      completed.preparedUnit.finishOwner)
      (ownerRootName following.preparedUnit.source.parameterNonzero following.preparedUnit.source) := by
  have parameter_eq := (completed.unit_point 1).trans
    ((congrArg (fun point : Canonical => (unitPolynomial site).eval point) point_eq).trans
      (following.unit_point 0).symm)
  have movement := budgets.unit_movement (contained 1 (of_decide_eq_true rfl))
  rewrite [← completed.unit_point 1, Norm.Basic.normSq_eq_canonical] at movement
  have followingRefines : following.preparedUnit.source.track.initial.box.Refines
      actual.data.source.track.initial.box := by
    have sourceBox := congrArg (fun owner => owner.track.initial.box) following.preparedUnit.source_eq
    have firstBox := following.unit.first_box 0 (by decide +kernel)
    have equal := sourceBox.trans firstBox
    exact Eq.mpr (congrArg (fun current : Box => current.Refines actual.data.source.track.initial.box) equal)
      (Box.refines_refl _)
  exact budgets.unit.retainedOwnersEquivalentOfEq parameter_eq
    completed.preparedUnit.finishOwner.parameterNonzero movement
    completed.preparedUnit.finishOwner following.preparedUnit.source
    completed.preparedUnit.prepared.finishOwner_refines followingRefines

end Continuation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian.Cofactor
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation.Reading
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Variation
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Transport
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Norm.Product
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

/-! # Accepted cofactor-root continuation on the actual conic meridian

The actual loop and radial phases give finite displacement bounds on the
same parameter and both conic coordinates. Their recovered base and affine
cofactor have squared variation density32. The original fixed-box preparer
therefore constructs actual finite accepted moves on the given source and
budget. Queries retain its stored owners and the existing cubic Lift.
No complement, homology or matrix conclusion follows from this local trace.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.RootIsolation

variable {site : Fin 2} {parameter : Canonical} (original : Point site parameter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (inside : Contains site parameter original.plus)

/-- An exact scalar coefficient scales the same squared displacement without evaluating its inputs. -/
private theorem scale_density (density ceiling gain width : Fraction.Rational)
    (coefficient : density * ceiling = gain) :
    (density * width ^ 2) * ceiling = gain * width ^ 2 :=
  (show (density * width ^ 2) * ceiling = (density * ceiling) * width ^ 2 by ring1).trans
    (congrArg (fun value : Fraction.Rational => value * width ^ 2) coefficient)

include regular bound inside in
/-- The recovered actual cubic base has squared variation density32 on the rational unit interval.

The parameter, first coordinate and second coordinate have respective
quadrance densities1,6,24. They use the same original phase, its actual
fixed radial parameter, and both original annulus ceilings. The exact
half-sum readback pays the stated coarse density internally.
-/
theorem transport_base_distance_le (left right : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside left) (rightInside : FixedRootBoxPath.Inside right) :
    Norm.Basic.normSq ((transport left original).base - (transport right original).base) ≤
      32 * (right - left) ^ 2 := by
  let alpha := Twist.radialParameter site parameter original.plus
  have alphaInside : 0 ≤ alpha ∧ alpha ≤ 1 := Twist.radialParameter_inside bound inside
  have scaledInside (time : Fraction.Rational) (admitted : FixedRootBoxPath.Inside time) :
      FixedRootBoxPath.Inside (time * alpha) :=
    ⟨Order.Arithmetic.mul_nonneg_direct admitted.1 alphaInside.1,
      ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct admitted.2 alphaInside.1).trans_eq
        (Fraction.Field.one_mul alpha)).trans alphaInside.2⟩
  have alphaSquare : alpha ^ 2 ≤ 1 :=
    (Order.Arithmetic.pow_le_pow_direct alphaInside.1 alphaInside.2 2).trans_eq (by decide +kernel)
  have squaredWidth : 0 ≤ (right - left) ^ 2 := Order.Arithmetic.sq_nonneg_direct _
  have scaleBound {value : Canonical}
      (actual : Norm.Basic.normSq value ≤ 384 * (right * alpha - left * alpha) ^ 2) :
      Norm.Basic.normSq value ≤ 384 * (right - left) ^ 2 := by
    have coefficient := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct alphaSquare
      (by decide +kernel : (0 : Fraction.Rational) ≤ 384)
    have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient squaredWidth
    exact actual.trans ((show 384 * (right * alpha - left * alpha) ^ 2 =
      (384 * alpha ^ 2) * (right - left) ^ 2 by ring1).trans_le (scaled.trans_eq (by ring1)))
  have loopClose := Twist.phase_square_distance_le left right leftInside rightInside
  have radialClose := scaleBound (Twist.phase_square_distance_le (left * alpha) (right * alpha)
    (scaledInside left leftInside) (scaledInside right rightInside))
  have conjugateClose := scaleBound (Twist.phase_conjugate_square_distance_le
    (left * alpha) (right * alpha) (scaledInside left leftInside) (scaledInside right rightInside))
  have plusBound : Norm.Basic.normSq original.plus ≤ (1 / 64 : Fraction.Rational) :=
    inside.2.trans_eq (by decide +kernel)
  have minusBound : Norm.Basic.normSq original.minus ≤ (1 / 64 : Fraction.Rational) :=
    (original_minus_bound original regular inside).trans_eq (by decide +kernel)
  have parameterDifference : parameterAt site parameter left - parameterAt site parameter right =
      ((Twist.phase left).value - (Twist.phase right).value) * (parameter - criticalValue site) := by
    calc
      _ = (parameterAt site parameter left - criticalValue site) -
          (parameterAt site parameter right - criticalValue site) := by ring1
      _ = (Twist.phase left).value * (parameter - criticalValue site) -
          (Twist.phase right).value * (parameter - criticalValue site) :=
        congrArg₂ (fun first last : Canonical => first - last)
          (displacement site parameter left) (displacement site parameter right)
      _ = _ := by ring1
  have parameterClose : Norm.Basic.normSq (parameterAt site parameter left - parameterAt site parameter right) ≤
      (right - left) ^ 2 := by
    rewrite [parameterDifference, Norm.Basic.normSq_mul]
    exact (Order.Arithmetic.mul_le_mul_direct
      (Twist.phase_distance_le left right leftInside rightInside) bound (Norm.Basic.normSq_nonneg _)
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) squaredWidth)).trans_eq
        ((scale_density 64 (1 / 64) 1 (right - left) (by decide +kernel)).trans (Fraction.Field.one_mul _))
  have plusDifference : (transport left original).plus - (transport right original).plus =
      ((Twist.phase (left * alpha)).value ^ 2 - (Twist.phase (right * alpha)).value ^ 2) * original.plus := by
    rewrite [transport_plus, transport_plus]
    change (Twist.phase (left * alpha)).value ^ 2 * original.plus -
      (Twist.phase (right * alpha)).value ^ 2 * original.plus = _
    ring1
  have plusClose : Norm.Basic.normSq ((transport left original).plus - (transport right original).plus) ≤
      6 * (right - left) ^ 2 := by
    rewrite [plusDifference, Norm.Basic.normSq_mul]
    exact (Order.Arithmetic.mul_le_mul_direct radialClose plusBound (Norm.Basic.normSq_nonneg _)
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) squaredWidth)).trans_eq
        (scale_density 384 (1 / 64) 6 (right - left) (by decide +kernel))
  have loopNorm (time : Fraction.Rational) : Norm.Basic.normSq ((Twist.phase time).value ^ 2) = 1 := by
    rewrite [Norm.Power.normSq_pow, (Twist.phase time).unit]
    decide +kernel
  have conjugateNorm (time : Fraction.Rational) :
      Norm.Basic.normSq (Basic.conj (Twist.phase time).value ^ 2) = 1 := by
    rewrite [Norm.Power.normSq_pow, Norm.Basic.normSq_conj, (Twist.phase time).unit]
    decide +kernel
  have productClose := Norm.Product.difference_le
    (firstLeft := (Twist.phase left).value ^ 2) (lastLeft := (Twist.phase right).value ^ 2)
    (firstRight := Basic.conj (Twist.phase (left * alpha)).value ^ 2)
    (lastRight := Basic.conj (Twist.phase (right * alpha)).value ^ 2)
    loopClose (conjugateNorm (left * alpha)).le (loopNorm right).le conjugateClose
  have productBound : Norm.Basic.normSq
      ((Twist.phase left).value ^ 2 * Basic.conj (Twist.phase (left * alpha)).value ^ 2 -
        (Twist.phase right).value ^ 2 * Basic.conj (Twist.phase (right * alpha)).value ^ 2) ≤
      1536 * (right - left) ^ 2 := productClose.trans_eq (by ring1)
  have minusDifference : (transport left original).minus - (transport right original).minus =
      ((Twist.phase left).value ^ 2 * Basic.conj (Twist.phase (left * alpha)).value ^ 2 -
        (Twist.phase right).value ^ 2 * Basic.conj (Twist.phase (right * alpha)).value ^ 2) * original.minus := by
    rewrite [transport_minus, transport_minus]
    change (Twist.phase left).value ^ 2 * Basic.conj (Twist.phase (left * alpha)).value ^ 2 * original.minus -
      (Twist.phase right).value ^ 2 * Basic.conj (Twist.phase (right * alpha)).value ^ 2 * original.minus = _
    ring1
  have minusClose : Norm.Basic.normSq ((transport left original).minus - (transport right original).minus) ≤
      24 * (right - left) ^ 2 := by
    rewrite [minusDifference, Norm.Basic.normSq_mul]
    exact (Order.Arithmetic.mul_le_mul_direct productBound minusBound (Norm.Basic.normSq_nonneg _)
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) squaredWidth)).trans_eq
        (scale_density 1536 (1 / 64) 24 (right - left) (by decide +kernel))
  have pairClose := (Norm.Bounds.normSq_add_le_two
    ((transport left original).minus - (transport right original).minus)
    ((transport left original).plus - (transport right original).plus)).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct minusClose plusClose) (by decide +kernel))
  have sumClose := (Norm.Bounds.normSq_add_le_two
    (parameterAt site parameter left - parameterAt site parameter right)
    (((transport left original).minus - (transport right original).minus) +
      ((transport left original).plus - (transport right original).plus))).trans
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.add_le_add_direct parameterClose pairClose) (by decide +kernel))
  have scalarBound : 2 * ((right - left) ^ 2 + 2 *
      (24 * (right - left) ^ 2 + 6 * (right - left) ^ 2)) ≤ 128 * (right - left) ^ 2 := by
    have coefficient := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (122 : Fraction.Rational) ≤ 128) squaredWidth
    exact (show 2 * ((right - left) ^ 2 + 2 *
      (24 * (right - left) ^ 2 + 6 * (right - left) ^ 2)) = 122 * (right - left) ^ 2 by ring1).trans_le coefficient
  have baseDifference : ((transport left original).base - (transport right original).base) * 2 =
      (parameterAt site parameter left - parameterAt site parameter right) +
        (((transport left original).minus - (transport right original).minus) +
          ((transport left original).plus - (transport right original).plus)) := by
    calc
      _ = (transport left original).base * 2 - (transport right original).base * 2 := by ring1
      _ = _ := by
        rewrite [(transport left original).base_mul_two, (transport right original).base_mul_two]
        ring1
  apply Order.Arithmetic.le_of_mul_le_mul_right_direct (c := (4 : Fraction.Rational)) _ (by decide +kernel)
  calc
    Norm.Basic.normSq ((transport left original).base - (transport right original).base) * 4 =
        Norm.Basic.normSq (((transport left original).base - (transport right original).base) * 2) := by
      rewrite [Norm.Basic.normSq_mul, show Norm.Basic.normSq (2 : Canonical) = 4 by decide +kernel]
      rfl
    _ = _ := congrArg Norm.Basic.normSq baseDifference
    _ ≤ 128 * (right - left) ^ 2 := sumClose.trans scalarBound
    _ = (32 * (right - left) ^ 2) * 4 := by ring1

namespace Cofactor

include regular bound inside in
/-- The actual affine cofactor path has the same finite density32 as its retained recovered base. -/
theorem distance_le (left right : Fraction.Rational)
    (leftInside : FixedRootBoxPath.Inside left) (rightInside : FixedRootBoxPath.Inside right) :
    Norm.Basic.normSq (point original left - point original right) ≤ 32 * (right - left) ^ 2 := by
  have difference : point original left - point original right =
      (transport left original).base - (transport right original).base := by
    rewrite [point_eq, point_eq]
    ring1
  rewrite [difference]
  exact transport_base_distance_le original regular bound inside left right leftInside rightInside

variable (source : Owner (UnitRoot.seed site ^ 2)) (budget : FixedRootBoxBudget.Budget source)
    (movement_eq : budget.movement = 1 / 2)

include regular bound inside movement_eq in
/-- The actual meridian cofactor constructs the original quantitative path owner on the SAME given budget.

Nonvanishing and both movement laws use the original node chart. Density32
is derived from the original phase formulas, so the later finite preparation
needs no supplied variation, sign or numerical comparison premise.
-/
@[expose] def path : FixedRootBoxPath.PathData budget budget :=
  { point := point original
    nonzero := fun time _ => nonzero original regular bound inside time
    firstMovement := fun time _ => by
      have actual := movement original regular bound inside time
      rewrite [Norm.Basic.normSq_eq_canonical] at actual
      exact actual.trans_eq movement_eq.symm
    secondMovement := fun time _ => by
      have actual := movement original regular bound inside time
      rewrite [Norm.Basic.normSq_eq_canonical] at actual
      exact actual.trans_eq movement_eq.symm
    scale := 32
    scale_nonnegative := by decide +kernel
    variation := fun left right leftInside rightInside => by
      have actual := distance_le original regular bound inside left right leftInside rightInside
      rewrite [Norm.Basic.normSq_eq_canonical] at actual
      exact actual }

include regular bound inside movement_eq in
/-- Prepare finite accepted cofactor moves, retaining the actual path factory and original result caches. -/
def prepare :
    (retained : { value : FixedRootBoxPath.PathData budget budget //
      value = path original regular bound inside source budget movement_eq }) ×
        FixedRootBoxPath.Preparation.Result retained.val :=
  let retained := path original regular bound inside source budget movement_eq
  let prepared := FixedRootBoxPath.Preparation.Result.build retained
  ⟨⟨retained, rfl⟩, prepared⟩

variable {actualPath : FixedRootBoxPath.PathData budget budget}
    (factory : actualPath = path original regular bound inside source budget movement_eq)

include factory in
/-- The whole retained path factory reads the exact cofactor of the SAME actual transported Point. -/
theorem path_point (time : Fraction.Rational) : actualPath.point time = point original time :=
  congrArg (fun value : FixedRootBoxPath.PathData budget budget => value.point time) factory

include factory in
/-- Reindex the GIVEN trace query owner by its actual cofactor formula without rebuilding that owner. -/
def unit (time : Fraction.Rational) (reading : FixedRootBoxPath.Preparation.Reading actualPath time) :
    Owner (point original time) :=
  SquareRoot.Owner.Transport.castOwnerParameter
    (path_point original regular bound inside source budget movement_eq factory time) reading.owner

/-- The same reindexed query retains its actual refinement into the original source Owner's box. -/
theorem unit_refines (time : Fraction.Rational) (reading : FixedRootBoxPath.Preparation.Reading actualPath time) :
    (unit original regular bound inside source budget movement_eq factory time reading).track.initial.box.Refines
      source.track.initial.box := by
  unfold unit
  rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
  exact reading.refines

variable (sourceFactory : source = UnitRoot.Transport.source site)

include sourceFactory in
/-- The GIVEN actual queried owner refines the original signed cofactor square. -/
theorem unit_signed (time : Fraction.Rational) (reading : FixedRootBoxPath.Preparation.Reading actualPath time) :
    (unit original regular bound inside source budget movement_eq factory time reading).track.initial.box.Refines
      (UnitRoot.box site) := by
  have sourceBox : source.track.initial.box = UnitRoot.box site :=
    (congrArg (fun value : Owner (UnitRoot.seed site ^ 2) => value.track.initial.box) sourceFactory).trans
      (UnitRoot.Transport.source_box site)
  exact Eq.mp (congrArg (fun box =>
    (unit original regular bound inside source budget movement_eq factory time reading).track.initial.box.Refines box)
      sourceBox) (unit_refines original regular bound inside source budget movement_eq factory time reading)

include sourceFactory in
/-- The SAME actual trace query agrees with the original independently retained signed patch owner. -/
def unit_agrees (time : Fraction.Rational) (reading : FixedRootBoxPath.Preparation.Reading actualPath time) :
    NamedEquivalent
      (ownerRootName
        (unit original regular bound inside source budget movement_eq factory time reading).parameterNonzero
        (unit original regular bound inside source budget movement_eq factory time reading))
      (ownerRootName (UnitRoot.owner site (transport time original).base
        (transport_base_inside original regular bound inside time)).parameterNonzero
        (UnitRoot.owner site (transport time original).base
          (transport_base_inside original regular bound inside time))) :=
  UnitRoot.Transport.retained_agrees site (transport time original).base
    (transport_base_inside original regular bound inside time)
    (unit original regular bound inside source budget movement_eq factory time reading)
    (unit_signed original regular bound inside source budget movement_eq factory sourceFactory time reading)

/-- Construct the original cubic lift on the SAME actual supplied trace query owner. -/
def liftReading (time : Fraction.Rational) (reading : FixedRootBoxPath.Preparation.Reading actualPath time) :
    Lift (transport time original)
      (unit original regular bound inside source budget movement_eq factory time reading) :=
  let sameUnit := unit original regular bound inside source budget movement_eq factory time reading
  Lift.ofUnit (transport time original) sameUnit

/-- Read the actual stored trace once and construct the actual cubic lift on that SAME returned Owner. -/
def readLift (prepared : FixedRootBoxPath.Preparation.Result actualPath) (time : Fraction.Rational)
    (admitted : FixedRootBoxPath.Inside time) :
    (queried : { value : FixedRootBoxPath.Preparation.Reading actualPath time //
      value = prepared.read time admitted }) ×
      Lift (transport time original)
        (unit original regular bound inside source budget movement_eq factory time queried.val) :=
  let queried := prepared.read time admitted
  let actual := liftReading original regular bound inside source budget movement_eq factory time queried
  ⟨⟨queried, rfl⟩, actual⟩

include sourceFactory in
/-- The actual time-zero trace query agrees with the GIVEN initial lift's original cofactor Owner. -/
def initial_root_agrees (reading : FixedRootBoxPath.Preparation.Reading actualPath 0)
    (initialInside : (spatialBox site).Contains original.base)
    (initial : Lift original (UnitRoot.owner site original.base initialInside)) :
    NamedEquivalent
      (ownerRootName (unit original regular bound inside source budget movement_eq factory 0 reading).parameterNonzero
        (unit original regular bound inside source budget movement_eq factory 0 reading))
      (ownerRootName initial.unitOwner.parameterNonzero initial.unitOwner) := by
  let queried := unit original regular bound inside source budget movement_eq factory 0 reading
  have same : point original 0 = (unitPolynomial site).eval original.base :=
    congrArg (fun value : Canonical => (unitPolynomial site).eval value) (transport_base_zero original)
  have firstRefines : queried.track.initial.box.Refines source.track.initial.box :=
    unit_refines original regular bound inside source budget movement_eq factory 0 reading
  have lastBox : initial.unitOwner.track.initial.box = source.track.initial.box := by
    have initialBox := (congrArg
      (fun value : Owner ((unitPolynomial site).eval original.base) => value.track.initial.box)
      initial.unitOwner_eq).trans (UnitRoot.owner_initial_box site original.base initialInside)
    have sourceBox := (congrArg
      (fun value : Owner (UnitRoot.seed site ^ 2) => value.track.initial.box) sourceFactory).trans
        (UnitRoot.Transport.source_box site)
    exact initialBox.trans sourceBox.symm
  have lastRefines : initial.unitOwner.track.initial.box.Refines source.track.initial.box := by
    rewrite [lastBox]
    exact Box.refines_refl _
  have paid : (UnitRoot.seed site ^ 2 - point original 0).normSq ≤ budget.movement := by
    have actual := movement original regular bound inside 0
    rewrite [Norm.Basic.normSq_eq_canonical] at actual
    exact actual.trans_eq movement_eq.symm
  exact budget.retainedOwnersEquivalentOfEq same queried.parameterNonzero paid queried initial.unitOwner
    firstRefines lastRefines

include sourceFactory in
/-- The GIVEN actual time-zero cubic lift agrees with the SAME GIVEN initial cubic channel. -/
def initial_value_agrees (reading : FixedRootBoxPath.Preparation.Reading actualPath 0)
    (initialInside : (spatialBox site).Contains original.base)
    (initial : Lift original (UnitRoot.owner site original.base initialInside))
    (actual : Lift (transport 0 original)
      (unit original regular bound inside source budget movement_eq factory 0 reading)) :
    NamedEquivalent actual.value.name initial.value.name := by
  have root := initial_root_agrees original regular bound inside source budget movement_eq factory sourceFactory
    reading initialInside initial
  have initialName := congrArg
    (fun value : Owner ((unitPolynomial site).eval original.base) => ownerRootName value.parameterNonzero value)
    initial.unitOwner_eq
  have roots : NamedEquivalent actual.unitRoot.value.name initial.unitRoot.value.name :=
    NamedEquivalent.transport (Lift.unitRoot_name actual).symm
      (initialName.trans (Lift.unitRoot_name initial).symm) root
  have ordinate : NamedEquivalent (Coherence.exact (transport 0 original).ordinate).name
      (Coherence.exact original.ordinate).name :=
    NamedEquivalent.transport rfl (congrArg Named.exact (transport_ordinate_zero original))
      (NamedEquivalent.refl _)
  rewrite [actual.value_eq, initial.value_eq]
  exact Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    _ _ _ _ roots ordinate

end Cofactor

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

end

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry.Deformation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Signed factor lift of the actual ruled short-arc deformation

Each fixed original arc fraction supplies the SAME ruled blend path. Its
normalized quadratic and cofactor remain in the original source Seed and
quarter reference budgets. Complete original finite root preparations and
requested-time query caches are retained; their actual factor certificates
produce the full cubic value through the original Values construction.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

open Purelib.RootIsolation.SquareRoot

namespace Deformation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.RootIsolation
open Factors (Budgets Values)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

/-- The exact same ruled blend has affine squared distance in its original blend parameter. -/
theorem blend_distance (geometry : Geometry source targetReading anchor.regular payment)
    (fraction left right : Fraction.Rational) :
    Norm.Basic.normSq (geometry.deformation fraction left - geometry.deformation fraction right) =
      Norm.Basic.normSq (Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction -
        coordinate site parameter 2 quarter positive (first + fraction * (last - first))) * (right - left) ^ 2 := by
  unfold Geometry.deformation
  rewrite [Affine.normSq_line_sub, show (left - right) ^ 2 = (right - left) ^ 2 by ring1]
  rfl

/-- Construct the normalized fixed-box continuation along one actual ruled blend of the SAME deformation.

The two budget indices are the identical original normalized source budget.
Whole-square factor movement pays every blend point, and the actual affine
blend displacement pays its time variation. No new source Seed is selected.
-/
def normalPath (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (ordered : first ≤ last) (fraction : Fraction.Rational) (fractionInside : FixedRootBoxPath.Inside fraction) :
    Factors.NormalPath budgets :=
  { point := fun blend => Clearance.normalizedRadicand site parameter (geometry.deformation fraction blend)
    nonzero := fun blend inside => budgets.normalized_nonzero
      (geometry.deformation_inside ordered fractionInside inside)
    firstMovement := fun blend inside => by
      have paid := budgets.normalized_movement (geometry.deformation_inside ordered fractionInside inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := fun blend inside => by
      have paid := budgets.normalized_movement (geometry.deformation_inside ordered fractionInside inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)) *
      Norm.Basic.normSq (Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction -
        coordinate site parameter 2 quarter positive (first + fraction * (last - first)))
    scale_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 801 / 64)
        (Norm.Basic.normSq_nonneg _)) (Norm.Basic.normSq_nonneg _)
    variation := by
      intro left right leftInside rightInside
      have spatial := Clearance.normalized_distance_le site parameter (Waist.direction quarter first)
        anchor.regular (geometry.deformation_inside ordered fractionInside leftInside)
        (geometry.deformation_inside ordered fractionInside rightInside)
      rewrite [blend_distance (anchor := anchor) geometry fraction left right] at spatial
      rewrite [Norm.Basic.normSq_eq_canonical
        (Clearance.normalizedRadicand site parameter (geometry.deformation fraction left) -
          Clearance.normalizedRadicand site parameter (geometry.deformation fraction right))] at spatial
      exact spatial.trans_eq (by ring1) }

/-- Construct the original cofactor continuation on the identical ruled blend and unchanged quarter budget. -/
def unitPath (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (ordered : first ≤ last) (fraction : Fraction.Rational) (fractionInside : FixedRootBoxPath.Inside fraction) :
    Factors.UnitPath budgets :=
  { point := fun blend => (unitPolynomial site).eval (geometry.deformation fraction blend)
    nonzero := fun blend inside => budgets.unit_nonzero
      (geometry.deformation_inside ordered fractionInside inside)
    firstMovement := fun blend inside => by
      have paid := budgets.unit_movement (geometry.deformation_inside ordered fractionInside inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := fun blend inside => by
      have paid := budgets.unit_movement (geometry.deformation_inside ordered fractionInside inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := Norm.Basic.normSq (Tangent.baseChord site parameter 2 quarter positive first (last - first) fraction -
      coordinate site parameter 2 quarter positive (first + fraction * (last - first)))
    scale_nonnegative := Norm.Basic.normSq_nonneg _
    variation := by
      intro left right _ _
      have distance := Clearance.cofactor_distance site
        (geometry.deformation fraction left) (geometry.deformation fraction right)
      rewrite [blend_distance (anchor := anchor) geometry fraction left right, Norm.Basic.normSq_eq_canonical
        ((unitPolynomial site).eval (geometry.deformation fraction left) -
          (unitPolynomial site).eval (geometry.deformation fraction right))] at distance
      exact distance.le }

/-- Original normalized/cofactor paths and their complete finite preparations at one retained original arc fraction.

Each whole factory equation refers to the exact cached path data, original
budgets and original ruled deformation. The preparations retain their actual
source/finish Owners and accepted advances. They are not physical affine
ClearSegments and do not replace the supplied paid spatial Route.
-/
@[expose] def Lift (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (ordered : first ≤ last) (fraction : Fraction.Rational) (fractionInside : FixedRootBoxPath.Inside fraction) :=
  Σ normal : { path : Factors.NormalPath budgets //
      path = normalPath budgets geometry ordered fraction fractionInside },
    Σ unit : { path : Factors.UnitPath budgets // path = unitPath budgets geometry ordered fraction fractionInside },
      { retained : FixedRootBoxPath.Preparation.Result normal.val × FixedRootBoxPath.Preparation.Result unit.val //
          Factors.PreparationCache normal.val retained.1 ∧ Factors.PreparationCache unit.val retained.2 }

namespace Lift

/-- Prepare both factor paths once, retaining their complete actual finite root-continuation results. -/
def build (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (ordered : first ≤ last) (fraction : Fraction.Rational) (fractionInside : FixedRootBoxPath.Inside fraction) :
    Lift budgets geometry ordered fraction fractionInside :=
  let normal := normalPath budgets geometry ordered fraction fractionInside
  let unit := unitPath budgets geometry ordered fraction fractionInside
  let preparedNormal := FixedRootBoxPath.Preparation.Result.build normal
  let preparedUnit := FixedRootBoxPath.Preparation.Result.build unit
  ⟨⟨normal, rfl⟩, ⟨⟨unit, rfl⟩, ⟨⟨preparedNormal, preparedUnit⟩,
    (by unfold Factors.PreparationCache; rfl), (by unfold Factors.PreparationCache; rfl)⟩⟩⟩

variable {budgets : Budgets anchor} {geometry : Geometry source targetReading anchor.regular payment}
variable {ordered : first ≤ last} {fraction : Fraction.Rational} {fractionInside : FixedRootBoxPath.Inside fraction}

/-- Read the SAME complete normalized path cache on the original ruled blend. -/
@[expose] def normal (completed : Lift budgets geometry ordered fraction fractionInside) := completed.1.val

/-- Read the SAME complete cofactor path cache on that identical blend. -/
@[expose] def unit (completed : Lift budgets geometry ordered fraction fractionInside) := completed.2.1.val

/-- Read the retained original normalized preparation, including all actual endpoint and advance caches. -/
@[expose] def preparedNormal (completed : Lift budgets geometry ordered fraction fractionInside) := completed.2.2.val.1

/-- Read the retained original cofactor preparation with its own actual endpoint and advance caches. -/
@[expose] def preparedUnit (completed : Lift budgets geometry ordered fraction fractionInside) := completed.2.2.val.2

/-- The normalized path cache is its entire original factory on the identical deformation and source budget. -/
theorem normal_eq (completed : Lift budgets geometry ordered fraction fractionInside) :
    completed.normal = normalPath budgets geometry ordered fraction fractionInside := completed.1.property

/-- The cofactor path cache is its entire original factory on the identical deformation and quarter budget. -/
theorem unit_eq (completed : Lift budgets geometry ordered fraction fractionInside) :
    completed.unit = unitPath budgets geometry ordered fraction fractionInside := completed.2.1.property

/-- The normalized finite preparation is the exact original factory on the SAME cached path data. -/
theorem preparedNormal_eq (completed : Lift budgets geometry ordered fraction fractionInside) :
    completed.preparedNormal = FixedRootBoxPath.Preparation.Result.build completed.normal := by
  have retained := completed.2.2.property.1
  unfold Factors.PreparationCache at retained
  exact retained

/-- The cofactor finite preparation is the exact original factory on its SAME separately cached path data. -/
theorem preparedUnit_eq (completed : Lift budgets geometry ordered fraction fractionInside) :
    completed.preparedUnit = FixedRootBoxPath.Preparation.Result.build completed.unit := by
  have retained := completed.2.2.property.2
  unfold Factors.PreparationCache at retained
  exact retained

/-- Every normalized path query reads the original quadratic at the exact SAME ruled-deformation point. -/
theorem normal_point (completed : Lift budgets geometry ordered fraction fractionInside) (blend : Fraction.Rational) :
    completed.normal.point blend =
      Clearance.normalizedRadicand site parameter (geometry.deformation fraction blend) := by
  rewrite [completed.normal_eq]
  unfold normalPath
  rfl

/-- Every cofactor path query reads the original affine factor at that identical ruled-deformation point. -/
theorem unit_point (completed : Lift budgets geometry ordered fraction fractionInside) (blend : Fraction.Rational) :
    completed.unit.point blend = (unitPolynomial site).eval (geometry.deformation fraction blend) := by
  rewrite [completed.unit_eq]
  unfold unitPath
  rfl

/-- Both exact requested-time query caches, their original parameter transports and one actual full cubic product.

The old preparations remain indices. Each query is performed once, and the
original Values cache retains the actual queried factor Owners, their full
certificates, product and CoordinateChannels at the same physical point.
-/
@[expose] def Reading (completed : Lift budgets geometry ordered fraction fractionInside)
    (blend : Fraction.Rational) (inside : FixedRootBoxPath.Inside blend) :=
  Σ normalQuery : { query : FixedRootBoxPath.Preparation.Reading completed.normal blend //
      query = completed.preparedNormal.read blend inside },
    Σ unitQuery : { query : FixedRootBoxPath.Preparation.Reading completed.unit blend //
        query = completed.preparedUnit.read blend inside },
      Σ normal : { owner : SquareRootContinuationChain.Owner
          (Clearance.normalizedRadicand site parameter (geometry.deformation fraction blend)) // owner =
          Owner.Transport.castOwnerParameter (completed.normal_point blend) normalQuery.val.owner },
        Σ unit : { owner : SquareRootContinuationChain.Owner
            ((unitPolynomial site).eval (geometry.deformation fraction blend)) // owner =
            Owner.Transport.castOwnerParameter (completed.unit_point blend) unitQuery.val.owner },
          { values : Values site parameter (geometry.deformation fraction blend) unit.val normal.val //
              values = Values.build unit.val normal.val }

namespace Reading

/-- Query each actual cached factor preparation once and retain the original full product/coordinate construction. -/
def build (completed : Lift budgets geometry ordered fraction fractionInside)
    (blend : Fraction.Rational) (inside : FixedRootBoxPath.Inside blend) : Reading completed blend inside :=
  let normalQuery := completed.preparedNormal.read blend inside
  let unitQuery := completed.preparedUnit.read blend inside
  let normal := Owner.Transport.castOwnerParameter (completed.normal_point blend) normalQuery.owner
  let unit := Owner.Transport.castOwnerParameter (completed.unit_point blend) unitQuery.owner
  let values := Values.build unit normal
  ⟨⟨normalQuery, rfl⟩, ⟨⟨unitQuery, rfl⟩, ⟨⟨normal, rfl⟩, ⟨⟨unit, rfl⟩, ⟨values, rfl⟩⟩⟩⟩⟩

variable {completed : Lift budgets geometry ordered fraction fractionInside}
variable {blend : Fraction.Rational} {inside : FixedRootBoxPath.Inside blend}

/-- Read the whole actual normalized query cache without replaying its preparation or advance. -/
@[expose] def normalQuery (reading : Reading completed blend inside) := reading.1.val

/-- Read the whole actual cofactor query cache without replaying its independent preparation or advance. -/
@[expose] def unitQuery (reading : Reading completed blend inside) := reading.2.1.val

/-- Read the original normalized query Owner with only its exact radicand index transported. -/
@[expose] def normal (reading : Reading completed blend inside) := reading.2.2.1.val

/-- Read the original cofactor query Owner with only its exact factor index transported. -/
@[expose] def unit (reading : Reading completed blend inside) := reading.2.2.2.1.val

/-- Read the complete cached full cubic product and original CoordinateChannels on those identical queried Owners. -/
@[expose] def values (reading : Reading completed blend inside) := reading.2.2.2.2.val

/-- The normalized query is the SAME original requested-time factory on the stored preparation. -/
theorem normalQuery_eq (reading : Reading completed blend inside) :
    reading.normalQuery = completed.preparedNormal.read blend inside := reading.1.property

/-- The cofactor query is the SAME original requested-time factory on its separately stored preparation. -/
theorem unitQuery_eq (reading : Reading completed blend inside) :
    reading.unitQuery = completed.preparedUnit.read blend inside := reading.2.1.property

/-- The normalized Owner is the exact original parameter transport of the SAME cached query Owner. -/
theorem normal_eq (reading : Reading completed blend inside) : reading.normal =
    Owner.Transport.castOwnerParameter (completed.normal_point blend) reading.normalQuery.owner :=
  reading.2.2.1.property

/-- The cofactor Owner is the exact original parameter transport of its SAME separately cached query Owner. -/
theorem unit_eq (reading : Reading completed blend inside) : reading.unit =
    Owner.Transport.castOwnerParameter (completed.unit_point blend) reading.unitQuery.owner :=
  reading.2.2.2.1.property

/-- The actual full product/cache is its entire original factory on the two SAME queried factor Owners. -/
theorem values_eq (reading : Reading completed blend inside) :
    reading.values = Values.build reading.unit reading.normal := reading.2.2.2.2.property

/-- The actual normalized query refines the identical original source Seed box. -/
theorem normal_refines (reading : Reading completed blend inside) :
    reading.normal.track.initial.box.Refines anchor.seed.owner.track.initial.box := by
  rewrite [reading.normal_eq, Owner.Transport.castOwnerParameter_initial_box]
  exact reading.normalQuery.refines

/-- The actual cofactor query refines the identical original prepared-quarter reference box. -/
theorem unit_refines (reading : Reading completed blend inside) :
    reading.unit.track.initial.box.Refines actual.data.source.track.initial.box := by
  rewrite [reading.unit_eq, Owner.Transport.castOwnerParameter_initial_box]
  exact reading.unitQuery.refines

end Reading
end Lift
end Deformation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Transport
public import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.Curves.Legendre.Degeneration.Conic.Rotation
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus
import Purelib.Curves.Legendre.Degeneration
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Signed cofactor roots over the actual conic meridian images

Both original conic radii remain bounded, so every recovered cubic base
stays inside the same node chart. One GIVEN signed reference Owner and its
GIVEN whole-patch budget construct actual cofactor owners on that image.
The original cubic Lift constructor consumes the SAME queried owner once.
At time zero, retained root-box comparisons and the exact original phase
endpoint compare the resulting cubic channel to the GIVEN initial lift.

This is the restriction of the original nonvanishing root chart to the
actual meridian image. It is not an accepted time-ordered root trace:
that further constructor needs the actual phase path's finite variation
bound. No complement, homology, matrix or fresh canonical basis agreement
is inferred from these local constructions.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} (original : Point site parameter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Rational))
    (inside : Contains site parameter original.plus)

include regular inside in
/-- The original conic product and annulus admission bound the SAME supplied second coordinate. -/
theorem original_minus_bound : Norm.Basic.normSq original.minus ≤ outerRadiusSq := by
  have same : original.minus = partner site parameter original.plus :=
    original.minus_eq_div (original.plus_ne_zero regular)
  exact (congrArg Norm.Basic.normSq same).trans_le (partner_contains regular inside).2

include inside in
/-- Every actual first meridian coordinate stays in the original conic square. -/
theorem transport_plus_inside (time : Rational) : coordinateBox.Contains (transport time original).plus :=
  coordinate_inside ((transport_plus_normSq time original).trans_le inside.2)

include regular inside in
/-- Every actual second meridian coordinate stays in that same original square. -/
theorem transport_minus_inside (time : Rational) : coordinateBox.Contains (transport time original).minus :=
  coordinate_inside ((transport_minus_normSq time original).trans_le
    (original_minus_bound original regular inside))

include regular bound inside in
/-- The recovered cubic base stays inside the smaller original parameter square at every rational time. -/
theorem transport_base_parameter_inside (time : Rational) :
    (parameterBox site).Contains (transport time original).base :=
  (transport time original).base_parameter_inside (parameter_inside bound time)
    (transport_plus_inside original inside time) (transport_minus_inside original regular inside time)

include regular bound inside in
/-- Every actual meridian base has the original node-chart margin from the remaining branch. -/
theorem transport_base_inside (time : Rational) : (spatialBox site).Contains (transport time original).base :=
  (transport time original).base_inside (parameter_inside bound time)
    (transport_plus_inside original inside time) (transport_minus_inside original regular inside time)

/-- The actual time-zero conic base is the unchanged original cubic base. -/
theorem transport_base_zero : (transport 0 original).base = original.base :=
  (Point.castParameter_base (parameter_zero site parameter) (transport 0 original)).symm.trans
    (congrArg Point.base (transport_zero original))

/-- The actual time-zero normalized ordinate is the unchanged original ordinate. -/
theorem transport_ordinate_zero : (transport 0 original).ordinate = original.ordinate :=
  (Point.castParameter_ordinate (parameter_zero site parameter) (transport 0 original)).symm.trans
    (congrArg Point.ordinate (transport_zero original))

namespace Cofactor

/-- The original affine cofactor evaluated on the SAME actual transported cubic base. -/
@[expose] def point (time : Rational) : Canonical := (unitPolynomial site).eval (transport time original).base

/-- The retained cofactor is x-1 at node zero and x at node one, on the actual same base. -/
theorem point_eq (time : Rational) : point original time = (transport time original).base - remainingValue site := by
  unfold point unitPolynomial
  exact Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval _ _

include regular bound inside in
/-- The entire actual cofactor image has the original positive one-quarter quadrance floor. -/
theorem lower (time : Rational) : (1 / 4 : Rational) ≤ Norm.Basic.normSq (point original time) :=
  unit_lower site (transport_base_inside original regular bound inside time)

include regular bound inside in
/-- The actual cofactor image is nonvanishing at every rational meridian time. -/
theorem nonzero (time : Rational) : point original time ≠ 0 :=
  unit_ne_zero site (transport_base_inside original regular bound inside time)

include regular bound inside in
/-- The same signed reference square pays at most one-half quadrance movement over the entire actual image. -/
theorem movement (time : Rational) :
    Norm.Basic.normSq (UnitRoot.seed site ^ 2 - point original time) ≤ 1 / 2 :=
  UnitRoot.variation_bound site (transport_base_inside original regular bound inside time)

variable (source : Owner (UnitRoot.seed site ^ 2))
    (sourceFactory : source = UnitRoot.Transport.source site)
    (budget : FixedRootBoxBudget.Budget source) (movement_eq : budget.movement = 1 / 2)

/-- One actual queried root retains the original signed square and this SAME cached positive clearance. -/
@[expose] def Reading (time : Rational) : Type :=
  { unit : Owner (point original time) // unit.track.initial.box = UnitRoot.box site ∧
    unit.track.initial.clearance.bound = budget.clearance }

include regular bound inside sourceFactory movement_eq in
/-- Construct one genuine fixed-box cofactor owner from the GIVEN original source and budget caches.

The actual transported base derives nonvanishing and movement internally.
The complete source factory identifies its signed square, while ownerAt
retains that exact box and the given budget's uniform positive clearance.
No sign is chosen from a matrix, endpoint label or square residual.
-/
def read (time : Rational) : Reading (original := original) (source := source) budget time := by
  have paid : (UnitRoot.seed site ^ 2 - point original time).normSq ≤ budget.movement := by
    have actual := movement original regular bound inside time
    rewrite [Norm.Basic.normSq_eq_canonical] at actual
    exact actual.trans_eq movement_eq.symm
  let unit := budget.ownerAt (nonzero original regular bound inside time) paid
  have sourceBox : source.track.initial.box = UnitRoot.box site :=
    (congrArg (fun value : Owner (UnitRoot.seed site ^ 2) => value.track.initial.box) sourceFactory).trans
      (UnitRoot.Transport.source_box site)
  exact ⟨unit, (budget.ownerAt_box _ _).trans sourceBox, budget.ownerAt_clearance _ _⟩

include regular bound inside sourceFactory movement_eq in
/-- Construct the actual full-cubic channel on one SAME bound queried cofactor owner.

The returned query retains its complete read factory. The existing Lift
constructor acquires that queried owner's certificate once and derives
both the original cubic-square comparison and the original forward conic
coordinate comparisons. A possible zero normalized ordinate is preserved;
no nonzero full-cubic Owner is asserted from cofactor clearance alone.
-/
def lift (time : Rational) :
    (queried : { value : Reading (original := original) (source := source) budget time //
      value = read original regular bound inside source sourceFactory budget movement_eq time }) ×
      Lift (transport time original) queried.val.val :=
  let queried := read original regular bound inside source sourceFactory budget movement_eq time
  let actual := Lift.ofUnit (transport time original) queried.val
  ⟨⟨queried, rfl⟩, actual⟩

include regular bound inside sourceFactory movement_eq in
/-- The actual queried time-zero cofactor agrees with the GIVEN initial lift's retained original signed root.

The scalar base readback transports only the radicand index. Both complete
Owners are passed to the original fixed-box comparison, and the initial
lift's actual owner factory derives its signed-box refinement internally.
-/
def zero_root_agrees (initialInside : (spatialBox site).Contains original.base)
    (initial : Lift original (UnitRoot.owner site original.base initialInside))
    (queried : Reading (original := original) (source := source) budget 0) :
    NamedEquivalent (ownerRootName queried.val.parameterNonzero queried.val)
      (ownerRootName initial.unitOwner.parameterNonzero initial.unitOwner) := by
  have same : point original 0 = (unitPolynomial site).eval original.base :=
    congrArg (fun value : Canonical => (unitPolynomial site).eval value) (transport_base_zero original)
  have sourceBox : source.track.initial.box = UnitRoot.box site :=
    (congrArg (fun value : Owner (UnitRoot.seed site ^ 2) => value.track.initial.box) sourceFactory).trans
      (UnitRoot.Transport.source_box site)
  have initialBox : initial.unitOwner.track.initial.box = UnitRoot.box site :=
    (congrArg (fun value : Owner ((unitPolynomial site).eval original.base) => value.track.initial.box)
      initial.unitOwner_eq).trans (UnitRoot.owner_initial_box site original.base initialInside)
  have firstRefines : queried.val.track.initial.box.Refines source.track.initial.box := by
    rewrite [queried.property.1, sourceBox]
    exact Box.refines_refl _
  have lastRefines : initial.unitOwner.track.initial.box.Refines source.track.initial.box := by
    rewrite [initialBox, sourceBox]
    exact Box.refines_refl _
  have paid : (UnitRoot.seed site ^ 2 - point original 0).normSq ≤ budget.movement := by
    have actual := movement original regular bound inside 0
    rewrite [Norm.Basic.normSq_eq_canonical] at actual
    exact actual.trans_eq movement_eq.symm
  exact budget.retainedOwnersEquivalentOfEq same queried.val.parameterNonzero paid queried.val initial.unitOwner
    firstRefines lastRefines

include regular bound inside sourceFactory movement_eq in
/-- The actual time-zero cubic channel agrees with the SAME GIVEN initial cubic lift.

The original cofactor comparison and exact normalized-ordinate readback
pay the product comparison. This is an operational initial-channel anchor;
it is not a whole-Owner identity, a complement gluing theorem or a cycle
or homology conclusion.
-/
def zero_value_agrees (initialInside : (spatialBox site).Contains original.base)
    (initial : Lift original (UnitRoot.owner site original.base initialInside))
    (queried : Reading (original := original) (source := source) budget 0)
    (actual : Lift (transport 0 original) queried.val) :
    NamedEquivalent actual.value.name initial.value.name := by
  have root := zero_root_agrees original regular bound inside source sourceFactory budget movement_eq
    initialInside initial queried
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

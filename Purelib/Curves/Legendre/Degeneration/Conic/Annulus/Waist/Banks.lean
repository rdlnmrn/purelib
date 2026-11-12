module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# The two oriented banks of the original Legendre waist

The first two original rational quarters run from the moving labelled branch
to the fixed labelled branch. Conjugating their unit directions and reversing
their parameter runs along the returning bank. These constructions retain the
full original conic points and signed cubic channels; coordinate exchange
proves the opposite-sheet comparison internally, including the branch points.
The segment projection does not identify this circuit with a canonical A/B
homology owner: that identification additionally requires a cut attachment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation

set_option genInjectivity false in
/-- The two consecutive quarters of the bank from the moving branch to the fixed branch. -/
inductive Half
  /-- The original first quarter, from the moving branch to the collision midpoint. -/ | first
  /-- The original second quarter, from the collision midpoint to the fixed branch. -/ | second

constructive_injectivity Half

/-- Read the original circuit quarter belonging to this forward bank half. -/
@[expose] def Half.quarter : Half → Quarter.UnitCircuitQuarter
  | .first => .first
  | .second => .second

/-- Conjugate the exact original unit direction without changing its unit-norm owner. -/
@[expose] def mirror (original : UnitVertex) : UnitVertex :=
  { value := Basic.conj original.value
    unit := (Norm.Basic.normSq_conj original.value).trans original.unit }

/-- Two geometric bank reflections recover the entire original certified unit direction. -/
theorem mirror_mirror (original : UnitVertex) : mirror (mirror original) = original :=
  UnitVertex.eq_of_value_eq (Basic.conj_conj original.value)

/-- The forward direction is the displayed original first or second rational quarter. -/
@[expose] def forwardDirection (half : Half) (time : Fraction.Rational) : UnitVertex :=
  direction half.quarter time

/-- The returning direction conjugates the same original bank while reversing its time parameter. -/
@[expose] def reverseDirection (half : Half) (time : Fraction.Rational) : UnitVertex :=
  mirror (forwardDirection half (1 - time))

/-- Reflection of a waist point is the exact coordinate exchange of that original conic point. -/
theorem point_mirror (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    point site parameter (mirror original) regular bound =
      (point site parameter original regular bound).exchange := by
  have first : (point site parameter original regular bound).exchange.plus =
      coordinate site parameter (mirror original) := by
    change (point site parameter original regular bound).minus = _
    exact point_minus site parameter original regular bound
  have ext {left right : Point site parameter} (plus : left.plus = right.plus)
      (minus : left.minus = right.minus) : left = right := by
    cases left with
    | mk leftPlus leftMinus leftEquation =>
      cases right with
      | mk rightPlus rightMinus rightEquation =>
        change leftPlus = rightPlus at plus
        change leftMinus = rightMinus at minus
        cases plus
        cases minus
        rfl
  apply ext
  · exact (point_plus site parameter (mirror original) regular bound).trans first.symm
  · change (point site parameter (mirror original) regular bound).minus =
      (point site parameter original regular bound).plus
    rewrite [point_minus, point_plus]
    change halfGap site parameter * Basic.conj (Basic.conj original.value) =
      halfGap site parameter * original.value
    rewrite [Basic.conj_conj]
    rfl

/-- The original signed cubic channels on reflected banks agree with negation.

The cofactor comparison is derived internally from the unchanged original base.
-/
def lift_mirror_agrees (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    NamedEquivalent (lift site parameter (mirror original) regular bound).value.name
      (lift site parameter original regular bound).value.neg.name := by
  have same := point_mirror site parameter original regular bound
  have compare {first last : Point site parameter} (equal : first = last.exchange)
      (firstInside : (spatialBox site).Contains first.base)
      (lastInside : (spatialBox site).Contains last.base)
      (firstLift : Lift first (UnitRoot.owner site first.base firstInside))
      (lastLift : Lift last (UnitRoot.owner site last.base lastInside)) :
      NamedEquivalent
        firstLift.value.name lastLift.value.neg.name := by
    cases equal
    exact Lift.exchange_patch_agrees lastLift firstLift
  exact compare same (point_inside _ _ _ regular bound) (point_inside _ _ _ regular bound)
    (lift site parameter (mirror original) regular bound) (lift site parameter original regular bound)

/-- The forward bank's exact rational coordinate along the moving-to-fixed branch segment. -/
@[expose] def segmentParameter (original : UnitVertex) : Fraction.Rational :=
  (1 - original.value.re) / 2

/-- Every retained unit direction projects into the same closed original branch segment. -/
theorem segmentParameter_bounds (original : UnitVertex) :
    0 ≤ segmentParameter original ∧ segmentParameter original ≤ 1 := by
  have square : original.value.re ^ 2 ≤ (1 : Fraction.Rational) ^ 2 := by
    have unit := original.unit
    change original.value.re ^ 2 + original.value.im ^ 2 = 1 at unit
    calc
      original.value.re ^ 2 = original.value.re ^ 2 + 0 := by ring1
      _ ≤ original.value.re ^ 2 + original.value.im ^ 2 :=
        Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.sq_nonneg_direct _)
      _ = _ := unit
  have upper := Arithmetic.le_of_sq_le_sq_direct (by decide +kernel) square
  have lower := Arithmetic.neg_le_of_sq_le_sq_direct (by decide +kernel) square
  constructor
  · exact Fraction.Order.Field.div_nonneg_direct
      (Arithmetic.sub_nonneg_direct upper) (by decide +kernel)
  · apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 2)).mpr
    have result := Arithmetic.sub_le_sub_left_direct lower 1
    change 1 - original.value.re ≤ 1 * 2
    calc
      _ ≤ 1 - -1 := result
      _ = _ := by decide +kernel

/-- The original cubic base is the displayed affine combination of the two retained labelled branch endpoints. -/
theorem point_base_segment (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter original regular bound).base =
      Paths.branchPoint parameter 1 +
        (⟨segmentParameter original, 0⟩ : Canonical) *
          (Paths.branchPoint parameter (fixedLabel site) - Paths.branchPoint parameter 1) := by
  have scalar : (⟨segmentParameter original, 0⟩ : Canonical) * 2 =
      1 - Components.Projection.realPart original.value := by
    apply Basic.ext
    · change segmentParameter original * 2 - 0 * 0 = 1 - original.value.re
      calc
        _ = segmentParameter original * 2 := by ring0
        _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
    · change segmentParameter original * 0 + 0 * 2 = 0 - 0
      ring1
  rewrite [point_base, ← center_add_halfGap site parameter, ← center_sub_halfGap site parameter]
  calc
    _ = center site parameter + halfGap site parameter *
        (1 - (⟨segmentParameter original, 0⟩ : Canonical) * 2) :=
      congrArg (fun value => center site parameter + halfGap site parameter * value) (by
        rewrite [scalar]
        ring1)
    _ = _ := by ring1

/-- Reflection preserves the exact original branch-segment coordinate. -/
theorem segmentParameter_mirror (original : UnitVertex) :
    segmentParameter (mirror original) = segmentParameter original := rfl

/-- The two forward bank halves meet at the identical original unit direction. -/
theorem forward_join : forwardDirection .first 1 = forwardDirection .second 0 :=
  directions_join.1

/-- The second reversed half joins the first reversed half at the identical reflected direction. -/
theorem reverse_join : reverseDirection .second 1 = reverseDirection .first 0 := by
  change mirror (forwardDirection .second (1 - 1)) = mirror (forwardDirection .first (1 - 0))
  rewrite [show (1 - 1 : Fraction.Rational) = 0 by decide +kernel,
    show (1 - 0 : Fraction.Rational) = 1 by decide +kernel]
  exact congrArg mirror forward_join.symm

/-- The bank circuit closes at both original real branch directions. -/
theorem directions_close :
    forwardDirection .second 1 = reverseDirection .second 0 ∧
      reverseDirection .first 1 = forwardDirection .first 0 := by
  constructor
  · apply UnitVertex.eq_of_value_eq
    change (direction .second 1).value = Basic.conj (direction .second (1 - 0)).value
    rewrite [show (1 - 0 : Fraction.Rational) = 1 by decide +kernel, direction_value,
      Stereographic.unitQuarterPoint_one]
    decide +kernel
  · apply UnitVertex.eq_of_value_eq
    change Basic.conj (direction .first (1 - 1)).value = (direction .first 0).value
    rewrite [show (1 - 1 : Fraction.Rational) = 0 by decide +kernel, direction_start_value]
    decide +kernel

/-- The forward bank begins at the original moving branch and ends at the original fixed branch. -/
theorem forward_endpoints (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter (forwardDirection .first 0) regular bound).base = Paths.branchPoint parameter 1 ∧
      (point site parameter (forwardDirection .second 1) regular bound).base =
        Paths.branchPoint parameter (fixedLabel site) := by
  constructor
  · exact (point_first_start site parameter regular bound).1
  · have join := congrArg (fun input => (point site parameter input regular bound).base) directions_join.2.1
    exact join.trans (point_third_start site parameter regular bound).1

/-- Both bank-switch endpoints have zero original normalized ordinate. -/
theorem forward_endpoint_ordinates (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter (forwardDirection .first 0) regular bound).ordinate = 0 ∧
      (point site parameter (forwardDirection .second 1) regular bound).ordinate = 0 := by
  constructor
  · exact (point_first_start site parameter regular bound).2
  · have join := congrArg (fun input => (point site parameter input regular bound).ordinate) directions_join.2.1
    exact join.trans (point_third_start site parameter regular bound).2

/-- Reindex the complete retained certificate along an exact radicand equality. -/
private def castCertificate {first last : Canonical} (equal : first = last)
    (root : CertifiedSquareRoot.Certificate first) : CertifiedSquareRoot.Certificate last := equal ▸ root

/-- Certificate transport agrees with transport of its identical original owner. -/
private theorem castCertificate_owner {first last : Canonical} (equal : first = last)
    (owner : Owner first) (root : CertifiedSquareRoot.Certificate first)
    (retained : root = owner.certificate owner.parameterNonzero) :
    castCertificate equal root =
      (SquareRoot.Owner.Transport.castOwnerParameter equal owner).certificate
        (SquareRoot.Owner.Transport.castOwnerParameter equal owner).parameterNonzero := by
  cases equal
  exact retained

/-- Reindexing the certificate preserves its cached actual root program. -/
private theorem castCertificate_value {first last : Canonical} (equal : first = last)
    (root : CertifiedSquareRoot.Certificate first) : (castCertificate equal root).value = root.value := by
  cases equal
  rfl

set_option genInjectivity false in
/-- Both geometric bank lifts at one retained direction, constructed with the identical cached cofactor certificate.

The full original forward lift remains an input. The return owner is its exact
radicand transport to the reflected conic point. Its root program is retained
unchanged; the independent opposite-sheet comparison consumes both actual
cubic products and the exact exchanged normalized ordinate.
-/
structure Reading {site : Fin 2} {parameter : Canonical} (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    {unit : Owner ((unitPolynomial site).eval (point site parameter original regular bound).base)}
    (forward : Lift (point site parameter original regular bound) unit) where
  /-- The exact original radicand equality derived from the geometric bank reflection. -/
  radicand_eq : (unitPolynomial site).eval (point site parameter original regular bound).base =
    (unitPolynomial site).eval (point site parameter (mirror original) regular bound).base
  /-- The actual returned cubic lift on the transported complete original cofactor owner. -/
  returned : Lift (point site parameter (mirror original) regular bound)
    (SquareRoot.Owner.Transport.castOwnerParameter radicand_eq unit)
  /-- The returned construction consumes the identical cached actual cofactor program. -/
  root_eq : returned.unitRoot.value = forward.unitRoot.value
  /-- The two retained actual cubic channels agree with the sheet negation. -/
  opposite : NamedEquivalent returned.value.name forward.value.neg.name

constructive_injectivity Reading

namespace Reading

/-- Construct the reflected bank lift by transporting the original cached certificate without acquiring another root. -/
def ofLift {site : Fin 2} {parameter : Canonical} (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    {unit : Owner ((unitPolynomial site).eval (point site parameter original regular bound).base)}
    (forward : Lift (point site parameter original regular bound) unit) : Reading original regular bound forward := by
  let originalPoint := point site parameter original regular bound
  let returnPoint := point site parameter (mirror original) regular bound
  have geometry : returnPoint = originalPoint.exchange := point_mirror site parameter original regular bound
  have base : returnPoint.base = originalPoint.base :=
    (congrArg Point.base geometry).trans originalPoint.exchange_base
  let equal := congrArg (unitPolynomial site).eval base.symm
  let returnUnit := SquareRoot.Owner.Transport.castOwnerParameter equal unit
  let returnRoot := castCertificate equal forward.unitRoot
  have originalRoot : forward.unitRoot = unit.certificate unit.parameterNonzero :=
    forward.unitRoot_eq.trans (congrArg (fun owner => owner.certificate owner.parameterNonzero) forward.unitOwner_eq)
  have retained : returnRoot = returnUnit.certificate returnUnit.parameterNonzero :=
    castCertificate_owner equal unit forward.unitRoot originalRoot
  let returned := Lift.ofRoot returnPoint returnUnit returnRoot retained
  have sameRoot : returned.unitRoot.value = forward.unitRoot.value :=
    (congrArg (fun root : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval returnPoint.base) => root.value)
      (Lift.ofRoot_unitRoot returnPoint returnUnit returnRoot retained)).trans
      (castCertificate_value equal forward.unitRoot)
  have compare {first last : Point site parameter} (equalPoint : first = last.exchange)
      {firstUnit : Owner ((unitPolynomial site).eval first.base)}
      {lastUnit : Owner ((unitPolynomial site).eval last.base)}
      (firstLift : Lift first firstUnit) (lastLift : Lift last lastUnit)
      (roots : firstLift.unitRoot.value = lastLift.unitRoot.value) :
      NamedEquivalent firstLift.value.name lastLift.value.neg.name := by
    cases equalPoint
    exact Lift.exchange_value_agrees lastLift firstLift
      (NamedEquivalent.transport (congrArg (fun value => value.name) roots).symm rfl (NamedEquivalent.refl _))
  exact
    { radicand_eq := equal
      returned := returned
      root_eq := sameRoot
      opposite := compare geometry returned forward sameRoot }

end Reading

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks

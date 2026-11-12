module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian.Cofactor.Path
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Lift
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Rotation
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic

/-! # The actual cubic chart endpoint and two independent annular lifts

The accepted trace query and independent chart executions retain distinct
cofactor Owners. The original explicit fibre cast and transport_one identify
only their actual base and normalized ordinate. Retained signed-box
comparisons and coherent product comparison derive channel agreement.
No complement return, positive twist convention, homology or matrix action
is asserted.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian.Cofactor

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

variable {site : Fin 2} {parameter : Canonical} (original : Point site parameter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (inside : Contains site parameter original.plus)
    (initialInside : (spatialBox site).Contains original.base)
    (initial : Lift original (UnitRoot.owner site original.base initialInside))

/-- The explicit returning fibre cast identifies the actual endpoint base with the SAME second stored chart image. -/
theorem endpoint_base (kept : Twist.Twice original regular bound inside initialInside initial) :
    (transport 1 original).base =
      (Twist.Twice.last original regular bound inside initialInside initial kept).1.val.base :=
  (Point.castParameter_base (parameter_one site parameter) (transport 1 original)).symm.trans
    (congrArg Point.base ((transport_one original).trans
      (Twist.Twice.target_eq original regular bound inside initialInside initial kept).symm))

/-- The same explicit cast preserves the actual normalized ordinate of the returning chart image. -/
theorem endpoint_ordinate (kept : Twist.Twice original regular bound inside initialInside initial) :
    (transport 1 original).ordinate =
      (Twist.Twice.last original regular bound inside initialInside initial kept).1.val.ordinate :=
  (Point.castParameter_ordinate (parameter_one site parameter) (transport 1 original)).symm.trans
    (congrArg Point.ordinate ((transport_one original).trans
      (Twist.Twice.target_eq original regular bound inside initialInside initial kept).symm))

variable (source : Owner (UnitRoot.seed site ^ 2)) (budget : FixedRootBoxBudget.Budget source)
    (movement_eq : budget.movement = 1 / 2)
    {actualPath : FixedRootBoxPath.PathData budget budget}
    (factory : actualPath = path original regular bound inside source budget movement_eq)
    (sourceFactory : source = UnitRoot.Transport.source site)

include sourceFactory in
/-- The GIVEN actual time-one query agrees with the independent twofold lift's actual signed cofactor Owner.

Both retained Owners are compared through their genuine refinements into
one original signed source box. The explicit endpoint-base equality changes
only the cofactor parameter index, not either Owner or its selected sign.
-/
def endpoint_root_agrees (reading : FixedRootBoxPath.Preparation.Reading actualPath 1)
    (kept : Twist.Twice original regular bound inside initialInside initial) :
    NamedEquivalent
      (ownerRootName (unit original regular bound inside source budget movement_eq factory 1 reading).parameterNonzero
        (unit original regular bound inside source budget movement_eq factory 1 reading))
      (ownerRootName
        (Twist.Twice.last original regular bound inside initialInside initial kept).2.unitOwner.parameterNonzero
        (Twist.Twice.last original regular bound inside initialInside initial kept).2.unitOwner) := by
  let queried := unit original regular bound inside source budget movement_eq factory 1 reading
  let target := Twist.Twice.last original regular bound inside initialInside initial kept
  have same : point original 1 = (unitPolynomial site).eval target.1.val.base :=
    congrArg (fun value : Canonical => (unitPolynomial site).eval value)
      (endpoint_base original regular bound inside initialInside initial kept)
  have firstRefines : queried.track.initial.box.Refines source.track.initial.box :=
    unit_refines original regular bound inside source budget movement_eq factory 1 reading
  have targetBox : target.2.unitOwner.track.initial.box = UnitRoot.box site :=
    (congrArg (fun value : Owner ((unitPolynomial site).eval target.1.val.base) => value.track.initial.box)
      target.2.unitOwner_eq).trans (UnitRoot.owner_initial_box site target.1.val.base
        (Twist.Twice.last_inside original regular bound inside initialInside initial kept))
  have sourceBox : source.track.initial.box = UnitRoot.box site :=
    (congrArg (fun value : Owner (UnitRoot.seed site ^ 2) => value.track.initial.box) sourceFactory).trans
      (UnitRoot.Transport.source_box site)
  have lastRefines : target.2.unitOwner.track.initial.box.Refines source.track.initial.box := by
    rewrite [targetBox, sourceBox]
    exact Box.refines_refl _
  have paid : (UnitRoot.seed site ^ 2 - point original 1).normSq ≤ budget.movement := by
    have actual := movement original regular bound inside 1
    rewrite [Norm.Basic.normSq_eq_canonical] at actual
    exact actual.trans_eq movement_eq.symm
  exact budget.retainedOwnersEquivalentOfEq same queried.parameterNonzero paid queried target.2.unitOwner
    firstRefines lastRefines

include sourceFactory in
/-- The GIVEN actual endpoint cubic channel agrees with the SAME independently retained twofold chart lift. -/
def endpoint_value_agrees (reading : FixedRootBoxPath.Preparation.Reading actualPath 1)
    (actual : Lift (transport 1 original)
      (unit original regular bound inside source budget movement_eq factory 1 reading))
    (kept : Twist.Twice original regular bound inside initialInside initial) :
    NamedEquivalent actual.value.name
      (Twist.Twice.last original regular bound inside initialInside initial kept).2.value.name := by
  let target := Twist.Twice.last original regular bound inside initialInside initial kept
  have root := endpoint_root_agrees original regular bound inside initialInside initial
    source budget movement_eq factory sourceFactory reading kept
  have targetName := congrArg
    (fun value : Owner ((unitPolynomial site).eval target.1.val.base) => ownerRootName value.parameterNonzero value)
    target.2.unitOwner_eq
  have roots : NamedEquivalent actual.unitRoot.value.name target.2.unitRoot.value.name :=
    NamedEquivalent.transport (Lift.unitRoot_name actual).symm
      (targetName.trans (Lift.unitRoot_name target.2).symm) root
  have ordinate : NamedEquivalent (Coherence.exact (transport 1 original).ordinate).name
      (Coherence.exact target.1.val.ordinate).name :=
    NamedEquivalent.transport rfl
      (congrArg Named.exact (endpoint_ordinate original regular bound inside initialInside initial kept))
      (NamedEquivalent.refl _)
  rewrite [actual.value_eq, target.2.value_eq]
  exact Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    _ _ _ _ roots ordinate

include sourceFactory in
/-- Build the two independent chart lifts once and compare with the SAME supplied accepted endpoint query.

The query retains its complete original prepared.read factory. Neither that
query, its supplied cubic Lift, the accepted preparation nor the GIVEN
initial Lift is executed again. Both independent chart execution factories
and their actual full Lift caches remain in the returned value.
-/
def attachEndpoint (prepared : FixedRootBoxPath.Preparation.Result actualPath)
    (queried : { value : FixedRootBoxPath.Preparation.Reading actualPath 1 //
      value = prepared.read 1 (by decide +kernel) })
    (actual : Lift (transport 1 original)
      (unit original regular bound inside source budget movement_eq factory 1 queried.val)) :
    (kept : { value : Twist.Twice original regular bound inside initialInside initial //
      value = Twist.twice original regular bound inside initialInside initial }) ×
      NamedEquivalent actual.value.name
        (Twist.Twice.last original regular bound inside initialInside initial kept.val).2.value.name :=
  let kept := Twist.twice original regular bound inside initialInside initial
  let compared := endpoint_value_agrees original regular bound inside initialInside initial
    source budget movement_eq factory sourceFactory queried.val actual kept
  ⟨⟨kept, rfl⟩, compared⟩

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian.Cofactor

end

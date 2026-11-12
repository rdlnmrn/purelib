module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual signed cofactor moves along original rational waist quarters

The retained reference owner and uniform budget certify the original cubic
base chart at every rational parameter. Its computed finite subdivision keeps
actual accepted owner moves and exact shared caches. The actual terminal
owner supplies the cubic channel and agrees with the independent signed lift.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Transport

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.RootIsolation

set_option genInjectivity false in
/-- The original quarter's actual reference owner, cached budget and whole rational path certificates.

The source and budget are stored once. The path retains both uses of this same
budget and its exact parameter readings, not a replacement polygon or a word.
-/
structure Data (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) where
  /-- The complete original signed reference owner cached once. -/ source : Owner (UnitRoot.seed site ^ 2)
  /-- The cache belongs to the original selected zero/one cofactor occurrence. -/
  source_eq : source = UnitRoot.Transport.source site
  /-- The whole-quarter budget on this exact retained reference owner. -/ budget : FixedRootBoxBudget.Budget source
  /-- The original whole-patch movement allowance remains one half. -/ movement_eq : budget.movement = 1 / 2
  /-- The actual original rational path with its whole-interval nonzero and variation certificates. -/
  path : FixedRootBoxPath.PathData budget budget
  /-- Every stored path point is the original cofactor evaluation on that same rational waist chart. -/
  point_eq : ∀ time, path.point time = cofactor site parameter quarter regular bound time

constructive_injectivity Data

namespace Data

/-- Derive whole-quarter root-path certificates from intrinsic regularity and the original parameter-distance bound. -/
def build (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Data site parameter quarter regular bound := by
  let source := UnitRoot.Transport.source site
  let budget := FixedRootBoxBudget.Budget.acquire source (1 / 2) (by decide +kernel) (by
    rewrite [UnitRoot.Transport.source_bound]
    decide +kernel)
  have movement (time : Fraction.Rational) :
      (UnitRoot.seed site ^ 2 - cofactor site parameter quarter regular bound time).normSq ≤ budget.movement := by
    have result := UnitRoot.variation_bound site (point_inside site parameter (direction quarter time) regular bound)
    rewrite [Norm.Basic.normSq_eq_canonical] at result
    exact result
  let path : FixedRootBoxPath.PathData budget budget :=
    { point := cofactor site parameter quarter regular bound
      nonzero := fun time _ => unit_ne_zero site (point_inside _ _ _ regular bound)
      firstMovement := fun time _ => movement time
      secondMovement := fun time _ => movement time
      scale := 4 * Norm.Basic.normSq (halfGap site parameter)
      scale_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)
      variation := by
        intro left right _ _
        have result := cofactor_distance_le site parameter quarter regular bound left right
        rewrite [Norm.Basic.normSq_eq_canonical,
          show (left - right) ^ 2 = (right - left) ^ 2 by ring1] at result
        exact result }
  exact
    { source := source
      source_eq := rfl
      budget := budget
      movement_eq := rfl
      path := path
      point_eq := fun _ => rfl }

end Data

set_option genInjectivity false in
/-- An actual complete finite quarter preparation retaining its original reference, budget, path and owner moves. -/
structure Quarter (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) where
  /-- The same original cached whole-quarter data used by preparation. -/
  data : Data site parameter quarter regular bound
  /-- The actual accepted advances, shared owner caches and computed finite depth on that exact path. -/
  prepared : FixedRootBoxPath.Preparation.Result data.path

constructive_injectivity Quarter

namespace Quarter

/-- Construct actual signed cofactor continuation on a whole rational quarter with computed finite depth. -/
def build (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Quarter site parameter quarter regular bound :=
  let data := Data.build site parameter quarter regular bound
  { data := data
    prepared := FixedRootBoxPath.Preparation.Result.build data.path }

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {regular : parameter ≠ criticalValue site}
variable {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}

/-- The actual advanced finish owner transported to the exact original cubic endpoint cofactor index. -/
def finishUnit (actual : Quarter site parameter quarter regular bound) :
    Owner ((unitPolynomial site).eval (Waist.point site parameter (direction quarter 1) regular bound).base) :=
  SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq 1) actual.prepared.finishOwner

/-- The actual advanced endpoint cofactor agrees with the independent signed owner at the same original cubic point. -/
def finishUnit_agrees (actual : Quarter site parameter quarter regular bound) :
    NamedEquivalent (ownerRootName actual.finishUnit.parameterNonzero actual.finishUnit)
      (ownerRootName
        (UnitRoot.owner site (Waist.point site parameter (direction quarter 1) regular bound).base
          (point_inside _ _ _ regular bound)).parameterNonzero
        (UnitRoot.owner site (Waist.point site parameter (direction quarter 1) regular bound).base
          (point_inside _ _ _ regular bound))) := by
  let independent := UnitRoot.owner site (Waist.point site parameter (direction quarter 1) regular bound).base
    (point_inside _ _ _ regular bound)
  let atPath := SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq 1).symm independent
  have refines : atPath.track.initial.box.Refines actual.data.source.track.initial.box := by
    rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box, UnitRoot.owner_initial_box,
      actual.data.source_eq, UnitRoot.Transport.source_box]
    exact Box.refines_refl _
  have independentAgreement := actual.data.path.firstRetained 1 (by decide +kernel) atPath refines
  have cachedName := congrArg (fun owner : Owner (actual.data.path.point 1) =>
    ownerRootName owner.parameterNonzero owner) actual.prepared.target_eq
  have moved := actual.prepared.finish_agrees.trans
    (NamedEquivalent.transport cachedName.symm rfl independentAgreement)
  exact NamedEquivalent.transport
    (ownerRootName_castOwnerParameter (actual.data.point_eq 1) actual.prepared.finishOwner).symm
    (ownerRootName_castOwnerParameter (actual.data.point_eq 1).symm independent) moved

/-- Construct actual original cubic channels using the same retained transported endpoint cofactor owner. -/
def finishLift (actual : Quarter site parameter quarter regular bound) :
    Lift (Waist.point site parameter (direction quarter 1) regular bound) actual.finishUnit :=
  let unit := actual.finishUnit
  let root := unit.certificate unit.parameterNonzero
  Lift.ofRoot (Waist.point site parameter (direction quarter 1) regular bound) unit root rfl

/-- The actual transported-cofactor cubic channel agrees with the independent original signed waist endpoint channel. -/
def finishLift_agrees (actual : Quarter site parameter quarter regular bound) :
    NamedEquivalent actual.finishLift.value.name
      (Waist.lift site parameter (direction quarter 1) regular bound).value.name :=
  Lift.value_agrees actual.finishLift (Waist.lift site parameter (direction quarter 1) regular bound)
    (NamedEquivalent.transport actual.finishLift.unitRoot_name.symm
      (Waist.lift site parameter (direction quarter 1) regular bound).unitRoot_name.symm actual.finishUnit_agrees)

end Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Transport

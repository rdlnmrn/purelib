module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Deformation
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual root continuation on the original radial deformation

The exact original scale `1+t` and its cofactor variation budget prepare a
finite trace of actual accepted owner moves. Requested parameters read the
same stored tree and retain original owners, complete cofactor certificates
and cubic lifts. Signed-patch comparisons are derived by the original retained
box machinery.

This establishes a root deformation. Equality of integrated differentials
requires its additional realized primitive-boundary and integral-homotopy
certificates; canonical cut attachment remains a separate construction.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Deformation.Transport

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.RootIsolation

/-- The original conic point at one exact retained radial-deformation parameter. -/
@[expose] def pointAt (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) : Point site parameter :=
  Radial.point site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1

set_option genInjectivity false in
/-- Original radial-deformation data retaining the actual source, one budget and the exact original cofactor path. -/
structure Data (site : Fin 2) (parameter : Canonical) (original : UnitVertex) where
  /-- The original parameter-distance admission certificate for the whole radial family. -/
  bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)
  /-- The complete original signed reference owner cached once. -/ source : Owner (UnitRoot.seed site ^ 2)
  /-- The retained source is the original selected signed reference occurrence. -/
  source_eq : source = UnitRoot.Transport.source site
  /-- The original whole-patch budget on that identical retained source. -/ budget : FixedRootBoxBudget.Budget source
  /-- The computed movement allowance remains the original one half. -/ movement_eq : budget.movement = 1 / 2
  /-- The actual original radial cofactor path with internally paid whole-interval certificates. -/
  path : FixedRootBoxPath.PathData budget budget
  /-- Every path reading is the exact original radial cofactor formula. -/
  points_eq : ∀ time, path.point time = Deformation.cofactor site parameter original time

constructive_injectivity Data

namespace Data

/-- Read the cofactor at the identical original conic point on an admitted requested radial parameter. -/
theorem point_eq {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
    (data : Data site parameter original) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
    data.path.point time = (unitPolynomial site).eval (pointAt site parameter original time inside).base :=
  (data.points_eq time).trans (Deformation.cofactor_eq site parameter original time inside)

/-- Prepare the original radial path on the supplied identical cached reference owner and budget. -/
def ofBudget (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (source : Owner (UnitRoot.seed site ^ 2)) (source_eq : source = UnitRoot.Transport.source site)
    (budget : FixedRootBoxBudget.Budget source) (movement_eq : budget.movement = 1 / 2) :
    Data site parameter original := by
  have movement (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
      (UnitRoot.seed site ^ 2 - Deformation.cofactor site parameter original time).normSq ≤ budget.movement := by
    have admission := Deformation.scale_bounds inside
    have result := UnitRoot.variation_bound site
      (Radial.point_inside site parameter (Deformation.scale time) original
        admission.1 admission.2.1 admission.2.2 bound)
    rewrite [← Deformation.cofactor_eq site parameter original time inside, Norm.Basic.normSq_eq_canonical] at result
    rewrite [movement_eq]
    exact result
  let path : FixedRootBoxPath.PathData budget budget :=
    { point := Deformation.cofactor site parameter original
      nonzero := by
        intro time inside
        rewrite [Deformation.cofactor_eq site parameter original time inside]
        have admission := Deformation.scale_bounds inside
        exact unit_ne_zero site
          (Radial.point_inside site parameter (Deformation.scale time) original
            admission.1 admission.2.1 admission.2.2 bound)
      firstMovement := movement
      secondMovement := movement
      scale := Norm.Basic.normSq (halfGap site parameter)
      scale_nonnegative := Norm.Basic.normSq_nonneg _
      variation := by
        intro left right leftInside rightInside
        have result := Deformation.cofactor_distance_le site parameter original left right leftInside rightInside
        rewrite [Norm.Basic.normSq_eq_canonical,
          show (left - right) ^ 2 = (right - left) ^ 2 by ring1] at result
        exact result }
  exact
    { bound := bound
      source := source
      source_eq := source_eq
      budget := budget
      movement_eq := movement_eq
      path := path
      points_eq := fun _ => rfl }

/-- Acquire the original signed reference and one budget and prepare the complete original radial-path data. -/
def build (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Data site parameter original :=
  let source := UnitRoot.Transport.source site
  let budget := FixedRootBoxBudget.Budget.acquire source (1 / 2) (by decide +kernel) (by
    rewrite [UnitRoot.Transport.source_bound]
    decide +kernel)
  ofBudget site parameter original bound source rfl budget rfl

end Data

set_option genInjectivity false in
/-- A complete finite trace of actual original cofactor-owner advances on the radial conic deformation. -/
structure Trace (site : Fin 2) (parameter : Canonical) (original : UnitVertex) where
  /-- The identical cached original reference, budget and radial-cofactor path. -/ data : Data site parameter original
  /-- The actual accepted finite moves and shared source/middle/finish caches on that exact path. -/
  prepared : FixedRootBoxPath.Preparation.Result data.path

constructive_injectivity Trace

namespace Trace

/-- Prepare actual original root moves from the same retained radial-path data. -/
def ofData {site : Fin 2} {parameter : Canonical} {original : UnitVertex} (data : Data site parameter original) :
    Trace site parameter original :=
  { data := data
    prepared := FixedRootBoxPath.Preparation.Result.build data.path }

/-- Construct the original whole radial root trace with computed sufficient finite depth. -/
def build (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Trace site parameter original :=
  ofData (Data.build site parameter original bound)

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}

/-- Query the identical stored radial preparation at the exact supplied unit-interval parameter. -/
def read (actual : Trace site parameter original) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
    FixedRootBoxPath.Preparation.Reading actual.data.path time :=
  actual.prepared.read time inside

/-- Reindex one cached actual query owner to the cofactor of the identical original radial conic point. -/
def unit (actual : Trace site parameter original) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
    (reading : FixedRootBoxPath.Preparation.Reading actual.data.path time) :
    Owner ((unitPolynomial site).eval (pointAt site parameter original time inside).base) :=
  SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq time inside) reading.owner

/-- The actual reindexed queried cofactor owner retains the original selected signed square. -/
theorem unit_signed (actual : Trace site parameter original) (time : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside time) (reading : FixedRootBoxPath.Preparation.Reading actual.data.path time) :
    (actual.unit time inside reading).track.initial.box.Refines (UnitRoot.box site) := by
  unfold unit
  rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
  have originalBox : actual.data.source.track.initial.box = UnitRoot.box site := by
    rewrite [actual.data.source_eq, UnitRoot.Transport.source_box]
    rfl
  exact Eq.mp (congrArg (fun box => reading.owner.track.initial.box.Refines box) originalBox) reading.refines

/-- The cached actual radial query agrees internally with the independent original signed cofactor owner. -/
def unit_agrees (actual : Trace site parameter original) (time : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside time) (reading : FixedRootBoxPath.Preparation.Reading actual.data.path time) :
    NamedEquivalent (ownerRootName (actual.unit time inside reading).parameterNonzero (actual.unit time inside reading))
      (ownerRootName
        (UnitRoot.owner site (pointAt site parameter original time inside).base
          (Radial.point_inside site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1
            (Deformation.scale_bounds inside).2.1
            (Deformation.scale_bounds inside).2.2 actual.data.bound)).parameterNonzero
        (UnitRoot.owner site (pointAt site parameter original time inside).base
          (Radial.point_inside site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1
            (Deformation.scale_bounds inside).2.1 (Deformation.scale_bounds inside).2.2 actual.data.bound))) :=
  UnitRoot.Transport.retained_agrees site (pointAt site parameter original time inside).base
    (Radial.point_inside site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1
      (Deformation.scale_bounds inside).2.1 (Deformation.scale_bounds inside).2.2 actual.data.bound)
    (actual.unit time inside reading) (actual.unit_signed time inside reading)

/-- Build the original cubic lift on the same supplied cached radial-query owner, acquiring its certificate once. -/
def lift (actual : Trace site parameter original) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
    (reading : FixedRootBoxPath.Preparation.Reading actual.data.path time) :
    Lift (pointAt site parameter original time inside) (actual.unit time inside reading) :=
  Lift.ofUnit (pointAt site parameter original time inside) (actual.unit time inside reading)

/-- The actual radial-query cubic channel agrees internally with the independent original signed radial lift. -/
def lift_agrees (actual : Trace site parameter original) (time : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside time) (reading : FixedRootBoxPath.Preparation.Reading actual.data.path time) :
    NamedEquivalent (actual.lift time inside reading).value.name
      (Radial.lift site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1
        (Deformation.scale_bounds inside).2.1 (Deformation.scale_bounds inside).2.2 actual.data.bound).value.name :=
  Lift.value_agrees (actual.lift time inside reading)
    (Radial.lift site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1
      (Deformation.scale_bounds inside).2.1 (Deformation.scale_bounds inside).2.2 actual.data.bound)
    (NamedEquivalent.transport (actual.lift time inside reading).unitRoot_name.symm
      (Radial.lift site parameter (Deformation.scale time) original (Deformation.scale_bounds inside).1
        (Deformation.scale_bounds inside).2.1
        (Deformation.scale_bounds inside).2.2 actual.data.bound).unitRoot_name.symm
      (actual.unit_agrees time inside reading))

end Trace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Deformation.Transport

module

public import Purelib.RootIsolation.Progressive.Power.Unit.Owner
public import Purelib.RootIsolation.Power.Unit.Source.Preparation
public import Purelib.RootIsolation.Owner.Local.Preparation
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Clearance
import Purelib.RootIsolation.Power.Unit.Radius
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Robust unit-power owners consuming their exact saved source state -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Unit.Owner.Preparation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial
open Purelib.RootIsolation

section

-- Keep dependent constructor checking at the retained canonical producer names.
attribute [local irreducible] unitRobustOwner Power.Unit.Source.unitRobustSourceState

set_option genInjectivity false in
/-- An original robust local owner retaining its actual prepared source state.

The parameter, degree and finite original occurrence index remain fixed. The
source equality identifies the original refinement request, and the complete
local-owner equality preserves its box, clearance and winding certificate. -/
structure Prepared {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value) where
  /-- The actual original refined source, retained for reuse. -/
  source : Power.Unit.Source.Preparation.Prepared nonzero unit degree degreeTwo index
  /-- The complete original local owner computed from that saved source. -/
  owner : Owner.Local.Preparation.Prepared (unitRobustOwner nonzero unit degree degreeTwo index)

constructive_injectivity Prepared

end

/-- Compute the original robust owner from its exact saved source state.

The Newton anchor uses the retained source box. The radius and clearance scale
are the original coefficient computations. Neither the canonical source
refinement nor the canonical local-owner producer is needed at runtime. -/
@[expose] def fromSource {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (source : Power.Unit.Source.Preparation.Prepared nonzero unit degree degreeTwo index) :
    Prepared nonzero unit degree degreeTwo index :=
  let center := Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter
    (Power.Gaussian.rootPolynomial parameter degree) source.val.box
  let box := Geometry.Rational.Box.Square.Centered.Affine.centeredSquare center
    (Power.Unit.Radius.unitRobustRadius unit degree degreeTwo)
    (Power.Unit.Radius.unitRobustRadius_pos unit degree degreeTwo).le
  let bound := Power.Unit.Clearance.unitRobustClearanceScale unit degree degreeTwo
  have boxEq : box = (unitRobustOwner nonzero unit degree degreeTwo index).box := by
    change box = Power.Unit.Box.unitRobustBox nonzero unit degree degreeTwo index
    rewrite [Power.Unit.Box.unitRobustBox_eq_centeredNewtonSquare]
    dsimp only [box, center]
    rewrite [source.property]
    rfl
  have boundEq : bound = (unitRobustOwner nonzero unit degree degreeTwo index).clearance.bound :=
    (Power.Unit.Clearance.unitRobustBoundaryClearance_bound_eq_scale nonzero unit degree degreeTwo index).symm
  ⟨source, Owner.Local.Preparation.fromReadback _ box bound boxEq boundEq⟩

/-- The prepared robust owner retains the exact supplied source object. -/
theorem fromSource_source {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (source : Power.Unit.Source.Preparation.Prepared nonzero unit degree degreeTwo index) :
    (fromSource nonzero unit degree degreeTwo index source).source = source := rfl

end Purelib.RootIsolation.Progressive.Power.Unit.Owner.Preparation

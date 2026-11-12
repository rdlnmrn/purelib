module

public import Purelib.Curves.Legendre.Paths.Preparation
public import Purelib.Data.Fin.Cases
public import Purelib.Curves.Legendre.Polynomial.Clearance
public import Purelib.Data.Vector.Dependent
public import Purelib.RootIsolation.Owner.Bridge.Rouche
public import Purelib.RootIsolation.Owner.Local.Transport
public import Purelib.Polynomial.Winding.Affine.HalfPlane
public import Purelib.Polynomial.Winding.Box.Affine
public import Purelib.Curves.Legendre.Rouche
import Purelib.Curves.Legendre.Polynomial.Winding
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Geometry.Rational.Box.Outside

/-!
# Original owners and bridges of separated Legendre branch boxes

A retained proper branch box determines one winding-one owner. Each affine
factor shares its boundary clearance and winding certificate on that same
box. The materialized factors supply both the original polynomial owner and
its sharp Rouché bridge without recomputing their clearances.
-/

public section

namespace Purelib.Curves.Legendre.Paths

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Geometry.Rational
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Boundary clearance and exact winding for one original branch factor on a labelled branch box.

The factor at the box's own label has winding four; each other factor has
winding zero. This certified view retains the original boundary-clearance
owner and the same polynomial, box and logical branch labels. -/
abbrev BranchFactorCertificate (lambda : Gaussian) (box : Box) (label rootLabel : Fin 3) :=
  {_clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
    (Linear.Translated.translatedCoordinate (branchPoint lambda rootLabel)) box //
    Winding.Box.Basic.quadrupledBoxWinding
      (Linear.Translated.translatedCoordinate (branchPoint lambda rootLabel)) box =
        if rootLabel = label then 4 else 0}

/-- Construct an original factor certificate on a retained branch rectangle.

The labelled root lies strictly inside the same original box. Its four
side gaps compute the boundary clearance and winding four. Each outside
factor consumes its retained original side for clearance and winding zero,
so transport can preserve that same selection. -/
@[expose] def branchFactorCertificate (lambda : Gaussian) (box : Box) (label : Fin 3)
    (inside : box.StrictContains (branchPoint lambda label))
    (outsideSides : ∀ rootLabel : Fin 3, rootLabel ≠ label → Box.OutsideSide box (branchPoint lambda rootLabel))
    (rootLabel : Fin 3) : BranchFactorCertificate lambda box label rootLabel := by
  by_cases same : rootLabel = label
  · subst rootLabel
    let clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
        (Linear.Translated.translatedCoordinate (branchPoint lambda label)) box :=
      Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearanceBox _
        inside.1 inside.2.1 inside.2.2.1 inside.2.2.2
    refine ⟨clearance, ?_⟩
    rewrite [if_pos rfl]
    exact Winding.Box.Affine.quadrupledBoxWinding_translatedCoordinate _
      inside.1 inside.2.1 inside.2.2.1 inside.2.2.2
  · let side := outsideSides rootLabel same
    let clearance := Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside
      (branchPoint lambda rootLabel) side
    refine ⟨clearance, ?_⟩
    rewrite [if_neg same]
    exact Winding.Affine.HalfPlane.factor_winding_zero_of_outside _
      ⟨inside.1.trans inside.2.1, inside.2.2.1.trans inside.2.2.2⟩ clearance side

/-- A materialized vector of the original three factor certificates on one labelled branch box.

The dependent entries retain the original logical root labels and their
same polynomial and box indices. Reading an entry uses stored data. -/
abbrev BranchFactors (lambda : Gaussian) (box : Box) (label : Fin 3) :=
  Vector.DependentVector (fun rootLabel => BranchFactorCertificate lambda box label rootLabel)

/-- Materialize all three original factor certificates on one separated branch rectangle.

The existing dependent vector evaluates each finite entry once, consuming
the retained original outside sides. Its exact stored certificates can be
consumed by both owner and bridge construction. -/
@[expose] def branchFactors (lambda : Gaussian) (box : Box) (label : Fin 3)
    (inside : box.StrictContains (branchPoint lambda label))
    (outsideSides : ∀ rootLabel : Fin 3, rootLabel ≠ label → Box.OutsideSide box (branchPoint lambda rootLabel)) :
    BranchFactors lambda box label :=
  Vector.DependentVector.ofFn (branchFactorCertificate lambda box label inside outsideSides)

/-- Reading a materialized factor returns the exact original certificate at the same logical root label. -/
theorem branchFactors_get (lambda : Gaussian) (box : Box) (label : Fin 3)
    (inside : box.StrictContains (branchPoint lambda label))
    (outsideSides : ∀ rootLabel : Fin 3, rootLabel ≠ label → Box.OutsideSide box (branchPoint lambda rootLabel))
    (rootLabel : Fin 3) :
    (branchFactors lambda box label inside outsideSides).get rootLabel =
      branchFactorCertificate lambda box label inside outsideSides rootLabel := by
  unfold branchFactors
  exact Vector.DependentVector.ofFn_get _ _

/-- The interior factor retains the minimum of its four original squared side gaps. -/
theorem branchFactorCertificate_bound_self (lambda : Gaussian) (box : Box) (label : Fin 3)
    (inside : box.StrictContains (branchPoint lambda label))
    (outsideSides : ∀ rootLabel : Fin 3, rootLabel ≠ label → Box.OutsideSide box (branchPoint lambda rootLabel)) :
    (branchFactorCertificate lambda box label inside outsideSides label).val.bound =
      min (((branchPoint lambda label).re - box.xLower) ^ 2)
        (min ((box.xUpper - (branchPoint lambda label).re) ^ 2)
          (min (((branchPoint lambda label).im - box.yLower) ^ 2)
            ((box.yUpper - (branchPoint lambda label).im) ^ 2))) := by
  unfold branchFactorCertificate
  rewrite [dif_pos rfl]
  rfl

/-- An exterior factor retains exactly its selected original outside side's squared margin. -/
theorem branchFactorCertificate_bound_of_ne (lambda : Gaussian) (box : Box) (label : Fin 3)
    (inside : box.StrictContains (branchPoint lambda label))
    (outsideSides : ∀ rootLabel : Fin 3, rootLabel ≠ label → Box.OutsideSide box (branchPoint lambda rootLabel))
    (rootLabel : Fin 3) (different : rootLabel ≠ label) :
    (branchFactorCertificate lambda box label inside outsideSides rootLabel).val.bound =
      (outsideSides rootLabel different).margin := by
  unfold branchFactorCertificate
  rewrite [dif_neg different]
  exact Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside_bound _ _

/-- Construct the original Legendre polynomial owner from the same retained factor vector.

The three stored clearances multiply on the original proper box, and their
retained winding laws sum to four. Exact polynomial transport preserves
the resulting original box and its product bound. -/
@[expose] def branchOwner (lambda : Gaussian) (box : Box) (label : Fin 3) (proper : box.Proper)
    (factors : BranchFactors lambda box label) :
    Owner.Local.Basic.LocalOwner (polynomial lambda) :=
  let zero := factors.get 0
  let moving := factors.get 1
  let one := factors.get 2
  let factorOwner : Owner.Local.Basic.LocalOwner (Polynomial.factorsAt lambda) :=
    { box := box
      proper := proper
      clearance := Polynomial.Clearance.factorsClearance zero.val moving.val one.val
      rawWindingFour := by
        apply Polynomial.Winding.factors_winding_of_sum proper zero.val moving.val one.val
        change Winding.Box.Basic.quadrupledBoxWinding
              (Linear.Translated.translatedCoordinate (branchPoint lambda 0)) box +
            Winding.Box.Basic.quadrupledBoxWinding
              (Linear.Translated.translatedCoordinate (branchPoint lambda 1)) box +
            Winding.Box.Basic.quadrupledBoxWinding
              (Linear.Translated.translatedCoordinate (branchPoint lambda 2)) box = 4
        rewrite [zero.property, moving.property, one.property]
        rcases Purelib.Data.Fin.Cases.three label with atZero | atOne | atTwo <;> subst label <;> decide }
  Owner.Local.Transport.castOwner (Polynomial.polynomial_eq_factorsAt lambda).symm factorOwner

/-- Constructing a branch owner retains exactly the original box of its cached factors. -/
theorem branchOwner_box (lambda : Gaussian) (box : Box) (label : Fin 3) (proper : box.Proper)
    (factors : BranchFactors lambda box label) :
    (branchOwner lambda box label proper factors).box = box := by
  unfold branchOwner
  exact Owner.Local.Transport.castOwner_box _ _

/-- The original branch owner's bound is the product of those same three stored factor bounds. -/
theorem branchOwner_clearance_bound (lambda : Gaussian) (box : Box) (label : Fin 3) (proper : box.Proper)
    (factors : BranchFactors lambda box label) :
    (branchOwner lambda box label proper factors).clearance.bound =
      (factors.get 0).val.bound * (factors.get 1).val.bound * (factors.get 2).val.bound := by
  unfold branchOwner
  rewrite [Owner.Local.Transport.castOwner_clearance_bound]
  rfl

/-- Construct an original owner bridge for a sufficiently small displacement of the moving Legendre root.

The source owner and sharp factor-move dominance consume the same stored
factor vector. The retained moving-factor bound pays the actual squared
parameter displacement; finite Rouché transfer constructs the target
clearance and winding on that same box. -/
@[expose] def branchBridge (source target : Gaussian) (box : Box) (label : Fin 3) (proper : box.Proper)
    (factors : BranchFactors source box label)
    (displacementSmall : Norm.Basic.normSq (source - target) < (factors.get 1).val.bound) :
    Owner.Bridge.Basic.OwnerBridge (polynomial source) (polynomial target) :=
  let owner := branchOwner source box label proper factors
  let dominance := Rouche.factorMoveDominanceAt source target
    (factors.get 0).val (factors.get 1).val (factors.get 2).val displacementSmall
  let comparison : Winding.Box.Rouche.Connection.OrientedRouche (polynomial source) (polynomial target) owner.box :=
    { perturbation := Polynomial.perturbationAt source target
      target_eq_add := Polynomial.target_eq_source_add_perturbationAt source target
      dominance := by
        change Clearance.Box.Dominance.Basic.BoundaryNormDominance
          (polynomial source) (Polynomial.perturbationAt source target)
          (branchOwner source box label proper factors).box
        rewrite [branchOwner_box]
        exact dominance }
  Owner.Bridge.Basic.OwnerBridge.ofForward owner comparison

/-- The original Rouché bridge retains the exact box of the shared factor vector. -/
theorem branchBridge_box (source target : Gaussian) (box : Box) (label : Fin 3) (proper : box.Proper)
    (factors : BranchFactors source box label)
    (displacementSmall : Norm.Basic.normSq (source - target) < (factors.get 1).val.bound) :
    (branchBridge source target box label proper factors displacementSmall).box = box := by
  unfold branchBridge
  rewrite [Owner.Bridge.Basic.OwnerBridge.ofForward_box]
  exact branchOwner_box _ _ _ _ _

/-- The bridge's source clearance is the product of the original three cached factor bounds. -/
theorem branchBridge_leftClearance_bound (source target : Gaussian) (box : Box) (label : Fin 3)
    (proper : box.Proper) (factors : BranchFactors source box label)
    (displacementSmall : Norm.Basic.normSq (source - target) < (factors.get 1).val.bound) :
    (branchBridge source target box label proper factors displacementSmall).leftClearance.bound =
      (factors.get 0).val.bound * (factors.get 1).val.bound * (factors.get 2).val.bound := by
  unfold branchBridge
  rewrite [Owner.Bridge.Basic.OwnerBridge.ofForward_leftClearance_bound]
  exact branchOwner_clearance_bound _ _ _ _ _

end Purelib.Curves.Legendre.Paths

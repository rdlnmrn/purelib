module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Independent signed cubic lifts of the actual annular chart twist

Each execution retains its actual target Point and whole annularTwist
factory before acquiring the original signed patch Owner and cubic Lift.
The second execution consumes the first retained Point. These are chart
channels, not a complement return or a homology-action certificate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

variable {site : Fin 2} {parameter : Canonical} (original : Point site parameter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (inside : Contains site parameter original.plus)

/-- One actual chart-twist image retains the whole original Point factory. -/
@[expose] def Image : Type := { value : Point site parameter // value = annularTwist original }

include inside in
/-- The retained image lies in the SAME original annulus by its actual twist factory. -/
theorem Image.contains (image : Image original) : Contains site parameter image.val.plus :=
  Eq.mpr (congrArg (fun value : Point site parameter => Contains site parameter value.plus) image.property)
    (annularTwist_contains original inside)

include regular bound inside in
/-- The actual retained image admits its recovered cubic base to the original signed patch. -/
theorem Image.base_inside (image : Image original) : (spatialBox site).Contains image.val.base := by
  have imageInside := Image.contains original inside image
  have second : image.val.minus = partner site parameter image.val.plus :=
    image.val.minus_eq_div (image.val.plus_ne_zero regular)
  exact image.val.base_inside
    (Waist.parameter_inside site parameter (bound.trans (by decide +kernel)))
    (coordinate_inside imageInside.2)
    (coordinate_inside ((congrArg Norm.Basic.normSq second).trans_le (partner_contains regular imageInside).2))

/-- One independent cubic chart lift retains its actual image and original signed cofactor Owner. -/
@[expose] def LiftedImage : Type 1 :=
  (image : Image original) ×
    Lift image.val (UnitRoot.owner site image.val.base (Image.base_inside original regular bound inside image))

/-- Execute the original chart twist once and build the cubic Lift on that SAME bound image. -/
def lift : LiftedImage original regular bound inside :=
  let image : Image original := ⟨annularTwist original, rfl⟩
  let actual := Lift.build image.val (Image.base_inside original regular bound inside image)
  ⟨image, actual⟩

variable (initialInside : (spatialBox site).Contains original.base)
    (initial : Lift original (UnitRoot.owner site original.base initialInside))

/-- Two independent chart executions retain the GIVEN initial Lift and both whole execution factories. -/
@[expose] def Twice : Type 1 :=
  (_keptInitial : { value : Lift original (UnitRoot.owner site original.base initialInside) // value = initial }) ×
  (first : { value : LiftedImage original regular bound inside // value = lift original regular bound inside }) ×
  { second : LiftedImage first.val.1.val regular bound (Image.contains original inside first.val.1) //
    second = lift first.val.1.val regular bound (Image.contains original inside first.val.1) }

/-- Apply the actual independent chart lift twice, passing the first stored Point to the second execution. -/
def twice : Twice original regular bound inside initialInside initial :=
  let first := lift original regular bound inside
  let second := lift first.1.val regular bound (Image.contains original inside first.1)
  ⟨⟨initial, rfl⟩, ⟨first, rfl⟩, ⟨second, rfl⟩⟩

/-- The first actual chart image and full cubic Lift in the retained pair. -/
@[expose] def Twice.first (kept : Twice original regular bound inside initialInside initial) :
    LiftedImage original regular bound inside := kept.2.1.val

/-- The second actual chart image and full cubic Lift on the SAME retained first Point. -/
@[expose] def Twice.last (kept : Twice original regular bound inside initialInside initial) :
    LiftedImage (Twice.first original regular bound inside initialInside initial kept).1.val regular bound
      (Image.contains original inside (Twice.first original regular bound inside initialInside initial kept).1) :=
  kept.2.2.val

/-- The final stored Point is the actual twofold original chart twist, preserving its complete conic equation. -/
theorem Twice.target_eq (kept : Twice original regular bound inside initialInside initial) :
    (Twice.last original regular bound inside initialInside initial kept).1.val =
      annularTwist (annularTwist original) :=
  (Twice.last original regular bound inside initialInside initial kept).1.property.trans
    (congrArg annularTwist (Twice.first original regular bound inside initialInside initial kept).1.property)

/-- The second stored Point has its internally derived original signed-patch admission. -/
theorem Twice.last_inside (kept : Twice original regular bound inside initialInside initial) :
    (spatialBox site).Contains (Twice.last original regular bound inside initialInside initial kept).1.val.base :=
  Image.base_inside (Twice.first original regular bound inside initialInside initial kept).1.val regular bound
    (Image.contains original inside (Twice.first original regular bound inside initialInside initial kept).1)
    (Twice.last original regular bound inside initialInside initial kept).1

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist

end

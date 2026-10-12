module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.Operations
public import Purelib.Measure.Weighted.Transform
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite restriction and pushforward

Restriction and pushforward are direct transformations of displayed weighted
lists.  Their measure identities are finite recursive calculations over
executable Boolean events.
-/

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- Scale every retained content weight by the supplied nonnegative rational factor. -/
def scale {α : Type} (content : Content α)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) : Content α :=
  ⟨scaleAtoms factor nonnegative content.atoms⟩

/-- Scaling content scales its exact total weight by the same factor. -/
theorem scale_total {α : Type} (content : Content α)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) :
    (content.scale factor nonnegative).total = factor * content.total :=
  totalWeight_scaleAtoms factor nonnegative content.atoms

/-- Scaling content scales every event measurement by the same factor. -/
theorem scale_measure {α : Type} (content : Content α)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (event : α → Bool) :
    (content.scale factor nonnegative).measure event =
      factor * content.measure event :=
  eventWeight_scaleAtoms factor nonnegative content.atoms event

end

/-- Concatenate the two exact content occurrence lists in their supplied order. -/
def append {α : Type} (left right : Content α) : Content α :=
  ⟨left.atoms ++ right.atoms⟩

/-- The total of appended contents is the sum of their exact totals. -/
theorem append_total {α : Type} (left right : Content α) :
    (left.append right).total = left.total + right.total :=
  totalWeight_append left.atoms right.atoms

/-- The measurement of an event in appended contents is the sum of its two original measurements. -/
theorem append_measure {α : Type} (left right : Content α)
    (event : α → Bool) :
    (left.append right).measure event =
      left.measure event + right.measure event :=
  eventWeight_append left.atoms right.atoms event

/-- Retain exactly the original content occurrences selected by the supplied Boolean event. -/
def restrict {α : Type} (content : Content α) (event : α → Bool) :
    Content α :=
  ⟨restrictAtoms content.atoms event⟩

/-- The restricted content total equals the original measurement of its condition. -/
theorem restrict_total {α : Type} (content : Content α)
    (event : α → Bool) :
    (content.restrict event).total = content.measure event :=
  totalWeight_restrictAtoms content.atoms event

/-- Measurement after restriction equals original measurement of the event intersected with the condition. -/
theorem restrict_measure {α : Type} (content : Content α)
    (condition event : α → Bool) :
    (content.restrict condition).measure event =
      content.measure (intersectionEvent event condition) :=
  eventWeight_restrictAtoms content.atoms condition event

/-- Map every retained content payload through the supplied function while keeping its exact occurrence weight. -/
def map {α β : Type} (content : Content α) (function : α → β) :
    Content β :=
  ⟨mapAtoms function content.atoms⟩

/-- Mapping content payloads preserves the exact total weight. -/
theorem map_total {α β : Type} (content : Content α)
    (function : α → β) :
    (content.map function).total = content.total :=
  totalWeight_mapAtoms function content.atoms

/-- Measurement on mapped content equals original measurement of the pulled-back event. -/
theorem map_measure {α β : Type} (content : Content α)
    (function : α → β) (event : β → Bool) :
    (content.map function).measure event =
      content.measure (fun item => event (function item)) :=
  eventWeight_mapAtoms function content.atoms event

/-- Form the exact left-major product occurrence list of the two contents with product weights. -/
def product {α β : Type} (left : Content α)
    (right : Content β) : Content (α × β) :=
  ⟨productAtoms left.atoms right.atoms⟩

/-- The total of the exact product content is the product of the two original totals. -/
theorem product_total {α β : Type} (left : Content α)
    (right : Content β) :
    (left.product right).total = left.total * right.total :=
  totalWeight_productAtoms left.atoms right.atoms

/-- A rectangular event has product-content measurement equal to the product of its two marginal measurements. -/
theorem product_measure_rectangle {α β : Type}
    (left : Content α) (right : Content β)
    (leftEvent : α → Bool) (rightEvent : β → Bool) :
    (left.product right).measure
        (fun pair => leftEvent pair.1 && rightEvent pair.2) =
      left.measure leftEvent * right.measure rightEvent :=
  eventWeight_productAtoms_rectangle left.atoms right.atoms
    leftEvent rightEvent

end Content

end Purelib.Measure

end

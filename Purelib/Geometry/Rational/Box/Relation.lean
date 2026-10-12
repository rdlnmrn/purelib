module
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Init.Prelude

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
-/

namespace Purelib.Geometry.Rational.Box.Relation

/-- Lift geometric separation proofs into the data universe expected by a decidable finite pair classification. -/
def BoxSeparated (left right : Rational.Box) : Type :=
  PLift (left.Separated right)

/-- Later owner boxes continue earlier owners exactly when they refine them. -/
def BoxContinues (old new : Rational.Box) : Prop :=
  new.Refines old

/-- A box continues itself by reflexive coordinate refinement. -/
theorem BoxContinues.refl (box : Rational.Box) :
  BoxContinues box box :=
  Rational.Box.refines_refl box

/-- Compose continuation certificates by reversing the order of the retained refinement chain. -/
theorem BoxContinues.trans {first second third :
  Rational.Box}
    (firstSecond : BoxContinues first second)
    (secondThird : BoxContinues second third) :
    BoxContinues first third :=
  Refines.trans secondThird firstSecond
end Purelib.Geometry.Rational.Box.Relation

end

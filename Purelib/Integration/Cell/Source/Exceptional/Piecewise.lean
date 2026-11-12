module
public import Purelib.Approximation.Rational.Exceptional.Modulus
public import Purelib.Integration.Partition.Unit.Ownership
import Purelib.Data.List.GetD
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite subdivision with piece-specific variation

The original normalized subdivision retains each regular piece and its own
effective variation radius. A finite minimum supplies one exceptional-source
modulus, with every cut and both endpoints treated as exceptional points.
-/

public section

namespace Purelib.Integration.SourceFrontier.Exceptional.Piecewise

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- A bounded rational source with effective variation on each original subdivision piece.

Each piece uses its own computed positive radius and its own variation law.
The retained partition is the original normalized cut chain; no requested
integration frontier or final error estimate is assumed. -/
structure Modulus (source : Fraction.Rational → Fraction.Rational) where
  /-- The original finite normalized subdivision. -/ partition : Unit.Normalized
  /-- The nonnegative global source magnitude. -/ magnitude : Fraction.Rational
  /-- The global magnitude includes the zero case. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- Every original rational unit reading is enclosed by the magnitude. -/ bounded :
    ∀ point, 0 ≤ point → point ≤ 1 → -magnitude ≤ source point ∧ source point ≤ magnitude
  /-- Compute the requested radius for each original subdivision interval. -/ radius :
    Interval → Fraction.Rational → Fraction.Rational
  /-- Every retained piece supplies a positive radius for a positive variation request. -/ radius_pos :
    ∀ interval ∈ partition.intervals, ∀ variation, 0 < variation → 0 < radius interval variation
  /-- The piece's radius controls source variation between ordered points in that original piece. -/ variation :
    ∀ interval ∈ partition.intervals, ∀ variation, 0 < variation → ∀ first second,
      interval.start ≤ first → first ≤ second → second ≤ interval.finish →
      (∀ point ∈ 0 :: 1 :: partition.cuts, ¬ (first ≤ point ∧ point ≤ second)) →
      second - first < radius interval variation →
        source first - variation ≤ source second ∧ source second ≤ source first + variation

constructive_injectivity Modulus

/-- Compute the finite minimum of a piece-radius list, capped at one. -/
@[expose] def minimumRadius (radius : Interval → Fraction.Rational) : List Interval → Fraction.Rational
  | [] => 1
  | interval :: remaining => min (radius interval) (minimumRadius radius remaining)

/-- A finite list of positive piece radii has a positive computed minimum. -/
theorem minimumRadius_pos (radius : Interval → Fraction.Rational) :
    ∀ intervals, (∀ interval ∈ intervals, 0 < radius interval) → 0 < minimumRadius radius intervals
  | [], _ => by
      change (0 : Fraction.Rational) < 1
      decide
  | interval :: remaining, positive => by
      apply Fraction.Order.Basic.lt_min
      · exact positive interval (List.Mem.head remaining)
      · apply minimumRadius_pos radius remaining
        intro entry member
        exact positive entry (List.Mem.tail interval member)

/-- The finite minimum is no greater than any retained piece's radius. -/
theorem minimumRadius_le (radius : Interval → Fraction.Rational) :
    ∀ intervals, ∀ interval ∈ intervals, minimumRadius radius intervals ≤ radius interval
  | [], _, member => by nomatch member
  | first :: remaining, interval, member => by
      cases member with
      | head => exact Fraction.Order.Basic.min_le_left _ _
      | tail _ member =>
          exact (Fraction.Order.Basic.min_le_right _ _).trans (minimumRadius_le radius remaining interval member)

/-- The original subdivision produces a finite-exception modulus using its exact cuts and piece radii.

The two endpoint exceptions permit arbitrary endpoint readings. Avoiding the
retained cuts makes both queried points belong to the same original piece;
the finite minimum selects a radius valid for that exact piece. -/
@[expose] def Modulus.toExceptional {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) : Exceptional.Modulus source where
  points := 0 :: 1 :: modulus.partition.cuts
  magnitude := modulus.magnitude
  magnitude_nonnegative := modulus.magnitude_nonnegative
  bounded := modulus.bounded
  radius := fun variation =>
    minimumRadius (fun interval => modulus.radius interval variation) modulus.partition.intervals
  radius_pos := by
    intro variation positive
    apply minimumRadius_pos
    intro interval member
    exact modulus.radius_pos interval member variation positive
  variation := by
    intro variation positive first second lower ordered upper avoids small
    have firstUpper : first ≤ 1 := ordered.trans upper
    have firstBelow : first < 1 := by
      apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
      intro oneLeFirst
      exact avoids 1 (List.Mem.tail 0 (List.Mem.head modulus.partition.cuts))
        ⟨firstUpper, oneLeFirst.trans ordered⟩
    let owner := modulus.partition.pointOwner first lower firstBelow
    have member := Purelib.Data.List.mem_of_getElem? modulus.partition.intervals owner.index owner.parent owner.at_index
    have secondInside : second ≤ owner.parent.finish := by
      apply Fraction.Order.Arithmetic.le_of_not_gt_direct
      intro beyond
      rcases modulus.partition.finish_is_cut member with last | cut
      · exact (not_lt_of_ge upper) (last ▸ beyond)
      · exact avoids owner.parent.finish (List.Mem.tail 0 (List.Mem.tail 1 cut))
          ⟨owner.point_lt_finish.le, beyond.le⟩
    have radiusBound := minimumRadius_le (fun interval => modulus.radius interval variation)
      modulus.partition.intervals owner.parent member
    exact modulus.variation owner.parent member variation positive first second owner.start_le ordered secondInside
      avoids (small.trans_le radiusBound)

end Purelib.Integration.SourceFrontier.Exceptional.Piecewise

end

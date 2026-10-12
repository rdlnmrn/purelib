module
import Purelib.Data.List.Filter
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Sector.Spread.Cleared
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Sector.Spread

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Resection.FiniteRegion

/-- A point matches all three measured resection spreads directly. This is the coordinate alternative requested by
Exercise 25.2 and contains no Euler or Four-point polynomial. -/
def MatchesResectionReadings
    (a₁ a₂ a₃ candidate : Geometry.Plane.Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) : Prop :=
  Quadrance.quadrance candidate a₁ ≠ 0 ∧
    Quadrance.quadrance candidate a₂ ≠ 0 ∧
    Quadrance.quadrance candidate a₃ ≠ 0 ∧
    Cleared.MatchesSectorSpread candidate a₂ a₃
      r₁Numerator r₁Denominator ∧
    Cleared.MatchesSectorSpread candidate a₁ a₃
      r₂Numerator r₂Denominator ∧
    Cleared.MatchesSectorSpread candidate a₁ a₂
      r₃Numerator r₃Denominator

/-- Decide the three nonzero quadrances and three cleared spread equations for a candidate point. -/
instance matchesResectionReadingsDecidable [DecidableEq K]
    (a₁ a₂ a₃ candidate : Geometry.Plane.Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) :
    Decidable (MatchesResectionReadings a₁ a₂ a₃ candidate
      r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator) := by
  unfold MatchesResectionReadings
    Purelib.Geometry.Plane.Sector.Spread.Cleared.MatchesSectorSpread
  infer_instance

/-- An executable alternative resection solver on any explicitly supplied finite search region. -/
def resectionSolutions [DecidableEq K]
    (candidates : List (Geometry.Plane.Point K))
    (a₁ a₂ a₃ : Geometry.Plane.Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) : List (Geometry.Plane.Point K) :=
  candidates.filter fun candidate => decide
    (Geometry.Resection.FiniteRegion.MatchesResectionReadings a₁ a₂ a₃ candidate
      r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator)

open Purelib.Data.List in
/-- Exercise 25.2: the direct finite solver returns all and only candidates whose three cleared coordinate-spread
equations match the readings. -/
theorem exercise_25_2 [DecidableEq K]
    (candidates : List (Geometry.Plane.Point K))
    (a₁ a₂ a₃ candidate : Geometry.Plane.Point K)
    (r₁Numerator r₁Denominator
      r₂Numerator r₂Denominator
      r₃Numerator r₃Denominator : K) :
    candidate ∈ resectionSolutions candidates a₁ a₂ a₃
        r₁Numerator r₁Denominator
        r₂Numerator r₂Denominator
        r₃Numerator r₃Denominator ↔
      candidate ∈ candidates ∧
        Geometry.Resection.FiniteRegion.MatchesResectionReadings a₁ a₂ a₃ candidate
          r₁Numerator r₁Denominator
          r₂Numerator r₂Denominator
          r₃Numerator r₃Denominator := by
  rewrite [resectionSolutions]
  constructor
  · intro member
    rcases Filter.mem_filter.mp member with ⟨original, selected⟩
    exact ⟨original, of_decide_eq_true selected⟩
  · intro selected
    exact Filter.mem_filter.mpr ⟨selected.1, decide_eq_true selected.2⟩

end Purelib.Geometry.Resection.FiniteRegion

end
end

end

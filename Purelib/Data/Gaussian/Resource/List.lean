module
import Purelib.Data.Nat.Order

public import Purelib.Data.Gaussian.Basic
-- Public normalized magnitude certificates retain the original model owner.
public import Purelib.Data.Gaussian.Resource.Model

import Mathlib.Order.Basic

section
section
@[expose] public section

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace Purelib.Polynomial.ClearingCalculationSize

open Purelib.Data
open Purelib.Data.Gaussian

end Purelib.Polynomial.ClearingCalculationSize

end

end

section
section
@[expose] public section

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace Purelib.Polynomial.ClearingCalculationSize

open Purelib.Data
open Purelib.Data.Gaussian

end Purelib.Polynomial.ClearingCalculationSize

end

end

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.NormalizedEliminant

open Purelib.Data Purelib.Data.Gaussian

end Purelib.Polynomial.NormalizedEliminant

end

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.NormalizedEliminant

open Purelib.Data Purelib.Data.Gaussian

end Purelib.Polynomial.NormalizedEliminant

end

namespace Purelib.Data.Gaussian.Resource.List

open Purelib.Data
open Purelib.Data.Gaussian

/-- Iterating displayed maximum updates retains the original initial bound.

Every update chooses the maximum of the previous bound and one actual list
entry's weight, so the original bound remains below the final fold reading. -/
private theorem foldl_max_initial_le (weight :
  Basic.Canonical → Nat) :
    ∀ (coefficients : List Basic.Canonical) (initial : Nat),
      initial ≤ coefficients.foldl
        (fun bound coefficient => max bound (weight coefficient)) initial
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (Nat.Order.le_max_left _ _).trans
        (Purelib.Data.Gaussian.Resource.List.foldl_max_initial_le weight remaining _)

/-- Every retained member weight is bounded by the iterated maximum.

The original list fold begins with the supplied initial bound. The membership
constructor identifies the actual entry whose weight contributes to that fold. -/
public theorem member_le_foldl_max (weight :
  Basic.Canonical → Nat) :
    ∀ (coefficients : List Basic.Canonical) (initial : Nat)
      (candidate : Basic.Canonical), candidate ∈ coefficients →
      weight candidate ≤ coefficients.foldl
        (fun bound coefficient => max bound (weight coefficient)) initial
  | [], _, _, member => by cases member
  | coefficient :: remaining, initial, candidate, member => by
      cases member with
      | head =>
          exact (Nat.Order.le_max_right _ _).trans
            (Purelib.Data.Gaussian.Resource.List.foldl_max_initial_le weight remaining _)
      | tail _ tail =>
          exact Purelib.Data.Gaussian.Resource.List.member_le_foldl_max weight remaining
            (max initial (weight coefficient)) candidate tail

end Purelib.Data.Gaussian.Resource.List

namespace Purelib.Data.Gaussian.Resource.List

open Purelib.Data
open Purelib.Data.Gaussian

/-- The initial magnitude bound remains below the retained coefficient maximum.

Each fold step keeps the previous bound as one contribution to the maximum,
so structural recursion preserves the original initial contribution. -/
public theorem foldl_componentMagnitude_max_initial_le : ∀ (coefficients :
  List Basic.Number)
    (initial : Nat), initial ≤ coefficients.foldl
      (fun bound coefficient => max bound (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude coefficient))
      initial
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (Nat.Order.le_max_left _ _).trans (Purelib.Data.Gaussian.Resource.List.foldl_componentMagnitude_max_initial_le
        remaining _)

/-- Every actual coefficient magnitude is bounded by the retained maximum fold.

The membership constructor identifies the source coefficient contributing to
the fold. The original Gaussian model supplies that coefficient's magnitude. -/
public theorem member_componentMagnitude_le_foldl_max : ∀ (coefficients :
  List Basic.Number)
    (initial : Nat) {candidate : Basic.Number}, candidate ∈ coefficients →
    Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude candidate ≤ coefficients.foldl
      (fun bound coefficient => max bound (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude coefficient))
      initial
  | [], _, _, member => nomatch member
  | coefficient :: remaining, initial, candidate, member => by
      cases member with
      | head =>
          exact (Nat.Order.le_max_right _ _).trans
            (Purelib.Data.Gaussian.Resource.List.foldl_componentMagnitude_max_initial_le remaining _)
      | tail _ tail =>
          exact Purelib.Data.Gaussian.Resource.List.member_componentMagnitude_le_foldl_max remaining
            (max initial (Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude coefficient)) tail

end Purelib.Data.Gaussian.Resource.List

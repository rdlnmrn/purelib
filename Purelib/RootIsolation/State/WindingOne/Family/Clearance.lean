module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.List.Minimum
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

public section

/-!
# Common boundary clearance of a winding family

The retained winding-one states supply positive boundary bounds in their
original list order. Their positive minimum gives a common target, including
the empty-family value one, below each indexed state's original clearance.
-/

namespace Purelib.RootIsolation.State.WindingOne.Family.Basic.WindingFamily

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-- Read the original winding states' boundary clearance bounds in order.

Mapping the retained state list reuses each correctness-bearing clearance
certificate and preserves the original occurrence alignment. -/
@[expose] def clearanceBounds
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : List Fraction.Rational :=
  family.states.map fun state => state.clearance.bound

/-- Every boundary-clearance bound retained by the original state list is strictly positive. -/
theorem clearanceBounds_positive
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) :
    ∀ bound ∈ family.clearanceBounds, 0 < bound := by
  intro bound member
  change bound ∈ family.states.map (fun state => state.clearance.bound) at member
  have original := Data.List.Map.mem_map.mp member
  rcases original with ⟨state, _stateMember, rfl⟩
  exact state.clearance.positive

/-- Compute one positive target below every retained boundary clearance.

The positive minimum uses the original ordered bound list; an empty family
retains the value one. -/
@[expose] def clearanceTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    family.clearanceBounds

/-- The original finite winding family has a strictly positive common clearance target. -/
theorem clearanceTarget_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : 0 < family.clearanceTarget :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    family.clearanceBounds_positive

/-- The common clearance target fits the clearance of each indexed original state. -/
theorem clearanceTarget_le_stateAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.clearanceTarget ≤
      (family.stateAtBoxIndex index).clearance.bound := by
  apply
    Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
  change _ ∈ family.states.map (fun state => state.clearance.bound)
  apply Data.List.Map.mem_map.mpr
  refine ⟨family.stateAtBoxIndex index, ?_, rfl⟩
  exact List.get_mem family.states
    ⟨index.val, family.boxes_length ▸ index.isLt⟩

/-- One quarter of the common clearance target fits one quarter of every retained state's clearance. -/
theorem clearanceTarget_quarter_le_stateAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.clearanceTarget / 4 ≤
      (family.stateAtBoxIndex index).clearance.bound / 4 := open Purelib.Algebra.Field in by
  simp only [ExplicitField.div_eq_mul_inv]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (family.clearanceTarget_le_stateAt index)
    (Fraction.Order.Field.inv_pos_direct
      (show (0 : Fraction.Rational) < 4 by decide)).le
end Purelib.RootIsolation.State.WindingOne.Family.Basic.WindingFamily

end

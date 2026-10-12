module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
public import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Basic
public import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Move.Budget

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.RootIsolation

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Parameter vertices reached after each finite move, including the final
vertex but excluding the initial one. -/
@[expose] def vertices {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} →
      Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish → List Gaussian.Basic.Canonical
  | _, _, .nil _ => []
  | _, _, .cons (middle := middle) _ remaining =>
      middle.value :: remaining.vertices
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Concatenating unit-move chains concatenates their retained parameter-vertex lists. -/
theorem vertices_append
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (first : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start middle)
    (second : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo middle finish) :
    (first.append second).vertices = first.vertices ++ second.vertices := by
  induction first with
  | nil => rfl
  | cons small remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.append,
        Power.Unit.Chain.Basic.UnitChain.vertices, List.cons_append, inductionHypothesis]
      rfl
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Following the retained parameter vertices reaches the chain's exact dependent finish vertex. -/
theorem vertices_terminal
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish),
      Polygon.Chain.terminal start.value chain.vertices = finish.value
  | _, _, .nil _ => rfl
  | _, _, .cons _ remaining => Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.vertices_terminal remaining
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end

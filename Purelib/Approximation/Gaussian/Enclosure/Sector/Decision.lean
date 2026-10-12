module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic

import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

namespace Purelib.Approximation.Gaussian.Enclosure.Sector

set_option genInjectivity false in
/-- The two finite exact outcomes of the redundant loop controller.

A unary outcome retains its whole-ball certificate. A sector outcome retains
the selected original eight-sector representative and its safe-ball
certificate for the same nominal ball. -/
public inductive Decision (ball : Ball) where
  /-- A whole-ball certificate for the unary output branch. -/ | unary (certificate : Large.UnaryBall ball)
  /-- A retained sector and its whole-ball safe-sector certificate. -/ | sector (sector :
    Data.ComplexContinuedFraction.Encoding.Sector)
    (certificate : Safe.SafeBall sector ball)

constructive_injectivity Decision

namespace Decision.sector

end Decision.sector

namespace Decision

open Purelib.Data.Rat in
/-- Explicit finite cover: once the radius request is met and the rational centre has squared norm at least one, a
bounded comparison returns either a sound unary branch or one of the eight sound sector branches.

The original rational upper-norm comparison selects the same branch.
Small retained squared radius supplies either the original sector certificate
or a strictly positive unary margin through direct scalar translation. -/
@[expose] public def decide (ball : Ball) (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq
  ball.center)
    (small : ball.radiusSq < Budget.uniformRadiusSq) : Decision ball := by
  by_cases upper : Data.Gaussian.Norm.Basic.normSq ball.center ≤ 13 / 6
  · exact .sector (Data.ComplexContinuedFraction.Encoding.Sector.select ball.center)
      (Safe.safeBall_of_extendedBand ⟨normLower, upper⟩ small)
  · apply Decision.unary
    unfold Large.UnaryBall
    have scaledRadius := Budget.scaled_radius_lt_allowance small
    calc
      (16 / 15) * 2 + 16 * ball.radiusSq <
          (16 / 15) * 2 + Budget.allowance :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct scaledRadius ((16 / 15) * 2)
      _ = 13 / 6 := Budget.unaryThreshold_add_allowance
      _ < Data.Gaussian.Norm.Basic.normSq ball.center := lt_of_not_ge upper

end Decision

end Purelib.Approximation.Gaussian.Enclosure.Sector

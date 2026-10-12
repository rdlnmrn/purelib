module

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.State
public import Purelib.RootIsolation.Exact.Step
import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Tactic.Ring.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Order

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Data

/-!
# Consuming an exact finite winding count

Recursion removes one retained positive region per requested count and
keeps the final support, exact track count and zero-winding remainder.
-/

namespace Purelib.RootIsolation.Exact.Run

set_option genInjectivity false in
/-- The final state after consuming the displayed exact remaining winding count.

The result retains the original support, zero total winding in the remaining regions and the exact increase in the
number of extracted tracks. -/
public structure RunResult
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (initial : Exact.State.IsolationState p ambient) (steps : Nat) where
  /-- The actual state after the displayed number of extraction steps. -/ final : Exact.State.IsolationState p ambient
  /-- The final state retains the original support exactly. -/ support_final : final.support = initial.support
  /-- The final remaining regions have total raw winding zero. -/ totalRaw_final : Winding.Box.Region.Sum.totalRaw
    final.regions = 0
  /-- The final track count is the original count plus the displayed number of steps. -/ tracks_length_final :
    final.tracks.length = initial.tracks.length + steps

constructive_injectivity RunResult

/-- Execute the original extraction recursion for the exact remaining count.

The retained region total is four times the requested natural count. Each
successor uses the same certified positive-region step and then consumes the
remaining count on its actual next state. -/
@[expose] public def run
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) :
    (steps : Nat) → (state : Exact.State.IsolationState p ambient) →
      Winding.Box.Region.Sum.totalRaw state.regions = (4 : Int) * steps → Exact.Run.RunResult state steps
  | 0, state, total =>
      { final := state
        support_final := rfl
        totalRaw_final := by
          change Winding.Box.Region.Sum.totalRaw state.regions = 0 at total
          exact total
        tracks_length_final := (Nat.add_zero state.tracks.length).symm }
  | steps + 1, state, total => by
      have positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions := by
        rewrite [total]
        exact Int.Order.mul_pos (by decide)
          (Int.Order.natCast_pos (Nat.zero_lt_succ steps))
      have nonnegative : ∀ region ∈ state.regions,
          0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
        intro region _member
        exact Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
          degreeAtLeastTwo squarefree elimination region.refinesAmbient
            region.proper region.clearance
      let first := Exact.Step.step degreeAtLeastTwo squarefree elimination state
        nonnegative positive
      have nextTotal : Winding.Box.Region.Sum.totalRaw first.next.regions = (4 : Int) * steps := by
        rw [first.totalRaw_next, total, Nat.cast_succ]
        ring1
      let tail := Purelib.RootIsolation.Exact.Run.run degreeAtLeastTwo squarefree elimination steps first.next
        nextTotal
      exact
        { final := tail.final
          support_final := tail.support_final.trans first.support_next
          totalRaw_final := tail.totalRaw_final
          tracks_length_final := by
            rw [tail.tracks_length_final, first.tracks_length_next]
            ring1 }

end Purelib.RootIsolation.Exact.Run

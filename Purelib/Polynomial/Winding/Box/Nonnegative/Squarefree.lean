module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Nonnegativity.Sequence
import Purelib.RootIsolation.State.Negative
import Purelib.RootIsolation.Track.Packing
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic

import Purelib.Data.Int.Order

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Nonnegative winding for squarefree polynomials

Finite negative-region removal would construct more pairwise-separated
winding-one tracks than the retained mesh packing bound permits.
-/

namespace Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree

/-- The raw winding of a clear squarefree box is nonnegative.

The retained polynomial has degree at least two and its original finite axis
elimination certificate. If winding were negative, its displayed removal
sequence would exceed the computed packing bound in the same ambient box. -/
public theorem quadrupledBoxWinding_nonnegative
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient box : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (refines : box.Refines ambient) (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    0 ≤ Winding.Box.Basic.quadrupledBoxWinding p box := open Purelib in by
  by_cases nonnegative : 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p box
  · exact nonnegative
  · have negative : Winding.Box.Basic.quadrupledBoxWinding p box < 0 :=
      Data.Int.Order.lt_of_not_le nonnegative
    let initial : RootIsolation.State.Negative.NegativeState p ambient :=
      { box := box
        refinesAmbient := refines
        proper := proper
        clearance := clearance
        rawWinding_neg := negative }
    let bound := RootIsolation.Track.Packing.packingBound squarefree ambient
    let sequence := RootIsolation.Nonnegativity.Sequence.iterate degreeAtLeastTwo squarefree elimination
      (bound + 1) initial
    have packed := RootIsolation.Track.Packing.family_card_le_packingBound
      ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)
      squarefree sequence.tracks (fun i => (sequence.tracks i).initial)
      sequence.pairwise
    have impossible : Nat.succ bound ≤ bound := by
      simpa only [Nat.succ_eq_add_one] using packed
    exact (Nat.not_succ_le_self bound impossible).elim

end Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree

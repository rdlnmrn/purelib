module

import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Sum
public import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Run
import Purelib.RootIsolation.Exact.State
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Separation.Basic

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-!
# Exact isolation from a retained clear region

An initial raw winding of four times the requested count determines the
original finite extraction run and its retained final partition.
-/

namespace Purelib.RootIsolation.Exact.Build

/-- Isolate exactly the requested number of tracks from a clear initial region.

Its raw winding is four times the retained natural count. The original finite
run returns the exact support and track list; global nonnegativity certifies
zero winding of every retained remainder region. -/
@[expose] public def isolateFromRegion
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : Clearance.Box.Region.ClearRegion p ambient) (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count) :
    Exact.Basic.Output p ambient count := by
  let state := Exact.State.IsolationState.initial initial
  have total : Winding.Box.Region.Sum.totalRaw state.regions = (4 : Int) * count := by
    change Winding.Box.Basic.quadrupledBoxWinding p initial.box + 0 = (4 : Int) * count
    rw [raw, add_zero]
  let result := Exact.Run.run degreeAtLeastTwo squarefree elimination count state total
  have nonnegative : ∀ region ∈ result.final.regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
    intro region _member
    exact Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      degreeAtLeastTwo squarefree elimination region.refinesAmbient
        region.proper region.clearance
  exact
    { support := initial.box
      support_refinesAmbient := initial.refinesAmbient
      tracks := result.final.tracks
      tracks_length := by
        rewrite [result.tracks_length_final]
        change 0 + count = count
        exact Nat.zero_add count
      tracks_pairwise := result.final.tracksPairwise
      remainder := result.final.regions
      remainder_pairwise := result.final.regionsPairwise
      remainder_rawWinding_zero := by
        intro region member
        exact Winding.Box.Region.Sum.rawWinding_eq_zero_of_mem_totalRaw_eq_zero
          result.final.regions nonnegative result.totalRaw_final member
      tracks_avoid_remainder := result.final.tracksAvoidRegions
      partition_covers := by
        intro z inside
        apply result.final.covers
        rw [result.support_final]
        exact inside }

end Purelib.RootIsolation.Exact.Build

module

import Purelib.Data.Rat.Fraction
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
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count)
    (request : Option Data.Rat.Fraction.Rational := none) :
    Exact.Basic.Output p ambient count := by
  let state := Exact.State.IsolationState.initial initial
  have total : Winding.Box.Region.Sum.totalRaw state.regions = (4 : Int) * count := by
    change Winding.Box.Basic.quadrupledBoxWinding p initial.box + 0 = (4 : Int) * count
    rw [raw, add_zero]
  let result := Exact.Run.run degreeAtLeastTwo squarefree elimination count state total request
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

/-- Each retained isolated track has the complete original Newton constructor on its own checked initial state. -/
public theorem isolateFromRegion_tracks_origin
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : Clearance.Box.Region.ClearRegion p ambient) (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count)
    (request : Option Data.Rat.Fraction.Rational) :
    ∀ track ∈ (isolateFromRegion degreeAtLeastTwo squarefree elimination initial count raw request).tracks,
      Track.Newton.Build.Origin degreeAtLeastTwo squarefree elimination track := by
  let state := Exact.State.IsolationState.initial initial
  have total : Winding.Box.Region.Sum.totalRaw state.regions = (4 : Int) * count := by
    change Winding.Box.Basic.quadrupledBoxWinding p initial.box + 0 = (4 : Int) * count
    rewrite [raw, add_zero]
    rfl
  exact Exact.Run.run_tracks_origin degreeAtLeastTwo squarefree elimination count state total request
    (fun _ impossible => nomatch impossible)

/-- The actual degree-indexed isolated track consumes the same original Newton refiner at every supplied request. -/
public theorem isolateFromRegion_trackAt_refine
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : Clearance.Box.Region.ClearRegion p ambient) (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count)
    (request : Option Data.Rat.Fraction.Rational) (index : Fin count)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    ((isolateFromRegion degreeAtLeastTwo squarefree elimination initial count raw request).trackAt index).refine
      current epsilon positive =
      Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination current epsilon positive := by
  let output := isolateFromRegion degreeAtLeastTwo squarefree elimination initial count raw request
  exact Track.Newton.Build.Origin.refine
    (isolateFromRegion_tracks_origin degreeAtLeastTwo squarefree elimination initial count raw request
      (output.trackAt index) (List.get_mem output.tracks (output.trackIndex index))) current epsilon positive

/-- Every track produced from an original clear region retains the same original Newton refiner. -/
public theorem isolateFromRegion_refine
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (initial : Clearance.Box.Region.ClearRegion p ambient) (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count)
    (request : Option Data.Rat.Fraction.Rational := none) :
    ∀ track ∈ (isolateFromRegion degreeAtLeastTwo squarefree elimination initial count raw request).tracks,
      track.refine = Track.Newton.Refinement.refineState degreeAtLeastTwo squarefree elimination := by
  intro track member
  rcases isolateFromRegion_tracks_origin degreeAtLeastTwo squarefree elimination initial count raw request
    track member with ⟨initial, same⟩
  exact congrArg (fun retained => retained.refine) same

end Purelib.RootIsolation.Exact.Build

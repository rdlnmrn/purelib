module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Separation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.State.WindingOne.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Exact finite root-isolation outputs

The output retains its ordered winding-one tracks, zero-winding remainder
regions and original support box, with exact coverage and separation
certificates. Its stored track-count equality reindexes the same retained
list at each requested finite degree index.
-/

namespace Purelib.RootIsolation.Exact.Basic

set_option genInjectivity false in
/-- An exact finite isolation retaining its original tracks and zero-winding remainder partition.

The displayed support and ordered track/remainder lists retain their coverage,
separation, winding and requested-count certificates for the same polynomial
and original ambient box. -/
public structure Output
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) (count : Nat)
      where
  /-- The retained support box containing the original finite partition. -/ support : Box
  /-- The retained support box lies within the original ambient box. -/ support_refinesAmbient : support.Refines ambient
  /-- The actual finite list of isolated winding-one tracks. -/ tracks : List
    (Track.Basic.WindingOneTrack p ambient)
  /-- The retained track list has exactly the requested number of entries. -/ tracks_length : tracks.length = count
  /-- Distinct entries of the retained track list have separated initial boxes. -/ tracks_pairwise : tracks.Pairwise
    Track.Separation.Basic.trackSeparated
  /-- The retained finite list of complementary clear regions. -/ remainder : List (Clearance.Box.Region.ClearRegion p
    ambient)
  /-- Distinct retained remainder regions have disjoint interiors. -/ remainder_pairwise : remainder.Pairwise
    Clearance.Box.Region.Basic.regionInteriorSeparated
  /-- Each original remainder region has exactly zero raw winding. -/ remainder_rawWinding_zero : ∀ region ∈ remainder,
    Winding.Box.Basic.quadrupledBoxWinding p region.box = 0
  /-- Each retained track avoids the interior of every original remainder region. -/ tracks_avoid_remainder : ∀ track ∈
    tracks, ∀ region ∈ remainder,
    ∀ {small : Box}, small.StrictInterior region.box →
      track.initial.box.Separated small
  /-- Every point of the support lies in a retained track box or a retained remainder region. -/ partition_covers : ∀ {z
    : Gaussian.Basic.Canonical}, support.Contains z →
    (∃ track ∈ tracks, track.initial.box.Contains z) ∨
      ∃ region ∈ remainder, region.box.Contains z

constructive_injectivity Output

/-- Reindex the original degree index by the retained equality for the track-list length. -/
@[expose] public def Output.trackIndex
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (index : Fin count) :
    Fin output.tracks.length :=
  Fin.cast output.tracks_length.symm index

/-- Read the original retained track at its certified degree index. -/
@[expose] public def Output.trackAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (index : Fin count) :
    Track.Basic.WindingOneTrack p ambient :=
  output.tracks.get (output.trackIndex index)

/-- Reindexing a track index preserves its natural value. -/
@[simp] public theorem Output.trackIndex_val
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (index : Fin count) :
    (output.trackIndex index).val = index.val := rfl

/-- Distinct degree indices select tracks with positively separated initial boxes. -/
public theorem Output.trackAt_pairwiseSeparated
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (left right : Fin count)
    (different : left ≠ right) :
    (output.trackAt left).initial.box.Separated
      (output.trackAt right).initial.box := open Purelib in by
  have indexDifferent : output.trackIndex left ≠ output.trackIndex right :=
    fun equal => different (Fin.ext (by
      calc
        left.val = (output.trackIndex left).val :=
          (output.trackIndex_val left).symm
        _ = (output.trackIndex right).val := congrArg Fin.val equal
        _ = right.val := output.trackIndex_val right))
  by_cases ordered : (output.trackIndex left).val <
      (output.trackIndex right).val
  · exact Data.List.Pairwise.pairwise_get_of_val_lt output.tracks_pairwise _ _ ordered
  · have reversed : (output.trackIndex right).val <
        (output.trackIndex left).val := by
      have unequalValues : (output.trackIndex left).val ≠
          (output.trackIndex right).val := by
        intro equal
        exact indexDifferent (Fin.ext equal)
      exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered)
        (Ne.symm unequalValues)
    exact Box.separated_symm
      (Data.List.Pairwise.pairwise_get_of_val_lt output.tracks_pairwise _ _ reversed)
end Purelib.RootIsolation.Exact.Basic

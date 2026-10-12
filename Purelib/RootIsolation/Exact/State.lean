module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Separation.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.RootIsolation.State.WindingOne.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data
open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-!
# Retained finite isolation partitions

The original support, remaining clear regions and extracted track list
carry their separation and joint-coverage certificates through each step.
-/

namespace Purelib.RootIsolation.Exact.State

set_option genInjectivity false in
/-- Retain a finite clear-region and winding-track partition of one support.

The original polynomial and ambient box index every region and track.
Pairwise separation, avoidance and coverage certificates concern precisely
these retained lists and the displayed support box. -/
public structure IsolationState (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (ambient : Box) where
  /-- The original support box retained throughout the finite isolation process. -/ support : Box
  /-- The support box refines the polynomial's original ambient box. -/ supportRefinesAmbient : support.Refines ambient
  /-- The actual finite list of clear regions still retained in the partition. -/ regions : List
    (Clearance.Box.Region.ClearRegion p ambient)
  /-- The retained regions have pairwise disjoint interiors. -/ regionsPairwise : regions.Pairwise
    Clearance.Box.Region.Basic.regionInteriorSeparated
  /-- The retained finite list of extracted winding-one tracks. -/ tracks : List
    (Track.Basic.WindingOneTrack p ambient)
  /-- The initial boxes of distinct retained tracks are positively separated. -/ tracksPairwise : tracks.Pairwise
    Track.Separation.Basic.trackSeparated
  /-- Each retained track avoids the interior of every remaining region. -/ tracksAvoidRegions : ∀ track ∈ tracks, ∀
    region ∈ regions,
    ∀ {small : Box}, small.StrictInterior region.box →
      track.initial.box.Separated small
  /-- The retained regions and initial track boxes jointly cover the original support. -/ covers : ∀ {z :
    Gaussian.Basic.Canonical}, support.Contains z →
    (∃ track ∈ tracks, track.initial.box.Contains z) ∨
      ∃ region ∈ regions, region.box.Contains z

constructive_injectivity IsolationState

/-- Initialize a partition with its original clear region and no tracks.

The region supplies the exact support, ambient refinement and singleton
coverage. The empty track list retains the original vacuous certificates. -/
@[expose] public def IsolationState.initial
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (region : Clearance.Box.Region.ClearRegion p ambient) : Exact.State.IsolationState p ambient where
  support := region.box
  supportRefinesAmbient := region.refinesAmbient
  regions := [region]
  regionsPairwise := Data.List.Pairwise.pairwise_singleton _ _
  tracks := []
  tracksPairwise := List.Pairwise.nil
  tracksAvoidRegions := by
    intro track member
    nomatch member
  covers := by
    intro z inside
    exact Or.inr ⟨region, List.mem_cons_self, inside⟩

end Purelib.RootIsolation.Exact.State

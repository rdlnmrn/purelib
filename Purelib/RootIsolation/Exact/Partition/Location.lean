module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Search
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.State.WindingOne.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Locations in an exact isolation partition

A location retains an index into the original track or remainder list. The
finite locator scans track boxes first and then remainder regions, using the
stored covering certificate to exclude an unsuccessful search.
-/

namespace Purelib.RootIsolation.Exact.Partition.Location

set_option genInjectivity false in
/-- An actual list index identifying one cell of the retained exact isolation partition.

The index selects either an original track's initial box or an original remainder region. -/
public inductive PartitionLocation
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) : Type
  /-- An index into the original retained track list. -/ | track (index : Fin output.tracks.length)
  /-- An index into the original retained remainder-region list. -/ | remainder (index : Fin output.remainder.length)

constructive_injectivity PartitionLocation

/-- Read the original box selected by a partition location.

A track location projects its stored initial box; a remainder location projects
the stored clear-region box at the retained index. -/
@[expose] public def PartitionLocation.box
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    {output : Exact.Basic.Output p ambient count} : PartitionLocation output → Box
  | .track index => (output.tracks.get index).initial.box
  | .remainder index => (output.remainder.get index).box

/-- Search the retained track boxes, then remainder regions, for the supplied point.

Return the original list index of the first containing cell when one exists. -/
@[expose] public def findPartitionLocation?
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (point : Gaussian.Basic.Canonical) :
    Option (PartitionLocation output) :=
  match Box.Search.findContainingIndex (fun track => track.initial.box) point
      output.tracks with
  | some index => some (.track index)
  | none =>
      match Box.Search.findContainingIndex (fun region => region.box) point
          output.remainder with
      | some index => some (.remainder index)
      | none => none

/-- Every returned partition location contains the original query point.

The proof follows the two finite searches and their original list indices,
using the corresponding containing-box certificate without rebuilding a cell. -/
public theorem findPartitionLocation_sound
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (point : Gaussian.Basic.Canonical)
    (location : PartitionLocation output)
    (found : findPartitionLocation? output point = some location) :
    location.box.Contains point := by
  unfold findPartitionLocation? at found
  cases trackFound : Box.Search.findContainingIndex
      (fun track : Track.Basic.WindingOneTrack p ambient => track.initial.box)
      point output.tracks with
  | some trackIndex =>
      rw [trackFound] at found
      have locationEq : location = .track trackIndex :=
        Option.some.inj found.symm
      subst location
      exact Box.Search.findContainingIndex_sound _ _ _ _ trackFound
  | none =>
      rw [trackFound] at found
      cases regionFound : Box.Search.findContainingIndex
          (fun region : Clearance.Box.Region.ClearRegion p ambient => region.box)
          point output.remainder with
      | none => rw [regionFound] at found; contradiction
      | some regionIndex =>
          rw [regionFound] at found
          have locationEq : location = .remainder regionIndex :=
            Option.some.inj found.symm
          subst location
          exact Box.Search.findContainingIndex_sound _ _ _ _ regionFound

/-- Every point in the retained support is found in its isolation partition.

The stored covering certificate supplies an actual track or remainder
occurrence. Finite search completeness excludes the absent result directly. -/
public theorem findPartitionLocation_ne_none
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) {point : Gaussian.Basic.Canonical}
    (inside : output.support.Contains point) :
    findPartitionLocation? output point ≠ none := by
  rcases output.partition_covers inside with
    ⟨track, trackMember, trackContains⟩ |
      ⟨region, regionMember, regionContains⟩
  · have trackExists : ∃ value ∈ output.tracks,
        value.initial.box.Contains point :=
      ⟨track, trackMember, trackContains⟩
    have trackFound := Box.Search.findContainingIndex_ne_none_of_exists
      (fun value : Track.Basic.WindingOneTrack p ambient => value.initial.box)
      point output.tracks trackExists
    unfold findPartitionLocation?
    cases found : Box.Search.findContainingIndex
        (fun value : Track.Basic.WindingOneTrack p ambient => value.initial.box)
        point output.tracks with
    | none => exact (trackFound found).elim
    | some index => exact Option.some_ne_none (PartitionLocation.track index)
  · have regionExists : ∃ value ∈ output.remainder,
        value.box.Contains point :=
      ⟨region, regionMember, regionContains⟩
    have regionFound := Box.Search.findContainingIndex_ne_none_of_exists
      (fun value : Clearance.Box.Region.ClearRegion p ambient => value.box)
      point output.remainder regionExists
    unfold findPartitionLocation?
    cases trackFound : Box.Search.findContainingIndex
        (fun value : Track.Basic.WindingOneTrack p ambient => value.initial.box)
        point output.tracks with
    | some index => exact Option.some_ne_none (PartitionLocation.track index)
    | none =>
        cases found : Box.Search.findContainingIndex
            (fun value : Clearance.Box.Region.ClearRegion p ambient => value.box)
            point output.remainder with
        | none => exact (regionFound found).elim
        | some index => exact Option.some_ne_none (PartitionLocation.remainder index)

/-- Locate a point certified inside the support of the original isolation partition.

The retained covering certificate makes the finite first-containing-cell search total. -/
@[expose] public def locatePartition
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (point : Gaussian.Basic.Canonical)
    (inside : output.support.Contains point) : PartitionLocation output :=
  match found : findPartitionLocation? output point with
  | some location => location
  | none => False.elim (findPartitionLocation_ne_none output inside found)

/-- The total partition locator returns a box containing the query point.

The result retains the same first-search index. Its containment certificate
comes from the successful search equation and the original covering witness. -/
public theorem locatePartition_contains
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (point : Gaussian.Basic.Canonical)
    (inside : output.support.Contains point) :
    (locatePartition output point inside).box.Contains point := by
  unfold locatePartition
  split
  next location found =>
    exact findPartitionLocation_sound output point location found
  next found =>
    exact (findPartitionLocation_ne_none output inside found).elim
end Purelib.RootIsolation.Exact.Partition.Location

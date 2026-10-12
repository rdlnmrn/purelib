module
import Purelib.Data.List.Membership
public import Purelib.Data.Rat.List.Minimum
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Exact.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Clearance margins of exact root partitions

The original output retains its ordered track boxes and remainder regions.
Their stored clearance bounds determine a common positive minimum, and each
original indexed occurrence is bounded below by that same partition margin.
-/

namespace Purelib.RootIsolation.Exact.Partition.Margin

/-- Collect the original clearance bounds of all retained track boxes and remainder regions.

The ordered track bounds are followed by the ordered remainder bounds. Every entry is read from the original clearance
certificate, retaining both lists and their occurrence order. -/
@[expose] public def partitionBounds
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) : List Fraction.Rational :=
  (output.tracks.map fun track => track.initial.clearance.bound) ++
    (output.remainder.map fun region => region.clearance.bound)

/-- Compute a common positive margin for the finite original isolation partition.

The same ordered clearance list is passed to the retained positive-minimum procedure. Its empty-list convention and
every finite branch remain unchanged. -/
@[expose] public def partitionMargin
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) : Fraction.Rational :=
  Data.Rat.List.Minimum.Maximality.positiveMinimum (partitionBounds output)

/-- The finite partition's computed common margin is strictly positive.

Every original list occurrence belongs to a retained track or remainder region. The corresponding stored clearance
certifies positivity of that same displayed entry. -/
public theorem partitionMargin_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) : 0 < partitionMargin output := by
  apply Data.Rat.List.Minimum.Maximality.positiveMinimum_pos
  intro value member
  change value ∈ (output.tracks.map fun track => track.initial.clearance.bound) ++
    (output.remainder.map fun region => region.clearance.bound) at member
  rcases Data.List.Membership.mem_append.mp member with trackMember | regionMember
  · rcases Data.List.Map.mem_map.mp trackMember with ⟨track, _member, rfl⟩
    exact track.initial.clearance.positive
  · rcases Data.List.Map.mem_map.mp regionMember with ⟨region, _member, rfl⟩
    exact region.clearance.positive

/-- The common partition margin fits every original retained track clearance. -/
public theorem partitionMargin_le_track
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (index : Fin output.tracks.length) :
    partitionMargin output ≤
      (output.tracks.get index).initial.clearance.bound := by
  apply Data.Rat.List.Minimum.Maximality.positiveMinimum_le_of_mem
  apply List.mem_append_left
  exact Data.List.Map.mem_map_of_mem (List.get_mem output.tracks index)

/-- The common partition margin fits every original retained remainder clearance. -/
public theorem partitionMargin_le_remainder
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count : Nat}
    (output : Exact.Basic.Output p ambient count) (index : Fin output.remainder.length) :
    partitionMargin output ≤
      (output.remainder.get index).clearance.bound := by
  apply Data.Rat.List.Minimum.Maximality.positiveMinimum_le_of_mem
  apply List.mem_append_right
  exact Data.List.Map.mem_map_of_mem (List.get_mem output.remainder index)
end Purelib.RootIsolation.Exact.Partition.Margin

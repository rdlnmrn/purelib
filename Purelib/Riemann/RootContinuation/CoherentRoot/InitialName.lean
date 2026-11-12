module

public import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.RootIsolation.Track.Approximation.Sampling
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Polynomial.Winding.Box.Region
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Agreement between original box-process names and retained geometric root channels -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Compare the original box-process samples with the actual cached geometric root samples.

Both finite programs refine the same original winding-one owner. Positive
source-region counting excludes separated boxes; an explicit overlap point
and both original diagonal budgets bound each pair of retained samples.
Independent starting indices and every later pair remain in the certificate.
-/
def initial_sampling_equivalent {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : FTA.Squarefree.Input polynomial) :
    Equivalence.Equivalent (Name.Sampling.approximation (Track.Approximation.Name.initialNamed track))
      root.approximation where
  compare firstStart secondStart target positive := by
    let quarter := target / 4
    have quarterPositive : 0 < quarter := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let firstIndex := Geometric.Search.firstQuarterBelow 1 firstStart quarter
    let secondIndex := root.approximation.refineIndex secondStart quarter quarterPositive
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := Geometric.Search.firstQuarterBelow_ge 1 firstStart quarter
        right_ge := root.approximation.refineIndex_ge secondStart quarter quarterPositive
        close := by
          intro firstLater secondLater firstOrder secondOrder
          let first := Track.Approximation.Sampling.stateAt track firstLater
          let second := root.stateAt secondLater
          let outer : Clearance.Box.Region.ClearRegion polynomial ambient :=
            ⟨track.initial.box, track.initial.refinesAmbient, track.initial.proper, track.initial.clearance⟩
          let left : Clearance.Box.Region.ClearRegion polynomial ambient :=
            ⟨first.box, first.refinesAmbient, first.proper, first.clearance⟩
          let right : Clearance.Box.Region.ClearRegion polynomial ambient :=
            ⟨second.box, second.refinesAmbient, second.proper, second.clearance⟩
          have leftWinding : 0 < Winding.Box.Basic.quadrupledBoxWinding polynomial left.box := by
            rewrite [first.rawWindingFour]
            decide
          have rightWinding : 0 < Winding.Box.Basic.quadrupledBoxWinding polynomial right.box := by
            rewrite [second.rawWindingFour]
            decide
          have rightNested := state_refines_of_le track (Nat.zero_le secondLater)
          rewrite [← root.stateAt_eq secondLater] at rightNested
          have overlap := Winding.Box.Region.not_separated_in_winding_one_region input outer left right
            track.initial.rawWindingFour leftWinding rightWinding
            (Track.Approximation.Sampling.refines_initial track firstLater) rightNested
          let point := Box.overlapPoint first.box second.box
          have inside := Box.contains_overlapPoint_of_not_separated overlap
          have firstBound := first.box.normSq_sub_le_diagonalSq first.box.contains_anchor inside.1
          have secondBound := second.box.normSq_sub_le_diagonalSq inside.2 second.box.contains_anchor
          have firstDiagonal : first.box.diagonalSq < quarter :=
            (Track.Approximation.Sampling.diagonal_lt track firstLater).trans_le
              ((Geometric.Basic.quarterRadius_antitone (by decide : (0 : Fraction.Rational) ≤ 1) firstOrder).trans
                (Geometric.Search.firstQuarterBelow_accurate 1 (by decide) firstStart quarter quarterPositive).le)
          have secondDiagonal := root.stateAt_diagonal_lt_of_refineIndex_le secondStart quarter quarterPositive
            secondOrder
          rewrite [Track.Approximation.Sampling.sample_eq_anchor, root.sample_stateAt]
          exact (Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_via first.box.anchor point second.box.anchor).trans_lt
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound) (by decide)).trans_lt
              ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct firstDiagonal secondDiagonal)).trans_eq (by
                  change 2 * (target / 4 + target / 4) = target
                  rewrite [Purelib.Data.Rat.Bounds.Quarter.two_quarters target, Fraction.Field.mul_comm]
                  exact Purelib.Data.Rat.Bounds.Quarter.half_mul_two target))) }

/-- The original productive box-process name agrees with its retained cached coherent root channel.

The source name keeps its process, parser origin and prefix history. Its actual
sampling program is compared to the retained root cache, then composed with
that same cache's ordinary CCL sampling comparison.
-/
def initial_named_equivalent {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : FTA.Squarefree.Input polynomial) :
    Equivalence.NamedEquivalent (Track.Approximation.Name.initialNamed track) root.value.name := by
  rewrite [root.value_approximation]
  exact (root.initial_sampling_equivalent input).trans
    (Equivalence.Equivalent.toNamed_sampling root.approximation).symm

end Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

end

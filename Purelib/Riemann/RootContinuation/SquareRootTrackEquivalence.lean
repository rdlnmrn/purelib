module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Separation.Certificate
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Search.Extraction
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.Track.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.Riemann.RootContinuation.RobustSquareRootPreparation
public import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.RootIsolation.Refinement.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.RootIsolation.Owner.Local.Track
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

/-!
# Operational equivalence from finite winding-one overlap

The reconditioning bridge is topological data.  This module turns that data
into the analytic statement needed by integration: two shrinking square-root
tracks joined by a strictly nested winding-one box name the same operational
CCL value.  The proof is entirely finite.  If two sufficiently small boxes
were separated inside one winding-one owner, finite winding additivity would
force winding at least two in that owner, contradicting its displayed winding
one certificate.  A rational overlap point then bounds the two displayed
anchors by the sum of their box diagonals.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

open Purelib.Data

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
public abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
public abbrev Gaussian := Basic.Canonical
/-- The original rational box type with retained coordinate bounds. -/
public abbrev Box := Purelib.Geometry.Rational.Box
/-- The original winding-one state indexed by its polynomial and ambient box. -/
public abbrev WindingOneState := Purelib.RootIsolation.State.WindingOne.Basic.WindingOneState
/-- The original executable winding-one root track. -/
public abbrev WindingOneTrack := Purelib.RootIsolation.Track.Basic.WindingOneTrack
/-- Operational equivalence of the two original Gaussian names. -/
public abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Extract a winding-one state supported in the exact outer box from the retained inner state.

The inner box refines the outer box, and its original clearance and winding witness feed the same quadratic extraction
with explicit axis elimination. -/
@[expose] public def supportedInside {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneState
      (SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneState
      (SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (refines : inner.box.Refines outer.box) :
    WindingOneState
      (SquareRootReconditioning.rootPolynomial parameter)
      outer.box := by
  let input := SquareRootReconditioning.isolationInput
    parameterNonzero
  let raw : State.Raw.RawWindingState
      (SquareRootReconditioning.rootPolynomial parameter)
      outer.box :=
    { box := inner.box
      refinesAmbient := refines
      proper := inner.proper
      clearance := inner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← inner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }
  exact (Newton.Search.Extraction.extract input.degreeAtLeastTwo
    input.squarefree
    (QuadraticAxisElimination.quadraticAxisElimination parameter)
    raw (epsilon := (1 : Coordinate)) (by decide)
    (QuadraticLineClearance.Owner.quadraticAxisClearances parameter)).state

open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- The extracted supported state refines the exact supplied inner box. -/
public theorem supportedInside_refines_inner {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneState
      (SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneState
      (SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (refines : inner.box.Refines outer.box) :
    (supportedInside parameterNonzero outer inner refines).box.Refines
      inner.box := by
  change (Newton.Search.Extraction.extract _ _ _ _ (epsilon := (1 : Coordinate))
    (by decide)
    (QuadraticLineClearance.Owner.quadraticAxisClearances parameter)).state.box.Refines inner.box
  exact Geometry.Rational.Box.Refinement.StrictInterior.refines
    (Newton.Search.Extraction.extract _ _ _ _ (epsilon := (1 : Coordinate))
      (by decide)
      (QuadraticLineClearance.Owner.quadraticAxisClearances parameter)).strict

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Every positive-index track state lies strictly inside the original initial box.

A positive index is a successor. The first retained refinement is strict,
and the later original state refines that same first state. -/
public theorem state_strict_initial_of_pos
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    {index : Nat} (positive : 0 < index) :
    (CoherentRoot.state track index).box.StrictInterior
      track.initial.box := by
  cases index with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ index =>
      have firstStrict :
          (CoherentRoot.state track 1).box.StrictInterior
            track.initial.box := by
        change
          (track.refine track.initial
            (Bounds.AccuracyRadius.accuracyRadius
              (CoherentRoot.stepTarget track 0))
            (Bounds.AccuracyRadius.accuracyRadius_pos
              (CoherentRoot.stepTarget_positive track 0))).box.StrictInterior
            track.initial.box
        exact track.strict _ _ _
      exact (Geometry.Rational.Box.Refinement.StrictInterior.of_refines firstStrict)
        (CoherentRoot.state_refines_of_le track
          (Nat.succ_le_succ (Nat.zero_le index)))

open Purelib.Geometry.Rational in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Tracks with strictly nested initial boxes cannot have separated later states of the same nonzero quadratic.

The outer index is positive. Separated supported winding-one states would force winding at least two inside the original
winding-one box. -/
public theorem states_not_separated_of_initial_strict
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (innerStrict : inner.initial.box.StrictInterior outer.initial.box)
    {outerIndex : Nat} (outerIndexPositive : 0 < outerIndex)
    (innerIndex : Nat) :
    ¬(CoherentRoot.state outer outerIndex).box.Separated
      (CoherentRoot.state inner innerIndex).box := by
  intro separated
  let polynomial :=
    SquareRootReconditioning.rootPolynomial parameter
  let input := SquareRootReconditioning.isolationInput
    parameterNonzero
  let outerState := CoherentRoot.state outer outerIndex
  let innerState := CoherentRoot.state inner innerIndex
  have outerStrict : outerState.box.StrictInterior outer.initial.box :=
    state_strict_initial_of_pos outer outerIndexPositive
  have innerRefinesInitial : innerState.box.Refines inner.initial.box :=
    CoherentRoot.state_refines_of_le inner (Nat.zero_le innerIndex)
  have innerStrictOuter : innerState.box.StrictInterior outer.initial.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.of_refines innerStrict) innerRefinesInitial
  let outerSupported := supportedInside parameterNonzero outer.initial
    outerState (Geometry.Rational.Box.Refinement.StrictInterior.refines outerStrict)
  let innerSupported := supportedInside parameterNonzero outer.initial
    innerState (Geometry.Rational.Box.Refinement.StrictInterior.refines innerStrictOuter)
  have outerSupportedRefines : outerSupported.box.Refines outerState.box :=
    supportedInside_refines_inner parameterNonzero outer.initial outerState
      (Geometry.Rational.Box.Refinement.StrictInterior.refines outerStrict)
  have innerSupportedRefines : innerSupported.box.Refines innerState.box :=
    supportedInside_refines_inner parameterNonzero outer.initial innerState
      (Geometry.Rational.Box.Refinement.StrictInterior.refines innerStrictOuter)
  have supportedSeparated : outerSupported.box.Separated innerSupported.box :=
    separated.of_refines outerSupportedRefines innerSupportedRefines
  have outerSupportedStrict :
      outerSupported.box.StrictInterior outer.initial.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.of_refines outerStrict) outerSupportedRefines
  have innerSupportedStrict :
      innerSupported.box.StrictInterior outer.initial.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.of_refines innerStrictOuter) innerSupportedRefines
  let region : Region.ClearRegion polynomial outer.initial.box :=
    { box := outer.initial.box
      refinesAmbient := Box.refines_refl _
      proper := outer.initial.proper
      clearance := outer.initial.clearance }
  have atLeastEight := State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
    input.degreeAtLeastTwo input.squarefree input.elimination region
      outerSupported innerSupported outerSupportedStrict innerSupportedStrict
        supportedSeparated
  have exactlyFour := outer.initial.rawWindingFour
  dsimp only [region] at atLeastEight
  rw [exactlyFour] at atLeastEight
  omega

open Purelib.Data.Rat in
/-- Twice the sum of two quarter-targets equals the original rational target. -/
private theorem two_quarter_sums (target : Coordinate) :
    2 * (target / 4 + target / 4) = target := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (4 : Coordinate) ≠ 0 by decide)
  calc
    (2 * (target / 4 + target / 4)) * 4 =
        2 * ((target / 4) * 4 + (target / 4) * 4) := by ring1
    _ = 2 * (target + target) := by
      rw [Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 4 := by ring1

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- Compare the original tailed root approximations when their initial boxes are strictly nested.

Both requested starting indices are respected. Later boxes overlap, and their retained quarter-target diagonal bounds
give the exact requested sample-distance estimate. -/
@[expose] public def approximationEquivalent_of_initial_strict
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (innerStrict : inner.initial.box.StrictInterior outer.initial.box) :
    Equivalence.Equivalent
      (CertifiedSquareRoot.approximation outer)
      (CertifiedSquareRoot.approximation inner) where
  compare := by
    intro outerStart innerStart target targetPositive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct targetPositive (by decide)
    let outerApprox := CertifiedSquareRoot.approximation outer
    let innerApprox := CertifiedSquareRoot.approximation inner
    let outerIndex := outerApprox.refineIndex (max outerStart 1)
      smallTarget smallPositive
    let innerIndex := innerApprox.refineIndex innerStart
      smallTarget smallPositive
    exact
      { leftIndex := outerIndex
        rightIndex := innerIndex
        left_ge := (show outerStart ≤ max outerStart 1 from by
          rewrite [Nat.Order.max_eq_natMax]
          exact Nat.Order.le_max_left outerStart 1).trans
          (outerApprox.refineIndex_ge (max outerStart 1)
            smallTarget smallPositive)
        right_ge := innerApprox.refineIndex_ge innerStart
          smallTarget smallPositive
        close := by
          intro outerLater innerLater outerOrder innerOrder
          let outerRawIndex := max
            (CertifiedSquareRoot.baseIndex outer) outerLater
          let innerRawIndex := max
            (CertifiedSquareRoot.baseIndex inner) innerLater
          have outerIndexPositive : 0 < outerRawIndex := by
            have oneLeOuterIndex : 1 ≤ outerIndex :=
              (show 1 ≤ max outerStart 1 from by
                rewrite [Nat.Order.max_eq_natMax]
                exact Nat.Order.le_max_right outerStart 1).trans
                (outerApprox.refineIndex_ge (max outerStart 1)
                  smallTarget smallPositive)
            have oneLeLater : 1 ≤ outerLater := oneLeOuterIndex.trans outerOrder
            exact oneLeLater.trans (by
              dsimp only [outerRawIndex]
              rewrite [Nat.Order.max_eq_natMax]
              exact Nat.Order.le_max_right _ _)
          have notSeparated := states_not_separated_of_initial_strict
            parameterNonzero outer inner innerStrict outerIndexPositive
              innerRawIndex
          let overlap := Box.overlapPoint
            (CoherentRoot.state outer outerRawIndex).box
            (CoherentRoot.state inner innerRawIndex).box
          have overlapInside :=
            Box.contains_overlapPoint_of_not_separated notSeparated
          have outerDistance :
              normSq
                ((CoherentRoot.state outer outerRawIndex).box.anchor -
                  overlap) ≤
                (CoherentRoot.state outer
                  outerRawIndex).box.diagonalSq :=
            by
              rw [← Norm.Basic.normSq_eq_canonical]
              exact (CoherentRoot.state outer
              outerRawIndex).box.normSq_sub_le_diagonalSq
                (CoherentRoot.state outer
                  outerRawIndex).box.contains_anchor overlapInside.1
          have innerDistance :
              normSq
                (overlap -
                  (CoherentRoot.state inner
                    innerRawIndex).box.anchor) ≤
                (CoherentRoot.state inner
                  innerRawIndex).box.diagonalSq :=
            by
              rw [← Norm.Basic.normSq_eq_canonical]
              exact (CoherentRoot.state inner
              innerRawIndex).box.normSq_sub_le_diagonalSq overlapInside.2
                (CoherentRoot.state inner
                  innerRawIndex).box.contains_anchor
          have outerRawOrder :
              max (CertifiedSquareRoot.baseIndex outer) outerIndex ≤
                outerRawIndex := by
            dsimp only [outerRawIndex]
            rewrite [Nat.Order.max_eq_natMax,
              Nat.Order.max_eq_natMax]
            exact Nat.Order.max_le_max (Nat.le_refl _) outerOrder
          have innerRawOrder :
              max (CertifiedSquareRoot.baseIndex inner) innerIndex ≤
                innerRawIndex := by
            dsimp only [innerRawIndex]
            rewrite [Nat.Order.max_eq_natMax,
              Nat.Order.max_eq_natMax]
            exact Nat.Order.max_le_max (Nat.le_refl _) innerOrder
          have outerDiagonalSmall :
              (CoherentRoot.state outer
                outerRawIndex).box.diagonalSq < smallTarget := by
            calc
              (CoherentRoot.state outer
                  outerRawIndex).box.diagonalSq ≤
                  Geometric.Basic.quarterRadius
                    (CoherentRoot.scale outer) outerRawIndex :=
                CoherentRoot.state_diagonal_le outer outerRawIndex
              _ ≤ Geometric.Basic.quarterRadius
                    (CoherentRoot.scale outer)
                    (max (CertifiedSquareRoot.baseIndex outer)
                      outerIndex) :=
                quarterRadius_antitone
                  (CoherentRoot.scale_positive outer).le
                  outerRawOrder
              _ < smallTarget := by
                exact outerApprox.refineIndex_accurate
                  (max outerStart 1) smallTarget smallPositive
          have innerDiagonalSmall :
              (CoherentRoot.state inner
                innerRawIndex).box.diagonalSq < smallTarget := by
            calc
              (CoherentRoot.state inner
                  innerRawIndex).box.diagonalSq ≤
                  Geometric.Basic.quarterRadius
                    (CoherentRoot.scale inner) innerRawIndex :=
                CoherentRoot.state_diagonal_le inner innerRawIndex
              _ ≤ Geometric.Basic.quarterRadius
                    (CoherentRoot.scale inner)
                    (max (CertifiedSquareRoot.baseIndex inner)
                      innerIndex) :=
                quarterRadius_antitone
                  (CoherentRoot.scale_positive inner).le
                  innerRawOrder
              _ < smallTarget := by
                exact innerApprox.refineIndex_accurate innerStart smallTarget
                  smallPositive
          rw [Norm.Basic.normSq_eq_canonical]
          simp only [CertifiedSquareRoot.approximation_sample]
          change normSq
              ((CoherentRoot.state outer outerRawIndex).box.anchor -
                (CoherentRoot.state inner
                  innerRawIndex).box.anchor) < target
          calc
            normSq
                ((CoherentRoot.state outer
                    outerRawIndex).box.anchor -
                  (CoherentRoot.state inner
                    innerRawIndex).box.anchor) ≤
                2 * (normSq
                    ((CoherentRoot.state outer
                      outerRawIndex).box.anchor - overlap) +
                  normSq (overlap -
                    (CoherentRoot.state inner
                      innerRawIndex).box.anchor)) :=
              by
                have scalar := Norm.Bounds.normSq_sub_le_via
                  (CoherentRoot.state outer outerRawIndex).box.anchor overlap
                  (CoherentRoot.state inner innerRawIndex).box.anchor
                simpa only [Norm.Basic.normSq_eq_canonical] using scalar
            _ ≤ 2 *
                ((CoherentRoot.state outer
                    outerRawIndex).box.diagonalSq +
                  (CoherentRoot.state inner
                    innerRawIndex).box.diagonalSq) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add outerDistance innerDistance) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  outerDiagonalSmall innerDiagonalSmall)
            _ = target := two_quarter_sums target }

section
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
/-- Strict initial-box containment gives equivalence of the two original apartness-prepared root names.

The finite overlap comparison retains both approximation owners and their
requested starting indices; their apartness preparation preserves that equivalence. -/
@[expose] public def rootEquivalent_of_initial_strict
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {outerAmbient innerAmbient : Box}
    (outer : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      outerAmbient)
    (inner : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      innerAmbient)
    (innerStrict : inner.initial.box.StrictInterior outer.initial.box) :
    NamedEquivalent
      (CertifiedSquareRoot.root parameterNonzero outer).name
      (CertifiedSquareRoot.root parameterNonzero inner).name := by
  let outerRaw := CertifiedSquareRoot.rawRoot outer
  let innerRaw := CertifiedSquareRoot.rawRoot inner
  have rawEquivalent : NamedEquivalent outerRaw.name innerRaw.name :=
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (approximationEquivalent_of_initial_strict parameterNonzero outer inner
        innerStrict)
  exact Equivalence.NamedEquivalent.trans
    (Equivalence.NamedEquivalent.symm
      (Name.Coherent.CoherentNamed.apartifyEquivalent outerRaw
        (CertifiedSquareRoot.possibleApart parameterNonzero outer)))
    (Equivalence.NamedEquivalent.trans rawEquivalent
      (Name.Coherent.CoherentNamed.apartifyEquivalent innerRaw
        (CertifiedSquareRoot.possibleApart parameterNonzero
          inner)))

/-- Recover equivalence of the original tailed approximations from their prepared root-name equivalence.

Each root name retains its original approximation and apartness certificate.
The supplied name equivalence transports through those exact retained preparations. -/
@[expose] public def approximationEquivalent_of_rootEquivalent
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    {firstAmbient secondAmbient : Box}
    (first : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      firstAmbient)
    (second : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      secondAmbient)
    (equivalent : NamedEquivalent
      (CertifiedSquareRoot.root parameterNonzero first).name
      (CertifiedSquareRoot.root parameterNonzero second).name) :
    Equivalence.Equivalent
      (CertifiedSquareRoot.approximation first)
      (CertifiedSquareRoot.approximation second) := by
  let firstApprox := CertifiedSquareRoot.approximation first
  let secondApprox := CertifiedSquareRoot.approximation second
  let firstRaw := CertifiedSquareRoot.rawRoot first
  let secondRaw := CertifiedSquareRoot.rawRoot second
  have firstRawToRoot : NamedEquivalent firstRaw.name
      (CertifiedSquareRoot.root parameterNonzero first).name :=
    Name.Coherent.CoherentNamed.apartifyEquivalent firstRaw
      (CertifiedSquareRoot.possibleApart parameterNonzero first)
  have secondRawToRoot : NamedEquivalent secondRaw.name
      (CertifiedSquareRoot.root parameterNonzero second).name :=
    Name.Coherent.CoherentNamed.apartifyEquivalent secondRaw
      (CertifiedSquareRoot.possibleApart parameterNonzero second)
  have rawEquivalent : NamedEquivalent firstRaw.name secondRaw.name :=
    Equivalence.NamedEquivalent.trans firstRawToRoot
      (Equivalence.NamedEquivalent.trans equivalent
        secondRawToRoot.symm)
  exact Equivalence.Equivalent.trans
    (Equivalence.Equivalent.symm
      (Equivalence.Equivalent.toNamed_sampling firstApprox))
    (Equivalence.Equivalent.trans rawEquivalent
      (Equivalence.Equivalent.toNamed_sampling secondApprox))

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- Equivalent certified roots from the two canonical isolated owners have the same sheet index.

Different indices have retained separated initial boxes; their exact positive gap contradicts the operational sample
comparison at that squared gap. -/
public theorem canonicalOwner_index_eq_of_rootEquivalent
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (firstIndex secondIndex : Fin 2)
    (equivalent : NamedEquivalent
      ((SquareRootReconditioning.canonicalOwner parameterNonzero
        firstIndex).certificate parameterNonzero).value.name
      ((SquareRootReconditioning.canonicalOwner parameterNonzero
        secondIndex).certificate parameterNonzero).value.name) :
    firstIndex = secondIndex := by
  by_cases equal : firstIndex = secondIndex
  · exact equal
  · let first := SquareRootReconditioning.canonicalOwner
      parameterNonzero firstIndex
    let second := SquareRootReconditioning.canonicalOwner
      parameterNonzero secondIndex
    have separated : first.track.initial.box.Separated
        second.track.initial.box := by
      let output := (SquareRootReconditioning.isolationInput
        parameterNonzero).isolation
      have firstCast : output.trackIndex firstIndex = firstIndex :=
        Fin.ext (output.trackIndex_val firstIndex)
      have secondCast : output.trackIndex secondIndex = secondIndex :=
        Fin.ext (output.trackIndex_val secondIndex)
      have separatedCast := output.trackAt_pairwiseSeparated firstIndex
        secondIndex equal
      rw [show output.trackAt firstIndex = output.tracks.get
          (output.trackIndex firstIndex) from rfl,
        show output.trackAt secondIndex = output.tracks.get
          (output.trackIndex secondIndex) from rfl,
        firstCast, secondCast] at separatedCast
      exact separatedCast
    let separation := Box.separationCertificate separated
    let approximationEquivalent := approximationEquivalent_of_rootEquivalent
      parameterNonzero first.track second.track equivalent
    let comparison := approximationEquivalent.compare 0 0 (separation.gap ^ 2)
      (Fraction.Order.Arithmetic.pow_pos_direct separation.positive 2)
    have firstInside : first.track.initial.box.Contains
        ((CertifiedSquareRoot.approximation first.track).sample
          comparison.leftIndex) := by
      rw [CertifiedSquareRoot.approximation_sample]
      exact (CoherentRoot.state_refines_of_le first.track
        (Nat.zero_le _)).contains
          (CoherentRoot.state first.track _).box.contains_anchor
    have secondInside : second.track.initial.box.Contains
        ((CertifiedSquareRoot.approximation second.track).sample
          comparison.rightIndex) := by
      rw [CertifiedSquareRoot.approximation_sample]
      exact (CoherentRoot.state_refines_of_le second.track
        (Nat.zero_le _)).contains
          (CoherentRoot.state second.track _).box.contains_anchor
    have lower := separation.lower firstInside secondInside
    have close := comparison.close (Nat.le_refl comparison.leftIndex)
      (Nat.le_refl comparison.rightIndex)
    exact ((not_lt_of_ge lower) close).elim

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Read the transported source owner as a target-quadratic track supported on the exact source initial box.

The original displacement certificate pays the source clearance, while the
nonzero target supplies the same quadratic degree and squarefree witnesses. -/
@[expose] public def transportedTrack {source target : Gaussian} {ambient : Box}
    (targetNonzero : target ≠ 0)
    (sourceTrack : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial source) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceTrack.initial.clearance.bound) :
    WindingOneTrack
      (SquareRootReconditioning.rootPolynomial target)
      sourceTrack.initial.box :=
  (SquareRootContinuation.transportedOwner
      sourceTrack.initial small).track
    (by
      rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
      exact SquareRootDegree.degreeTwo_atLeastTwo)
    (Gaussian.Squarefree.squarefree targetNonzero
      SquareRootDegree.degreeTwo)

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The transported track retains the exact source initial box. -/
@[simp] public theorem transportedTrack_initial_box {source target : Gaussian}
    {ambient : Box} (targetNonzero : target ≠ 0)
    (sourceTrack : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial source) ambient)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceTrack.initial.clearance.bound) :
    (transportedTrack targetNonzero sourceTrack small).initial.box =
      sourceTrack.initial.box := rfl

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- Continuation preserves comparison through a common source track strictly inside both original owners.

The target is nonzero, and its displacement satisfies the separate clearance bounds of both source tracks and the common
track. -/
@[expose] public def rootEquivalent_continued_of_common_source
    {source target : Gaussian} (targetNonzero : target ≠ 0)
    {firstAmbient secondAmbient commonAmbient : Box}
    (first : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial source)
      firstAmbient)
    (second : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial source)
      secondAmbient)
    (common : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial source)
      commonAmbient)
    (commonStrictFirst : common.initial.box.StrictInterior first.initial.box)
    (commonStrictSecond : common.initial.box.StrictInterior second.initial.box)
    (firstSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      first.initial.clearance.bound)
    (secondSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      second.initial.clearance.bound)
    (commonSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      common.initial.clearance.bound) :
    NamedEquivalent
      (CertifiedSquareRoot.root targetNonzero
        (SquareRootContinuation.continuedTrack targetNonzero
          first.initial firstSmall)).name
      (CertifiedSquareRoot.root targetNonzero
        (SquareRootContinuation.continuedTrack targetNonzero
          second.initial secondSmall)).name := by
  let firstTarget := SquareRootContinuation.continuedTrack
    targetNonzero first.initial firstSmall
  let secondTarget := SquareRootContinuation.continuedTrack
    targetNonzero second.initial secondSmall
  let commonTarget := SquareRootContinuation.continuedTrack
    targetNonzero common.initial commonSmall
  let firstOuter := transportedTrack targetNonzero first firstSmall
  let secondOuter := transportedTrack targetNonzero second secondSmall
  have firstTargetStrict : firstTarget.initial.box.StrictInterior
      firstOuter.initial.box := by
    change firstTarget.initial.box.StrictInterior first.initial.box
    exact SquareRootContinuation.continuedTrack_initial_strict_source
      targetNonzero first.initial firstSmall
  have secondTargetStrict : secondTarget.initial.box.StrictInterior
      secondOuter.initial.box := by
    change secondTarget.initial.box.StrictInterior second.initial.box
    exact SquareRootContinuation.continuedTrack_initial_strict_source
      targetNonzero second.initial secondSmall
  have commonTargetRefines : commonTarget.initial.box.Refines
      common.initial.box :=
    SquareRootContinuation.continuedTrack_initial_refines_source
      targetNonzero common.initial commonSmall
  have commonTargetStrictFirst : commonTarget.initial.box.StrictInterior
      firstOuter.initial.box := by
    change commonTarget.initial.box.StrictInterior first.initial.box
    exact (Geometry.Rational.Box.Refinement.StrictInterior.of_refines commonStrictFirst) commonTargetRefines
  have commonTargetStrictSecond : commonTarget.initial.box.StrictInterior
      secondOuter.initial.box := by
    change commonTarget.initial.box.StrictInterior second.initial.box
    exact (Geometry.Rational.Box.Refinement.StrictInterior.of_refines commonStrictSecond) commonTargetRefines
  have firstOuterToFirst := rootEquivalent_of_initial_strict targetNonzero
    firstOuter firstTarget firstTargetStrict
  have firstOuterToCommon := rootEquivalent_of_initial_strict targetNonzero
    firstOuter commonTarget commonTargetStrictFirst
  have secondOuterToSecond := rootEquivalent_of_initial_strict targetNonzero
    secondOuter secondTarget secondTargetStrict
  have secondOuterToCommon := rootEquivalent_of_initial_strict targetNonzero
    secondOuter commonTarget commonTargetStrictSecond
  exact Equivalence.NamedEquivalent.trans firstOuterToFirst.symm
    (Equivalence.NamedEquivalent.trans firstOuterToCommon
      (Equivalence.NamedEquivalent.trans
        secondOuterToCommon.symm secondOuterToSecond))

open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- The two advanced owners have equivalent root names under their retained common-source clearance certificates.

Both continuation operations use the same target and the retained common
source track, with separate clearance payments for each original owner. -/
@[expose] public def rootEquivalent_advance_of_common_source
    {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second common :
      SquareRootContinuationChain.Owner source)
    (commonStrictFirst :
      common.track.initial.box.StrictInterior first.track.initial.box)
    (commonStrictSecond :
      common.track.initial.box.StrictInterior second.track.initial.box)
    (firstSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      first.track.initial.clearance.bound)
    (secondSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      second.track.initial.clearance.bound)
    (commonSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      common.track.initial.clearance.bound) :
    NamedEquivalent
      ((first.advance targetNonzero firstSmall).certificate
        targetNonzero).value.name
      ((second.advance targetNonzero secondSmall).certificate
        targetNonzero).value.name :=
  rootEquivalent_continued_of_common_source targetNonzero first.track
    second.track common.track commonStrictFirst commonStrictSecond firstSmall
      secondSmall commonSmall

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- Direct and two-stage continuation from the same original owner give equivalent target root names.

The intermediate and target parameters are nonzero; the supplied direct and staged displacement bounds refer to the
exact retained source and intermediate states. -/
@[expose] public def rootEquivalent_continued_compose
    {source middle target : Gaussian}
    (middleNonzero : middle ≠ 0) (targetNonzero : target ≠ 0)
    {sourceAmbient : Box}
    (sourceTrack : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial source)
      sourceAmbient)
    (sourceMiddleSmall : normSq (source - middle) <
      sourceTrack.initial.clearance.bound)
    (sourceTargetSmall : normSq (source - target) <
      sourceTrack.initial.clearance.bound)
    (middleTargetSmall : normSq (middle - target) <
      (SquareRootContinuation.continuedTrack middleNonzero
        sourceTrack.initial (by
            simpa only [Norm.Basic.normSq_eq_canonical]
              using sourceMiddleSmall)).initial.clearance.bound) :
    NamedEquivalent
      (CertifiedSquareRoot.root targetNonzero
        (SquareRootContinuation.continuedTrack targetNonzero
          sourceTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceTargetSmall))).name
      (CertifiedSquareRoot.root targetNonzero
        (SquareRootContinuation.continuedTrack targetNonzero
          (SquareRootContinuation.continuedTrack middleNonzero
            sourceTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceMiddleSmall)).initial
          (by simpa only [Norm.Basic.normSq_eq_canonical] using middleTargetSmall))).name := by
  let middleTrack := SquareRootContinuation.continuedTrack
    middleNonzero sourceTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceMiddleSmall)
  let directTrack := SquareRootContinuation.continuedTrack
    targetNonzero sourceTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceTargetSmall)
  let stagedTrack := SquareRootContinuation.continuedTrack
    targetNonzero middleTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using middleTargetSmall)
  let outer := transportedTrack targetNonzero sourceTrack (by
      simpa only [Norm.Basic.normSq_eq_canonical]
        using sourceTargetSmall)
  have directStrict : directTrack.initial.box.StrictInterior
      outer.initial.box := by
    change directTrack.initial.box.StrictInterior sourceTrack.initial.box
    exact SquareRootContinuation.continuedTrack_initial_strict_source
      targetNonzero sourceTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceTargetSmall)
  have middleStrict : middleTrack.initial.box.StrictInterior
      sourceTrack.initial.box :=
    SquareRootContinuation.continuedTrack_initial_strict_source
      middleNonzero sourceTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceMiddleSmall)
  have stagedRefinesMiddle : stagedTrack.initial.box.Refines
      middleTrack.initial.box :=
    SquareRootContinuation.continuedTrack_initial_refines_source
      targetNonzero middleTrack.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using middleTargetSmall)
  have stagedStrict : stagedTrack.initial.box.StrictInterior
      outer.initial.box := by
    change stagedTrack.initial.box.StrictInterior sourceTrack.initial.box
    exact (Geometry.Rational.Box.Refinement.StrictInterior.of_refines middleStrict) stagedRefinesMiddle
  have outerToDirect := rootEquivalent_of_initial_strict targetNonzero outer
    directTrack directStrict
  have outerToStaged := rootEquivalent_of_initial_strict targetNonzero outer
    stagedTrack stagedStrict
  exact Equivalence.NamedEquivalent.trans outerToDirect.symm
    outerToStaged

section
open Purelib.Approximation.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
/-- The robustly prepared owner has the same operational root as the original owner.

The retained robust bridge and its strict initial containments give a finite
common-track comparison without replacing either source owner. -/
@[expose] public def rootEquivalent_robustPrepare
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment
      polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
    (owner : SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    NamedEquivalent
      (owner.certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name
      ((RobustSquareRootPreparation.prepared
          segment parameter inside owner rootDiameter
          rootDiameterPositive).certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name := by
  let common := RobustSquareRootPreparation.bridgeTrack
    segment parameter inside owner rootDiameter rootDiameterPositive
  let robust := RobustSquareRootPreparation.prepared
    segment parameter inside owner rootDiameter rootDiameterPositive
  have oldToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) owner.track common
    (RobustSquareRootPreparation.bridgeTrack_initial_strict_owner
      segment parameter inside owner rootDiameterPositive)
  have robustToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) robust.track common
    (RobustSquareRootPreparation.bridgeTrack_initial_strict_prepared
      segment parameter inside owner rootDiameterPositive)
  exact Equivalence.NamedEquivalent.trans oldToCommon
    (Equivalence.NamedEquivalent.symm robustToCommon)

/-- The uniformly prepared owner has the same operational root as the original owner.

Uniform preparation retains its common bridge and strict source containment;
that exact finite relation supplies the comparison of root names. -/
@[expose] public def rootEquivalent_uniformPrepare
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment
      polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    NamedEquivalent
      (owner.certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name
      ((UniformSquareRootPreparation.prepared
          segment parameter inside owner rootDiameter
          rootDiameterPositive).certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name := by
  let common := UniformSquareRootPreparation.bridgeTrack
    segment parameter inside owner rootDiameter rootDiameterPositive
  let uniform := UniformSquareRootPreparation.prepared
    segment parameter inside owner rootDiameter rootDiameterPositive
  have oldToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) owner.track common
    (UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
      segment parameter inside owner rootDiameterPositive)
  have uniformToCommon := rootEquivalent_of_initial_strict
    (segment.pointAt_eval_ne_zero parameter inside) uniform.track common
    (UniformSquareRootPreparation.bridgeTrack_initial_strict_prepared
      segment parameter inside owner rootDiameterPositive)
  exact Equivalence.NamedEquivalent.trans oldToCommon
    (Equivalence.NamedEquivalent.symm uniformToCommon)

end

open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Restarting the original track at its positive preparation index preserves its operational root.

The original positive-index state is strictly inside the initial owner,
and the restarted track retains the same refinement operation and certificates. -/
@[expose] public def rootEquivalent_prepare {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : SquareRootContinuationChain.Owner parameter)
    (target : Coordinate) (positive : 0 < target) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((owner.prepare target positive).certificate parameterNonzero).value.name := by
  exact rootEquivalent_of_initial_strict parameterNonzero owner.track
    (owner.prepare target positive).track
    (by
      change
        (CoherentRoot.state owner.track
          (SquareRootContinuationChain.Owner.preparationIndex
            owner target positive)).box.StrictInterior owner.track.initial.box
      exact state_strict_initial_of_pos owner.track
        (SquareRootContinuationChain.Owner.preparationIndex_positive
          owner target positive))

open Purelib.Riemann.Topology in
/-- Quantitative Newton preparation preserves the original owner's operational root.

The retained preparation state remains strictly inside its source owner,
so their finite overlap comparison relates the original and prepared names. -/
@[expose] public def rootEquivalent_quantitativePrepare {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : SquareRootContinuationChain.Owner parameter)
    (target : Coordinate) (positive : 0 < target) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((owner.quantitativePrepare parameterNonzero target positive).certificate
        parameterNonzero).value.name := by
  exact rootEquivalent_of_initial_strict parameterNonzero owner.track
    (owner.quantitativePrepare parameterNonzero target positive).track
    (owner.quantitativePrepare_initial_strict parameterNonzero target positive)

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Continuation at an unchanged nonzero parameter preserves the original operational root.

The zero displacement meets the retained clearance bound, and the original
preparation relation compares the resulting target name with its source. -/
@[expose] public def rootEquivalent_advance_same {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : SquareRootContinuationChain.Owner parameter)
    (small : normSq (parameter - parameter) <
      owner.track.initial.clearance.bound) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((owner.advance parameterNonzero (by simpa only [Norm.Basic.normSq_eq_canonical] using small)).certificate
        parameterNonzero).value.name := by
  exact rootEquivalent_of_initial_strict parameterNonzero owner.track
    (owner.advance parameterNonzero (by simpa only [Norm.Basic.normSq_eq_canonical] using small)).track
    (SquareRootContinuation.continuedTrack_initial_strict_source
      parameterNonzero owner.track.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using small))

open Purelib.Polynomial.Dense.Gaussian in
/-- Restart the original track at the supplied state while retaining its refinement operation and certificates.

Only the initial state changes; the original refine, strict and diagonal
certificates are retained with the same polynomial and ambient box. -/
@[expose] public def restart {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (initial : WindingOneState polynomial ambient) :
    WindingOneTrack polynomial ambient where
  initial := initial
  refine := track.refine
  nested := track.nested
  strict := track.strict
  accurate := track.accurate

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Compare two root tracks using a retained common track and its exact radius refinement.

The common initial box lies strictly in the old box; the retained refined state is exactly the common refinement and
lies strictly in the fresh box. -/
@[expose] public def rootEquivalent_of_common_bridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {oldAmbient commonAmbient freshAmbient : Box}
    (old : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      oldAmbient)
    (common : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      commonAmbient)
    (fresh : WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      freshAmbient)
    (commonStrictOld : common.initial.box.StrictInterior old.initial.box)
    (refinementRadius : Coordinate) (refinementPositive : 0 < refinementRadius)
    (refined : WindingOneState
      (SquareRootReconditioning.rootPolynomial parameter)
      commonAmbient)
    (refined_eq : refined = common.refine common.initial refinementRadius
      refinementPositive)
    (refinedStrictFresh : refined.box.StrictInterior fresh.initial.box) :
    NamedEquivalent
      (CertifiedSquareRoot.root parameterNonzero old).name
      (CertifiedSquareRoot.root parameterNonzero fresh).name := by
  let commonTail := restart common refined
  have commonTailStrictCommon :
      commonTail.initial.box.StrictInterior common.initial.box := by
    rw [show commonTail.initial = refined from rfl, refined_eq]
    exact common.strict _ _ _
  have oldToCommon := rootEquivalent_of_initial_strict parameterNonzero
    old common commonStrictOld
  have commonToTail := rootEquivalent_of_initial_strict parameterNonzero
    common commonTail commonTailStrictCommon
  have freshToTail := rootEquivalent_of_initial_strict parameterNonzero
    fresh commonTail refinedStrictFresh
  exact Equivalence.NamedEquivalent.trans oldToCommon
    (Equivalence.NamedEquivalent.trans commonToTail
      (Equivalence.NamedEquivalent.symm freshToTail))

open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Read the retained reconditioning bridge as equivalence between the original and assigned fresh root names.

The bridge retains a common track, strict source containment and exact
radius refinement into the independently assigned fresh owner. -/
@[expose] public def rootEquivalent_of_bridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (owner : SquareRootContinuationChain.Owner parameter)
    (reset : SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    NamedEquivalent
      (owner.certificate parameterNonzero).value.name
      ((SquareRootReconditioning.freshOwner parameterNonzero
        owner).certificate parameterNonzero).value.name := by
  exact rootEquivalent_of_common_bridge parameterNonzero owner.track
    reset.common
    (SquareRootReconditioning.freshOwner parameterNonzero
      owner).track
    reset.commonInitialStrictOwner reset.refinementRadius
    reset.refinementRadiusPositive reset.refined reset.refined_eq
    reset.refinedStrictFresh

section
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
/-- Restart the retained bridge's common track at its exact stored refined state.

The stored state and refinement equation come from the same bridge, and
the restarted track keeps its original refinement functions and certificates. -/
@[expose] public def commonTailOfBridge {parameter : Gaussian}
    {parameterNonzero : parameter ≠ 0}
    {owner : SquareRootContinuationChain.Owner parameter}
    (reset : SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    WindingOneTrack
      (SquareRootReconditioning.rootPolynomial parameter)
      (Bounds.RootRadius.Box.largeSquareBox
        (SquareRootReconditioning.rootPolynomial parameter)) :=
  restart reset.common reset.refined

/-- Package the exact common-tail track as a square-root owner in its original global box.

The nonzero radicand, coefficient-computed ambient and retained bridge tail
remain the original data defining this common owner. -/
@[expose] public def commonOwnerOfBridge {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {owner : SquareRootContinuationChain.Owner parameter}
    (reset : SquareRootReconditioning.Bridge parameterNonzero
      owner) : SquareRootContinuationChain.Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := Bounds.RootRadius.Box.largeSquareBox
    (SquareRootReconditioning.rootPolynomial parameter)
  track := commonTailOfBridge reset

end

open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- The common bridge owner retains exactly the common-tail track. -/
@[simp] public theorem commonOwnerOfBridge_track {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {owner : SquareRootContinuationChain.Owner parameter}
    (reset : SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    (commonOwnerOfBridge parameterNonzero reset).track =
      commonTailOfBridge reset := rfl

open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- The retained common-tail initial box lies strictly inside the original owner's initial box. -/
public theorem commonTailOfBridge_initial_strict_owner {parameter : Gaussian}
    {parameterNonzero : parameter ≠ 0}
    {owner : SquareRootContinuationChain.Owner parameter}
    (reset : SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    (commonTailOfBridge reset).initial.box.StrictInterior
      owner.track.initial.box := by
  apply (Geometry.Rational.Box.Refinement.StrictInterior.of_refines reset.commonInitialStrictOwner)
  change reset.refined.box.Refines reset.common.initial.box
  rw [reset.refined_eq]
  exact Geometry.Rational.Box.Refinement.StrictInterior.refines (reset.common.strict _ _ _)

open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- The retained common-tail initial box lies strictly inside the exact assigned fresh owner's initial box. -/
public theorem commonTailOfBridge_initial_strict_fresh {parameter : Gaussian}
    {parameterNonzero : parameter ≠ 0}
    {owner : SquareRootContinuationChain.Owner parameter}
    (reset : SquareRootReconditioning.Bridge parameterNonzero
      owner) :
    (commonTailOfBridge reset).initial.box.StrictInterior
      (SquareRootReconditioning.freshOwner parameterNonzero
        owner).track.initial.box := by
  exact reset.refinedStrictFresh

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Equivalent original root owners select exactly the same independently isolated fresh owner.

Their retained reconditioning bridges identify both root names with canonical isolated names, forcing equality of the
exact selected sheet indices. -/
public theorem freshOwner_eq_of_rootEquivalent {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (first second :
      SquareRootContinuationChain.Owner parameter)
    (equivalent : NamedEquivalent
      (first.certificate parameterNonzero).value.name
      (second.certificate parameterNonzero).value.name) :
    SquareRootReconditioning.freshOwner parameterNonzero first =
      SquareRootReconditioning.freshOwner parameterNonzero
        second := by
  let firstReset := SquareRootReconditioning.bridge
    parameterNonzero first
  let secondReset := SquareRootReconditioning.bridge
    parameterNonzero second
  have firstToFresh := rootEquivalent_of_bridge parameterNonzero first
    firstReset
  have secondToFresh := rootEquivalent_of_bridge parameterNonzero second
    secondReset
  have freshEquivalent := Equivalence.NamedEquivalent.trans
    firstToFresh.symm
      (Equivalence.NamedEquivalent.trans equivalent
        secondToFresh)
  let firstIndex : Fin 2 :=
    (SquareRootReconditioning.assignment parameterNonzero
      first).owner.owner
  let secondIndex : Fin 2 :=
    (SquareRootReconditioning.assignment parameterNonzero
      second).owner.owner
  have indexEqual : firstIndex = secondIndex :=
    canonicalOwner_index_eq_of_rootEquivalent parameterNonzero firstIndex
      secondIndex (by
        simpa only [firstIndex, secondIndex,
          SquareRootReconditioning.freshOwner_eq_canonicalOwner]
          using freshEquivalent)
  rw [SquareRootReconditioning.freshOwner_eq_canonicalOwner,
    SquareRootReconditioning.freshOwner_eq_canonicalOwner]
  exact congrArg
    (SquareRootReconditioning.canonicalOwner parameterNonzero)
    indexEqual

section
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
/-- The actual initial clearance of the fresh owner assigned to the original source owner. -/
public abbrev freshSourceClearance {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : SquareRootContinuationChain.Owner source) :
    Coordinate :=
  (SquareRootReconditioning.freshOwner sourceNonzero owner).track
    |>.initial.clearance.bound

/-- The actual initial clearance of the exact common tail in the original owner's reconditioning bridge. -/
public abbrev bridgeTailClearance {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : SquareRootContinuationChain.Owner source) :
    Coordinate :=
  (commonTailOfBridge
    (SquareRootReconditioning.bridge sourceNonzero owner)).initial
      |>.clearance.bound

/-- The actual clearance after one refinement of the assigned fresh source owner. -/
public abbrev freshCommonClearance {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : SquareRootContinuationChain.Owner source) :
    Coordinate :=
  ((SquareRootReconditioning.freshOwner sourceNonzero owner).refineAt
      1).track.initial.clearance.bound

end

section
open Purelib.Riemann.Topology
/-- Seven exact displacement bounds supporting continuation of two equivalent source owners.

The original, fresh and bridge clearances remain separate for both inputs; a final bound concerns the first fresh
owner's retained one-step refinement. -/
public structure ContinuationCongruenceSmall {source : Gaussian}
    (sourceNonzero : source ≠ 0)
    (first second : SquareRootContinuationChain.Owner source)
    (target : Gaussian) : Prop where
  /-- The exact source-to-target displacement is below the first original owner's clearance. -/ firstSmall : normSq
    (source - target) < first.track.initial.clearance.bound
  /-- The exact source-to-target displacement is below the second original owner's clearance. -/ secondSmall : normSq
    (source - target) < second.track.initial.clearance.bound
  /-- The displacement is below the first owner's assigned fresh clearance. -/ firstFresh : normSq (source - target) <
    freshSourceClearance sourceNonzero first
  /-- The displacement is below the second owner's assigned fresh clearance. -/ secondFresh : normSq (source - target) <
    freshSourceClearance sourceNonzero second
  /-- The displacement is below the first owner's exact common-tail clearance. -/ firstBridge : normSq (source - target)
    <
    bridgeTailClearance sourceNonzero first
  /-- The displacement is below the second owner's exact common-tail clearance. -/ secondBridge : normSq (source -
    target) <
    bridgeTailClearance sourceNonzero second
  /-- The displacement is below the clearance of the first fresh owner's retained one-step refinement. -/ freshCommon :
    normSq (source - target) <
    freshCommonClearance sourceNonzero first

/-- Decide all seven retained rational displacement-to-clearance comparisons.

The original nested comparisons select success with all seven witnesses,
or the first failing comparison with its exact obstruction proof. -/
public instance continuationCongruenceSmallDecidable {source : Gaussian}
    (sourceNonzero : source ≠ 0)
    (first second : SquareRootContinuationChain.Owner source)
    (target : Gaussian) :
    Decidable (ContinuationCongruenceSmall sourceNonzero first second target) := by
  by_cases firstSmall : normSq (source - target) <
      first.track.initial.clearance.bound
  · by_cases secondSmall : normSq (source - target) <
        second.track.initial.clearance.bound
    · by_cases firstFresh : normSq (source - target) <
          freshSourceClearance sourceNonzero first
      · by_cases secondFresh : normSq (source - target) <
            freshSourceClearance sourceNonzero second
        · by_cases firstBridge : normSq (source - target) <
              bridgeTailClearance sourceNonzero first
          · by_cases secondBridge : normSq (source - target) <
                bridgeTailClearance sourceNonzero second
            · by_cases freshCommon : normSq (source - target) <
                  freshCommonClearance sourceNonzero first
              · exact isTrue
                  { firstSmall := firstSmall
                    secondSmall := secondSmall
                    firstFresh := firstFresh
                    secondFresh := secondFresh
                    firstBridge := firstBridge
                    secondBridge := secondBridge
                    freshCommon := freshCommon }
              · exact isFalse (fun small => freshCommon small.freshCommon)
            · exact isFalse (fun small => secondBridge small.secondBridge)
          · exact isFalse (fun small => firstBridge small.firstBridge)
        · exact isFalse (fun small => secondFresh small.secondFresh)
      · exact isFalse (fun small => firstFresh small.firstFresh)
    · exact isFalse (fun small => secondSmall small.secondSmall)
  · exact isFalse (fun small => firstSmall small.firstSmall)

end

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Read the certified root name of the exact owner continued to the supplied nonzero target.

The retained displacement certificate controls the continuation of the same
source initial state; the target certificate reads that exact continued track. -/
@[expose] public def continuedRootName {source target : Gaussian}
    (targetNonzero : target ≠ 0)
    (owner : SquareRootContinuationChain.Owner source)
    (small : normSq (source - target) <
      owner.track.initial.clearance.bound) : Name.Basic.Named :=
  (CertifiedSquareRoot.root targetNonzero
    (SquareRootContinuation.continuedTrack targetNonzero
      owner.track.initial (by simpa only [Norm.Basic.normSq_eq_canonical] using small))).name

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Topology in
/-- Read the certified operational root name of the original nonzero source owner.

The original owner certificate supplies its retained value and name without
constructing a new track or selecting another finite isolation. -/
@[expose] public def ownerRootName {source : Gaussian} (sourceNonzero : source ≠ 0)
    (owner : SquareRootContinuationChain.Owner source) :
    Name.Basic.Named :=
  (owner.certificate sourceNonzero).value.name

section
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
/-- Continue an original owner and its assigned fresh owner through their retained common bridge tail.

Separate displacement witnesses pay the original, fresh and bridge clearances at the same nonzero target. -/
@[expose] public def rootEquivalent_continued_to_bridgeFresh
    {source target : Gaussian} {sourceNonzero : source ≠ 0}
    (targetNonzero : target ≠ 0)
    {owner : SquareRootContinuationChain.Owner source}
    (reset : SquareRootReconditioning.Bridge sourceNonzero owner)
    (ownerSmall : normSq (source - target) <
      owner.track.initial.clearance.bound)
    (freshSmall : normSq (source - target) <
      (SquareRootReconditioning.freshOwner sourceNonzero
        owner).track.initial.clearance.bound)
    (bridgeSmall : normSq (source - target) <
      (commonTailOfBridge reset).initial.clearance.bound) :
    NamedEquivalent
      (continuedRootName targetNonzero owner ownerSmall)
      (continuedRootName targetNonzero
        (SquareRootReconditioning.freshOwner sourceNonzero owner)
        freshSmall) := by
  exact rootEquivalent_continued_of_common_source targetNonzero owner.track
    (SquareRootReconditioning.freshOwner sourceNonzero owner).track
      (commonTailOfBridge reset)
      (commonTailOfBridge_initial_strict_owner reset)
      (commonTailOfBridge_initial_strict_fresh reset)
      (by simpa only [Norm.Basic.normSq_eq_canonical] using ownerSmall) (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using freshSmall) (by simpa only [Norm.Basic.normSq_eq_canonical] using bridgeSmall)

/-- Equal source owners yield equivalent continued root names under the retained one-step common-refinement bound.

The same original one-step refinement lies strictly in both identified source
owners, and all three clearance bounds pay the common-target continuation. -/
@[expose] public def rootEquivalent_continued_of_owner_eq
    {source target : Gaussian}
    (targetNonzero : target ≠ 0)
    (first second : SquareRootContinuationChain.Owner source)
    (equal : first = second)
    (firstSmall : normSq (source - target) <
      first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) <
      second.track.initial.clearance.bound)
    (commonSmall : normSq (source - target) <
      (first.refineAt 1).track.initial.clearance.bound) :
    NamedEquivalent
      (continuedRootName targetNonzero first firstSmall)
      (continuedRootName targetNonzero second secondSmall) := by
  have commonStrictFirst : (first.refineAt 1).track.initial.box.StrictInterior
      first.track.initial.box := by
    change (CoherentRoot.state first.track 1).box.StrictInterior
      first.track.initial.box
    exact state_strict_initial_of_pos first.track (by decide)
  have commonStrictSecond : (first.refineAt 1).track.initial.box.StrictInterior
      second.track.initial.box := by
    rw [← equal]
    exact commonStrictFirst
  exact rootEquivalent_continued_of_common_source targetNonzero
    first.track second.track (first.refineAt 1).track commonStrictFirst
      commonStrictSecond (by simpa only [Norm.Basic.normSq_eq_canonical] using firstSmall) (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using secondSmall) (by
            simpa only [Norm.Basic.normSq_eq_canonical]
              using commonSmall)

end

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Continue the two equivalent original root owners using all seven retained clearance comparisons.

Their independently assigned fresh owners are exactly equal; the two original bridges and common fresh refinement
compose the target-name equivalence. -/
@[expose] public def rootEquivalent_continued_of_rootEquivalent
    {source target : Gaussian} (sourceNonzero : source ≠ 0)
    (targetNonzero : target ≠ 0)
    (first second : SquareRootContinuationChain.Owner source)
    (sourceEquivalent : NamedEquivalent
      (ownerRootName sourceNonzero first)
      (ownerRootName sourceNonzero second))
    (small : ContinuationCongruenceSmall sourceNonzero first second target) :
    NamedEquivalent
      (continuedRootName targetNonzero first small.firstSmall)
      (continuedRootName targetNonzero second small.secondSmall) := by
  have firstToFresh := rootEquivalent_continued_to_bridgeFresh targetNonzero
    (SquareRootReconditioning.bridge sourceNonzero first)
      small.firstSmall small.firstFresh small.firstBridge
  have freshEqual := freshOwner_eq_of_rootEquivalent sourceNonzero first second
    sourceEquivalent
  have freshToFresh := rootEquivalent_continued_of_owner_eq targetNonzero
    (SquareRootReconditioning.freshOwner sourceNonzero first)
    (SquareRootReconditioning.freshOwner sourceNonzero second)
      freshEqual small.firstFresh small.secondFresh small.freshCommon
  have secondToFresh := rootEquivalent_continued_to_bridgeFresh targetNonzero
    (SquareRootReconditioning.bridge sourceNonzero second)
      small.secondSmall small.secondFresh small.secondBridge
  exact Equivalence.NamedEquivalent.trans firstToFresh
    (Equivalence.NamedEquivalent.trans freshToFresh
      secondToFresh.symm)

end Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

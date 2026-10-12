module
import Purelib.Data.Fin.Cardinality
import Purelib.Data.Fin.Product.Code
import Purelib.Data.Nat.Multiplication
public import Purelib.Data.Rat.Bounds.Mesh
import Purelib.Data.Rat.Grid.Index
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Grid.Enlarged
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Separation.Squarefree

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite grid packing of winding-one tracks

The original mesh assigns refined anchors to finite grid cells. Local
uniqueness makes that retained assignment injective and bounds its size.
-/

namespace Purelib.RootIsolation.Track.Packing

/-- Compute a finite grid bound for separated winding tracks of a squarefree polynomial.

The derivative uniqueness threshold determines the rational mesh side and hence the horizontal and vertical cell counts
of the original ambient box. -/
@[expose] public def packingBound
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (ambient : Box) : Nat :=
  let side := Data.Rat.Bounds.Mesh.meshSide (Dense.Gaussian.Derivative.Separation.Uniqueness.uniquenessDiagonalThreshold
    squarefree ambient)
  (Box.Grid.Enlarged.horizontalIntervals ambient side + 1) *
    (Box.Grid.Enlarged.verticalIntervals ambient side + 1)

/-- A separated finite track family satisfies its computed grid-packing bound.

Each supplied state is refined by its original corresponding track at the
same mesh request. The retained anchors determine bounded grid indices;
local squarefree uniqueness makes their row-major assignment injective. -/
public theorem family_card_le_packingBound
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) {count : Nat}
    (tracks : Fin count → Basic.WindingOneTrack p ambient)
    (states : (i : Fin count) → State.WindingOne.Basic.WindingOneState p ambient)
    (pairwiseSeparated : ∀ i j, i ≠ j →
      (states i).box.Separated (states j).box) :
    count ≤ Track.Packing.packingBound squarefree ambient := by
  let threshold := Dense.Gaussian.Derivative.Separation.Uniqueness.uniquenessDiagonalThreshold squarefree ambient
  let side := Data.Rat.Bounds.Mesh.meshSide threshold
  let horizontal := Box.Grid.Enlarged.horizontalIntervals ambient side
  let vertical := Box.Grid.Enlarged.verticalIntervals ambient side
  have thresholdPositive := Dense.Gaussian.Derivative.Separation.Uniqueness.uniquenessDiagonalThreshold_pos squarefree
    ambient
  have sidePositive : 0 < side := Data.Rat.Bounds.Mesh.meshSide_pos thresholdPositive
  let refined : (i : Fin count) → State.WindingOne.Basic.WindingOneState p ambient := fun i =>
    (tracks i).refine (states i) side sidePositive
  have refinedDiagonal (i : Fin count) :
      (refined i).box.diagonalSq ≤ side ^ 2 :=
    (tracks i).accurate (states i) side sidePositive
  let cell : Fin count → Fin (horizontal + 1) × Fin (vertical + 1) :=
    fun i =>
      (Data.Rat.Grid.Index.coordinateIndex ambient.xLower side (refined i).box.anchor.re horizontal,
       Data.Rat.Grid.Index.coordinateIndex ambient.yLower side (refined i).box.anchor.im vertical)
  have refinedCell (i : Fin count) :
      (refined i).box.Refines
        (Box.Grid.Enlarged.enlargedCell ambient side sidePositive.le
          (cell i).1 (cell i).2) := by
    exact Box.Grid.Enlarged.box_refines_anchor_enlargedCell sidePositive
      (refined i).refinesAmbient (refinedDiagonal i)
  have cellInjective : Function.Injective cell := by
    intro i j equal
    by_cases same : i = j
    · exact same
    · have separated := pairwiseSeparated i j same
      have refinedSeparated := separated.of_refines
        ((tracks i).nested (states i) side sidePositive)
        ((tracks j).nested (states j) side sidePositive)
      have first : (cell i).1 = (cell j).1 := congrArg Prod.fst equal
      have second : (cell i).2 = (cell j).2 := congrArg Prod.snd equal
      let common := Box.Grid.Enlarged.enlargedCell ambient side sidePositive.le
        (cell i).1 (cell i).2
      have leftCommon : (refined i).box.Refines common := refinedCell i
      have rightCommon : (refined j).box.Refines common := by
        have raw := refinedCell j
        rw [← first, ← second] at raw
        exact raw
      have commonSmall : common.diagonalSq < threshold := by
        rw [Box.Grid.Enlarged.enlargedCell_diagonalSq]
        exact Data.Rat.Bounds.Mesh.eight_meshSide_sq_lt thresholdPositive
      exact (Track.Separation.Squarefree.separated_tracks_not_supported_in_small_common_box
        degreePositive squarefree (tracks i) (tracks j) (refined i)
        (refined j) refinedSeparated common leftCommon rightCommon commonSmall).elim
  let code : Fin count → Fin ((horizontal + 1) * (vertical + 1)) := fun i =>
    ⟨(cell i).1.val * (vertical + 1) + (cell i).2.val, by
      have firstStep : (cell i).1.val * (vertical + 1) + (cell i).2.val <
          ((cell i).1.val + 1) * (vertical + 1) := by
        calc
          (cell i).1.val * (vertical + 1) + (cell i).2.val <
              (cell i).1.val * (vertical + 1) + (vertical + 1) :=
            Nat.add_lt_add_left (cell i).2.isLt _
          _ = ((cell i).1.val + 1) * (vertical + 1) := by
            rw [Data.Nat.Multiplication.right_distrib, Nat.one_mul]
      have secondStep : ((cell i).1.val + 1) * (vertical + 1) ≤
          (horizontal + 1) * (vertical + 1) :=
        Nat.mul_le_mul_right (vertical + 1) (cell i).1.isLt
      exact firstStep.trans_le secondStep⟩
  have codeInjective : Function.Injective code := by
    intro i j equal
    apply cellInjective
    apply Data.Fin.Product.Code.pairCode_injective
    exact Fin.ext_iff.mp equal
  simpa only [Track.Packing.packingBound, threshold, side, horizontal, vertical] using
    Data.Fin.Cardinality.fin_card_le_of_injective_direct code codeInjective

end Purelib.RootIsolation.Track.Packing

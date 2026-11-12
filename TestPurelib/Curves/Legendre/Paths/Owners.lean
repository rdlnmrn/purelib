module

import Purelib.Curves.Legendre.Paths.Owners
import Purelib.Data.Fin.Cases
import Purelib.Geometry.Rational.Box.Outside
import Purelib.Geometry.Rational.Box.Outside.Transport

/-! # Original Legendre owners and factor-move bridges on a shared rectangle -/

namespace TestPurelib.Curves.Legendre.Paths.Owners

open Purelib
open Purelib.Curves.Legendre.Paths
open Purelib.Geometry.Rational
open Purelib.RootIsolation

/-- The original moving root starts to the right of the zero projection at height one. -/
def source : Gaussian := gaussian (1 / 8) 1

/-- The original moving root ends to the left of the zero projection at the same height. -/
def target : Gaussian := gaussian (-1 / 8) 1

/-- One broad original rectangle strictly contains both moving-root endpoints. -/
def movingBox : Box where
  xLower := -1 / 2
  xUpper := 1 / 2
  yLower := 1 / 2
  yUpper := 3 / 2
  x_valid := by decide
  y_valid := by decide

/-- The retained rectangle is proper. -/
theorem proper : movingBox.Proper := by
  change (-1 / 2 : Coordinate) < 1 / 2 ∧ (1 / 2 : Coordinate) < 3 / 2
  decide

/-- The original source moving root lies strictly inside the same retained rectangle. -/
theorem inside : movingBox.StrictContains (branchPoint source 1) := by
  change (-1 / 2 : Coordinate) < 1 / 8 ∧ (1 / 8 : Coordinate) < 1 / 2 ∧
    (1 / 2 : Coordinate) < 1 ∧ (1 : Coordinate) < 3 / 2
  decide

/-- Each other original source branch lies outside the same retained rectangle. -/
theorem otherOutside (rootLabel : Fin 3) (different : rootLabel ≠ 1) :
    ¬ movingBox.Contains (branchPoint source rootLabel) := by
  rcases Data.Fin.Cases.three rootLabel with atZero | atOne | atTwo
  · subst rootLabel
    decide
  · exact (different atOne).elim
  · subst rootLabel
    decide

/-- Materialize the three original factor certificates once on the shared moving-root rectangle. -/
def factors : BranchFactors source movingBox 1 :=
  branchFactors source movingBox 1 inside
    (fun rootLabel different => Box.outsideSide (otherOutside rootLabel different))

/-- The original affine factors retain their exact computed side-gap bounds. -/
theorem factorBounds : (factors.get 0).val.bound = 1 / 4 ∧
    (factors.get 1).val.bound = 9 / 64 ∧ (factors.get 2).val.bound = 1 / 4 := by
  dsimp only [factors]
  rewrite [branchFactors_get, branchFactors_get, branchFactors_get,
    branchFactorCertificate_bound_of_ne _ _ _ _ _ _ (by decide),
    branchFactorCertificate_bound_self,
    branchFactorCertificate_bound_of_ne _ _ _ _ _ _ (by decide)]
  constructor
  · change ((1 / 2 - 0) ^ 2 : Coordinate) = 1 / 4
    decide
  · constructor
    · change min ((1 / 8 + 1 / 2) ^ 2 : Coordinate)
        (min ((1 / 2 - 1 / 8) ^ 2) (min ((1 - 1 / 2) ^ 2) ((3 / 2 - 1) ^ 2))) = 9 / 64
      decide +kernel
    · change ((1 - 1 / 2) ^ 2 : Coordinate) = 1 / 4
      decide

/-- The broad rectangle is centered at the projected crossing rather than at the source moving root. -/
example : movingBox.xLower ≠ source.re - 1 / 2 := by decide

/-- Both original moving-root endpoints remain in the same retained rectangle. -/
example : movingBox.StrictContains source ∧ movingBox.StrictContains target := by
  constructor
  · exact inside
  · change (-1 / 2 : Coordinate) < -1 / 8 ∧ (-1 / 8 : Coordinate) < 1 / 2 ∧
      (1 / 2 : Coordinate) < 1 ∧ (1 : Coordinate) < 3 / 2
    decide

/-- The original owner consumes the same materialized factor vector. -/
def owner : Owner.Local.Basic.LocalOwner (polynomial source) :=
  branchOwner source movingBox 1 proper factors

/-- The original owner retains the supplied rectangle. -/
example : owner.box = movingBox := by
  dsimp only [owner]
  exact branchOwner_box _ _ _ _ _

/-- The exact owner bound is the product of the original cached factor bounds. -/
example : owner.clearance.bound = 9 / 1024 := by
  dsimp only [owner]
  rewrite [branchOwner_clearance_bound]
  rewrite [factorBounds.1, factorBounds.2.1, factorBounds.2.2]
  decide +kernel

/-- The actual squared parameter displacement is below the retained moving-factor bound. -/
theorem displacementSmall :
    Data.Gaussian.Norm.Basic.normSq (source - target) < (factors.get 1).val.bound := by
  rewrite [factorBounds.2.1]
  change ((1 / 8 - (-1 / 8)) ^ 2 + (1 - 1) ^ 2 : Coordinate) < 9 / 64
  decide +kernel

/-- Construct the original Rouché bridge from those same cached source factors. -/
def bridge : Owner.Bridge.Basic.OwnerBridge (polynomial source) (polynomial target) :=
  branchBridge source target movingBox 1 proper factors displacementSmall

/-- The original bridge uses that same rectangle at both polynomial endpoints. -/
example : bridge.box = movingBox := by
  dsimp only [bridge]
  exact branchBridge_box _ _ _ _ _ _ _

/-- The bridge reuses the exact original source factor bounds. -/
example : bridge.leftClearance.bound = 9 / 1024 := by
  dsimp only [bridge]
  rewrite [branchBridge_leftClearance_bound]
  rewrite [factorBounds.1, factorBounds.2.1, factorBounds.2.2]
  decide +kernel

/-- The source and target original polynomial readings both have winding four on their shared box. -/
example :
    Polynomial.Winding.Box.Basic.quadrupledBoxWinding (polynomial source) bridge.box = 4 ∧
      Polynomial.Winding.Box.Basic.quadrupledBoxWinding (polynomial target) bridge.box = 4 :=
  ⟨bridge.leftWindingFour, bridge.rightWindingFour⟩

/-- The target-side bridge clearance is computed and strictly positive. -/
example : 0 < bridge.rightClearance.bound := bridge.rightClearance.positive

/-- The original branch order changes across the retained above-zero root motion. -/
example : (branchOrder source 0).forward 0 = 0 ∧ (branchOrder target 0).forward 0 = 1 := by decide

namespace RetainedSides

/-- The original zero-branch square has radius one quarter. -/
def box : Box where
  xLower := -1 / 4
  xUpper := 1 / 4
  yLower := -1 / 4
  yUpper := 1 / 4
  x_valid := by decide
  y_valid := by decide

/-- The original anchor root lies above the square at its right coordinate boundary. -/
def anchor : Gaussian := gaussian (1 / 4) 1

/-- The original source root has moved slightly to the right of the retained anchor. -/
def source : Gaussian := gaussian (3 / 8) 1

/-- The original target root takes one further step in the same direction. -/
def target : Gaussian := gaussian (1 / 2) 1

/-- The retained anchor outside side is the top side with gap three quarters. -/
def anchorSide : Box.OutsideSide box anchor := .top (by decide)

/-- Transport retains that same top side for the original source root. -/
def sourceSide : Box.OutsideSide box source :=
  anchorSide.rebase source (1 / 8) (by decide) (by decide +kernel)

/-- The retained transported side keeps its actual squared top gap. -/
example : sourceSide.margin = 9 / 16 := by decide +kernel

/-- The generic transport bound is paid by that same original transported side. -/
example : (anchorSide.gap - 1 / 8) ^ 2 ≤ sourceSide.margin :=
  anchorSide.rebase_margin_lower source (1 / 8) _ _

/-- The original source moving root is outside the retained zero-branch square. -/
theorem sourceOutside : ¬ box.Contains source := by decide

/-- Reselecting at the source would instead retain the right side's much smaller squared gap. -/
example : (Box.outsideSide sourceOutside).margin = 1 / 64 := by decide +kernel

/-- That reselected side cannot pay for the actual next parameter step. -/
example : ¬ Data.Gaussian.Norm.Basic.normSq (source - target) < (Box.outsideSide sourceOutside).margin := by
  decide +kernel

/-- The original retained square is proper. -/
theorem proper : box.Proper := by
  change (-1 / 4 : Coordinate) < 1 / 4 ∧ (-1 / 4 : Coordinate) < 1 / 4
  decide

/-- The labelled original zero branch lies strictly inside its same retained square. -/
theorem inside : box.StrictContains (branchPoint source 0) := by
  change (-1 / 4 : Coordinate) < 0 ∧ (0 : Coordinate) < 1 / 4 ∧
    (-1 / 4 : Coordinate) < 0 ∧ (0 : Coordinate) < 1 / 4
  decide

/-- The fixed original one branch lies to the right of the retained square. -/
def oneSide : Box.OutsideSide box (1 : Gaussian) := .right (by decide)

/-- The original factor family selects its retained source top side and fixed one side. -/
def outsideSides (rootLabel : Fin 3) (different : rootLabel ≠ 0) :
    Box.OutsideSide box (branchPoint source rootLabel) :=
  if moving : rootLabel = 1 then moving.symm ▸ sourceSide
  else
    have fixed : rootLabel = 2 := by
      rcases Data.Fin.Cases.three rootLabel with zero | one | two
      · exact (different zero).elim
      · exact (moving one).elim
      · exact two
    fixed.symm ▸ oneSide

/-- Materialize the original factors using the actual retained outside-side data. -/
def factors : BranchFactors source box 0 := branchFactors source box 0 inside outsideSides

/-- The original moving factor consumes the same transported top side and its exact bound. -/
theorem movingBound : (factors.get 1).val.bound = 9 / 16 := by
  dsimp only [factors]
  rewrite [branchFactors_get, branchFactorCertificate_bound_of_ne _ _ _ _ _ _ (by decide)]
  decide +kernel

/-- The actual source-to-target displacement is below the same retained moving-factor clearance. -/
theorem displacementSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < (factors.get 1).val.bound := by
  rewrite [movingBound]
  change ((3 / 8 - 1 / 2) ^ 2 + (1 - 1) ^ 2 : Coordinate) < 9 / 16
  decide +kernel

/-- The original source-to-target bridge consumes that same retained factor family. -/
def bridge : Owner.Bridge.Basic.OwnerBridge (polynomial source) (polynomial target) :=
  branchBridge source target box 0 proper factors displacementSmall

/-- The resulting original bridge retains the same fixed-branch square and both exact winding laws. -/
example : bridge.box = box ∧
    Polynomial.Winding.Box.Basic.quadrupledBoxWinding (polynomial source) bridge.box = 4 ∧
    Polynomial.Winding.Box.Basic.quadrupledBoxWinding (polynomial target) bridge.box = 4 :=
  ⟨branchBridge_box _ _ _ _ _ _ _, bridge.leftWindingFour, bridge.rightWindingFour⟩

end RetainedSides

end TestPurelib.Curves.Legendre.Paths.Owners

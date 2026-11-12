module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.Site

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

@[expose] public section

/-!
# Finite endpoints of the standard reference bridges

The left endpoint of every standard cut is finite in both degree shapes,
including the final reference cut.  Its executable representative is exactly
the indexed root at position `2 * cutIndex`, not an independently chosen root.
These identities tie the owner-closed bridge geometry to the original cuts.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

/-- The left index of every standard cut is strictly below the original polynomial degree. -/
theorem pair_left_lt_degree {genus : Nat} (curve : HyperellipticCurve genus)
    (index : Fin (genus + 1)) :
    (standardPair index).left.val < curve.polynomial.natDegree := by
  have bound := index.isLt
  cases curve.degreeShape with
  | odd equal => rw [equal]; change 2 * index.val < 2 * genus + 1; omega0
  | even equal => rw [equal]; change 2 * index.val < 2 * genus + 2; omega0

/-- The original left endpoint of every standard cut is a finite ramification site. -/
theorem pair_left_ne_infinity_ofData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin (genus + 1)) :
    (configurationOfData curve branches).siteAt (standardPair index).left ≠
      .infinity := by
  intro equal
  have codes := congrArg code equal
  rw [configurationOfData_siteAt_code] at codes
  change (standardPair index).left.val = (configurationOfData curve
    branches).branches.siteCount at codes
  rw [(configurationOfData curve branches).branches.count_eq] at codes
  exact (Nat.ne_of_lt (pair_left_lt_degree
    curve index)) codes

/-- Finite left endpoint, including the reference cut in odd degree. -/
def pairLeftIndexOfData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin (genus + 1)) :
    Data.Index (configurationOfData curve branches).branches :=
  Site.index ((configurationOfData curve branches).siteAt (standardPair
    index).left)
    (pair_left_ne_infinity_ofData curve
      branches index)

/-- The retained left site is exactly the finite occurrence recovered by the original index operation. -/
theorem siteAt_pair_left {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin (genus + 1)) :
    (configurationOfData curve branches).siteAt (standardPair index).left =
      .finite (pairLeftIndexOfData curve
        branches index) :=
  index_spec _
    (pair_left_ne_infinity_ofData curve
    branches index)

/-- The retained left root occurrence has index twice the original cut index. -/
theorem pairLeftIndexOfData_val {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin (genus + 1)) :
    (pairLeftIndexOfData curve branches
      index).val = 2 * index.val := by
  have codes := congrArg code
    (siteAt_pair_left curve branches index)
  rw [configurationOfData_siteAt_code] at codes
  exact codes.symm

/-- Restricting to a basis cut recovers its original standard left endpoint index. -/
theorem pairLeftIndexOfData_basis {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin genus) :
    pairLeftIndexOfData curve branches
      (Fin.castSucc index) = basisPairLeftIndexOfData curve branches index :=
  finite.inj ((siteAt_pair_left curve
    branches (Fin.castSucc index)).symm.trans
    (configurationOfData_siteAt_basisPair_left curve branches index))

/-- Every original basis cut left endpoint differs from the reference cut left endpoint. -/
theorem basisLeft_ne_referenceLeft {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin genus) :
    basisPairLeftIndexOfData curve branches index ≠
      pairLeftIndexOfData curve branches
      (Fin.last genus) := by
  intro equal
  rw [← pairLeftIndexOfData_basis] at equal
  have values := congrArg Fin.val equal
  rw [pairLeftIndexOfData_val,
    pairLeftIndexOfData_val] at values
  have bound := index.isLt
  change 2 * index.val = 2 * genus at values
  omega0

end Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

/-- A cut with the displayed finite left endpoint selects that same original occurrence as representative. -/
theorem Geometry.representative_of_left {genus : Nat} {curve : HyperellipticCurve genus}
    {branches : Data curve} (geometry : Cuts.Geometry curve branches)
    (index : Data.Index branches) (equal : geometry.leftSite = .finite index) :
    Geometry.representative geometry = index := by
  rcases geometry with ⟨left, right, different, certificate⟩
  cases certificate with
  | finite => exact finite.inj equal
  | toInfinity => exact finite.inj equal
  | fromInfinity => cases equal
  | linearToInfinity => exact finite.inj equal
  | infinityToLinear => cases equal

/-- The standard cut representative is exactly its original retained left endpoint occurrence. -/
theorem standardCutRepresentative {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) (index : Fin (genus + 1)) :
    Geometry.representative ((Cuts.systemOfData curve branches).cutAt index) =
      BranchConfiguration.pairLeftIndexOfData curve branches
        index := by
  apply Geometry.representative_of_left
  exact ((Cuts.systemOfData curve branches).left_eq index).trans
    (BranchConfiguration.siteAt_pair_left curve branches index)

end Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchCutLifts

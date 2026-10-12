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
theorem pair_left_lt_degree {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (index : Fin (genus + 1)) :
    (BranchConfiguration.standardPair index).left.val < curve.polynomial.natDegree := by
  have bound := index.isLt
  cases curve.degreeShape with
  | odd equal => rw [equal]; change 2 * index.val < 2 * genus + 1; omega0
  | even equal => rw [equal]; change 2 * index.val < 2 * genus + 2; omega0

/-- The original left endpoint of every standard cut is a finite ramification site. -/
theorem pair_left_ne_infinity_ofData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin (genus + 1)) :
    (BranchConfiguration.configurationOfData curve branches).siteAt (BranchConfiguration.standardPair index).left ≠
      .infinity := by
  intro equal
  have codes := congrArg Site.code equal
  rw [BranchConfiguration.configurationOfData_siteAt_code] at codes
  change (BranchConfiguration.standardPair index).left.val = (BranchConfiguration.configurationOfData curve
    branches).branches.siteCount at codes
  rw [(BranchConfiguration.configurationOfData curve branches).branches.count_eq] at codes
  exact (Nat.ne_of_lt (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pair_left_lt_degree
    curve index)) codes

/-- Finite left endpoint, including the reference cut in odd degree. -/
def pairLeftIndexOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin (genus + 1)) :
    Data.Index (BranchConfiguration.configurationOfData curve branches).branches :=
  Site.index ((BranchConfiguration.configurationOfData curve branches).siteAt (BranchConfiguration.standardPair
    index).left)
    (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pair_left_ne_infinity_ofData curve
      branches index)

/-- The retained left site is exactly the finite occurrence recovered by the original index operation. -/
theorem siteAt_pair_left {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin (genus + 1)) :
    (BranchConfiguration.configurationOfData curve branches).siteAt (BranchConfiguration.standardPair index).left =
      .finite (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve
        branches index) :=
  Site.index_spec _
    (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pair_left_ne_infinity_ofData curve
    branches index)

/-- The retained left root occurrence has index twice the original cut index. -/
theorem pairLeftIndexOfData_val {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin (genus + 1)) :
    (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve branches
      index).val = 2 * index.val := by
  have codes := congrArg Site.code
    (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.siteAt_pair_left curve branches index)
  rw [BranchConfiguration.configurationOfData_siteAt_code] at codes
  exact codes.symm

/-- Restricting to a basis cut recovers its original standard left endpoint index. -/
theorem pairLeftIndexOfData_basis {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) :
    Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve branches
      (Fin.castSucc index) = BranchConfiguration.basisPairLeftIndexOfData curve branches index :=
  finite.inj ((Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.siteAt_pair_left curve
    branches (Fin.castSucc index)).symm.trans
    (BranchConfiguration.configurationOfData_siteAt_basisPair_left curve branches index))

/-- Every original basis cut left endpoint differs from the reference cut left endpoint. -/
theorem basisLeft_ne_referenceLeft {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus) :
    BranchConfiguration.basisPairLeftIndexOfData curve branches index ≠
      Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve branches
      (Fin.last genus) := by
  intro equal
  rw [← Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData_basis] at equal
  have values := congrArg Fin.val equal
  rw [Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData_val,
    Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData_val] at values
  have bound := index.isLt
  change 2 * index.val = 2 * genus at values
  omega0

end Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

/-- A cut with the displayed finite left endpoint selects that same original occurrence as representative. -/
theorem Geometry.representative_of_left {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} (geometry : Cuts.Geometry curve branches)
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
theorem standardCutRepresentative {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin (genus + 1)) :
    Geometry.representative ((Cuts.systemOfData curve branches).cutAt index) =
      Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve branches
        index := by
  apply Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchCutLifts.Geometry.representative_of_left
  exact ((Cuts.systemOfData curve branches).left_eq index).trans
    (Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchConfiguration.siteAt_pair_left curve branches index)

end Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives.BranchCutLifts

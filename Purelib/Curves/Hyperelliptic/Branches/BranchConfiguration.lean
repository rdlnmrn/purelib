module
import Purelib.Data.Nat.Division
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

public import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Fin
import Init.Data.Fin.Basic
public import Init.Data.Function
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

@[expose] public section

/-!
# Degree-shaped finite branch configurations

The finite root family is reindexed as the `2g+2` ramification sites of the
double cover.  In odd degree the last site is the ramified point at infinity;
in even degree every site is finite.  Consecutive sites are paired into the
standard `g+1` branch-cut labels, with finite proofs of injectivity, coverage,
and endpoint distinction.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

set_option genInjectivity false in
/-- One ramification site: an indexed finite polynomial root or the point at infinity used only by the odd-degree shape.

Finite sites retain their original branch-family index. The infinity constructor is a separate semantic endpoint, used
only by the curve degree shape. -/
inductive Site {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : Type
  /-- A finite root occurrence indexed by the original retained branch family. -/ | finite (index : Data.Index branches)
  /-- The ramified point at infinity used by the odd-degree shape. -/ | infinity

constructive_injectivity Site

namespace Site

section
open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.Site
/-- Numerical code used to prove that the shape-dependent enumeration is injective without deciding equality of semantic
root data. -/
def code {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} : Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches ->
      Nat
  | .finite index => index.val
  | .infinity => branches.siteCount

/-- Read the retained finite root name, returning none at infinity. -/
def name? {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} : Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches ->
      Option BranchIsolation.Named
  | .finite index => some (Data.name branches index)
  | .infinity => none

/-- Read the retained coherent finite root name, returning none at infinity. -/
def coherentName? {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} : Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches ->
      Option Coherent.CoherentNamed
  | .finite index => some (Data.coherentName branches index)
  | .infinity => none

/-- Read the exact finite root-track anchor, returning none at infinity. -/
def anchor? {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} : Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches ->
      Option Data.Gaussian.Basic.Canonical
  | .finite index => some (Data.anchor branches index)
  | .infinity => none

/-- Extract the finite root index from a site proved not to be infinity. -/
def index {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} (site : Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve
      branches)
    (notInfinity : site ≠ .infinity) : Data.Index branches :=
  match site with
  | .finite index => index
  | .infinity => (notInfinity rfl).elim

end

/-- A site proved finite is exactly the finite constructor on its extracted original root index. -/
theorem index_spec {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    (site : Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches) (notInfinity : site ≠ .infinity) :
    site = .finite (site.index notInfinity) := by
  cases site with
  | finite => rfl
  | infinity => exact (notInfinity rfl).elim

end Site

/-- Odd-degree enumeration: all finite roots followed by infinity. -/
def oddAt {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (count_eq : branches.siteCount = 2 * genus + 1) :
    Fin (2 * genus + 2) -> Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches :=
  Data.Fin.lastCases .infinity fun index =>
    .finite (Fin.cast count_eq.symm index)

/-- The odd-degree enumeration retains each numerical position as its site code. -/
@[simp] theorem oddAt_code {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (count_eq : branches.siteCount = 2 * genus + 1)
    (position : Fin (2 * genus + 2)) :
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt branches count_eq position).code = position.val :=
      by
  rcases Data.Fin.lastCases_split position with equal | ⟨index, equal⟩
  · subst position
    unfold Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt
    rw [Data.Fin.lastCases_last]
    unfold Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code
    rw [Fin.val_last]
    exact count_eq
  · subst position
    unfold Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt
    rw [Data.Fin.lastCases_castSucc]
    unfold Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code
    rfl

/-- Distinct positions select distinct sites in the odd-degree enumeration. -/
theorem oddAt_injective {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (count_eq : branches.siteCount = 2 * genus + 1) :
    Function.Injective (Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt branches count_eq) := by
  intro left right equal
  apply Fin.ext
  have codes := congrArg Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code equal
  rw [Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt_code,
    Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt_code] at codes
  exact codes

/-- Even-degree enumeration: every ramification site is a finite root. -/
def evenAt {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (count_eq : branches.siteCount = 2 * genus + 2) :
    Fin (2 * genus + 2) -> Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches :=
  fun position => .finite (Fin.cast count_eq.symm position)

/-- The even-degree enumeration retains each numerical position as its site code. -/
@[simp] theorem evenAt_code {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (count_eq : branches.siteCount = 2 * genus + 2)
    (position : Fin (2 * genus + 2)) :
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt branches count_eq position).code = position.val :=
      by
  unfold Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt
    Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code
  rfl

/-- Distinct positions select distinct finite sites in the even-degree enumeration. -/
theorem evenAt_injective {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (count_eq : branches.siteCount = 2 * genus + 2) :
    Function.Injective (Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt branches count_eq) := by
  intro left right equal
  apply Fin.ext
  have codes := congrArg Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code equal
  rw [Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt_code,
    Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt_code] at codes
  exact codes

set_option genInjectivity false in
/-- The automatically isolated and exactly reindexed branch configuration.

The retained finite branch family supplies every indexed ramification site. The ordered site map keeps its original
source labels and its explicit injectivity witness. -/
structure Configuration {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The original degree-complete retained finite root family. -/ branches : BranchIsolation.Data curve
  /-- The ordered ramification-site family, including infinity only for odd degree. -/ siteAt : Fin (2 * genus + 2) ->
    Curves.Hyperelliptic.Branches.BranchConfiguration.Site curve branches
  /-- Different positions in the retained configuration select different sites. -/ siteAt_injective : Function.Injective
    siteAt

constructive_injectivity Configuration

/-- Reindex the retained finite root family by the curve degree shape.

Odd degree appends the ramified infinity site; even degree uses only finite sites. Both cases preserve the original
branch data and certify injectivity. -/
def configurationOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : Curves.Hyperelliptic.Branches.BranchConfiguration.Configuration curve :=
      by
  cases curve.degreeShape with
  | odd degreeEqual =>
      have countEqual : branches.siteCount = 2 * genus + 1 :=
        branches.count_eq.trans degreeEqual
      exact
        { branches := branches
          siteAt := Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt branches countEqual
          siteAt_injective := Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt_injective branches countEqual }
  | even degreeEqual =>
      have countEqual : branches.siteCount = 2 * genus + 2 :=
        branches.count_eq.trans degreeEqual
      exact
        { branches := branches
          siteAt := Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt branches countEqual
          siteAt_injective := Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt_injective branches countEqual }

/-- Automatically isolated canonical branch configuration. -/
def configuration {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Curves.Hyperelliptic.Branches.BranchConfiguration.Configuration curve :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve (BranchIsolation.data curve)

/-- The shape-selected enumeration retains the original numerical site position. -/
@[simp] theorem configurationOfData_siteAt_code {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (position : Fin (2 * genus + 2)) :
    ((Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt position).code =
      position.val := by
  cases curve with
  | mk polynomial nonzero squarefree degreeShape =>
      cases degreeShape with
      | odd degreeEqual =>
          exact Curves.Hyperelliptic.Branches.BranchConfiguration.oddAt_code branches
            (branches.count_eq.trans degreeEqual) position
      | even degreeEqual =>
          exact Curves.Hyperelliptic.Branches.BranchConfiguration.evenAt_code branches
            (branches.count_eq.trans degreeEqual) position

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration in
/-- The canonical branch configuration preserves the numerical position as the site code, independently of the odd/even
degree shape. -/
@[simp] theorem configuration_siteAt_code {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (position : Fin (2 * genus + 2)) :
    ((configuration curve).siteAt position).code = position.val :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData_siteAt_code curve (BranchIsolation.data curve)
    position

/-! ## Standard finite pairing into branch cuts -/

set_option genInjectivity false in
/-- The two consecutive labels assigned to one of the `g+1` standard cuts.

Both labels belong to the same original degree-shaped ramification enumeration. Their inequality distinguishes the two
endpoints without replacing either index. -/
structure Pair (genus : Nat) where
  /-- The first finite position in the retained pair of ramification sites. -/ left : Fin (2 * genus + 2)
  /-- The second finite position in the retained pair of ramification sites. -/ right : Fin (2 * genus + 2)
  /-- The two retained ramification positions are distinct. -/ different : left ≠ right

constructive_injectivity Pair

/-- Pair each even numerical ramification position with its immediate odd successor. -/
def standardPair {genus : Nat} (index : Fin (genus + 1)) : Curves.Hyperelliptic.Branches.BranchConfiguration.Pair genus
  where
  left := ⟨2 * index.val, by
    have bound := index.isLt
    omega0⟩
  right := ⟨2 * index.val + 1, by
    have bound := index.isLt
    omega0⟩
  different := by
    intro equal
    have values := congrArg Fin.val equal
    change 2 * index.val = 2 * index.val + 1 at values
    omega0

/-- Both endpoints of each of the first `g` standard pairs occur strictly before the polynomial degree. In odd degree
this excludes the final ramification site at infinity. -/
theorem basisPair_left_lt_degree {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).left.val <
      curve.polynomial.natDegree := by
  have bound := index.isLt
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      simp only [Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair, Fin.val_castSucc]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      simp only [Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair, Fin.val_castSucc]
      omega0

/-- The second endpoint of each basis cut lies strictly below the defining polynomial degree. -/
theorem basisPair_right_lt_degree {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).right.val <
      curve.polynomial.natDegree := by
  have bound := index.isLt
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      simp only [Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair, Fin.val_castSucc]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      simp only [Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair, Fin.val_castSucc]
      omega0

/-- The first endpoint of any basis cut is a finite root occurrence for any explicit degree-complete branch family. -/
theorem basisPair_left_ne_infinity_ofData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt
        (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).left ≠
      .infinity := by
  intro equal
  have codes := congrArg Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code equal
  rw [Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData_siteAt_code] at codes
  change (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).left.val =
    (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches.siteCount at codes
  rw [(Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches.count_eq] at codes
  exact (Nat.ne_of_lt (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_left_lt_degree curve index)) codes

/-- The second endpoint of any basis cut is a finite root occurrence for any explicit degree-complete branch family. -/
theorem basisPair_right_ne_infinity_ofData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt
        (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).right ≠
      .infinity := by
  intro equal
  have codes := congrArg Curves.Hyperelliptic.Branches.BranchConfiguration.Site.code equal
  rw [Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData_siteAt_code] at codes
  change (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).right.val =
    (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches.siteCount at codes
  rw [(Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches.count_eq] at codes
  exact (Nat.ne_of_lt (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_right_lt_degree curve index)) codes

/-- Root index of the first endpoint of a standard basis cut in explicit branch data. -/
def basisPairLeftIndexOfData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    Data.Index (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.Site.index
    ((Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt
      (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).left)
    (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_left_ne_infinity_ofData curve branches index)

/-- Root index of the second endpoint of a standard basis cut in explicit branch data. -/
def basisPairRightIndexOfData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    Data.Index (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.Site.index
    ((Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt
      (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).right)
    (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_right_ne_infinity_ofData curve branches index)

/-- The first endpoint of a retained-data basis cut is its exact extracted finite root occurrence. -/
@[simp] theorem configurationOfData_siteAt_basisPair_left {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt
        (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).left =
      .finite (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairLeftIndexOfData curve branches index)
        :=
  by
    unfold Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairLeftIndexOfData
    exact Curves.Hyperelliptic.Branches.BranchConfiguration.Site.index_spec _
      (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_left_ne_infinity_ofData curve branches index)

/-- The second endpoint of a retained-data basis cut is its exact extracted finite root occurrence. -/
@[simp] theorem configurationOfData_siteAt_basisPair_right {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    (Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).siteAt
        (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc index)).right =
      .finite (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairRightIndexOfData curve branches index)
        :=
  by
    unfold Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairRightIndexOfData
    exact Curves.Hyperelliptic.Branches.BranchConfiguration.Site.index_spec _
      (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_right_ne_infinity_ofData curve branches index)

/-! The automatic names below retain the original public interface. -/

section
open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
/-- The first endpoint of each canonical basis cut is finite. -/
theorem basisPair_left_ne_infinity {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc
      index)).left ≠
      .infinity :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_left_ne_infinity_ofData curve (BranchIsolation.data curve)
    index

/-- The second endpoint of each canonical basis cut is finite. -/
theorem basisPair_right_ne_infinity {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc
      index)).right ≠
      .infinity :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.basisPair_right_ne_infinity_ofData curve (BranchIsolation.data
    curve) index

/-- Extract the original finite root index of the first canonical basis-cut endpoint. -/
def basisPairLeftIndex {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (index : Fin genus) : Data.Index (configuration curve).branches :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairLeftIndexOfData curve (BranchIsolation.data curve) index

/-- Extract the original finite root index of the second canonical basis-cut endpoint. -/
def basisPairRightIndex {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (index : Fin genus) : Data.Index (configuration curve).branches :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairRightIndexOfData curve (BranchIsolation.data curve) index

/-- The first canonical basis-cut site is its exact extracted finite root occurrence. -/
@[simp] theorem configuration_siteAt_basisPair_left {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc
      index)).left =
      .finite (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairLeftIndex curve index) :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData_siteAt_basisPair_left curve
    (BranchIsolation.data curve) index

/-- The second canonical basis-cut site is its exact extracted finite root occurrence. -/
@[simp] theorem configuration_siteAt_basisPair_right {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair (Fin.castSucc
      index)).right =
      .finite (Curves.Hyperelliptic.Branches.BranchConfiguration.basisPairRightIndex curve index) :=
  Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData_siteAt_basisPair_right curve
    (BranchIsolation.data curve) index

end

/-- Pair containing a displayed branch label. -/
def pairOf {genus : Nat} (position : Fin (2 * genus + 2)) :
    Fin (genus + 1) :=
  ⟨position.val / 2, by
    have bound := position.isLt
    omega0⟩

open Purelib.Data.Nat in
/-- Every branch label is exactly the left or right endpoint of its computed standard pair.

Division by two retains the original pair index. The exact quotient-remainder equation shows that the displayed label is
its pair's even endpoint or its immediate odd successor. -/
theorem standardPair_covers {genus : Nat}
    (position : Fin (2 * genus + 2)) :
    position = (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair
      (Curves.Hyperelliptic.Branches.BranchConfiguration.pairOf position)).left \/
      position = (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair
        (Curves.Hyperelliptic.Branches.BranchConfiguration.pairOf position)).right := by
  have remainderBound : position.val % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have division := Division.mod_add_div position.val 2
  by_cases even : position.val % 2 = 0
  · left
    apply Fin.ext
    dsimp [Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair,
      Curves.Hyperelliptic.Branches.BranchConfiguration.pairOf]
    omega0
  · have odd : position.val % 2 = 1 := by omega0
    right
    apply Fin.ext
    dsimp [Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair,
      Curves.Hyperelliptic.Branches.BranchConfiguration.pairOf]
    omega0

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
/-- The two semantic endpoints of one standard cut are distinct because the global branch enumeration is injective. -/
theorem cutEndpoints_different {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (configuration :
      Curves.Hyperelliptic.Branches.BranchConfiguration.Configuration curve)
    (index : Fin (genus + 1)) :
    configuration.siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).left ≠
      configuration.siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).right := by
  intro equal
  exact (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).different
    (configuration.siteAt_injective equal)

/-- Every finite endpoint of a standard cut retains its persistent root name; the odd-degree infinity endpoint is
represented by `none`. -/
def cutEndpointNames {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (configuration :
      Curves.Hyperelliptic.Branches.BranchConfiguration.Configuration curve)
    (index : Fin (genus + 1)) : Option BranchIsolation.Named × Option Named :=
  ((configuration.siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).left).name?,
    (configuration.siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).right).name?)

/-- Coherent versions of the same finite endpoint names, ready for arithmetic composition with the analytic layer. -/
def cutEndpointCoherentNames {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (configuration :
      Curves.Hyperelliptic.Branches.BranchConfiguration.Configuration curve)
    (index : Fin (genus + 1)) :
    Option Coherent.CoherentNamed ×
      Option Coherent.CoherentNamed :=
  ((configuration.siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).left).coherentName?,
    (configuration.siteAt (Curves.Hyperelliptic.Branches.BranchConfiguration.standardPair index).right).coherentName?)

end Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration

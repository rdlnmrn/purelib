import CCL.Riemann.BranchIsolation
import mathlib.Data.ConstructiveFin

/-!
# Degree-shaped finite branch configurations

The finite root family is reindexed as the `2g+2` ramification sites of the
double cover.  In odd degree the last site is the ramified point at infinity;
in even degree every site is finite.  Consecutive sites are paired into the
standard `g+1` branch-cut labels, with finite proofs of injectivity, coverage,
and endpoint distinction.
-/

namespace CCL.Riemann.BranchConfiguration

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchIsolation

/-- One ramification site: an indexed finite polynomial root or the point at
infinity used only by the odd-degree shape. -/
inductive Site {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) : Type
  | finite (index : Data.Index branches)
  | infinity

namespace Site

/-- Numerical code used to prove that the shape-dependent enumeration is
injective without deciding equality of semantic root data. -/
def code {genus : Nat} {curve : HyperellipticCurve genus}
    {branches : Data curve} : Site curve branches -> Nat
  | .finite index => index.val
  | .infinity => branches.siteCount

def name? {genus : Nat} {curve : HyperellipticCurve genus}
    {branches : Data curve} : Site curve branches -> Option Named
  | .finite index => some (Data.name branches index)
  | .infinity => none

def coherentName? {genus : Nat} {curve : HyperellipticCurve genus}
    {branches : Data curve} : Site curve branches ->
      Option CCL.ProgressiveCoherence.CoherentNamed
  | .finite index => some (Data.coherentName branches index)
  | .infinity => none

def anchor? {genus : Nat} {curve : HyperellipticCurve genus}
    {branches : Data curve} : Site curve branches ->
      Option RFAP.ConstructiveGaussian.Gaussian
  | .finite index => some (Data.anchor branches index)
  | .infinity => none

/-- Extract the finite root index from a site proved not to be infinity. -/
def finiteIndex {genus : Nat} {curve : HyperellipticCurve genus}
    {branches : Data curve} (site : Site curve branches)
    (notInfinity : site ≠ .infinity) : Data.Index branches :=
  match site with
  | .finite index => index
  | .infinity => (notInfinity rfl).elim

theorem finiteIndex_spec {genus : Nat}
    {curve : HyperellipticCurve genus} {branches : Data curve}
    (site : Site curve branches) (notInfinity : site ≠ .infinity) :
    site = .finite (site.finiteIndex notInfinity) := by
  cases site with
  | finite => rfl
  | infinity => exact (notInfinity rfl).elim

end Site

/-- Odd-degree enumeration: all finite roots followed by infinity. -/
def oddAt {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve)
    (count_eq : branches.siteCount = 2 * genus + 1) :
    Fin (2 * genus + 2) -> Site curve branches :=
  QuotientFreeFin.lastCases .infinity fun index =>
    .finite (Fin.cast count_eq.symm index)

@[simp] theorem oddAt_code {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (count_eq : branches.siteCount = 2 * genus + 1)
    (position : Fin (2 * genus + 2)) :
    (oddAt branches count_eq position).code = position.val := by
  rcases QuotientFreeFin.lastCases_split position with equal | ⟨index, equal⟩
  · subst position
    unfold oddAt
    rw [QuotientFreeFin.lastCases_last]
    unfold Site.code
    rw [Fin.val_last]
    exact count_eq
  · subst position
    unfold oddAt
    rw [QuotientFreeFin.lastCases_castSucc]
    unfold Site.code
    rfl

theorem oddAt_injective {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (count_eq : branches.siteCount = 2 * genus + 1) :
    Function.Injective (oddAt branches count_eq) := by
  intro left right equal
  apply Fin.ext
  have codes := congrArg Site.code equal
  rw [oddAt_code, oddAt_code] at codes
  exact codes

/-- Even-degree enumeration: every ramification site is a finite root. -/
def evenAt {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve)
    (count_eq : branches.siteCount = 2 * genus + 2) :
    Fin (2 * genus + 2) -> Site curve branches :=
  fun position => .finite (Fin.cast count_eq.symm position)

@[simp] theorem evenAt_code {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (count_eq : branches.siteCount = 2 * genus + 2)
    (position : Fin (2 * genus + 2)) :
    (evenAt branches count_eq position).code = position.val := by
  unfold evenAt Site.code
  rfl

theorem evenAt_injective {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (count_eq : branches.siteCount = 2 * genus + 2) :
    Function.Injective (evenAt branches count_eq) := by
  intro left right equal
  apply Fin.ext
  have codes := congrArg Site.code equal
  rw [evenAt_code, evenAt_code] at codes
  exact codes

/-- The automatically isolated and exactly reindexed branch configuration. -/
structure Configuration {genus : Nat} (curve : HyperellipticCurve genus) where
  branches : Data curve
  siteAt : Fin (2 * genus + 2) -> Site curve branches
  siteAt_injective : Function.Injective siteAt

def configurationOfData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) : Configuration curve := by
  cases curve.degreeShape with
  | odd degreeEqual =>
      have countEqual : branches.siteCount = 2 * genus + 1 :=
        branches.count_eq.trans degreeEqual
      exact
        { branches := branches
          siteAt := oddAt branches countEqual
          siteAt_injective := oddAt_injective branches countEqual }
  | even degreeEqual =>
      have countEqual : branches.siteCount = 2 * genus + 2 :=
        branches.count_eq.trans degreeEqual
      exact
        { branches := branches
          siteAt := evenAt branches countEqual
          siteAt_injective := evenAt_injective branches countEqual }

/-- Automatically isolated canonical branch configuration. -/
def configuration {genus : Nat} (curve : HyperellipticCurve genus) :
    Configuration curve :=
  configurationOfData curve (data curve)

@[simp] theorem configurationOfData_siteAt_code {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (position : Fin (2 * genus + 2)) :
    ((configurationOfData curve branches).siteAt position).code =
      position.val := by
  cases curve with
  | mk polynomial nonzero squarefree degreeShape =>
      cases degreeShape with
      | odd degreeEqual =>
          exact oddAt_code branches
            (branches.count_eq.trans degreeEqual) position
      | even degreeEqual =>
          exact evenAt_code branches
            (branches.count_eq.trans degreeEqual) position

/-- The canonical branch configuration preserves the numerical position as
the site code, independently of the odd/even degree shape. -/
@[simp] theorem configuration_siteAt_code {genus : Nat}
    (curve : HyperellipticCurve genus) (position : Fin (2 * genus + 2)) :
    ((configuration curve).siteAt position).code = position.val :=
  configurationOfData_siteAt_code curve (data curve) position

/-! ## Standard finite pairing into branch cuts -/

/-- The two consecutive labels assigned to one of the `g+1` standard cuts. -/
structure Pair (genus : Nat) where
  left : Fin (2 * genus + 2)
  right : Fin (2 * genus + 2)
  different : left ≠ right

def standardPair {genus : Nat} (index : Fin (genus + 1)) : Pair genus where
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

/-- Both endpoints of each of the first `g` standard pairs occur strictly
before the polynomial degree.  In odd degree this excludes the final
ramification site at infinity. -/
theorem basisPair_left_lt_degree {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    (standardPair (Fin.castSucc index)).left.val <
      curve.polynomial.natDegree := by
  have bound := index.isLt
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      simp only [standardPair, Fin.val_castSucc]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      simp only [standardPair, Fin.val_castSucc]
      omega0

theorem basisPair_right_lt_degree {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    (standardPair (Fin.castSucc index)).right.val <
      curve.polynomial.natDegree := by
  have bound := index.isLt
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      simp only [standardPair, Fin.val_castSucc]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      simp only [standardPair, Fin.val_castSucc]
      omega0

/-- The first endpoint of any basis cut is a finite root occurrence for any
explicit degree-complete branch family. -/
theorem basisPair_left_ne_infinity_ofData {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (index : Fin genus) :
    (configurationOfData curve branches).siteAt
        (standardPair (Fin.castSucc index)).left ≠
      .infinity := by
  intro equal
  have codes := congrArg Site.code equal
  rw [configurationOfData_siteAt_code] at codes
  change (standardPair (Fin.castSucc index)).left.val =
    (configurationOfData curve branches).branches.siteCount at codes
  rw [(configurationOfData curve branches).branches.count_eq] at codes
  exact (Nat.ne_of_lt (basisPair_left_lt_degree curve index)) codes

/-- The second endpoint of any basis cut is a finite root occurrence for any
explicit degree-complete branch family. -/
theorem basisPair_right_ne_infinity_ofData {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (index : Fin genus) :
    (configurationOfData curve branches).siteAt
        (standardPair (Fin.castSucc index)).right ≠
      .infinity := by
  intro equal
  have codes := congrArg Site.code equal
  rw [configurationOfData_siteAt_code] at codes
  change (standardPair (Fin.castSucc index)).right.val =
    (configurationOfData curve branches).branches.siteCount at codes
  rw [(configurationOfData curve branches).branches.count_eq] at codes
  exact (Nat.ne_of_lt (basisPair_right_lt_degree curve index)) codes

/-- Root index of the first endpoint of a standard basis cut in explicit
branch data. -/
def basisPairLeftIndexOfData {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (index : Fin genus) :
    Data.Index (configurationOfData curve branches).branches :=
  Site.finiteIndex
    ((configurationOfData curve branches).siteAt
      (standardPair (Fin.castSucc index)).left)
    (basisPair_left_ne_infinity_ofData curve branches index)

/-- Root index of the second endpoint of a standard basis cut in explicit
branch data. -/
def basisPairRightIndexOfData {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (index : Fin genus) :
    Data.Index (configurationOfData curve branches).branches :=
  Site.finiteIndex
    ((configurationOfData curve branches).siteAt
      (standardPair (Fin.castSucc index)).right)
    (basisPair_right_ne_infinity_ofData curve branches index)

@[simp] theorem configurationOfData_siteAt_basisPair_left {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (index : Fin genus) :
    (configurationOfData curve branches).siteAt
        (standardPair (Fin.castSucc index)).left =
      .finite (basisPairLeftIndexOfData curve branches index) :=
  by
    unfold basisPairLeftIndexOfData
    exact Site.finiteIndex_spec _
      (basisPair_left_ne_infinity_ofData curve branches index)

@[simp] theorem configurationOfData_siteAt_basisPair_right {genus : Nat}
    (curve : HyperellipticCurve genus) (branches : Data curve)
    (index : Fin genus) :
    (configurationOfData curve branches).siteAt
        (standardPair (Fin.castSucc index)).right =
      .finite (basisPairRightIndexOfData curve branches index) :=
  by
    unfold basisPairRightIndexOfData
    exact Site.finiteIndex_spec _
      (basisPair_right_ne_infinity_ofData curve branches index)

/-! The automatic names below retain the original public interface. -/

theorem basisPair_left_ne_infinity {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (standardPair (Fin.castSucc index)).left ≠
      .infinity :=
  basisPair_left_ne_infinity_ofData curve (data curve) index

theorem basisPair_right_ne_infinity {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (standardPair (Fin.castSucc index)).right ≠
      .infinity :=
  basisPair_right_ne_infinity_ofData curve (data curve) index

def basisPairLeftIndex {genus : Nat} (curve : HyperellipticCurve genus)
    (index : Fin genus) : Data.Index (configuration curve).branches :=
  basisPairLeftIndexOfData curve (data curve) index

def basisPairRightIndex {genus : Nat} (curve : HyperellipticCurve genus)
    (index : Fin genus) : Data.Index (configuration curve).branches :=
  basisPairRightIndexOfData curve (data curve) index

@[simp] theorem configuration_siteAt_basisPair_left {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (standardPair (Fin.castSucc index)).left =
      .finite (basisPairLeftIndex curve index) :=
  configurationOfData_siteAt_basisPair_left curve (data curve) index

@[simp] theorem configuration_siteAt_basisPair_right {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
    (configuration curve).siteAt (standardPair (Fin.castSucc index)).right =
      .finite (basisPairRightIndex curve index) :=
  configurationOfData_siteAt_basisPair_right curve (data curve) index

/-- Pair containing a displayed branch label. -/
def pairOf {genus : Nat} (position : Fin (2 * genus + 2)) :
    Fin (genus + 1) :=
  ⟨position.val / 2, by
    have bound := position.isLt
    omega0⟩

/-- Every branch label is exactly the left or right endpoint of its computed
standard pair. -/
theorem standardPair_covers {genus : Nat}
    (position : Fin (2 * genus + 2)) :
    position = (standardPair (pairOf position)).left \/
      position = (standardPair (pairOf position)).right := by
  have remainderBound : position.val % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have division := Nat.mod_add_div position.val 2
  by_cases even : position.val % 2 = 0
  · left
    apply Fin.ext
    dsimp [standardPair, pairOf]
    omega0
  · have odd : position.val % 2 = 1 := by omega0
    right
    apply Fin.ext
    dsimp [standardPair, pairOf]
    omega0

/-- The two semantic endpoints of one standard cut are distinct because the
global branch enumeration is injective. -/
theorem cutEndpoints_different {genus : Nat}
    {curve : HyperellipticCurve genus} (configuration : Configuration curve)
    (index : Fin (genus + 1)) :
    configuration.siteAt (standardPair index).left ≠
      configuration.siteAt (standardPair index).right := by
  intro equal
  exact (standardPair index).different
    (configuration.siteAt_injective equal)

/-- Every finite endpoint of a standard cut retains its persistent root name;
the odd-degree infinity endpoint is represented by `none`. -/
def cutEndpointNames {genus : Nat}
    {curve : HyperellipticCurve genus} (configuration : Configuration curve)
    (index : Fin (genus + 1)) : Option Named × Option Named :=
  ((configuration.siteAt (standardPair index).left).name?,
    (configuration.siteAt (standardPair index).right).name?)

/-- Coherent versions of the same finite endpoint names, ready for arithmetic
composition with the analytic layer. -/
def cutEndpointCoherentNames {genus : Nat}
    {curve : HyperellipticCurve genus} (configuration : Configuration curve)
    (index : Fin (genus + 1)) :
    Option CCL.ProgressiveCoherence.CoherentNamed ×
      Option CCL.ProgressiveCoherence.CoherentNamed :=
  ((configuration.siteAt (standardPair index).left).coherentName?,
    (configuration.siteAt (standardPair index).right).coherentName?)

end CCL.Riemann.BranchConfiguration

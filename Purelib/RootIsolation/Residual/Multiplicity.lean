module

public import Purelib.RootIsolation.Residual.Global.Assignment
public import Purelib.RootIsolation.FTA.Squarefree.Preparation
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Selection
public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Residual localization through original multiplicity factors

The original decomposition owns every positive-degree factor and its
multiplicity. A structural cache prepares each factor once, retaining its
exact linear reading or complete original isolation. One positive finite
minimum transfers a small source residual to a nearby original factor root.
-/

public section

namespace Purelib.RootIsolation.Residual.Multiplicity

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (positiveEntries unitValue)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Basic (multiplicityCount unitQuadrance_pos)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Selection (SmallFactor selectSmallFactorUsing)

set_option genInjectivity false in
/-- A prepared original squarefree multiplicity factor and its retained root data.

Linear data keeps the exact original coefficient root and computed inverse
slope quadrance. Nonlinear data keeps its checked axis preparation and own degree-many
isolation, with the original source and coefficient square as support.
-/
inductive Factor (entry : PositiveEntry) where
  /-- Retain the exact original linear root and one computed inverse-slope quadrance. -/
  | linear (degree : entry.part.polynomial.natDegree = 1)
      (data : Roots.Linear.RootData entry.part.polynomial) (inverseNorm : Rational)
      (inverseNorm_eq : inverseNorm = normSq data.leading⁻¹)
  /-- Retain the original nonlinear input with its own checked axes and complete isolation. -/
  | higher (degree : 2 ≤ entry.part.polynomial.natDegree)
      (preparation : FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩)

constructive_injectivity Factor

namespace Factor

/-- Prepare the original factor once, using exact coefficient readback for degree one and finite isolation otherwise. -/
def ofEntry (entry : PositiveEntry) : Factor entry := by
  if degree : entry.part.polynomial.natDegree = 1 then
    let data := Roots.Linear.rootData degree
    let inverseNorm := normSq data.leading⁻¹
    exact .linear degree data inverseNorm rfl
  else
    have higher : 2 ≤ entry.part.polynomial.natDegree := by
      have positive := entry.degreePositive
      omega0
    let input : FTA.Squarefree.Input entry.part.polynomial := ⟨entry.part.squarefree, higher⟩
    let preparation := FTA.Squarefree.Preparation.ofInput input
    exact .higher higher preparation

/-- A nonlinear entry retains the original complete preparation at the same degree witness. -/
theorem ofEntry_higher (entry : PositiveEntry) (higher : 2 ≤ entry.part.polynomial.natDegree) :
    ofEntry entry = .higher higher (FTA.Squarefree.Preparation.ofInput ⟨entry.part.squarefree, higher⟩) := by
  have notOne : entry.part.polynomial.natDegree ≠ 1 := by
    intro same
    exact (by decide +kernel : ¬ (2 : Nat) ≤ 1) (same ▸ higher)
  unfold ofEntry
  rewrite [dif_neg notOne]
  rfl

/-- A higher factor equal to its original constructor retains that same original preparation. -/
theorem higher_preparation_eq (entry : PositiveEntry) (degree : 2 ≤ entry.part.polynomial.natDegree)
    (preparation : FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩)
    (same : Factor.higher degree preparation = ofEntry entry) :
    preparation = FTA.Squarefree.Preparation.ofInput ⟨entry.part.squarefree, degree⟩ := by
  have equal := same.trans (ofEntry_higher entry degree)
  exact Factor.higher.inj equal

/-- Compute a point-independent residual target for a positive requested localization radius. -/
@[expose] def threshold {entry : PositiveEntry} (factor : Factor entry) (epsilon : Rational) : Rational :=
  match factor with
  | .linear _ _ inverseNorm _ => epsilon ^ 2 / (1 + inverseNorm)
  | .higher degree _ =>
      let input : FTA.Squarefree.Input entry.part.polynomial := ⟨entry.part.squarefree, degree⟩
      min (Global.Bounds.outsideResidualThreshold entry.part.polynomial)
        (Global.Assignment.insideResidualTarget input epsilon)

/-- Every prepared factor has a positive localization target at a positive radius. -/
theorem threshold_positive {entry : PositiveEntry} (factor : Factor entry) {epsilon : Rational}
    (epsilonPositive : 0 < epsilon) : 0 < factor.threshold epsilon := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    have inverseNonnegative : 0 ≤ inverseNorm := by
      rewrite [inverseNorm_eq]
      exact Norm.Basic.normSq_nonneg _
    exact Fraction.Order.Field.div_pos_direct
      (Arithmetic.pow_pos_direct epsilonPositive 2)
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) inverseNonnegative)
  | higher degree preparation =>
    exact Fraction.Order.Basic.lt_min
      (Global.Bounds.outsideResidualThreshold_pos entry.degreePositive)
      (Global.Assignment.insideResidualTarget_pos ⟨entry.part.squarefree, degree⟩ epsilonPositive)

set_option genInjectivity false in
/-- A nearby root reading or localized track referring to the same prepared original factor.

The nonlinear assignment's dependent owner index belongs to the original
stored isolation. The linear distance concerns its original exact coefficient
root; neither case asserts that an approximate sample is an exact root.
-/
inductive Localized {entry : PositiveEntry} : Factor entry → Canonical → Rational → Type where
  /-- Bound the distance to the original exact linear root at the requested radius. -/
  | linear {degree : entry.part.polynomial.natDegree = 1}
      {data : Roots.Linear.RootData entry.part.polynomial} {inverseNorm : Rational}
      {inverseNorm_eq : inverseNorm = normSq data.leading⁻¹} {sample : Canonical} {epsilon : Rational}
      (near : normSq (sample - data.point) < epsilon ^ 2) :
      Localized (.linear degree data inverseNorm inverseNorm_eq) sample epsilon
  /-- Retain a nearby winding-one track and its owner in the same stored original isolation. -/
  | higher {degree : 2 ≤ entry.part.polynomial.natDegree}
      {preparation : FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩}
      {sample : Canonical} {epsilon : Rational}
      (assignment : Global.Assignment.AssignedResult ⟨entry.part.squarefree, degree⟩ sample epsilon
        preparation.boxes.isolation) :
      Localized (.higher degree preparation) sample epsilon

constructive_injectivity Localized

/-- A higher factor's small residual places its actual sample inside the original coefficient square. -/
theorem higher_contains {entry : PositiveEntry} (degree : 2 ≤ entry.part.polynomial.natDegree)
    (preparation : FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩)
    (sample : Canonical) {epsilon : Rational}
    (small : normSq (entry.part.polynomial.eval sample) < (Factor.higher degree preparation).threshold epsilon) :
    (Bounds.RootRadius.Box.largeSquareBox entry.part.polynomial).Contains sample := by
  have outsideSmall := small.trans_le (Fraction.Order.Basic.min_le_left _ _)
  by_cases contains : (Bounds.RootRadius.Box.largeSquareBox entry.part.polynomial).Contains sample
  · exact contains
  · exact (not_lt_of_ge (Global.Bounds.outsideResidualThreshold_le degree sample contains) outsideSmall).elim

/-- Localize a sufficiently small original factor residual using its same retained preparation.

The linear branch uses the stored inverse-slope quadrance. The nonlinear
threshold excludes the outside of the original support and then consumes its
stored ownership function. No isolation producer is called here.
-/
def localize {entry : PositiveEntry} (factor : Factor entry) (sample : Canonical) {epsilon : Rational}
    (epsilonPositive : 0 < epsilon)
    (small : normSq (entry.part.polynomial.eval sample) < factor.threshold epsilon) :
    Localized factor sample epsilon := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    have nonnegative : 0 ≤ inverseNorm := by
      rewrite [inverseNorm_eq]
      exact Norm.Basic.normSq_nonneg _
    have positive : 0 < 1 + inverseNorm :=
      Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) nonnegative
    have inverseLe : inverseNorm ≤ 1 + inverseNorm := by
      have bound := Arithmetic.add_le_add_direct (show (0 : Rational) ≤ 1 by decide)
        (show inverseNorm ≤ inverseNorm from Fraction.Order.Basic.le_refl _)
      rewrite [zero_add] at bound
      exact bound
    have paid := (Fraction.Order.Field.lt_div_iff_pos positive).mp small
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct inverseLe
      (Norm.Basic.normSq_nonneg (entry.part.polynomial.eval sample))
    have identity : normSq (sample - data.point) = inverseNorm * normSq (entry.part.polynomial.eval sample) := by
      rewrite [data.displacement_eq sample, Norm.Basic.normSq_mul, inverseNorm_eq]
      rfl
    have paidReversed : (1 + inverseNorm) * normSq (entry.part.polynomial.eval sample) < epsilon ^ 2 := by
      rewrite [Fraction.Field.mul_comm]
      exact paid
    exact .linear (by
      rewrite [identity]
      exact scaled.trans_lt paidReversed)
  | higher degree preparation =>
    let input : FTA.Squarefree.Input entry.part.polynomial := ⟨entry.part.squarefree, degree⟩
    have inside := higher_contains degree preparation sample small
    exact .higher (Global.Assignment.assignInsideWithElimination input preparation.elimination preparation.boxes
      preparation.support sample inside epsilonPositive
      (small.trans_le (Fraction.Order.Basic.min_le_right _ _)))

/-- The higher-factor locator retains its complete original prepared-axis assignment. -/
theorem localize_higher_eq {entry : PositiveEntry} (degree : 2 ≤ entry.part.polynomial.natDegree)
    (preparation : FTA.Squarefree.Preparation ⟨entry.part.squarefree, degree⟩)
    (sample : Canonical) {epsilon : Rational} (positive : 0 < epsilon)
    (small : normSq (entry.part.polynomial.eval sample) < (Factor.higher degree preparation).threshold epsilon)
    (inside : (Bounds.RootRadius.Box.largeSquareBox entry.part.polynomial).Contains sample) :
    (Factor.higher degree preparation).localize sample positive small =
      Localized.higher (Global.Assignment.assignInsideWithElimination ⟨entry.part.squarefree, degree⟩
        preparation.elimination preparation.boxes preparation.support sample inside positive
          (small.trans_le (Fraction.Order.Basic.min_le_right _ _))) := (rfl)

/-- Read the exact original linear root when retained by the localized result.

Nonlinear results retain their winding track in the full localization
certificate. This projection reads only stored exact-root data and proves
the equation for the same original factor polynomial.
-/
def Localized.exact? {entry : PositiveEntry} {factor : Factor entry} {sample : Canonical} {epsilon : Rational}
    (localized : Localized factor sample epsilon) : Option (Roots.Certificate.ExactRoot entry.part.polynomial) :=
  match factor, localized with
  | .linear _ data _ _, .linear _ => some ⟨data.point, data.root⟩
  | .higher _ _, .higher _ => none

end Factor

set_option genInjectivity false in
/-- A structural preparation cache indexed by the original ordered positive multiplicity factors. -/
inductive Family : List PositiveEntry → Type where
  /-- The empty original factor list has no preparation entries. -/
  | nil : Family []
  /-- Store the original head preparation and its actual retained tail. -/
  | cons {head : PositiveEntry} {tail : List PositiveEntry} (factor : Factor head) (remaining : Family tail) :
      Family (head :: tail)

constructive_injectivity Family

namespace Family

/-- Prepare each original positive multiplicity factor once in its original order. -/
def ofEntries : (entries : List PositiveEntry) → Family entries
  | [] => .nil
  | head :: tail => .cons (Factor.ofEntry head) (ofEntries tail)

/-- The empty original factor list retains its empty preparation. -/
theorem ofEntries_nil : ofEntries [] = .nil := (rfl)

/-- The original ordered factor spine retains its complete head and recursive tail. -/
theorem ofEntries_cons (head : PositiveEntry) (tail : List PositiveEntry) :
    ofEntries (head :: tail) = .cons (Factor.ofEntry head) (ofEntries tail) := (rfl)

/-- Read the stored original preparation at the same bounded factor-list index. -/
@[expose] def get : {entries : List PositiveEntry} → Family entries → (index : Fin entries.length) →
    Factor (entries.get index)
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨index + 1, bound⟩ => get tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Lookup in an original prepared spine retains the complete original same-entry factor constructor. -/
theorem get_ofEntries (entries : List PositiveEntry) (index : Fin entries.length) :
    (ofEntries entries).get index = Factor.ofEntry (entries.get index) := by
  induction entries with
  | nil => exact Fin.elim0 index
  | cons head tail inductionHypothesis =>
      rcases index with ⟨index, bound⟩
      cases index with
      | zero => rfl
      | succ index => exact inductionHypothesis ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Compute one positive common residual target from the actual stored factor preparations. -/
@[expose] def threshold {entries : List PositiveEntry} (family : Family entries) (epsilon : Rational) : Rational :=
  match family with
  | .nil => 1
  | .cons head tail => min (head.threshold epsilon) (tail.threshold epsilon)

/-- The finite common target is positive for every positive radius, including the empty-family unit case. -/
theorem threshold_positive {entries : List PositiveEntry} (family : Family entries) {epsilon : Rational}
    (epsilonPositive : 0 < epsilon) : 0 < family.threshold epsilon := by
  induction family with
  | nil => exact (show (0 : Rational) < 1 by decide)
  | cons head tail inductionHypothesis =>
    exact Fraction.Order.Basic.lt_min (head.threshold_positive epsilonPositive) inductionHypothesis

/-- The common residual target is no larger than the target of any original indexed factor. -/
theorem threshold_le_get : {entries : List PositiveEntry} → (family : Family entries) →
    (index : Fin entries.length) → (epsilon : Rational) →
      family.threshold epsilon ≤ (family.get index).threshold epsilon
  | [], .nil, index, _ => Fin.elim0 index
  | _ :: _, .cons _ _, ⟨0, _⟩, _ => Fraction.Order.Basic.min_le_left _ _
  | _ :: _, .cons _ tail, ⟨index + 1, bound⟩, epsilon =>
      (Fraction.Order.Basic.min_le_right _ _).trans
        (threshold_le_get tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩ epsilon)

end Family

variable {polynomial : CoefficientPolynomial}

set_option genInjectivity false in
/-- Original-decomposition localization data retaining every same-index factor preparation. -/
structure Preparation (decomposition : Squarefree.Decomposition polynomial) where
  /-- The actual retained positive multiplicity list, computed once before factor preparation. -/
  entries : List PositiveEntry
  /-- The stored list belongs to the same original source decomposition. -/
  entries_eq : entries = decomposition.positiveMultiplicityEntries
  /-- The actual factor cache on that same stored original ordered list. -/
  factors : Family entries
  /-- The stored original omitted-unit quadrance. -/
  unitQuadrance : Rational
  /-- The stored unit is the same original decomposition's omitted-unit quadrance. -/
  unitQuadrance_eq : unitQuadrance = Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition
  /-- The stored total multiplicity of the same original ordered list. -/
  count : Nat
  /-- The total consumes that same retained original list. -/
  count_eq : count = multiplicityCount entries

constructive_injectivity Preparation

namespace Preparation

/-- Attach one retained ordered factor family to its original source decomposition.

The entry equality keeps every original factor and multiplicity. The supplied
unit quadrance retains its original readback, and total multiplicity consumes
the retained list. Neither the basis nor the factor family is recomputed. -/
@[expose] def ofFamily (decomposition : Squarefree.Decomposition polynomial)
    (entries : List PositiveEntry) (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (factors : Family entries) (unit : Rational)
    (unitEq : unit = Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition) :
    Preparation decomposition :=
  let count := multiplicityCount entries
  ⟨entries, entriesEq, factors, unit, unitEq, count, rfl⟩

/-- Build every original factor preparation once from the retained source decomposition. -/
def ofDecomposition (decomposition : Squarefree.Decomposition polynomial) : Preparation decomposition :=
  let basis := decomposition.multiplicityBasis
  let entries := positiveEntries basis.entries
  let factors := Family.ofEntries entries
  let unit := normSq (unitValue basis.entries)
  ofFamily decomposition entries rfl factors unit rfl

/-- Shared factor assembly preserves every field of the original decomposition constructor. -/
private theorem ofDecomposition_eq_original (decomposition : Squarefree.Decomposition polynomial) :
    ofDecomposition decomposition = (by
      let basis := decomposition.multiplicityBasis
      let entries := positiveEntries basis.entries
      let factors := Family.ofEntries entries
      let unitQuadrance := normSq (unitValue basis.entries)
      let count := multiplicityCount entries
      exact ⟨entries, rfl, factors, unitQuadrance, rfl, count, rfl⟩) := (rfl)

/-- A retained original factor spine preserves the complete original decomposition preparation. -/
theorem ofFamily_eq_ofDecomposition (decomposition : Squarefree.Decomposition polynomial)
    (entries : List PositiveEntry) (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (factors : Family entries) (unit : Rational)
    (unitEq : unit = Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition)
    (factorsEq : factors = Family.ofEntries entries) :
    ofFamily decomposition entries entriesEq factors unit unitEq = ofDecomposition decomposition := by
  cases entriesEq
  cases factorsEq
  cases unitEq
  rfl

/-- An authenticated original decomposition preparation retains each complete original factor constructor. -/
theorem get_eq {decomposition : Squarefree.Decomposition polynomial} (preparation : Preparation decomposition)
    (same : preparation = ofDecomposition decomposition) (index : Fin preparation.entries.length) :
    preparation.factors.get index = Factor.ofEntry (preparation.entries.get index) := by
  cases same
  exact Family.get_ofEntries _ index

/-- Compute the original polynomial's positive residual threshold for the requested localization radius.

The omitted unit quadrance and exact total multiplicity scale the same finite
common factor target. Repeated occurrences keep their original exponents.
-/
@[expose] def threshold {decomposition : Squarefree.Decomposition polynomial}
    (preparation : Preparation decomposition) (epsilon : Rational) : Rational :=
  preparation.unitQuadrance * (preparation.factors.threshold epsilon) ^ preparation.count

/-- A positive requested radius gives a positive original-polynomial localization threshold. -/
theorem threshold_positive {decomposition : Squarefree.Decomposition polynomial}
    (preparation : Preparation decomposition) {epsilon : Rational} (epsilonPositive : 0 < epsilon) :
    0 < preparation.threshold epsilon := by
  have unitPositive : 0 < preparation.unitQuadrance := by
    rewrite [preparation.unitQuadrance_eq]
    exact unitQuadrance_pos decomposition
  exact Arithmetic.mul_pos_direct unitPositive
    (Arithmetic.pow_pos_direct (preparation.factors.threshold_positive epsilonPositive) _)

set_option genInjectivity false in
/-- A selected original multiplicity factor and its nearby root data from the same stored preparation.

Both the bounded index and residual witness concern the original source
decomposition. The localized result consumes that exact indexed preparation,
including its original nonlinear isolation or exact linear root.
-/
structure Localization {decomposition : Squarefree.Decomposition polynomial}
    (preparation : Preparation decomposition) (sample : Canonical) (epsilon : Rational) where
  /-- The original finite scan's index and small-factor residual witness. -/
  selected : SmallFactor decomposition sample
    (preparation.factors.threshold epsilon) preparation.entries
  /-- The nearby original root reading or track at that same retained factor index. -/
  localized : Factor.Localized (preparation.factors.get selected.index) sample epsilon

constructive_injectivity Localization

/-- Select the original small-residual factor without executing its root locator.

The retained decomposition, positive entries, unit quadrance and common
threshold determine the same ordered finite scan. The selected bounded index
and residual witness remain attached to that exact original source. -/
@[expose] def selectFactor {decomposition : Squarefree.Decomposition polynomial}
    (preparation : Preparation decomposition) (sample : Canonical) {epsilon : Rational}
    (epsilonPositive : 0 < epsilon)
    (small : normSq (polynomial.eval sample) < preparation.threshold epsilon) :
    SmallFactor decomposition sample (preparation.factors.threshold epsilon) preparation.entries :=
  selectSmallFactorUsing decomposition
    preparation.entries preparation.entries_eq sample (preparation.factors.threshold_positive epsilonPositive) (by
      change normSq (polynomial.eval sample) < preparation.threshold epsilon at small
      unfold threshold at small
      rewrite [preparation.unitQuadrance_eq, preparation.count_eq] at small
      exact small)

/-- Localize a sufficiently small source residual through the same cached original multiplicity factors.

The finite scan chooses an actual original factor. The common target supplies
its local threshold, and the selected stored preparation produces nearby root
data without recomputing a decomposition or isolation.
-/
def localize {decomposition : Squarefree.Decomposition polynomial} (preparation : Preparation decomposition)
    (sample : Canonical) {epsilon : Rational} (epsilonPositive : 0 < epsilon)
    (small : normSq (polynomial.eval sample) < preparation.threshold epsilon) :
    Localization preparation sample epsilon :=
  let selected := preparation.selectFactor sample epsilonPositive small
  let factor := preparation.factors.get selected.index
  let localized := factor.localize sample epsilonPositive
    (selected.residualSmall.trans_le (preparation.factors.threshold_le_get selected.index epsilon))
  ⟨selected, localized⟩

/-- Assemble complete original localization from its retained selected factor and same-factor locator.

Both supplied values retain their complete original defining equalities.
The original bounded factor index, small residual and localized owner remain
attached; neither selection nor localization is rerun by this constructor. -/
@[expose] def localizeFromFactor {decomposition : Squarefree.Decomposition polynomial}
    (preparation : Preparation decomposition) (sample : Canonical) {epsilon : Rational}
    (positive : 0 < epsilon) (small : normSq (polynomial.eval sample) < preparation.threshold epsilon)
    (selected : SmallFactor decomposition sample (preparation.factors.threshold epsilon) preparation.entries)
    (selectedEq : selected = preparation.selectFactor sample positive small)
    (localized : Factor.Localized (preparation.factors.get selected.index) sample epsilon)
    (localizedEq : localized = (preparation.factors.get selected.index).localize sample positive
      (selected.residualSmall.trans_le (preparation.factors.threshold_le_get selected.index epsilon))) :
    {value : Localization preparation sample epsilon // value = preparation.localize sample positive small} :=
  ⟨⟨selected, localized⟩, by
    cases selectedEq
    cases localizedEq
    rfl⟩

end Preparation

end Purelib.RootIsolation.Residual.Multiplicity

end

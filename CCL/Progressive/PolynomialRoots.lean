import mathlib.Data.ConstructiveList
import mathlib.RFAP.FinitePolynomialExtensionality
import mathlib.Tactic.QuotientFreeRing
import CCL.Bridge.Box
import CCL.Progressive.FiniteTable
import RFAP.Newton.Extraction
import RFAP.Winding.Homotopy

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace CCL.ProgressivePolynomialRoots

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian

/-! ## Positive minima of finite request lists -/

/-- Minimum of one explicit finite list of positive targets, with `1` as the
harmless empty-list target. -/
def finitePositiveMinimum (values : List Coordinate) : Coordinate :=
  values.foldr min 1

theorem finitePositiveMinimum_pos
    (values : List Coordinate) (positive : ∀ value ∈ values, 0 < value) :
    0 < finitePositiveMinimum values := by
  induction values with
  | nil => exact (by decide)
  | cons head tail inductionHypothesis =>
      rw [finitePositiveMinimum, List.foldr_cons]
      exact lt_min (positive head (by simp))
        (inductionHypothesis fun value member =>
          positive value (by simp [member]))

theorem finitePositiveMinimum_le_of_mem
    {values : List Coordinate} {value : Coordinate}
    (member : value ∈ values) : finitePositiveMinimum values ≤ value := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [finitePositiveMinimum, List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-! ## Finite coefficientwise proximity -/

/-- Equal-length coefficient tables whose displayed coefficient differences
have a common squared-norm bound. -/
def CoefficientsClose : List Gaussian → List Gaussian → Coordinate → Prop
  | [], [], _ => True
  | left :: leftTail, right :: rightTail, bound =>
      normSq (left - right) ≤ bound ∧
        CoefficientsClose leftTail rightTail bound
  | _, _, _ => False

/-! ## Finite simultaneous coefficient readings -/

/-- One coherent coefficient at one explicitly displayed finite process
state.  The state is dependent on the coefficient channel and is stored with
it rather than selected from a completed value. -/
structure CoefficientState where
  channel : CoherentNamed
  state : channel.name.process.State

namespace CoefficientState

/-- The process's constructive witness at this finite state. -/
def value (entry : CoefficientState) : Gaussian :=
  (entry.channel.name.process.witness entry.state).val

theorem value_possible (entry : CoefficientState) :
    entry.channel.name.process.Possible entry.state entry.value :=
  (entry.channel.name.process.witness entry.state).property

def allowance (entry : CoefficientState) : Coordinate :=
  entry.channel.coherent.allowance entry.state

theorem allowance_nonneg (entry : CoefficientState) :
    0 ≤ entry.allowance :=
  entry.channel.coherent.allowance_nonneg entry.state

/-- Refine one coefficient state by one displayed positive rational request. -/
def refine (entry : CoefficientState) (request : Coordinate)
    (positive : 0 < request) : CoefficientState :=
  { channel := entry.channel
    state := entry.channel.name.process.refine entry.state request positive }

@[simp] theorem refine_channel (entry : CoefficientState)
    (request : Coordinate) (positive : 0 < request) :
    (entry.refine request positive).channel = entry.channel := rfl

theorem refine_value_possible_before (entry : CoefficientState)
    (request : Coordinate) (positive : 0 < request) :
    entry.channel.name.process.Possible entry.state
      (entry.refine request positive).value :=
  entry.channel.name.process.refine_persists entry.state request positive
    (entry.refine request positive).value_possible

end CoefficientState

/-- A displayed finite table of the non-leading coefficients of a monic
polynomial.  Coefficients are stored in the same high-to-low order as the RFAP
dense polynomial implementation. -/
structure CoefficientTable where
  entries : List CoefficientState

namespace CoefficientTable

def degree (table : CoefficientTable) : Nat := table.entries.length

def values (table : CoefficientTable) : List Gaussian :=
  table.entries.map CoefficientState.value

/-- Exact monic rational polynomial read at the table's current finite
states. -/
def polynomial (table : CoefficientTable) : GaussianPolynomial :=
  ⟨1 :: table.values⟩

@[simp] theorem values_length (table : CoefficientTable) :
    table.values.length = table.degree := by
  simp only [values, degree, List.length_map]

theorem polynomial_normalized (table : CoefficientTable) :
    table.polynomial.normalize = table.polynomial := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [polynomial, RFAP.ComputablePolynomial.DensePolynomial.normalize]

@[simp] theorem polynomial_natDegree (table : CoefficientTable) :
    table.polynomial.natDegree = table.degree := by
  change
    table.polynomial.normalize.coeffs.length - 1 = table.degree
  rw [table.polynomial_normalized]
  simp only [polynomial, List.length_cons, values_length]
  omega

/-- One positive request small enough for every coherence modulus in the
finite table. -/
def requestTarget : List CoefficientState → Coordinate → Coordinate
  | [], target => target
  | entry :: remaining, target =>
      CCL.ProgressiveCoherence.Coherent.commonRequest
        (requestTarget remaining target)
        (entry.channel.coherent.accuracyRequest target)

theorem requestTarget_pos : ∀ (entries : List CoefficientState)
    {target : Coordinate}, 0 < target → 0 < requestTarget entries target
  | [], _target, positive => positive
  | entry :: remaining, _target, positive =>
      CCL.ProgressiveCoherence.Coherent.commonRequest_pos
        (requestTarget_pos remaining positive)
        (entry.channel.coherent.accuracyRequest_pos positive)

theorem requestTarget_lt_accuracy_of_mem :
    ∀ (entries : List CoefficientState) {entry : CoefficientState},
      entry ∈ entries → ∀ {target : Coordinate}, 0 < target →
        requestTarget entries target <
          entry.channel.coherent.accuracyRequest target
  | [], entry, member, target, positive => by
      simp only [List.not_mem_nil] at member
  | head :: remaining, entry, member, target, positive => by
      rcases List.mem_cons.mp member with equal | tailMember
      · subst head
        exact CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
          (requestTarget_pos remaining positive)
          (entry.channel.coherent.accuracyRequest_pos positive)
      · exact
          (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
            (requestTarget_pos remaining positive)
            (head.channel.coherent.accuracyRequest_pos positive)).trans
              (requestTarget_lt_accuracy_of_mem remaining tailMember positive)

/-- Refine every displayed coefficient by the same finite table request. -/
def refine (table : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) : CoefficientTable :=
  let request := requestTarget table.entries target
  let requestPositive := requestTarget_pos table.entries positive
  ⟨table.entries.map fun entry => entry.refine request requestPositive⟩

@[simp] theorem refine_degree (table : CoefficientTable)
    (target : Coordinate) (positive : 0 < target) :
    (table.refine target positive).degree = table.degree := by
  simp only [refine, degree, List.length_map]

/-- Every refined coefficient has coherence allowance strictly below the
common visible target. -/
theorem refine_allowance_lt
    (table : CoefficientTable) {entry : CoefficientState}
    (member : entry ∈ table.entries) (target : Coordinate)
    (positive : 0 < target) :
    (entry.refine (requestTarget table.entries target)
      (requestTarget_pos table.entries positive)).allowance < target := by
  exact entry.channel.coherent.refine_accurate entry.state target positive
    (requestTarget table.entries target)
    (requestTarget_pos table.entries positive)
    (requestTarget_lt_accuracy_of_mem table.entries member positive)

/-- Every entry of one finite coefficient table has allowance below the same
displayed target. -/
def AllowancesLt : List CoefficientState → Coordinate → Prop
  | [], _ => True
  | entry :: remaining, target =>
      entry.allowance < target ∧ AllowancesLt remaining target

theorem AllowancesLt.mono : ∀ {entries : List CoefficientState}
    {small large : Coordinate}, AllowancesLt entries small → small ≤ large →
      AllowancesLt entries large
  | [], _small, _large, _bounded, _order => trivial
  | _entry :: _remaining, _small, _large, bounded, order =>
      ⟨bounded.1.trans_le order, AllowancesLt.mono bounded.2 order⟩

/-- Two readings have the same ordered progressive coefficient channels.
Only their dependent finite process states may differ. -/
def SameChannels : List CoefficientState → List CoefficientState → Prop
  | [], [] => True
  | left :: leftTail, right :: rightTail =>
      left.channel = right.channel ∧ SameChannels leftTail rightTail
  | _, _ => False

theorem sameChannels_refl : ∀ entries : List CoefficientState,
    SameChannels entries entries
  | [] => trivial
  | _ :: remaining => ⟨rfl, sameChannels_refl remaining⟩

theorem sameChannels_trans : ∀ {first second third :
    List CoefficientState}, SameChannels first second →
      SameChannels second third → SameChannels first third
  | [], [], [], _firstSecond, _secondThird => trivial
  | [], [], _ :: _, _firstSecond, secondThird => by
      simp only [SameChannels] at secondThird
  | [], _ :: _, _, firstSecond, _secondThird => by
      simp only [SameChannels] at firstSecond
  | _ :: _, [], _, firstSecond, _secondThird => by
      simp only [SameChannels] at firstSecond
  | _ :: _, _ :: _, [], _firstSecond, secondThird => by
      simp only [SameChannels] at secondThird
  | first :: firstTail, second :: secondTail, third :: thirdTail,
      firstSecond, secondThird =>
      ⟨firstSecond.1.trans secondThird.1,
        sameChannels_trans firstSecond.2 secondThird.2⟩

theorem sameChannels_length : ∀ {left right : List CoefficientState},
    SameChannels left right → left.length = right.length
  | [], [], _same => rfl
  | [], _ :: _, same => by simp only [SameChannels] at same
  | _ :: _, [], same => by simp only [SameChannels] at same
  | _left :: leftTail, _right :: rightTail, same => by
      simp only [SameChannels] at same
      simp only [List.length_cons]
      exact congrArg Nat.succ (sameChannels_length same.2)

theorem degree_eq_of_sameChannels
    {left right : CoefficientTable}
    (same : SameChannels left.entries right.entries) :
    left.degree = right.degree :=
  sameChannels_length same

private theorem coefficientsClose_of_sameChannels :
    ∀ {left right : List CoefficientState} {target : Coordinate},
      SameChannels left right → AllowancesLt left target →
        AllowancesLt right target →
          CoefficientsClose
            (left.map CoefficientState.value)
            (right.map CoefficientState.value) (8 * target)
  | [], [], target, _same, _leftSmall, _rightSmall => trivial
  | [], _ :: _, target, same, _leftSmall, _rightSmall => by
      simp only [SameChannels] at same
  | _ :: _, [], target, same, _leftSmall, _rightSmall => by
      simp only [SameChannels] at same
  | ⟨leftChannel, leftState⟩ :: leftTail,
      ⟨rightChannel, rightState⟩ :: rightTail, target, same,
      leftSmall, rightSmall => by
      simp only [SameChannels, AllowancesLt] at same leftSmall rightSmall
      rcases same with ⟨channelEqual, tailSame⟩
      subst rightChannel
      simp only [List.map_cons, CoefficientsClose]
      constructor
      · have close := leftChannel.coherent.possible_close
          (leftChannel.name.process.witness leftState).property
          (leftChannel.name.process.witness rightState).property
        exact (calc
          normSq
              ((leftChannel.name.process.witness leftState).val -
                (leftChannel.name.process.witness rightState).val) ≤
              4 * (leftChannel.coherent.allowance leftState +
                leftChannel.coherent.allowance rightState) := close
          _ < 4 * (target + target) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide)
              (RFAP.ConstructiveFraction.add_lt_add_direct
                leftSmall.1 rightSmall.1)
          _ = 8 * target := by ring1).le
      · exact coefficientsClose_of_sameChannels tailSame
          leftSmall.2 rightSmall.2

/-- Any two sufficiently accurate finite readings of the same ordered
coefficient channels are coefficientwise close.  This is the form used to
guard a root owner against all later readings, not merely against one
particular refinement call. -/
theorem values_close_of_sameChannels
    {left right : CoefficientTable} {target : Coordinate}
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries target)
    (rightSmall : AllowancesLt right.entries target) :
    CoefficientsClose left.values right.values (8 * target) := by
  simpa only [values] using
    coefficientsClose_of_sameChannels same leftSmall rightSmall

private theorem sameChannels_map_refine
    (entries : List CoefficientState) (request : Coordinate)
    (positive : 0 < request) :
    SameChannels entries (entries.map fun entry =>
      entry.refine request positive) := by
  induction entries with
  | nil => trivial
  | cons entry remaining inductionHypothesis =>
      simp only [List.map_cons, SameChannels,
        CoefficientState.refine_channel]
      exact ⟨trivial, inductionHypothesis⟩

theorem sameChannels_refine (table : CoefficientTable)
    (target : Coordinate) (positive : 0 < target) :
    SameChannels table.entries (table.refine target positive).entries := by
  simp only [refine]
  exact sameChannels_map_refine table.entries
    (requestTarget table.entries target)
    (requestTarget_pos table.entries positive)

private theorem refine_allowances_lt_list :
    ∀ (allEntries entries : List CoefficientState)
      (target : Coordinate) (positive : 0 < target),
      (∀ entry, entry ∈ entries → entry ∈ allEntries) →
      AllowancesLt
        (entries.map fun entry =>
          entry.refine (requestTarget allEntries target)
            (requestTarget_pos allEntries positive)) target
  | allEntries, [], target, positive, included => trivial
  | allEntries, entry :: remaining, target, positive, included => by
      simp only [List.map_cons, AllowancesLt]
      constructor
      · exact entry.channel.coherent.refine_accurate entry.state target positive
          (requestTarget allEntries target)
          (requestTarget_pos allEntries positive)
          (requestTarget_lt_accuracy_of_mem allEntries
            (included entry List.mem_cons_self) positive)
      · exact refine_allowances_lt_list allEntries remaining target positive
          (by
            intro tailEntry tailMember
            exact included tailEntry
              (List.mem_cons_of_mem entry tailMember))

theorem refine_allowances_lt (table : CoefficientTable)
    (target : Coordinate) (positive : 0 < target) :
    AllowancesLt (table.refine target positive).entries target := by
  simpa only [refine] using
    refine_allowances_lt_list table.entries table.entries target positive
      (fun entry member => member)

private theorem coefficientsClose_refine :
    ∀ (allEntries entries : List CoefficientState)
      (target : Coordinate) (positive : 0 < target),
      (∀ entry, entry ∈ entries → entry ∈ allEntries) →
      AllowancesLt entries target →
      CoefficientsClose
        (entries.map CoefficientState.value)
        (entries.map fun entry =>
          (entry.refine (requestTarget allEntries target)
            (requestTarget_pos allEntries positive)).value)
        (8 * target)
  | allEntries, [], target, positive, _included, _allowances => trivial
  | allEntries, entry :: remaining, target, positive, included, allowances => by
      rcases allowances with ⟨oldSmall, tailSmall⟩
      simp only [List.map_cons, CoefficientsClose]
      constructor
      · have member : entry ∈ allEntries :=
          included entry List.mem_cons_self
        have newSmall :
            (entry.refine (requestTarget allEntries target)
              (requestTarget_pos allEntries positive)).allowance < target :=
          entry.channel.coherent.refine_accurate entry.state target positive
            (requestTarget allEntries target)
            (requestTarget_pos allEntries positive)
            (requestTarget_lt_accuracy_of_mem allEntries member positive)
        have close := entry.channel.coherent.possible_close
          entry.value_possible
          (entry.refine (requestTarget allEntries target)
            (requestTarget_pos allEntries positive)).value_possible
        exact (calc
            normSq
                (entry.value -
                  (entry.refine (requestTarget allEntries target)
                    (requestTarget_pos allEntries positive)).value) ≤
                4 *
                  (entry.allowance +
                    (entry.refine (requestTarget allEntries target)
                      (requestTarget_pos allEntries positive)).allowance) := close
            _ < 4 * (target + target) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct oldSmall newSmall)
            _ = 8 * target := by ring1).le
      · exact coefficientsClose_refine allEntries remaining target positive
          (by
            intro tailEntry tailMember
            exact included tailEntry
              (List.mem_cons_of_mem entry tailMember))
          tailSmall

/-- A simultaneous refinement of a table whose current allowances are below
`target` changes every displayed coefficient by quadrance at most
`8 * target`. -/
theorem values_close_refine (table : CoefficientTable)
    (target : Coordinate) (positive : 0 < target)
    (currentSmall : AllowancesLt table.entries target) :
    CoefficientsClose table.values (table.refine target positive).values
      (8 * target) := by
  simpa only [values, refine, List.map_map, Function.comp_def] using
    coefficientsClose_refine table.entries table.entries target positive
      (fun entry member => member) currentSmall

end CoefficientTable

/-! ## Finite coefficient extensionality over Gaussian rationals -/

/-- A bounded list of pairwise distinct Gaussian-rational probes. -/
def gaussianProbePoints (count : Nat) : List Gaussian :=
  List.map (fun value : Nat => (value : Gaussian)) (List.range count)

theorem gaussianProbePoints_nodup (count : Nat) :
    (gaussianProbePoints count).Nodup := by
  unfold gaussianProbePoints
  apply QuotientFreeList.nodup_map_of_injective
    (function := fun value : Nat => (value : Gaussian))
  · intro left right equal
    have realEqual := congrArg (fun value : Gaussian => value.re) equal
    simp only [natCast_re] at realEqual
    exact RFAP.ConstructiveFraction.natCast_injective_direct realEqual
  · exact RFAP.finiteRange_nodup count

@[simp] theorem gaussianProbePoints_length (count : Nat) :
    (gaussianProbePoints count).length = count := by
  unfold gaussianProbePoints
  rw [List.length_map, List.length_range]

/-- Equality on every Gaussian rational identifies normalized coefficient
lists.  The proof uses only the displayed probe prefix whose length is the
coefficient count of the difference. -/
theorem gaussian_normalized_eq_of_eval_eq
    {left right : GaussianPolynomial}
    (leftNormalized : left.normalize = left)
    (rightNormalized : right.normalize = right)
    (equal : ∀ point : Gaussian, left.eval point = right.eval point) :
    left = right := by
  have differenceZero : (left - right).isZero = true := by
    by_cases zero : (left - right).isZero = true
    · exact zero
    · have nonzero : (left - right).isZero = false := by simpa using zero
      have zeros : ∀ point ∈
          gaussianProbePoints (left - right).degreeCount,
          (left - right).eval point = 0 := by
        intro point member
        rw [RFAP.ComputablePolynomial.DensePolynomial.eval_sub, equal point]
        exact RFAP.ConstructiveGaussian.Gaussian.sub_self _
      have tooMany :=
        RFAP.FinitePolynomialExtensionality.nodup_zeros_length_lt_degreeCount
          (left - right) nonzero
          (gaussianProbePoints (left - right).degreeCount)
          (gaussianProbePoints_nodup _) zeros
      rw [gaussianProbePoints_length] at tooMany
      exact (Nat.lt_irrefl _ tooMany).elim
  exact RFAP.FinitePolynomialExtensionality.normalized_eq_of_sub_isZero
    leftNormalized rightNormalized differenceZero

theorem add_sub_left_eq_of_normalized
    (base later : GaussianPolynomial)
    (laterNormalized : later.normalize = later) :
    base + (later - base) = later := by
  apply gaussian_normalized_eq_of_eval_eq
  · exact RFAP.ComputablePolynomial.DensePolynomial.normalize_add _ _
  · exact laterNormalized
  · intro point
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_add,
      RFAP.ComputablePolynomial.DensePolynomial.eval_sub]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im] <;> ring1

/-! ## A coefficientwise high-to-low Horner bound -/

/-- Coarse square-root-free Horner perturbation budget for `count`
high-to-low coefficients, one coefficientwise quadrance bound, and one input
quadrance bound. -/
def hornerPerturbationBudget : Nat → Coordinate → Coordinate → Coordinate
  | 0, _, _ => 0
  | count + 1, coefficientBound, inputNormSq =>
      2 * (coefficientBound * inputNormSq ^ count +
        hornerPerturbationBudget count coefficientBound inputNormSq)

theorem hornerPerturbationBudget_nonneg : ∀ count
    {coefficientBound inputNormSq : Coordinate},
    0 ≤ coefficientBound → 0 ≤ inputNormSq →
      0 ≤ hornerPerturbationBudget count coefficientBound inputNormSq
  | 0, _coefficientBound, _inputNormSq, _coefficientNonnegative,
      _inputNonnegative => le_rfl
  | count + 1, coefficientBound, inputNormSq, coefficientNonnegative,
      inputNonnegative =>
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            coefficientNonnegative
            (RFAP.ConstructiveFraction.pow_nonneg_direct inputNonnegative
              count))
          (hornerPerturbationBudget_nonneg count coefficientNonnegative
            inputNonnegative))

private theorem add_pos_of_pos_of_nonneg_direct
    {left right : Coordinate} (leftPositive : 0 < left)
    (rightNonnegative : 0 ≤ right) : 0 < left + right := by
  constructor
  · have sumNonnegative :=
      RFAP.ConstructiveFraction.add_le_add_direct leftPositive.le
        rightNonnegative
    have zeroIdentity : (0 : Coordinate) + 0 = 0 := by ring1
    rwa [zeroIdentity] at sumNonnegative
  · intro sumNonpositive
    apply leftPositive.2
    have leftLeSum :=
      RFAP.ConstructiveFraction.add_le_add_direct (first := left)
        (second := left) (third := 0) (fourth := right) le_rfl
        rightNonnegative
    have leftIdentity : left + (0 : Coordinate) = left := by ring1
    rw [leftIdentity] at leftLeSum
    exact RFAP.ConstructiveFraction.le_trans left (left + right) 0
      leftLeSum sumNonpositive

private theorem add_pos_of_nonneg_of_pos_direct
    {left right : Coordinate} (leftNonnegative : 0 ≤ left)
    (rightPositive : 0 < right) : 0 < left + right := by
  have swapped : left + right = right + left := by ring1
  rw [swapped]
  exact add_pos_of_pos_of_nonneg_direct rightPositive leftNonnegative

theorem hornerPerturbationBudget_pos_of_count_pos : ∀ count
    {coefficientBound inputNormSq : Coordinate},
    0 < count → 0 < coefficientBound → 0 ≤ inputNormSq →
      0 < hornerPerturbationBudget count coefficientBound inputNormSq
  | 0, _coefficientBound, _inputNormSq, countPositive,
      _coefficientPositive, _inputNonnegative => by
      omega
  | count + 1, coefficientBound, inputNormSq, _countPositive,
      coefficientPositive, inputNonnegative => by
      have powerNonnegative :=
        RFAP.ConstructiveFraction.pow_nonneg_direct inputNonnegative count
      cases count with
      | zero =>
          change 0 < 2 * (coefficientBound * inputNormSq ^ 0 + 0)
          exact RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.natCast_pos_direct (n := 2)
              (by decide))
            (add_pos_of_pos_of_nonneg_direct
              (RFAP.ConstructiveFraction.mul_pos_direct coefficientPositive
                (by
                  rw [pow_zero]
                  decide)) le_rfl)
      | succ remaining =>
          have tailPositive :=
            hornerPerturbationBudget_pos_of_count_pos (remaining + 1)
              (by omega) coefficientPositive inputNonnegative
          exact RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.natCast_pos_direct (n := 2)
              (by decide))
            (add_pos_of_nonneg_of_pos_direct
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                coefficientPositive.le powerNonnegative)
              tailPositive)

/-- The Horner budget is exactly linear in its common coefficientwise
quadrance bound. -/
theorem hornerPerturbationBudget_scale : ∀ count
    (factor coefficientBound inputNormSq : Coordinate),
    hornerPerturbationBudget count (factor * coefficientBound) inputNormSq =
      factor *
        hornerPerturbationBudget count coefficientBound inputNormSq
  | 0, factor, coefficientBound, inputNormSq => by
      change (0 : Coordinate) = factor * 0
      rw [RFAP.ConstructiveFraction.mul_zero_direct]
  | count + 1, factor, coefficientBound, inputNormSq => by
      change
        2 * ((factor * coefficientBound) * inputNormSq ^ count +
          hornerPerturbationBudget count (factor * coefficientBound)
            inputNormSq) =
          factor *
            (2 * (coefficientBound * inputNormSq ^ count +
              hornerPerturbationBudget count coefficientBound inputNormSq))
      rw [hornerPerturbationBudget_scale count factor coefficientBound
        inputNormSq]
      ring1

private theorem evalCoeffs_sub_expansion
    (left right : Gaussian) (leftTail rightTail : List Gaussian)
    (input : Gaussian) (tailLength : leftTail.length = rightTail.length) :
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
        (left :: leftTail) -
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
        (right :: rightTail) =
      (left - right) * input ^ leftTail.length +
        (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input leftTail -
          RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
            rightTail) := by
  rw [RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_cons_expansion,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_cons_expansion,
    tailLength]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1

/-- Componentwise coefficient quadrance controls the exact dense Horner
evaluation difference. -/
theorem normSq_evalCoeffs_sub_le : ∀ (left right : List Gaussian)
    (input : Gaussian) (coefficientBound : Coordinate),
    CoefficientsClose left right coefficientBound →
      normSq
          (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input left -
            RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input right) ≤
        hornerPerturbationBudget left.length coefficientBound (normSq input)
  | [], [], input, coefficientBound, _close => by
      change normSq ((0 : Gaussian) - 0) ≤ 0
      rw [sub_self, normSq_zero]
  | [], _ :: _, input, coefficientBound, close => by
      simp only [CoefficientsClose] at close
  | _ :: _, [], input, coefficientBound, close => by
      simp only [CoefficientsClose] at close
  | left :: leftTail, right :: rightTail, input, coefficientBound, close => by
      rcases close with ⟨headClose, tailClose⟩
      have tailLength : leftTail.length = rightTail.length := by
        clear headClose
        induction leftTail generalizing rightTail with
        | nil => cases rightTail <;> simp_all [CoefficientsClose]
        | cons leftHead leftRest inductionHypothesis =>
            cases rightTail with
            | nil => simp_all [CoefficientsClose]
            | cons rightHead rightRest =>
                simp only [CoefficientsClose] at tailClose
                simp only [List.length_cons]
                exact congrArg Nat.succ
                  (inductionHypothesis rightRest tailClose.2)
      rw [evalCoeffs_sub_expansion left right leftTail rightTail input
        tailLength]
      calc
        normSq
            ((left - right) * input ^ leftTail.length +
              (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
                  leftTail -
                RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
                  rightTail)) ≤
            2 *
              (normSq ((left - right) * input ^ leftTail.length) +
                normSq
                  (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
                      leftTail -
                    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
                      rightTail)) :=
          normSq_add_le_two _ _
        _ = 2 *
            (normSq (left - right) * normSq input ^ leftTail.length +
              normSq
                (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
                    leftTail -
                  RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
                    rightTail)) := by
          rw [normSq_mul, normSq_pow]
        _ ≤ 2 *
            (coefficientBound * normSq input ^ leftTail.length +
              hornerPerturbationBudget leftTail.length coefficientBound
                (normSq input)) := by
          apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              headClose
              (RFAP.ConstructiveFraction.pow_nonneg_direct
                (normSq_nonneg input) leftTail.length))
            (normSq_evalCoeffs_sub_le leftTail rightTail input coefficientBound
              tailClose)
        _ = hornerPerturbationBudget (left :: leftTail).length
            coefficientBound (normSq input) := rfl

theorem hornerPerturbationBudget_mono_input : ∀ count
    {coefficientBound small large : Coordinate},
    0 ≤ coefficientBound → 0 ≤ small → small ≤ large →
      hornerPerturbationBudget count coefficientBound small ≤
        hornerPerturbationBudget count coefficientBound large
  | 0, _coefficientBound, _small, _large, _coefficientNonnegative,
      _smallNonnegative, _order => le_rfl
  | count + 1, coefficientBound, small, large, coefficientNonnegative,
      smallNonnegative, order => by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.pow_le_pow_direct smallNonnegative order
            count)
          coefficientNonnegative)
        (hornerPerturbationBudget_mono_input count coefficientNonnegative
          smallNonnegative order)

/-- The coefficientwise bound made uniform over one rational box. -/
theorem normSq_evalCoeffs_sub_le_onBox
    (left right : List Gaussian) (coefficientBound : Coordinate)
    (coefficientNonnegative : 0 ≤ coefficientBound) (box : Box)
    {input : Gaussian} (inside : box.Contains input)
    (close : CoefficientsClose left right coefficientBound) :
    normSq
        (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input left -
          RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input right) ≤
      hornerPerturbationBudget left.length coefficientBound box.normSqBound :=
  (normSq_evalCoeffs_sub_le left right input coefficientBound close).trans
    (hornerPerturbationBudget_mono_input left.length coefficientNonnegative
      (normSq_nonneg input) (box.normSq_le_normSqBound inside))

theorem monicCoefficientsClose
    {left right : List Gaussian} {bound : Coordinate}
    (nonnegative : 0 ≤ bound)
    (close : CoefficientsClose left right bound) :
    CoefficientsClose (1 :: left) (1 :: right) bound := by
  constructor
  · rw [sub_self, normSq_zero]
    exact nonnegative
  · exact close

/-! ## Simultaneous value/derivative coefficient perturbation -/

abbrev PerturbationBounds := RFAP.PolynomialBounds.HornerNormBounds

/-- One automatic-Horner perturbation step.  `value` bounds the difference
of the two running values and `slope` bounds the difference of the two
running derivatives. -/
def perturbationBoundsStep (inputNormSq coefficientBound : Coordinate)
    (bounds : PerturbationBounds) : PerturbationBounds where
  value := 2 * (bounds.value * inputNormSq + coefficientBound)
  slope := 2 * (bounds.slope * inputNormSq + bounds.value)

/-- Repeat the same coefficientwise perturbation bound through a finite
automatic-Horner scan. -/
def perturbationBoundsFrom : Nat → Coordinate → Coordinate →
    PerturbationBounds → PerturbationBounds
  | 0, _, _, bounds => bounds
  | count + 1, coefficientBound, inputNormSq, bounds =>
      perturbationBoundsFrom count coefficientBound inputNormSq
        (perturbationBoundsStep inputNormSq coefficientBound bounds)

def coefficientPerturbationBounds (count : Nat)
    (coefficientBound inputNormSq : Coordinate) : PerturbationBounds :=
  perturbationBoundsFrom count coefficientBound inputNormSq ⟨0, 0⟩

private theorem perturbationBoundsFrom_nonneg : ∀ count
    {coefficientBound inputNormSq : Coordinate}
    (bounds : PerturbationBounds),
    0 ≤ coefficientBound → 0 ≤ inputNormSq →
      0 ≤ bounds.value → 0 ≤ bounds.slope →
      0 ≤ (perturbationBoundsFrom count coefficientBound
        inputNormSq bounds).value ∧
      0 ≤ (perturbationBoundsFrom count coefficientBound
        inputNormSq bounds).slope
  | 0, _coefficientBound, _inputNormSq, bounds,
      _coefficientNonnegative, _inputNonnegative,
      valueNonnegative, slopeNonnegative =>
      ⟨valueNonnegative, slopeNonnegative⟩
  | count + 1, coefficientBound, inputNormSq, bounds,
      coefficientNonnegative, inputNonnegative,
      valueNonnegative, slopeNonnegative => by
      apply perturbationBoundsFrom_nonneg count
        (perturbationBoundsStep inputNormSq coefficientBound bounds)
        coefficientNonnegative inputNonnegative
      · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              valueNonnegative inputNonnegative)
            coefficientNonnegative)
      · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              slopeNonnegative inputNonnegative)
            valueNonnegative)

theorem coefficientPerturbationBounds_nonneg
    (count : Nat) {coefficientBound inputNormSq : Coordinate}
    (coefficientNonnegative : 0 ≤ coefficientBound)
    (inputNonnegative : 0 ≤ inputNormSq) :
    0 ≤ (coefficientPerturbationBounds count coefficientBound
      inputNormSq).value ∧
    0 ≤ (coefficientPerturbationBounds count coefficientBound
      inputNormSq).slope :=
  perturbationBoundsFrom_nonneg count ⟨0, 0⟩ coefficientNonnegative
    inputNonnegative le_rfl le_rfl

private theorem perturbationBoundsFrom_scale : ∀ count
    (factor coefficientBound inputNormSq : Coordinate)
    (bounds : PerturbationBounds),
    perturbationBoundsFrom count (factor * coefficientBound) inputNormSq
        ⟨factor * bounds.value, factor * bounds.slope⟩ =
      let output := perturbationBoundsFrom count coefficientBound
        inputNormSq bounds
      ⟨factor * output.value, factor * output.slope⟩
  | 0, factor, coefficientBound, inputNormSq, bounds => rfl
  | count + 1, factor, coefficientBound, inputNormSq, bounds => by
      change perturbationBoundsFrom count (factor * coefficientBound)
          inputNormSq
          (perturbationBoundsStep inputNormSq (factor * coefficientBound)
            ⟨factor * bounds.value, factor * bounds.slope⟩) = _
      have stepIdentity :
          perturbationBoundsStep inputNormSq (factor * coefficientBound)
              ⟨factor * bounds.value, factor * bounds.slope⟩ =
            let next := perturbationBoundsStep inputNormSq coefficientBound
              bounds
            ⟨factor * next.value, factor * next.slope⟩ := by
        rcases bounds with ⟨value, slope⟩
        simp only [perturbationBoundsStep]
        congr 1 <;> ring1
      rw [stepIdentity]
      exact perturbationBoundsFrom_scale count factor coefficientBound
        inputNormSq (perturbationBoundsStep inputNormSq coefficientBound bounds)

theorem coefficientPerturbationBounds_scale
    (count : Nat) (factor coefficientBound inputNormSq : Coordinate) :
    coefficientPerturbationBounds count (factor * coefficientBound)
        inputNormSq =
      let output := coefficientPerturbationBounds count coefficientBound
        inputNormSq
      ⟨factor * output.value, factor * output.slope⟩ := by
  simpa only [coefficientPerturbationBounds,
    RFAP.ConstructiveFraction.mul_zero_direct] using
      perturbationBoundsFrom_scale count factor coefficientBound
        inputNormSq ⟨0, 0⟩

private theorem evalDerivativeCoeffs_sub_bounds :
    ∀ (left right : List Gaussian) (input : Gaussian)
      (coefficientBound inputNormSq : Coordinate)
      (leftValue leftDerivative rightValue rightDerivative : Gaussian)
      (bounds : PerturbationBounds),
      CoefficientsClose left right coefficientBound →
      normSq input ≤ inputNormSq →
      0 ≤ coefficientBound → 0 ≤ inputNormSq →
      0 ≤ bounds.value → 0 ≤ bounds.slope →
      normSq (leftValue - rightValue) ≤ bounds.value →
      normSq (leftDerivative - rightDerivative) ≤ bounds.slope →
      let leftResult := left.foldl
        (RFAP.ComputableDerivative.evalDerivativeStep input)
        (leftValue, leftDerivative)
      let rightResult := right.foldl
        (RFAP.ComputableDerivative.evalDerivativeStep input)
        (rightValue, rightDerivative)
      let finalBounds := perturbationBoundsFrom left.length
        coefficientBound inputNormSq bounds
      normSq (leftResult.1 - rightResult.1) ≤ finalBounds.value ∧
        normSq (leftResult.2 - rightResult.2) ≤ finalBounds.slope
  | [], [], input, coefficientBound, inputNormSq,
      leftValue, leftDerivative, rightValue, rightDerivative, bounds,
      _close, _inputBound, _coefficientNonnegative, _inputNonnegative,
      _valueNonnegative, _slopeNonnegative, valueBound, derivativeBound =>
      ⟨valueBound, derivativeBound⟩
  | [], _ :: _, input, coefficientBound, inputNormSq,
      leftValue, leftDerivative, rightValue, rightDerivative, bounds,
      close, _inputBound, _coefficientNonnegative, _inputNonnegative,
      _valueNonnegative, _slopeNonnegative, _valueBound, _derivativeBound => by
      simp only [CoefficientsClose] at close
  | _ :: _, [], input, coefficientBound, inputNormSq,
      leftValue, leftDerivative, rightValue, rightDerivative, bounds,
      close, _inputBound, _coefficientNonnegative, _inputNonnegative,
      _valueNonnegative, _slopeNonnegative, _valueBound, _derivativeBound => by
      simp only [CoefficientsClose] at close
  | left :: leftTail, right :: rightTail, input, coefficientBound,
      inputNormSq, leftValue, leftDerivative, rightValue, rightDerivative,
      bounds, close, inputBound, coefficientNonnegative, inputNonnegative,
      valueNonnegative, slopeNonnegative, valueBound, derivativeBound => by
      rcases close with ⟨headClose, tailClose⟩
      let nextLeftValue := leftValue * input + left
      let nextRightValue := rightValue * input + right
      let nextLeftDerivative := leftDerivative * input + leftValue
      let nextRightDerivative := rightDerivative * input + rightValue
      let nextBounds := perturbationBoundsStep inputNormSq coefficientBound bounds
      have nextValueIdentity : nextLeftValue - nextRightValue =
          (leftValue - rightValue) * input + (left - right) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [nextLeftValue, nextRightValue, sub_re, sub_im, add_re,
            add_im, mul_re, mul_im] <;> ring1
      have nextDerivativeIdentity :
          nextLeftDerivative - nextRightDerivative =
            (leftDerivative - rightDerivative) * input +
              (leftValue - rightValue) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [nextLeftDerivative, nextRightDerivative, sub_re, sub_im,
            add_re, add_im, mul_re, mul_im] <;> ring1
      have valueProduct :
          normSq (leftValue - rightValue) * normSq input ≤
            bounds.value * inputNormSq :=
        RFAP.ConstructiveFraction.mul_le_mul_direct valueBound inputBound
          (normSq_nonneg input) valueNonnegative
      have derivativeProduct :
          normSq (leftDerivative - rightDerivative) * normSq input ≤
            bounds.slope * inputNormSq :=
        RFAP.ConstructiveFraction.mul_le_mul_direct derivativeBound inputBound
          (normSq_nonneg input) slopeNonnegative
      have nextValueBound :
          normSq (nextLeftValue - nextRightValue) ≤ nextBounds.value := by
        rw [nextValueIdentity]
        calc
          normSq ((leftValue - rightValue) * input + (left - right)) ≤
              2 * (normSq ((leftValue - rightValue) * input) +
                normSq (left - right)) := normSq_add_le_two _ _
          _ = 2 * (normSq (leftValue - rightValue) * normSq input +
                normSq (left - right)) := by rw [normSq_mul]
          _ ≤ 2 * (bounds.value * inputNormSq + coefficientBound) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add valueProduct headClose) (by decide)
          _ = nextBounds.value := rfl
      have nextDerivativeBound :
          normSq (nextLeftDerivative - nextRightDerivative) ≤
            nextBounds.slope := by
        rw [nextDerivativeIdentity]
        calc
          normSq ((leftDerivative - rightDerivative) * input +
              (leftValue - rightValue)) ≤
              2 * (normSq ((leftDerivative - rightDerivative) * input) +
                normSq (leftValue - rightValue)) := normSq_add_le_two _ _
          _ = 2 * (normSq (leftDerivative - rightDerivative) * normSq input +
                normSq (leftValue - rightValue)) := by rw [normSq_mul]
          _ ≤ 2 * (bounds.slope * inputNormSq + bounds.value) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add derivativeProduct valueBound) (by decide)
          _ = nextBounds.slope := rfl
      have nextNonnegative := perturbationBoundsFrom_nonneg 1 bounds
        coefficientNonnegative inputNonnegative valueNonnegative
        slopeNonnegative
      simpa only [List.foldl_cons, List.length_cons,
        perturbationBoundsFrom, RFAP.ComputableDerivative.evalDerivativeStep,
        nextLeftValue, nextRightValue, nextLeftDerivative,
        nextRightDerivative, nextBounds] using
        evalDerivativeCoeffs_sub_bounds leftTail rightTail input
          coefficientBound inputNormSq nextLeftValue nextLeftDerivative
          nextRightValue nextRightDerivative nextBounds tailClose inputBound
          coefficientNonnegative inputNonnegative nextNonnegative.1
          nextNonnegative.2 nextValueBound nextDerivativeBound

/-- One finite coefficientwise bound simultaneously controls evaluation and
automatic-derivative evaluation at the same displayed input. -/
theorem normSq_evalDerivative_sub_le
    (left right : List Gaussian) (input : Gaussian)
    (coefficientBound inputNormSq : Coordinate)
    (close : CoefficientsClose left right coefficientBound)
    (inputBound : normSq input ≤ inputNormSq)
    (coefficientNonnegative : 0 ≤ coefficientBound)
    (inputNonnegative : 0 ≤ inputNormSq) :
    let leftResult := RFAP.ComputableDerivative.evalDerivativeCoeffs input left
    let rightResult := RFAP.ComputableDerivative.evalDerivativeCoeffs input right
    let bounds := coefficientPerturbationBounds left.length coefficientBound
      inputNormSq
    normSq (leftResult.1 - rightResult.1) ≤ bounds.value ∧
      normSq (leftResult.2 - rightResult.2) ≤ bounds.slope := by
  simpa only [RFAP.ComputableDerivative.evalDerivativeCoeffs,
    coefficientPerturbationBounds] using
    evalDerivativeCoeffs_sub_bounds left right input coefficientBound
      inputNormSq 0 0 0 0 ⟨0, 0⟩ close inputBound coefficientNonnegative
      inputNonnegative le_rfl le_rfl (by rw [sub_self, normSq_zero])
      (by rw [sub_self, normSq_zero])

/-! ## Uniform finite coefficient and Taylor majorants -/

def CoefficientsNormLe : List Gaussian → Coordinate → Prop
  | [], _ => True
  | coefficient :: remaining, bound =>
      normSq coefficient ≤ bound ∧ CoefficientsNormLe remaining bound

/-- Positive maximum of the displayed coefficient quadrances. -/
def coefficientNormMaximum (coefficients : List Gaussian) : Coordinate :=
  coefficients.foldr (fun coefficient bound => max (normSq coefficient) bound) 1

theorem coefficientNormMaximum_pos (coefficients : List Gaussian) :
    0 < coefficientNormMaximum coefficients := by
  induction coefficients with
  | nil => exact (by decide)
  | cons coefficient remaining inductionHypothesis =>
      exact inductionHypothesis.trans_le (le_max_right _ _)

theorem coefficient_norm_le_maximum : ∀ {coefficients : List Gaussian}
    {coefficient : Gaussian}, coefficient ∈ coefficients →
    normSq coefficient ≤ coefficientNormMaximum coefficients
  | [], coefficient, member => by simp at member
  | head :: remaining, coefficient, member => by
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact le_max_left _ _
      · exact (coefficient_norm_le_maximum tailMember).trans
          (le_max_right _ _)

theorem coefficientsNormLe_maximum (coefficients : List Gaussian) :
    CoefficientsNormLe coefficients (coefficientNormMaximum coefficients) := by
  induction coefficients with
  | nil => trivial
  | cons head remaining inductionHypothesis =>
      constructor
      · exact le_max_left _ _
      · exact CoefficientsNormLe_mono inductionHypothesis
          (le_max_right _ _)
where
  CoefficientsNormLe_mono : ∀ {values : List Gaussian} {small large : Coordinate},
      CoefficientsNormLe values small → small ≤ large →
        CoefficientsNormLe values large
    | [], small, large, _bounded, _order => trivial
    | _ :: remaining, small, large, bounded, order =>
        ⟨bounded.1.trans order,
          CoefficientsNormLe_mono bounded.2 order⟩

theorem CoefficientsNormLe.mono : ∀ {values : List Gaussian}
    {small large : Coordinate}, CoefficientsNormLe values small →
      small ≤ large → CoefficientsNormLe values large
  | [], _small, _large, _bounded, _order => trivial
  | _ :: _remaining, _small, _large, bounded, order =>
      ⟨bounded.1.trans order, CoefficientsNormLe.mono bounded.2 order⟩

/-- Coarse common coefficient bound for every reading admitted at `target`. -/
def admittedCoefficientBound (reference : List Gaussian)
    (target : Coordinate) : Coordinate :=
  2 * (coefficientNormMaximum reference + 8 * target)

theorem admittedCoefficientBound_pos (reference : List Gaussian)
    {target : Coordinate} (positive : 0 < target) :
    0 < admittedCoefficientBound reference target :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (add_pos (coefficientNormMaximum_pos reference)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) positive))

theorem coefficientsNormLe_of_close : ∀
    {reference reading : List Gaussian} {target : Coordinate},
    CoefficientsClose reference reading (8 * target) →
    0 ≤ target →
    CoefficientsNormLe reading (admittedCoefficientBound reference target)
  | [], [], target, _close, _targetNonnegative => trivial
  | [], _ :: _, target, close, _targetNonnegative => by
      simp only [CoefficientsClose] at close
  | _ :: _, [], target, close, _targetNonnegative => by
      simp only [CoefficientsClose] at close
  | reference :: referenceTail, reading :: readingTail, target,
      close, targetNonnegative => by
      rcases close with ⟨headClose, tailClose⟩
      constructor
      · have referenceBound : normSq reference ≤
            coefficientNormMaximum (reference :: referenceTail) :=
          le_max_left _ _
        have identity : reading = (reading - reference) + reference := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im] <;> ring1
        rw [identity]
        calc
          normSq ((reading - reference) + reference) ≤
              2 * (normSq (reading - reference) + normSq reference) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq (reference - reading) + normSq reference) := by
            have reverse : reading - reference = -(reference - reading) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [reverse, normSq_neg]
          _ ≤ 2 * (8 * target +
                coefficientNormMaximum (reference :: referenceTail)) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add headClose referenceBound) (by decide)
          _ = admittedCoefficientBound (reference :: referenceTail) target := by
            unfold admittedCoefficientBound
            ring1
      · have tailBound := coefficientsNormLe_of_close tailClose
          targetNonnegative
        apply tailBound.mono
        unfold admittedCoefficientBound
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        change coefficientNormMaximum referenceTail + 8 * target ≤
          max (normSq reference) (coefficientNormMaximum referenceTail) +
            8 * target
        exact add_le_add
          (show coefficientNormMaximum referenceTail ≤
              max (normSq reference) (coefficientNormMaximum referenceTail)
            from le_max_right _ _)
          le_rfl

abbrev UniformTaylorBounds := RFAP.PolynomialBounds.HornerTaylorNormBounds

def uniformTaylorStep (inputNormSq coefficientBound : Coordinate)
    (bounds : UniformTaylorBounds) : UniformTaylorBounds where
  value := 2 * (bounds.value * inputNormSq + coefficientBound)
  slope := 2 * (bounds.slope * inputNormSq + bounds.value)
  remainder := 2 * (bounds.slope + inputNormSq * bounds.remainder)

def uniformTaylorBoundsFrom : Nat → Coordinate → Coordinate →
    UniformTaylorBounds → UniformTaylorBounds
  | 0, _, _, bounds => bounds
  | count + 1, coefficientBound, inputNormSq, bounds =>
      uniformTaylorBoundsFrom count coefficientBound inputNormSq
        (uniformTaylorStep inputNormSq coefficientBound bounds)

def uniformTaylorBounds (count : Nat)
    (coefficientBound inputNormSq : Coordinate) : UniformTaylorBounds :=
  uniformTaylorBoundsFrom count coefficientBound inputNormSq ⟨0, 0, 0⟩

private theorem denseTaylorFold_le_uniform : ∀
    (coefficients : List Gaussian) {coefficientBound inputNormSq : Coordinate}
    (actual uniform : UniformTaylorBounds),
    CoefficientsNormLe coefficients coefficientBound →
    0 ≤ coefficientBound → 0 ≤ inputNormSq →
    0 ≤ actual.value → 0 ≤ actual.slope →
    0 ≤ actual.remainder →
    actual.value ≤ uniform.value →
    actual.slope ≤ uniform.slope →
    actual.remainder ≤ uniform.remainder →
    let actualFinal := coefficients.foldl
      (RFAP.PolynomialBounds.HornerTaylorNormBounds.step inputNormSq) actual
    let uniformFinal := uniformTaylorBoundsFrom coefficients.length
      coefficientBound inputNormSq uniform
    actualFinal.value ≤ uniformFinal.value ∧
      actualFinal.slope ≤ uniformFinal.slope ∧
      actualFinal.remainder ≤ uniformFinal.remainder
  | [], coefficientBound, inputNormSq, actual, uniform,
      _bounded, _coefficientNonnegative, _inputNonnegative,
      _actualValueNonnegative, _actualSlopeNonnegative,
      _actualRemainderNonnegative, valueOrder, slopeOrder, remainderOrder =>
      ⟨valueOrder, slopeOrder, remainderOrder⟩
  | coefficient :: remaining, coefficientBound, inputNormSq, actual, uniform,
      bounded, coefficientNonnegative, inputNonnegative,
      actualValueNonnegative, actualSlopeNonnegative,
      actualRemainderNonnegative, valueOrder, slopeOrder, remainderOrder => by
      let actualNext := RFAP.PolynomialBounds.HornerTaylorNormBounds.step
        inputNormSq actual coefficient
      let uniformNext := uniformTaylorStep inputNormSq coefficientBound uniform
      have actualNextNonnegative :
          0 ≤ actualNext.value ∧ 0 ≤ actualNext.slope ∧
            0 ≤ actualNext.remainder := by
        constructor
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                actualValueNonnegative inputNonnegative)
              (normSq_nonneg coefficient))
        constructor
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                actualSlopeNonnegative inputNonnegative)
              actualValueNonnegative)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg actualSlopeNonnegative
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                inputNonnegative actualRemainderNonnegative))
      have valueNext : actualNext.value ≤ uniformNext.value := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            valueOrder inputNonnegative) bounded.1
      have slopeNext : actualNext.slope ≤ uniformNext.slope := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            slopeOrder inputNonnegative) valueOrder
      have remainderNext : actualNext.remainder ≤ uniformNext.remainder := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact add_le_add slopeOrder
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            remainderOrder inputNonnegative)
      simpa only [List.foldl_cons, List.length_cons,
        uniformTaylorBoundsFrom, actualNext, uniformNext] using
        denseTaylorFold_le_uniform remaining actualNext uniformNext bounded.2
          coefficientNonnegative inputNonnegative actualNextNonnegative.1
          actualNextNonnegative.2.1 actualNextNonnegative.2.2 valueNext
          slopeNext remainderNext

theorem denseHornerTaylor_le_uniform
    (polynomial : GaussianPolynomial) (box : Box)
    {coefficientBound : Coordinate}
    (bounded : CoefficientsNormLe polynomial.coeffs coefficientBound)
    (coefficientNonnegative : 0 ≤ coefficientBound) :
    let actual := RFAP.PolynomialBounds.denseHornerTaylorNormBounds
      polynomial box
    let uniform := uniformTaylorBounds polynomial.coeffs.length
      coefficientBound box.normSqBound
    actual.value ≤ uniform.value ∧ actual.slope ≤ uniform.slope ∧
      actual.remainder ≤ uniform.remainder := by
  simpa only [RFAP.PolynomialBounds.denseHornerTaylorNormBounds,
    uniformTaylorBounds] using
    denseTaylorFold_le_uniform polynomial.coeffs ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
      bounded coefficientNonnegative box.normSqBound_nonneg le_rfl le_rfl
      le_rfl le_rfl le_rfl le_rfl

private theorem denseHornerNormTaylor_fields : ∀
    (coefficients : List Gaussian) (inputNormSq : Coordinate)
    (normBounds : RFAP.PolynomialBounds.HornerNormBounds)
    (taylorBounds : RFAP.PolynomialBounds.HornerTaylorNormBounds),
    normBounds.value = taylorBounds.value →
    normBounds.slope = taylorBounds.slope →
    let normFinal := coefficients.foldl
      (RFAP.PolynomialBounds.HornerNormBounds.step inputNormSq) normBounds
    let taylorFinal := coefficients.foldl
      (RFAP.PolynomialBounds.HornerTaylorNormBounds.step inputNormSq)
        taylorBounds
    normFinal.value = taylorFinal.value ∧
      normFinal.slope = taylorFinal.slope
  | [], inputNormSq, normBounds, taylorBounds, valueEqual, slopeEqual =>
      ⟨valueEqual, slopeEqual⟩
  | coefficient :: remaining, inputNormSq, normBounds, taylorBounds,
      valueEqual, slopeEqual => by
      simp only [List.foldl_cons]
      apply denseHornerNormTaylor_fields remaining inputNormSq
      · simp only [RFAP.PolynomialBounds.HornerNormBounds.step,
          RFAP.PolynomialBounds.HornerTaylorNormBounds.step]
        rw [valueEqual]
      · simp only [RFAP.PolynomialBounds.HornerNormBounds.step,
          RFAP.PolynomialBounds.HornerTaylorNormBounds.step]
        rw [valueEqual, slopeEqual]

theorem denseHornerNormTaylor_slope
    (polynomial : GaussianPolynomial) (box : Box) :
    (RFAP.PolynomialBounds.denseHornerNormBounds polynomial box).slope =
      (RFAP.PolynomialBounds.denseHornerTaylorNormBounds polynomial box).slope :=
  (denseHornerNormTaylor_fields polynomial.coeffs box.normSqBound
    ⟨0, 0⟩ ⟨0, 0, 0⟩ rfl rfl).2

private theorem coefficientsClose_zero_of_normLe : ∀
    {coefficients : List Gaussian} {bound : Coordinate},
    CoefficientsNormLe coefficients bound →
    CoefficientsClose coefficients (coefficients.map fun _ => 0) bound
  | [], bound, _bounded => trivial
  | coefficient :: remaining, bound, bounded => by
      simp only [List.map_cons, CoefficientsClose]
      constructor
      · simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_zero] using bounded.1
      · exact coefficientsClose_zero_of_normLe bounded.2

private theorem evalDerivativeCoeffs_zero : ∀
    (coefficients : List Gaussian) (input : Gaussian),
    RFAP.ComputableDerivative.evalDerivativeCoeffs input
      (coefficients.map fun _ => 0) = (0, 0)
  | [], input => rfl
  | _ :: remaining, input => by
      change (0 :: remaining.map (fun _ => 0)).foldl
        (RFAP.ComputableDerivative.evalDerivativeStep input) (0, 0) = (0, 0)
      rw [List.foldl_cons]
      simp only [RFAP.ComputableDerivative.evalDerivativeStep,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
      exact evalDerivativeCoeffs_zero remaining input

/-- A common coefficient quadrance bound controls the automatic derivative
at every input with the displayed norm bound. -/
theorem normSq_evalDerivativeCoeffs_le_uniform
    (coefficients : List Gaussian) (input : Gaussian)
    (coefficientBound inputNormSq : Coordinate)
    (bounded : CoefficientsNormLe coefficients coefficientBound)
    (inputBound : normSq input ≤ inputNormSq)
    (coefficientNonnegative : 0 ≤ coefficientBound)
    (inputNonnegative : 0 ≤ inputNormSq) :
    normSq
        (RFAP.ComputableDerivative.evalDerivativeCoeffs input coefficients).2 ≤
      (coefficientPerturbationBounds coefficients.length coefficientBound
        inputNormSq).slope := by
  have close := coefficientsClose_zero_of_normLe bounded
  have result := normSq_evalDerivative_sub_le coefficients
    (coefficients.map fun _ => 0) input coefficientBound inputNormSq close
    inputBound coefficientNonnegative inputNonnegative
  rw [evalDerivativeCoeffs_zero coefficients input] at result
  simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_zero] using result.2

namespace CoefficientTable

/-- Coefficient multiplying a common allowance target in the automatic
derivative perturbation estimate. -/
def refinementDerivativeScale (table : CoefficientTable)
    (box : Box) : Coordinate :=
  (coefficientPerturbationBounds (table.degree + 1) 8
    box.normSqBound).slope

theorem refinementDerivativeScale_nonneg (table : CoefficientTable)
    (box : Box) : 0 ≤ table.refinementDerivativeScale box :=
  (coefficientPerturbationBounds_nonneg (table.degree + 1)
    (by decide) box.normSqBound_nonneg).2

/-- Uniform derivative-evaluation budget between two sufficiently accurate
readings of the same coefficient channels. -/
def refinementDerivativeBound (table : CoefficientTable)
    (target : Coordinate) (box : Box) : Coordinate :=
  (coefficientPerturbationBounds (table.degree + 1) (8 * target)
    box.normSqBound).slope

theorem refinementDerivativeBound_eq_target_mul_scale
    (table : CoefficientTable) (target : Coordinate) (box : Box) :
    table.refinementDerivativeBound target box =
      target * table.refinementDerivativeScale box := by
  rw [refinementDerivativeBound, refinementDerivativeScale]
  have coefficientOrder : (8 : Coordinate) * target = target * 8 := by ring1
  rw [coefficientOrder,
    coefficientPerturbationBounds_scale (table.degree + 1) target 8
      box.normSqBound]

/-- The coefficientwise automatic-Horner estimate, specialized to the
derivatives of two monic readings. -/
theorem derivative_eval_sub_le_of_sameChannels
    (left right : CoefficientTable) (target : Coordinate)
    (positive : 0 < target)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries target)
    (rightSmall : AllowancesLt right.entries target)
    (box : Box) {input : Gaussian} (inside : box.Contains input) :
    normSq
        ((RFAP.ConstructiveGCD.derivative left.polynomial).eval input -
          (RFAP.ConstructiveGCD.derivative right.polynomial).eval input) ≤
      left.refinementDerivativeBound target box := by
  have close := values_close_of_sameChannels same leftSmall rightSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le
  have monicClose := monicCoefficientsClose coefficientNonnegative close
  have bounds := normSq_evalDerivative_sub_le
    (1 :: left.values) (1 :: right.values) input (8 * target)
      box.normSqBound monicClose (box.normSq_le_normSqBound inside)
      coefficientNonnegative box.normSqBound_nonneg
  simp only [RFAP.ConstructiveGCD.derivative]
  rw [RFAP.ComputableDerivative.eval_derivative,
    RFAP.ComputableDerivative.eval_derivative]
  change normSq
      ((RFAP.ComputableDerivative.evalDerivativeCoeffs input
        (1 :: left.values)).2 -
       (RFAP.ComputableDerivative.evalDerivativeCoeffs input
        (1 :: right.values)).2) ≤ _
  simpa only [refinementDerivativeBound, List.length_cons,
    left.values_length] using bounds.2

/-- Positive coefficient multiplying the requested allowance target in the
uniform Horner perturbation budget on one box. -/
def refinementEvaluationScale (table : CoefficientTable)
    (box : Box) : Coordinate :=
  hornerPerturbationBudget (table.degree + 1) 8 box.normSqBound

theorem refinementEvaluationScale_pos (table : CoefficientTable)
    (box : Box) : 0 < table.refinementEvaluationScale box :=
  hornerPerturbationBudget_pos_of_count_pos (table.degree + 1)
    (by omega) (by decide) box.normSqBound_nonneg

theorem refinementEvaluationScale_eq_of_sameChannels
    (left right : CoefficientTable)
    (same : SameChannels left.entries right.entries) (box : Box) :
    left.refinementEvaluationScale box =
      right.refinementEvaluationScale box := by
  unfold refinementEvaluationScale
  rw [degree_eq_of_sameChannels same]

/-- Uniform box-evaluation budget for one simultaneous coefficient-table
refinement. -/
def refinementEvaluationBound (table : CoefficientTable)
    (target : Coordinate) (box : Box) : Coordinate :=
  hornerPerturbationBudget (table.degree + 1) (8 * target)
    box.normSqBound

theorem refinementEvaluationBound_eq_of_sameChannels
    (left right : CoefficientTable)
    (same : SameChannels left.entries right.entries)
    (target : Coordinate) (box : Box) :
    left.refinementEvaluationBound target box =
      right.refinementEvaluationBound target box := by
  unfold refinementEvaluationBound
  rw [degree_eq_of_sameChannels same]

theorem refinementEvaluationBound_eq_target_mul_scale
    (table : CoefficientTable) (target : Coordinate) (box : Box) :
    table.refinementEvaluationBound target box =
      target * table.refinementEvaluationScale box := by
  rw [refinementEvaluationBound, refinementEvaluationScale]
  have coefficientOrder : (8 : Coordinate) * target = target * 8 := by ring1
  rw [coefficientOrder,
    hornerPerturbationBudget_scale (table.degree + 1) target 8
      box.normSqBound]

theorem refinementEvaluationBound_nonneg (table : CoefficientTable)
    {target : Coordinate} (positive : 0 < target) (box : Box) :
    0 ≤ table.refinementEvaluationBound target box :=
  hornerPerturbationBudget_nonneg (table.degree + 1)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le)
    box.normSqBound_nonneg

/-- A source-computed positive allowance target whose complete Horner budget
is strictly below one displayed owner clearance.  The target is deliberately
formed as `clearance / (clearance + scale)`: this avoids a square root and
works uniformly at every finite degree. -/
def stabilityTarget (table : CoefficientTable) (box : Box)
    (clearance : RFAP.BoxClearance.BoundaryClearance table.polynomial box) :
    Coordinate :=
  clearance.bound /
    (clearance.bound + table.refinementEvaluationScale box)

/-- The same source-computed stability target when only a positive lower
bound for the future clearance is available. -/
def stabilityTargetForBound (table : CoefficientTable) (box : Box)
    (bound : Coordinate) : Coordinate :=
  bound / (bound + table.refinementEvaluationScale box)

theorem stabilityTargetForBound_pos (table : CoefficientTable) (box : Box)
    {bound : Coordinate} (positive : 0 < bound) :
    0 < table.stabilityTargetForBound box bound :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos positive (table.refinementEvaluationScale_pos box))

theorem refinementEvaluationBound_stabilityTargetForBound_lt
    (table : CoefficientTable) (box : Box) {bound : Coordinate}
    (positive : 0 < bound) :
    table.refinementEvaluationBound
        (table.stabilityTargetForBound box bound) box < bound := by
  rw [table.refinementEvaluationBound_eq_target_mul_scale]
  let scale := table.refinementEvaluationScale box
  have scalePositive : 0 < scale := table.refinementEvaluationScale_pos box
  have denominatorPositive : 0 < bound + scale :=
    add_pos positive scalePositive
  change bound / (bound + scale) * scale < bound
  calc
    bound / (bound + scale) * scale =
        (bound * scale) / (bound + scale) := by
      change (bound * (bound + scale)⁻¹) * scale =
        (bound * scale) * (bound + scale)⁻¹
      ring1
    _ < bound := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        denominatorPositive).2
      exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by
          calc
            scale = 0 + scale := by ring1
            _ < bound + scale :=
              RFAP.ConstructiveFraction.add_lt_add_right_direct
                positive scale)

theorem stabilityTarget_pos (table : CoefficientTable) (box : Box)
    (clearance : RFAP.BoxClearance.BoundaryClearance table.polynomial box) :
    0 < table.stabilityTarget box clearance :=
  RFAP.ConstructiveFraction.div_pos_direct clearance.positive
    (add_pos clearance.positive (table.refinementEvaluationScale_pos box))

theorem refinementEvaluationBound_stabilityTarget_lt
    (table : CoefficientTable) (box : Box)
    (clearance : RFAP.BoxClearance.BoundaryClearance table.polynomial box) :
    table.refinementEvaluationBound
        (table.stabilityTarget box clearance) box < clearance.bound := by
  rw [table.refinementEvaluationBound_eq_target_mul_scale]
  let scale := table.refinementEvaluationScale box
  have scalePositive : 0 < scale := table.refinementEvaluationScale_pos box
  have denominatorPositive : 0 < clearance.bound + scale :=
    add_pos clearance.positive scalePositive
  change clearance.bound / (clearance.bound + scale) * scale <
    clearance.bound
  calc
    clearance.bound / (clearance.bound + scale) * scale =
        (clearance.bound * scale) / (clearance.bound + scale) := by
      change (clearance.bound * (clearance.bound + scale)⁻¹) * scale =
        (clearance.bound * scale) * (clearance.bound + scale)⁻¹
      ring1
    _ < clearance.bound := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos
        denominatorPositive).2
      exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        clearance.positive (by
          calc
            scale = 0 + scale := by ring1
            _ < clearance.bound + scale :=
              RFAP.ConstructiveFraction.add_lt_add_right_direct
                clearance.positive scale)

/-- The exact monic polynomial assembled after a simultaneous coefficient
refinement differs from the preceding monic reading by no more than the
computed uniform Horner budget anywhere in the displayed box. -/
theorem polynomial_eval_sub_refine_le_onBox
    (table : CoefficientTable) (target : Coordinate)
    (positive : 0 < target)
    (currentSmall : AllowancesLt table.entries target)
    (box : Box) {input : Gaussian} (inside : box.Contains input) :
    normSq
        (table.polynomial.eval input -
          (table.refine target positive).polynomial.eval input) ≤
      table.refinementEvaluationBound target box := by
  have close := table.values_close_refine target positive currentSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le
  have monicClose := monicCoefficientsClose coefficientNonnegative close
  change normSq
      (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
          (1 :: table.values) -
        RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
          (1 :: (table.refine target positive).values)) ≤
    hornerPerturbationBudget (table.degree + 1) (8 * target)
      box.normSqBound
  simpa only [List.length_cons, table.values_length] using
    normSq_evalCoeffs_sub_le_onBox
      (1 :: table.values) (1 :: (table.refine target positive).values)
      (8 * target) coefficientNonnegative box inside monicClose

/-- Exact finite difference polynomial for one simultaneous refinement. -/
def refinementPerturbation (table : CoefficientTable)
    (target : Coordinate) (positive : 0 < target) : GaussianPolynomial :=
  (table.refine target positive).polynomial - table.polynomial

theorem polynomial_add_refinementPerturbation
    (table : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) :
    table.polynomial + table.refinementPerturbation target positive =
      (table.refine target positive).polynomial := by
  exact add_sub_left_eq_of_normalized table.polynomial
    (table.refine target positive).polynomial
    (table.refine target positive).polynomial_normalized

theorem refinementPerturbation_eval_le_onBox
    (table : CoefficientTable) (target : Coordinate)
    (positive : 0 < target)
    (currentSmall : AllowancesLt table.entries target)
    (box : Box) {input : Gaussian} (inside : box.Contains input) :
    normSq ((table.refinementPerturbation target positive).eval input) ≤
      table.refinementEvaluationBound target box := by
  rw [refinementPerturbation,
    RFAP.ComputablePolynomial.DensePolynomial.eval_sub]
  have reversed :
      (table.refine target positive).polynomial.eval input -
          table.polynomial.eval input =
        -(table.polynomial.eval input -
          (table.refine target positive).polynomial.eval input) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
  rw [reversed, normSq_neg]
  exact table.polynomial_eval_sub_refine_le_onBox target positive currentSmall
    box inside

/-- Exact difference polynomial between two finite readings of the same
progressive coefficient channels. -/
def readingPerturbation (left right : CoefficientTable) : GaussianPolynomial :=
  right.polynomial - left.polynomial

theorem polynomial_add_readingPerturbation
    (left right : CoefficientTable) :
    left.polynomial + readingPerturbation left right = right.polynomial :=
  add_sub_left_eq_of_normalized left.polynomial right.polynomial
    right.polynomial_normalized

/-- Uniform Horner bound between any two accurate readings of the same
channel table. -/
theorem polynomial_eval_sub_le_of_sameChannels
    (left right : CoefficientTable) (target : Coordinate)
    (positive : 0 < target)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries target)
    (rightSmall : AllowancesLt right.entries target)
    (box : Box) {input : Gaussian} (inside : box.Contains input) :
    normSq (left.polynomial.eval input - right.polynomial.eval input) ≤
      left.refinementEvaluationBound target box := by
  have close := values_close_of_sameChannels same leftSmall rightSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le
  have monicClose := monicCoefficientsClose coefficientNonnegative close
  change normSq
      (RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
          (1 :: left.values) -
        RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs input
          (1 :: right.values)) ≤
    hornerPerturbationBudget (left.degree + 1) (8 * target)
      box.normSqBound
  simpa only [List.length_cons, left.values_length] using
    normSq_evalCoeffs_sub_le_onBox
      (1 :: left.values) (1 :: right.values) (8 * target)
      coefficientNonnegative box inside monicClose

theorem readingPerturbation_eval_le_onBox
    (left right : CoefficientTable) (target : Coordinate)
    (positive : 0 < target)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries target)
    (rightSmall : AllowancesLt right.entries target)
    (box : Box) {input : Gaussian} (inside : box.Contains input) :
    normSq ((readingPerturbation left right).eval input) ≤
      left.refinementEvaluationBound target box := by
  rw [readingPerturbation,
    RFAP.ComputablePolynomial.DensePolynomial.eval_sub]
  have reversed :
      right.polynomial.eval input - left.polynomial.eval input =
        -(left.polynomial.eval input - right.polynomial.eval input) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
  rw [reversed, normSq_neg]
  exact polynomial_eval_sub_le_of_sameChannels left right target positive
    same leftSmall rightSmall box inside

/-- Linear coefficient-allowance scale for the error in transporting one
reference Bézout identity to another reading. -/
def bezoutPerturbationScale
    (table : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate table.polynomial)
    (box : Box) : Coordinate :=
  2 *
    (RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.left box *
        table.refinementEvaluationScale box +
      RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.right box *
        table.refinementDerivativeScale box)

theorem bezoutPerturbationScale_pos
    (table : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate table.polynomial)
    (box : Box) : 0 < table.bezoutPerturbationScale squarefree box := by
  have leftProductPositive : 0 <
      RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.left box *
        table.refinementEvaluationScale box :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.PolynomialBounds.denseEvalNormMajorant_pos squarefree.left box)
      (table.refinementEvaluationScale_pos box)
  have rightProductNonnegative : 0 ≤
      RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.right box *
        table.refinementDerivativeScale box :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
        squarefree.right box).le
      (table.refinementDerivativeScale_nonneg box)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg leftProductPositive rightProductNonnegative)

/-- A reference-computed target making the complete approximate-Bézout
error at most `1/16`, without any square-root choice. -/
def bezoutStabilityTarget
    (table : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate table.polynomial)
    (box : Box) : Coordinate :=
  1 / (16 * table.bezoutPerturbationScale squarefree box)

theorem bezoutStabilityTarget_pos
    (table : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate table.polynomial)
    (box : Box) : 0 < table.bezoutStabilityTarget squarefree box :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (table.bezoutPerturbationScale_pos squarefree box))

theorem bezoutStabilityTarget_mul_scale_le
    (table : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate table.polynomial)
    (box : Box) :
    table.bezoutStabilityTarget squarefree box *
        table.bezoutPerturbationScale squarefree box ≤
      (1 / 16 : Coordinate) := by
  let scale := table.bezoutPerturbationScale squarefree box
  have scalePositive : 0 < scale :=
    table.bezoutPerturbationScale_pos squarefree box
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (show (0 : Coordinate) < 16 by decide)).mpr
  calc
    (table.bezoutStabilityTarget squarefree box * scale) * 16 =
        table.bezoutStabilityTarget squarefree box * (16 * scale) := by ring1
    _ = 1 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1
      (16 * scale)
      (ne_of_gt (RFAP.ConstructiveFraction.mul_pos_direct
        (by decide) scalePositive))
    _ ≤ 1 := le_rfl

/-- The exact reference Bézout identity remains an approximate identity for
every sufficiently accurate reading of the same channels. -/
theorem approximateBezout_error_le
    (left right : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate left.polynomial)
    (box : Box) (target : Coordinate) (positive : 0 < target)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries target)
    (rightSmall : AllowancesLt right.entries target)
    {point : Gaussian} (inside : box.Contains point) :
    normSq
        (1 - (squarefree.left.eval point * right.polynomial.eval point +
          squarefree.right.eval point *
            (RFAP.ConstructiveGCD.derivative right.polynomial).eval point)) ≤
      target * left.bezoutPerturbationScale squarefree box := by
  let leftValue := squarefree.left.eval point
  let rightValue := squarefree.right.eval point
  let valueDifference :=
    left.polynomial.eval point - right.polynomial.eval point
  let derivativeDifference :=
    (RFAP.ConstructiveGCD.derivative left.polynomial).eval point -
      (RFAP.ConstructiveGCD.derivative right.polynomial).eval point
  have identity :
      1 - (leftValue * right.polynomial.eval point + rightValue *
          (RFAP.ConstructiveGCD.derivative right.polynomial).eval point) =
        leftValue * valueDifference + rightValue * derivativeDifference := by
    have reference := squarefree.identity point
    dsimp only [leftValue, rightValue, valueDifference, derivativeDifference]
    rw [reference]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  have leftMajorant :=
    RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
      squarefree.left inside
  have rightMajorant :=
    RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
      squarefree.right inside
  have valueBound := left.polynomial_eval_sub_le_of_sameChannels right target
    positive same leftSmall rightSmall box inside
  have derivativeBound := left.derivative_eval_sub_le_of_sameChannels right
    target positive same leftSmall rightSmall box inside
  have valueProduct : normSq leftValue * normSq valueDifference ≤
      RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.left box *
        left.refinementEvaluationBound target box :=
    RFAP.ConstructiveFraction.mul_le_mul_direct leftMajorant valueBound
      (normSq_nonneg valueDifference)
      (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
        squarefree.left box).le
  have derivativeProduct :
      normSq rightValue * normSq derivativeDifference ≤
        RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.right box *
          left.refinementDerivativeBound target box :=
    RFAP.ConstructiveFraction.mul_le_mul_direct rightMajorant derivativeBound
      (normSq_nonneg derivativeDifference)
      (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
        squarefree.right box).le
  rw [identity]
  calc
    normSq (leftValue * valueDifference + rightValue * derivativeDifference) ≤
        2 * (normSq (leftValue * valueDifference) +
          normSq (rightValue * derivativeDifference)) :=
      normSq_add_le_two _ _
    _ = 2 * (normSq leftValue * normSq valueDifference +
          normSq rightValue * normSq derivativeDifference) := by
      rw [normSq_mul, normSq_mul]
    _ ≤ 2 *
        (RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.left box *
            left.refinementEvaluationBound target box +
          RFAP.PolynomialBounds.denseEvalNormMajorant squarefree.right box *
            left.refinementDerivativeBound target box) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add valueProduct derivativeProduct) (by decide)
    _ = target * left.bezoutPerturbationScale squarefree box := by
      rw [left.refinementEvaluationBound_eq_target_mul_scale,
        left.refinementDerivativeBound_eq_target_mul_scale]
      unfold bezoutPerturbationScale
      ring1

/-- Construct robust derivative separation for an admitted reading from one
fixed exact reference Bézout certificate. -/
def robustDerivativeSeparation
    (left right : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate left.polynomial)
    (box : Box)
    (same : SameChannels left.entries right.entries)
    (leftSmall : AllowancesLt left.entries
      (left.bezoutStabilityTarget squarefree box))
    (rightSmall : AllowancesLt right.entries
      (left.bezoutStabilityTarget squarefree box)) :
    RFAP.DerivativeSeparation.Certificate right.polynomial box :=
  RFAP.DerivativeSeparation.ofApproximateBezout right.polynomial
    squarefree.left squarefree.right box (by
      intro point inside
      exact (left.approximateBezout_error_le right squarefree box
        (left.bezoutStabilityTarget squarefree box)
        (left.bezoutStabilityTarget_pos squarefree box) same leftSmall
        rightSmall inside).trans
          (left.bezoutStabilityTarget_mul_scale_le squarefree box))

/-! ### Majorants known before an admitted reading is revealed -/

/-- Coefficient quadrance bound shared by every reading admitted at
`target`.  It depends only on the displayed reference reading and the
requested allowance, not on the later process states. -/
def admittedExtractionCoefficientBound
    (reference : CoefficientTable) (target : Coordinate) : Coordinate :=
  admittedCoefficientBound (1 :: reference.values) target

/-- Uniform Horner/Taylor scan for every monic reading admitted at
`target`. -/
def admittedExtractionTaylorBounds
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    UniformTaylorBounds :=
  uniformTaylorBounds (reference.degree + 1)
    (reference.admittedExtractionCoefficientBound target) box.normSqBound

/-- Positive Lipschitz majorant known from the reference reading. -/
def admittedExtractionLipschitz
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    Coordinate :=
  max 1 (reference.admittedExtractionTaylorBounds target box).slope

/-- Positive Taylor-remainder majorant known from the reference reading. -/
def admittedExtractionTaylor
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    Coordinate :=
  max 1 (reference.admittedExtractionTaylorBounds target box).remainder

/-- Positive derivative-evaluation majorant known from the reference
reading. -/
def admittedExtractionDerivative
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    Coordinate :=
  max 1
    (coefficientPerturbationBounds (reference.degree + 1)
      (reference.admittedExtractionCoefficientBound target)
      box.normSqBound).slope

theorem admittedExtractionLipschitz_pos
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    0 < reference.admittedExtractionLipschitz target box :=
  (show (0 : Coordinate) < 1 by decide).trans_le (le_max_left _ _)

theorem admittedExtractionTaylor_pos
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    0 < reference.admittedExtractionTaylor target box :=
  (show (0 : Coordinate) < 1 by decide).trans_le (le_max_left _ _)

theorem admittedExtractionDerivative_pos
    (reference : CoefficientTable) (target : Coordinate) (box : Box) :
    0 < reference.admittedExtractionDerivative target box :=
  (show (0 : Coordinate) < 1 by decide).trans_le (le_max_left _ _)

/-- Package the precomputed bounds as the exact majorant resource consumed
by separated Newton extraction after the later reading has been obtained. -/
def admittedExtractionMajorants
    (reference reading : CoefficientTable) (target : Coordinate)
    (positive : 0 < target)
    (same : SameChannels reference.entries reading.entries)
    (referenceSmall : AllowancesLt reference.entries target)
    (readingSmall : AllowancesLt reading.entries target)
    (box : Box) :
    RFAP.NewtonExtraction.ExtractionMajorants reading.polynomial box := by
  have close := values_close_of_sameChannels same referenceSmall readingSmall
  have coefficientNonnegative : 0 ≤ 8 * target :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) positive.le
  have monicClose := monicCoefficientsClose coefficientNonnegative close
  have bounded : CoefficientsNormLe (1 :: reading.values)
      (reference.admittedExtractionCoefficientBound target) := by
    exact coefficientsNormLe_of_close monicClose positive.le
  have coefficientBoundPositive :
      0 < reference.admittedExtractionCoefficientBound target := by
    exact admittedCoefficientBound_pos (1 :: reference.values) positive
  have degreeEqual : reading.degree = reference.degree :=
    (degree_eq_of_sameChannels same).symm
  have coefficientsLength : reading.polynomial.coeffs.length =
      reference.degree + 1 := by
    change (1 :: reading.values).length = reference.degree + 1
    simp only [List.length_cons, reading.values_length, degreeEqual]
  have taylorBounds := denseHornerTaylor_le_uniform reading.polynomial box
    bounded coefficientBoundPositive.le
  rw [coefficientsLength] at taylorBounds
  have derivativeBound : ∀ {point : Gaussian}, box.Contains point →
      normSq
          ((RFAP.ConstructiveGCD.derivative reading.polynomial).eval point) ≤
        (coefficientPerturbationBounds (reference.degree + 1)
          (reference.admittedExtractionCoefficientBound target)
          box.normSqBound).slope := by
    intro point inside
    have automatic := normSq_evalDerivativeCoeffs_le_uniform
      (1 :: reading.values) point
      (reference.admittedExtractionCoefficientBound target) box.normSqBound
      bounded (box.normSq_le_normSqBound inside)
      coefficientBoundPositive.le box.normSqBound_nonneg
    simp only [RFAP.ConstructiveGCD.derivative]
    rw [RFAP.ComputableDerivative.eval_derivative]
    change normSq
        (RFAP.ComputableDerivative.evalDerivativeCoeffs point
          (1 :: reading.values)).2 ≤ _
    simpa only [List.length_cons, reading.values_length, degreeEqual] using
      automatic
  exact
    { lipschitz := reference.admittedExtractionLipschitz target box
      lipschitz_pos := reference.admittedExtractionLipschitz_pos target box
      lipschitz_upper := by
        unfold RFAP.PolynomialBounds.denseLipschitzBound
          RFAP.PolynomialBounds.denseEvalNormLipschitzBound
          admittedExtractionLipschitz
        rw [denseHornerNormTaylor_slope]
        exact max_le_max le_rfl (by
          simpa only [admittedExtractionTaylorBounds] using taylorBounds.2.1)
      taylor := reference.admittedExtractionTaylor target box
      taylor_pos := reference.admittedExtractionTaylor_pos target box
      taylor_upper := by
        unfold RFAP.PolynomialBounds.denseTaylorRemainderBound
          RFAP.PolynomialBounds.denseEvalTaylorRemainderBound
          admittedExtractionTaylor
        exact max_le_max le_rfl (by
          simpa only [admittedExtractionTaylorBounds] using taylorBounds.2.2)
      derivative := reference.admittedExtractionDerivative target box
      derivative_pos := reference.admittedExtractionDerivative_pos target box
      derivative_upper := by
        intro point inside
        exact (derivativeBound inside).trans (le_max_right _ _) }

end CoefficientTable

/-! ## From a uniform error bound to finite Rouché data -/

/-- A strict uniform perturbation bound below a displayed boundary clearance
is exactly the finite norm-dominance record consumed by constructive Rouché
transfer. -/
def boundaryNormDominanceOfUniformBound
    (base perturbation : GaussianPolynomial) (box : Box)
    (clearance : RFAP.BoxClearance.BoundaryClearance base box)
    (bound : Coordinate)
    (strict : bound < clearance.bound)
    (uniform : ∀ z : Gaussian, RFAP.BoxClearance.OnBoxBoundary box z →
      normSq (perturbation.eval z) ≤ bound) :
    RFAP.WindingHomotopy.BoundaryNormDominance base perturbation box where
  margin := clearance.bound - bound
  positive := RFAP.ConstructiveFraction.sub_pos_direct strict
  lower := by
    intro z boundary
    exact RFAP.ConstructiveFraction.sub_le_sub_direct
      (clearance.lower z boundary) (uniform z boundary)

/-- The same finite coefficient estimate constructs a boundary-clearance
certificate for the perturbed polynomial. -/
def boundaryClearance_add_of_uniformBound
    (base perturbation : GaussianPolynomial) (box : Box)
    (proper : box.Proper)
    (clearance : RFAP.BoxClearance.BoundaryClearance base box)
    (bound : Coordinate)
    (strict : bound < clearance.bound)
    (uniform : ∀ z : Gaussian, RFAP.BoxClearance.OnBoxBoundary box z →
      normSq (perturbation.eval z) ≤ bound) :
    RFAP.BoxClearance.BoundaryClearance (base + perturbation) box :=
  RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
    base perturbation box proper
      (boundaryNormDominanceOfUniformBound base perturbation box clearance
        bound strict uniform)

/-- Constructive Rouché transfer preserves the exact quadrupled winding of
the displayed box. -/
theorem quadrupledBoxWinding_add_eq_of_uniformBound
    (base perturbation : GaussianPolynomial) (box : Box)
    (proper : box.Proper)
    (clearance : RFAP.BoxClearance.BoundaryClearance base box)
    (bound : Coordinate)
    (strict : bound < clearance.bound)
    (uniform : ∀ z : Gaussian, RFAP.BoxClearance.OnBoxBoundary box z →
      normSq (perturbation.eval z) ≤ bound) :
    RFAP.Winding.quadrupledBoxWinding (base + perturbation) box =
      RFAP.Winding.quadrupledBoxWinding base box :=
  RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    base perturbation box proper clearance
    (boundaryNormDominanceOfUniformBound base perturbation box clearance
        bound strict uniform)

/-! ## Uniform transport between arbitrary accurate channel readings -/

/-- A root owner guarded against every other reading of the same channels
whose displayed allowances meet the common target. -/
structure StableChannelReadings
    (left right : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) (box : Box) where
  same : CoefficientTable.SameChannels left.entries right.entries
  leftSmall : CoefficientTable.AllowancesLt left.entries target
  rightSmall : CoefficientTable.AllowancesLt right.entries target
  proper : box.Proper
  clearance : RFAP.BoxClearance.BoundaryClearance left.polynomial box
  budget_lt : left.refinementEvaluationBound target box < clearance.bound

namespace StableChannelReadings

def perturbation
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (_transfer : StableChannelReadings left right target positive box) :
    GaussianPolynomial :=
  CoefficientTable.readingPerturbation left right

theorem rightPolynomial_eq_add
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (transfer : StableChannelReadings left right target positive box) :
    right.polynomial = left.polynomial + transfer.perturbation :=
  (left.polynomial_add_readingPerturbation right).symm

def dominance
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (transfer : StableChannelReadings left right target positive box) :
    RFAP.WindingHomotopy.BoundaryNormDominance left.polynomial
      transfer.perturbation box :=
  boundaryNormDominanceOfUniformBound left.polynomial transfer.perturbation box
    transfer.clearance (left.refinementEvaluationBound target box)
    transfer.budget_lt (by
      intro point boundary
      exact left.readingPerturbation_eval_le_onBox right target positive
        transfer.same transfer.leftSmall transfer.rightSmall box boundary.1)

def rightClearance
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (transfer : StableChannelReadings left right target positive box) :
    RFAP.BoxClearance.BoundaryClearance right.polynomial box := by
  rw [transfer.rightPolynomial_eq_add]
  exact RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
    left.polynomial transfer.perturbation box transfer.proper
      transfer.dominance

/-- The transported clearance with a bound determined entirely by the left
reading, its displayed clearance, the common allowance target, and the box.
Unlike the general homotopy clearance, this formula is available before the
right process states are revealed. -/
def explicitRightClearance
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (transfer : StableChannelReadings left right target positive box) :
    RFAP.BoxClearance.BoundaryClearance right.polynomial box where
  bound :=
    (transfer.clearance.bound -
        left.refinementEvaluationBound target box) ^ 2 /
      (4 * RFAP.PolynomialBounds.denseEvalNormMajorant
        left.polynomial box)
  positive := by
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct transfer.budget_lt) 2)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
          left.polynomial box))
  lower := by
    intro point boundary
    rw [transfer.rightPolynomial_eq_add]
    exact
      (RFAP.NewtonWinding.boundaryClearance_add_of_dominance_with_majorant
        left.polynomial transfer.perturbation box transfer.dominance
        (RFAP.PolynomialBounds.denseEvalNormMajorant left.polynomial box)
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos left.polynomial box)
        (by
          intro z onBoundary
          exact RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
            left.polynomial onBoundary.1)).lower point boundary

@[simp] theorem explicitRightClearance_bound
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (transfer : StableChannelReadings left right target positive box) :
    transfer.explicitRightClearance.bound =
      (transfer.clearance.bound -
          left.refinementEvaluationBound target box) ^ 2 /
        (4 * RFAP.PolynomialBounds.denseEvalNormMajorant
          left.polynomial box) := by
  rfl

theorem rightWinding_eq
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (transfer : StableChannelReadings left right target positive box) :
    RFAP.Winding.quadrupledBoxWinding right.polynomial box =
      RFAP.Winding.quadrupledBoxWinding left.polynomial box := by
  rw [transfer.rightPolynomial_eq_add]
  exact RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    left.polynomial transfer.perturbation box transfer.proper
      transfer.clearance transfer.dominance

end StableChannelReadings

/-! ## Transport with a retained coarse evaluation box -/

/-- Rouché transport on `box`, with the coefficient perturbation estimated
on a retained enclosing `budgetBox`.  Keeping that coarse box in the state is
what permits the next allowance target to be chosen before the newly refined
owner box has been calculated. -/
structure CoarseStableChannelReadings
    (left right : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) (box budgetBox : Box) where
  same : CoefficientTable.SameChannels left.entries right.entries
  leftSmall : CoefficientTable.AllowancesLt left.entries target
  rightSmall : CoefficientTable.AllowancesLt right.entries target
  proper : box.Proper
  refinesBudget : box.Refines budgetBox
  clearance : RFAP.BoxClearance.BoundaryClearance left.polynomial box
  budget_lt : left.refinementEvaluationBound target budgetBox < clearance.bound

namespace CoarseStableChannelReadings

def perturbation
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box budgetBox : Box}
    (_transfer : CoarseStableChannelReadings left right target positive box
      budgetBox) : GaussianPolynomial :=
  CoefficientTable.readingPerturbation left right

theorem rightPolynomial_eq_add
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : CoarseStableChannelReadings left right target positive box
      budgetBox) :
    right.polynomial = left.polynomial + transfer.perturbation :=
  (left.polynomial_add_readingPerturbation right).symm

def dominance
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : CoarseStableChannelReadings left right target positive box
      budgetBox) :
    RFAP.WindingHomotopy.BoundaryNormDominance left.polynomial
      transfer.perturbation box :=
  boundaryNormDominanceOfUniformBound left.polynomial transfer.perturbation box
    transfer.clearance (left.refinementEvaluationBound target budgetBox)
    transfer.budget_lt (by
      intro point boundary
      exact left.readingPerturbation_eval_le_onBox right target positive
        transfer.same transfer.leftSmall transfer.rightSmall budgetBox
        (transfer.refinesBudget.contains boundary.1))

/-- Explicit transported clearance whose numerical bound is known before the
right coefficient states are revealed. -/
def explicitRightClearance
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : CoarseStableChannelReadings left right target positive box
      budgetBox) :
    RFAP.BoxClearance.BoundaryClearance right.polynomial box where
  bound :=
    (transfer.clearance.bound -
        left.refinementEvaluationBound target budgetBox) ^ 2 /
      (4 * RFAP.PolynomialBounds.denseEvalNormMajorant
        left.polynomial box)
  positive := by
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct transfer.budget_lt) 2)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
          left.polynomial box))
  lower := by
    intro point boundary
    rw [transfer.rightPolynomial_eq_add]
    exact
      (RFAP.NewtonWinding.boundaryClearance_add_of_dominance_with_majorant
        left.polynomial transfer.perturbation box transfer.dominance
        (RFAP.PolynomialBounds.denseEvalNormMajorant left.polynomial box)
        (RFAP.PolynomialBounds.denseEvalNormMajorant_pos left.polynomial box)
        (by
          intro z onBoundary
          exact RFAP.PolynomialBounds.normSq_eval_le_denseEvalNormMajorant
            left.polynomial onBoundary.1)).lower point boundary

@[simp] theorem explicitRightClearance_bound
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : CoarseStableChannelReadings left right target positive box
      budgetBox) :
    transfer.explicitRightClearance.bound =
      (transfer.clearance.bound -
          left.refinementEvaluationBound target budgetBox) ^ 2 /
        (4 * RFAP.PolynomialBounds.denseEvalNormMajorant
          left.polynomial box) := rfl

theorem rightWinding_eq
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box budgetBox : Box}
    (transfer : CoarseStableChannelReadings left right target positive box
      budgetBox) :
    RFAP.Winding.quadrupledBoxWinding right.polynomial box =
      RFAP.Winding.quadrupledBoxWinding left.polynomial box := by
  rw [transfer.rightPolynomial_eq_add]
  exact RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    left.polynomial transfer.perturbation box transfer.proper
      transfer.clearance transfer.dominance

end CoarseStableChannelReadings

/-! ## Polynomial-independent finite root-owner families -/

/-- The local data needed to continue one winding-one owner.  Unlike a full
Paper-I track, it does not bake in a fixed ambient box; this makes the same
rational box reusable as the ambient of the next coefficient reading. -/
structure LocalOwner (p : GaussianPolynomial) where
  box : Box
  proper : box.Proper
  clearance : RFAP.BoxClearance.BoundaryClearance p box
  rawWindingFour :
    RFAP.Winding.quadrupledBoxWinding p box = 4

namespace LocalOwner

/-- Regard the local owner as a winding-one initial state whose ambient is
the owner box itself. -/
def initialState {p : GaussianPolynomial} (owner : LocalOwner p) :
    RFAP.ShrinkingTrack.WindingOneState p owner.box where
  box := owner.box
  refinesAmbient := RFAP.Boxes.Box.refines_refl owner.box
  proper := owner.proper
  clearance := owner.clearance
  rawWindingFour := owner.rawWindingFour
  ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary owner.clearance
  ambientRightClearance := RFAP.BoxClearance.rightOfBoundary owner.clearance
  ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary owner.clearance
  ambientTopClearance := RFAP.BoxClearance.topOfBoundary owner.clearance

/-- Total finite shrinking program generated from one local owner. -/
def track
    {p : GaussianPolynomial} (owner : LocalOwner p)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate p) :
    RFAP.ShrinkingTrack.WindingOneTrack p owner.box :=
  let input : RFAP.BoxFTA.Input p := ⟨squarefree, degreeAtLeastTwo⟩
  RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo squarefree input.elimination
    owner.initialState

end LocalOwner

/-- An explicitly indexed, pairwise-separated family of local root owners. -/
structure OwnerFamily (p : GaussianPolynomial) (count : Nat) where
  owner : Fin count → LocalOwner p
  pairwiseSeparated : ∀ left right, left ≠ right →
    (owner left).box.Separated (owner right).box

namespace OwnerFamily

/-- Forget the global Paper-I support/remainder partition while retaining its
exact degree-indexed root-owner family. -/
def ofResult
    {p : GaussianPolynomial} (result : CCL.BoxRFAPBridge.Result p) :
    OwnerFamily p p.natDegree where
  owner index :=
    { box := (result.trackAt index).initial.box
      proper := (result.trackAt index).initial.proper
      clearance := (result.trackAt index).initial.clearance
      rawWindingFour := (result.trackAt index).initial.rawWindingFour }
  pairwiseSeparated := result.trackAt_pairwiseSeparated

/-- Degree-indexed owner family specialized to the coefficient table's
displayed degree. -/
def ofTableResult
    (table : CoefficientTable)
    (result : CCL.BoxRFAPBridge.Result table.polynomial) :
    OwnerFamily table.polynomial table.degree := by
  rw [← table.polynomial_natDegree]
  exact ofResult result

def trackAt
    {p : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate p)
    (index : Fin count) :
    RFAP.ShrinkingTrack.WindingOneTrack p (family.owner index).box :=
  (family.owner index).track degreeAtLeastTwo squarefree

/-- Simultaneously shrink every member of a finite owner family for the same
fixed displayed polynomial. -/
def refine
    {p : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate p)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    OwnerFamily p count where
  owner index :=
    let track := family.trackAt degreeAtLeastTwo squarefree index
    let next := track.refine track.initial epsilon positive
    { box := next.box
      proper := next.proper
      clearance := next.clearance
      rawWindingFour := next.rawWindingFour }
  pairwiseSeparated := by
    intro left right different
    let leftTrack := family.trackAt degreeAtLeastTwo squarefree left
    let rightTrack := family.trackAt degreeAtLeastTwo squarefree right
    exact RFAP.Boxes.Box.Separated.of_refines
      (family.pairwiseSeparated left right different)
      (leftTrack.nested leftTrack.initial epsilon positive)
      (rightTrack.nested rightTrack.initial epsilon positive)

theorem refine_nested
    {p : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate p)
    (epsilon : Coordinate) (positive : 0 < epsilon) (index : Fin count) :
    ((family.refine degreeAtLeastTwo squarefree epsilon positive).owner
      index).box.Refines (family.owner index).box :=
  (family.trackAt degreeAtLeastTwo squarefree index).nested
    (family.trackAt degreeAtLeastTwo squarefree index).initial epsilon positive

theorem refine_strict
    {p : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate p)
    (epsilon : Coordinate) (positive : 0 < epsilon) (index : Fin count) :
    ((family.refine degreeAtLeastTwo squarefree epsilon positive).owner
      index).box.StrictInterior (family.owner index).box :=
  (family.trackAt degreeAtLeastTwo squarefree index).strict
    (family.trackAt degreeAtLeastTwo squarefree index).initial epsilon positive

theorem refine_accurate
    {p : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily p count)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate p)
    (epsilon : Coordinate) (positive : 0 < epsilon) (index : Fin count) :
    ((family.refine degreeAtLeastTwo squarefree epsilon positive).owner
      index).box.diagonalSq ≤ epsilon ^ 2 :=
  (family.trackAt degreeAtLeastTwo squarefree index).accurate
    (family.trackAt degreeAtLeastTwo squarefree index).initial epsilon positive

end OwnerFamily

/-! ## Owner-family transport across one coefficient reading -/

/-- Per-owner safe coefficient targets for an arbitrary degree-sized local
family. -/
def ownerFamilyStabilityTargets
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) : List Coordinate :=
  List.ofFn fun index : Fin table.degree =>
    table.stabilityTarget (family.owner index).box
      (family.owner index).clearance

theorem ownerFamilyStabilityTargets_positive
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) :
    ∀ target ∈ ownerFamilyStabilityTargets table family, 0 < target := by
  intro target member
  rw [ownerFamilyStabilityTargets, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact table.stabilityTarget_pos (family.owner index).box
    (family.owner index).clearance

def ownerFamilyStabilityTarget
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) : Coordinate :=
  finitePositiveMinimum (ownerFamilyStabilityTargets table family)

theorem ownerFamilyStabilityTarget_pos
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) :
    0 < ownerFamilyStabilityTarget table family :=
  finitePositiveMinimum_pos _
    (ownerFamilyStabilityTargets_positive table family)

theorem ownerFamilyStabilityTarget_le
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree)
    (index : Fin table.degree) :
    ownerFamilyStabilityTarget table family ≤
      table.stabilityTarget (family.owner index).box
        (family.owner index).clearance := by
  apply finitePositiveMinimum_le_of_mem
  rw [ownerFamilyStabilityTargets, List.mem_ofFn]
  exact ⟨index, rfl⟩

/-- A complete family-level Rouché transfer between two sufficiently
accurate readings of the same progressive coefficient channels. -/
structure GuardedFamilyTransfer
    (left right : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) where
  same : CoefficientTable.SameChannels left.entries right.entries
  leftSmall : CoefficientTable.AllowancesLt left.entries target
  rightSmall : CoefficientTable.AllowancesLt right.entries target
  degreeAtLeastTwo : 2 ≤ left.degree
  family : OwnerFamily left.polynomial left.degree
  stable : ∀ index : Fin left.degree,
    left.refinementEvaluationBound target (family.owner index).box <
      (family.owner index).clearance.bound
  rightSquarefree : RFAP.Squarefree.SquarefreeCertificate right.polynomial

namespace GuardedFamilyTransfer

/-- Build the complete family transfer at the common coefficient target
computed from every current owner boundary. -/
def ofComputedTarget
    (left right : CoefficientTable)
    (same : CoefficientTable.SameChannels left.entries right.entries)
    (degreeAtLeastTwo : 2 ≤ left.degree)
    (family : OwnerFamily left.polynomial left.degree)
    (leftSmall : CoefficientTable.AllowancesLt left.entries
      (ownerFamilyStabilityTarget left family))
    (rightSmall : CoefficientTable.AllowancesLt right.entries
      (ownerFamilyStabilityTarget left family))
    (rightSquarefree : RFAP.Squarefree.SquarefreeCertificate
      right.polynomial) :
    GuardedFamilyTransfer left right
      (ownerFamilyStabilityTarget left family)
      (ownerFamilyStabilityTarget_pos left family) where
  same := same
  leftSmall := leftSmall
  rightSmall := rightSmall
  degreeAtLeastTwo := degreeAtLeastTwo
  family := family
  stable := by
    intro index
    have commonLe := ownerFamilyStabilityTarget_le left family index
    have scaleNonnegative :
        0 ≤ left.refinementEvaluationScale (family.owner index).box :=
      (left.refinementEvaluationScale_pos (family.owner index).box).le
    have localBudget := left.refinementEvaluationBound_stabilityTarget_lt
      (family.owner index).box (family.owner index).clearance
    rw [left.refinementEvaluationBound_eq_target_mul_scale] at localBudget ⊢
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      commonLe scaleNonnegative).trans_lt localBudget
  rightSquarefree := rightSquarefree

/-- The canonical next-reading specialization: request every coefficient at
the family-computed target, with the later allowance and channel proofs
filled by coherence. -/
def refineAtComputedTarget
    (table : CoefficientTable) (degreeAtLeastTwo : 2 ≤ table.degree)
    (family : OwnerFamily table.polynomial table.degree)
    (currentSmall : CoefficientTable.AllowancesLt table.entries
      (ownerFamilyStabilityTarget table family))
    (nextSquarefree : RFAP.Squarefree.SquarefreeCertificate
      (table.refine (ownerFamilyStabilityTarget table family)
        (ownerFamilyStabilityTarget_pos table family)).polynomial) :
    GuardedFamilyTransfer table
      (table.refine (ownerFamilyStabilityTarget table family)
        (ownerFamilyStabilityTarget_pos table family))
      (ownerFamilyStabilityTarget table family)
      (ownerFamilyStabilityTarget_pos table family) :=
  ofComputedTarget table
    (table.refine (ownerFamilyStabilityTarget table family)
      (ownerFamilyStabilityTarget_pos table family))
    (table.sameChannels_refine (ownerFamilyStabilityTarget table family)
      (ownerFamilyStabilityTarget_pos table family))
    degreeAtLeastTwo family currentSmall
    (table.refine_allowances_lt (ownerFamilyStabilityTarget table family)
      (ownerFamilyStabilityTarget_pos table family))
    nextSquarefree

theorem rightDegreeAtLeastTwo
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive) :
    2 ≤ right.polynomial.natDegree := by
  rw [right.polynomial_natDegree,
    ← left.degree_eq_of_sameChannels transfer.same]
  exact transfer.degreeAtLeastTwo

def ownerTransferAt
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive)
    (index : Fin left.degree) :
    StableChannelReadings left right target positive
      (transfer.family.owner index).box where
  same := transfer.same
  leftSmall := transfer.leftSmall
  rightSmall := transfer.rightSmall
  proper := (transfer.family.owner index).proper
  clearance := (transfer.family.owner index).clearance
  budget_lt := transfer.stable index

/-- The same rational owner boxes, now carrying winding and clearance for
the later coefficient reading. -/
def transportedFamily
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive) :
    OwnerFamily right.polynomial left.degree where
  owner index :=
    { box := (transfer.family.owner index).box
      proper := (transfer.family.owner index).proper
      clearance := (transfer.ownerTransferAt index).rightClearance
      rawWindingFour := by
        rw [(transfer.ownerTransferAt index).rightWinding_eq]
        exact (transfer.family.owner index).rawWindingFour }
  pairwiseSeparated := transfer.family.pairwiseSeparated

/-- Transport all owners and then strictly shrink them for the later exact
rational polynomial. -/
def refinedFamily
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    OwnerFamily right.polynomial left.degree :=
  transfer.transportedFamily.refine transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive

theorem refinedFamily_nested
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (index : Fin left.degree) :
    ((transfer.refinedFamily epsilon epsilonPositive).owner index).box.Refines
      (transfer.family.owner index).box :=
  transfer.transportedFamily.refine_nested transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive index

theorem refinedFamily_strict
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (index : Fin left.degree) :
    ((transfer.refinedFamily epsilon epsilonPositive).owner index).box.StrictInterior
      (transfer.family.owner index).box :=
  transfer.transportedFamily.refine_strict transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive index

theorem refinedFamily_accurate
    {left right : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (transfer : GuardedFamilyTransfer left right target positive)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (index : Fin left.degree) :
    ((transfer.refinedFamily epsilon epsilonPositive).owner index).box.diagonalSq ≤
      epsilon ^ 2 :=
  transfer.transportedFamily.refine_accurate transfer.rightDegreeAtLeastTwo
    transfer.rightSquarefree epsilon epsilonPositive index

end GuardedFamilyTransfer

/-! ## One certified progressive-coefficient continuation step -/

/-- Sufficient finite data for transporting one winding box through one
simultaneous coefficient refinement. -/
structure StableRefinement
    (table : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) (box : Box) where
  currentSmall : CoefficientTable.AllowancesLt table.entries target
  proper : box.Proper
  clearance : RFAP.BoxClearance.BoundaryClearance table.polynomial box
  budget_lt : table.refinementEvaluationBound target box < clearance.bound

namespace StableRefinement

def nextTable
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (_step : StableRefinement table target positive box) : CoefficientTable :=
  table.refine target positive

def perturbation
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (_step : StableRefinement table target positive box) : GaussianPolynomial :=
  table.refinementPerturbation target positive

theorem polynomial_eq_add
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (step : StableRefinement table target positive box) :
    step.nextTable.polynomial = table.polynomial + step.perturbation := by
  exact (table.polynomial_add_refinementPerturbation target positive).symm

def dominance
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (step : StableRefinement table target positive box) :
    RFAP.WindingHomotopy.BoundaryNormDominance table.polynomial
      step.perturbation box :=
  boundaryNormDominanceOfUniformBound table.polynomial step.perturbation box
    step.clearance (table.refinementEvaluationBound target box)
    step.budget_lt (by
      intro point boundary
      exact table.refinementPerturbation_eval_le_onBox target positive
        step.currentSmall box boundary.1)

/-- The refined monic polynomial has a computed positive clearance on the
same rational box. -/
def nextClearance
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (step : StableRefinement table target positive box) :
    RFAP.BoxClearance.BoundaryClearance step.nextTable.polynomial box := by
  rw [step.polynomial_eq_add]
  exact RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
    table.polynomial step.perturbation box step.proper step.dominance

/-- Exact winding is retained by the newly read progressive polynomial. -/
theorem next_winding_eq
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (step : StableRefinement table target positive box) :
    RFAP.Winding.quadrupledBoxWinding step.nextTable.polynomial box =
      RFAP.Winding.quadrupledBoxWinding table.polynomial box := by
  rw [step.polynomial_eq_add]
  exact RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    table.polynomial step.perturbation box step.proper step.clearance
      step.dominance

@[simp] theorem next_degree
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target} {box : Box}
    (step : StableRefinement table target positive box) :
    step.nextTable.degree = table.degree :=
  table.refine_degree target positive

end StableRefinement

/-! ## A complete finite family of transported simple-root owners -/

/-- One higher-degree simple-root chamber.  The current displayed monic
polynomial already has its exact degree-many RFAP isolation.  A single common
coefficient target is small enough on every owner boundary, and the next
exact rational reading carries the squarefree certificate needed for further
Newton refinement. -/
structure HigherChamber
    (table : CoefficientTable) (target : Coordinate)
    (positive : 0 < target) where
  degreeAtLeastTwo : 2 ≤ table.polynomial.natDegree
  currentSmall : CoefficientTable.AllowancesLt table.entries target
  owners : CCL.BoxRFAPBridge.Result table.polynomial
  nextSquarefree : RFAP.Squarefree.SquarefreeCertificate
    (table.refine target positive).polynomial
  stable : ∀ index : Fin table.polynomial.natDegree,
    table.refinementEvaluationBound target
        (owners.trackAt index).initial.box <
      (owners.trackAt index).initial.clearance.bound

/-- Per-owner coefficient targets computed from the current exact boundary
clearances and Horner scales. -/
def higherOwnerStabilityTargets
    (table : CoefficientTable)
    (owners : CCL.BoxRFAPBridge.Result table.polynomial) : List Coordinate :=
  List.ofFn fun index : Fin table.polynomial.natDegree =>
    table.stabilityTarget (owners.trackAt index).initial.box
      (owners.trackAt index).initial.clearance

theorem higherOwnerStabilityTargets_positive
    (table : CoefficientTable)
    (owners : CCL.BoxRFAPBridge.Result table.polynomial) :
    ∀ target ∈ higherOwnerStabilityTargets table owners, 0 < target := by
  intro target member
  rw [higherOwnerStabilityTargets, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact table.stabilityTarget_pos (owners.trackAt index).initial.box
    (owners.trackAt index).initial.clearance

/-- One positive coefficient target simultaneously safe on all exactly
degree-many owner boundaries. -/
def higherStabilityTarget
    (table : CoefficientTable)
    (owners : CCL.BoxRFAPBridge.Result table.polynomial) : Coordinate :=
  finitePositiveMinimum (higherOwnerStabilityTargets table owners)

theorem higherStabilityTarget_pos
    (table : CoefficientTable)
    (owners : CCL.BoxRFAPBridge.Result table.polynomial) :
    0 < higherStabilityTarget table owners :=
  finitePositiveMinimum_pos _
    (higherOwnerStabilityTargets_positive table owners)

theorem higherStabilityTarget_le_owner
    (table : CoefficientTable)
    (owners : CCL.BoxRFAPBridge.Result table.polynomial)
    (index : Fin table.polynomial.natDegree) :
    higherStabilityTarget table owners ≤
      table.stabilityTarget (owners.trackAt index).initial.box
        (owners.trackAt index).initial.clearance := by
  apply finitePositiveMinimum_le_of_mem
  rw [higherOwnerStabilityTargets, List.mem_ofFn]
  exact ⟨index, rfl⟩

/-- Public constructor which computes the common perturbation target from
the complete owner family.  The caller supplies only the semantic statement
that the current coefficient allowances have already crossed that target
and the finite squarefree result of the next displayed reading. -/
def higherChamberOfComputedTarget
    (table : CoefficientTable)
    (degreeAtLeastTwo : 2 ≤ table.polynomial.natDegree)
    (owners : CCL.BoxRFAPBridge.Result table.polynomial)
    (currentSmall : CoefficientTable.AllowancesLt table.entries
      (higherStabilityTarget table owners))
    (nextSquarefree : RFAP.Squarefree.SquarefreeCertificate
      (table.refine (higherStabilityTarget table owners)
        (higherStabilityTarget_pos table owners)).polynomial) :
    HigherChamber table (higherStabilityTarget table owners)
      (higherStabilityTarget_pos table owners) where
  degreeAtLeastTwo := degreeAtLeastTwo
  currentSmall := currentSmall
  owners := owners
  nextSquarefree := nextSquarefree
  stable := by
    intro index
    let box := (owners.trackAt index).initial.box
    let clearance := (owners.trackAt index).initial.clearance
    let common := higherStabilityTarget table owners
    let localTarget := table.stabilityTarget box clearance
    have commonLe : common ≤ localTarget :=
      higherStabilityTarget_le_owner table owners index
    have scaleNonnegative :
        0 ≤ table.refinementEvaluationScale box :=
      (table.refinementEvaluationScale_pos box).le
    have localBudget :=
      table.refinementEvaluationBound_stabilityTarget_lt box clearance
    rw [table.refinementEvaluationBound_eq_target_mul_scale] at localBudget ⊢
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      commonLe scaleNonnegative).trans_lt
        localBudget

namespace HigherChamber

abbrev Index
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (_chamber : HigherChamber table target positive) :=
  Fin table.polynomial.natDegree

def stepAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    StableRefinement table target positive
      (chamber.owners.trackAt index).initial.box where
  currentSmall := chamber.currentSmall
  proper := (chamber.owners.trackAt index).initial.proper
  clearance := (chamber.owners.trackAt index).initial.clearance
  budget_lt := chamber.stable index

def nextInput
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive) :
    RFAP.BoxFTA.Input (table.refine target positive).polynomial where
  squarefree := chamber.nextSquarefree
  degreeAtLeastTwo := by
    rw [(table.refine target positive).polynomial_natDegree,
      table.refine_degree target positive, ← table.polynomial_natDegree]
    exact chamber.degreeAtLeastTwo

/-- The transported polynomial has winding one on the preceding owner's
whole box.  Taking that box itself as ambient supplies all four required
ambient-line certificates directly from the transported boundary clearance. -/
def nextInitialAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    RFAP.ShrinkingTrack.WindingOneState
      (table.refine target positive).polynomial
      (chamber.owners.trackAt index).initial.box := by
  let old := (chamber.owners.trackAt index).initial
  let step := chamber.stepAt index
  let clearance := step.nextClearance
  exact
    { box := old.box
      refinesAmbient := RFAP.Boxes.Box.refines_refl old.box
      proper := old.proper
      clearance := clearance
      rawWindingFour := by
        change RFAP.Winding.quadrupledBoxWinding step.nextTable.polynomial
            old.box = 4
        rw [step.next_winding_eq]
        exact old.rawWindingFour
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

/-- A total shrinking track for the transported owner.  Its ambient box is
literally the preceding owner box, so every later request retains finite owner
identity without relabelling roots. -/
def nextTrackAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    RFAP.ShrinkingTrack.WindingOneTrack
      (table.refine target positive).polynomial
      (chamber.owners.trackAt index).initial.box :=
  RFAP.ShrinkingTrack.ofInitial
    chamber.nextInput.degreeAtLeastTwo chamber.nextSquarefree
    chamber.nextInput.elimination (chamber.nextInitialAt index)

theorem nextTrackAt_initial_box
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    (chamber.nextTrackAt index).initial.box =
      (chamber.owners.trackAt index).initial.box := rfl

theorem nextTrackAt_pairwiseSeparated
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (left right : chamber.Index) (different : left ≠ right) :
    (chamber.nextTrackAt left).initial.box.Separated
      (chamber.nextTrackAt right).initial.box :=
  chamber.owners.trackAt_pairwiseSeparated left right different

/-- One arbitrary-accuracy refinement of a transported owner, strictly
inside the preceding owner's box. -/
def requestAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    RFAP.ShrinkingTrack.WindingOneState
      (table.refine target positive).polynomial
      (chamber.owners.trackAt index).initial.box :=
  (chamber.nextTrackAt index).refine
    (chamber.nextTrackAt index).initial epsilon epsilonPositive

theorem requestAt_strict_owner
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    (chamber.requestAt index epsilon epsilonPositive).box.StrictInterior
      (chamber.owners.trackAt index).initial.box :=
  (chamber.nextTrackAt index).strict
    (chamber.nextTrackAt index).initial epsilon epsilonPositive

theorem requestAt_accurate
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    (chamber.requestAt index epsilon epsilonPositive).box.diagonalSq ≤
      epsilon ^ 2 :=
  (chamber.nextTrackAt index).accurate
    (chamber.nextTrackAt index).initial epsilon epsilonPositive

theorem requestAt_pairwiseSeparated
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (left right : chamber.Index) (different : left ≠ right)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    (chamber.requestAt left epsilon epsilonPositive).box.Separated
      (chamber.requestAt right epsilon epsilonPositive).box :=
  RFAP.Boxes.Box.Separated.of_refines
    (chamber.nextTrackAt_pairwiseSeparated left right different)
    ((chamber.nextTrackAt left).nested
      (chamber.nextTrackAt left).initial epsilon epsilonPositive)
    ((chamber.nextTrackAt right).nested
      (chamber.nextTrackAt right).initial epsilon epsilonPositive)

/-! ### CCL observations of every transported owner -/

/-- Empty-word persistent CCL state for one transported owner. -/
def persistentInitialAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) :
    CCL.PersistentTrack.State (chamber.nextTrackAt index) :=
  CCL.PersistentTrack.State.initial (chamber.nextTrackAt index)

/-- One persistent bit-and-accuracy request on a transported owner. -/
def persistentRequestAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    CCL.PersistentTrack.State (chamber.nextTrackAt index) :=
  (chamber.persistentInitialAt index).request epsilon epsilonPositive count

/-- Parallel exact rational sample request on the same deterministic
transported track.  This supplies the polynomial residual certificate while
the persistent state supplies the already-running raw CCL word. -/
def sampleRequestAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    CCL.BoxRFAPBridge.Request
      (chamber.nextTrackAt index) (chamber.nextTrackAt index).initial
      epsilon epsilonPositive :=
  CCL.BoxRFAPBridge.request (chamber.nextTrackAt index)
    (chamber.nextTrackAt index).initial epsilon epsilonPositive

theorem persistentRequestAt_box_eq_sampleRequestAt
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).numerical.box =
      (chamber.sampleRequestAt index epsilon epsilonPositive).next.box := rfl

theorem persistentRequestAt_word_length
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).cursor.machine.emitted.length =
      count := by
  have initialLength :
      (chamber.persistentInitialAt index).cursor.machine.emitted.length = 0 := rfl
  have length := (chamber.persistentInitialAt index).request_word_length
    epsilon epsilonPositive count
  rw [initialLength, Nat.zero_add] at length
  exact length

theorem persistentRequestAt_box_refines_owner
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).numerical.box.Refines
      (chamber.owners.trackAt index).initial.box := by
  exact (chamber.persistentRequestAt index epsilon epsilonPositive count).numericalRefinesInitial

theorem persistentRequestAt_accurate
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) (count : Nat) :
    (chamber.persistentRequestAt index epsilon epsilonPositive count).numerical.box.diagonalSq ≤
      epsilon ^ 2 :=
  (chamber.persistentInitialAt index).request_box_accurate epsilon
    epsilonPositive count

theorem persistentRequestAt_pairwiseSeparated
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (left right : chamber.Index) (different : left ≠ right)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (count : Nat) :
    (chamber.persistentRequestAt left epsilon epsilonPositive count).numerical.box.Separated
      (chamber.persistentRequestAt right epsilon epsilonPositive count).numerical.box :=
  RFAP.Boxes.Box.Separated.of_refines
    (chamber.owners.trackAt_pairwiseSeparated left right different)
    (chamber.persistentRequestAt_box_refines_owner left epsilon
      epsilonPositive count)
    (chamber.persistentRequestAt_box_refines_owner right epsilon
      epsilonPositive count)

theorem sampleRequestAt_residual_le
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) :
    normSq
        ((table.refine target positive).polynomial.eval
          (chamber.sampleRequestAt index epsilon epsilonPositive).sample.point) ≤
      CCL.BoxRFAPBridge.residualConstant
          (table.refine target positive).polynomial
          (chamber.owners.trackAt index).initial.box * epsilon ^ 2 :=
  (chamber.sampleRequestAt index epsilon epsilonPositive).sampleResidual_le_requested
    chamber.nextInput.degreePositive

/-- Every live parser candidate after the request remains owned by the same
preceding rational root box. -/
theorem persistentRequestAt_candidate_in_owner
    {table : CoefficientTable} {target : Coordinate}
    {positive : 0 < target}
    (chamber : HigherChamber table target positive)
    (index : chamber.Index) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon) (count : Nat)
    {tail : Gaussian}
    (possible : CCL.ProgressiveMachineSemantics.SemanticMode.possible
      (chamber.persistentRequestAt index epsilon epsilonPositive count).cursor.machine.mode
      tail) :
    ∃ value : Gaussian,
      (chamber.owners.trackAt index).initial.box.Contains value ∧
        (CCL.PersistentProgressive.Machine.image
          (chamber.persistentRequestAt index epsilon epsilonPositive count).cursor.machine
          tail).Equivalent (CCL.Proj.affine value) := by
  exact (chamber.persistentRequestAt index epsilon epsilonPositive count).candidate_in_initial_box
    possible

end HigherChamber

/-! ## Certified simple-root chambers for repeatable continuation -/

/-- Per-owner allowance targets which simultaneously retain the reference
Bézout separation and the owner's initial boundary clearance. -/
def simpleRootOwnerTargets
    (reference : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (owners : OwnerFamily reference.polynomial reference.degree) :
    List Coordinate :=
  List.ofFn fun index : Fin reference.degree =>
    min
      (reference.bezoutStabilityTarget squarefree
        (owners.owner index).box)
      (reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance)

theorem simpleRootOwnerTargets_positive
    (reference : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (owners : OwnerFamily reference.polynomial reference.degree) :
    ∀ target ∈ simpleRootOwnerTargets reference squarefree owners,
      0 < target := by
  intro target member
  rw [simpleRootOwnerTargets, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact lt_min
    (reference.bezoutStabilityTarget_pos squarefree
      (owners.owner index).box)
    (reference.stabilityTarget_pos (owners.owner index).box
      (owners.owner index).clearance)

/-- One common positive allowance target for the complete finite owner
family. -/
def simpleRootChamberTarget
    (reference : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (owners : OwnerFamily reference.polynomial reference.degree) : Coordinate :=
  finitePositiveMinimum
    (simpleRootOwnerTargets reference squarefree owners)

theorem simpleRootChamberTarget_pos
    (reference : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (owners : OwnerFamily reference.polynomial reference.degree) :
    0 < simpleRootChamberTarget reference squarefree owners :=
  finitePositiveMinimum_pos _
    (simpleRootOwnerTargets_positive reference squarefree owners)

theorem simpleRootChamberTarget_le_bezout
    (reference : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (owners : OwnerFamily reference.polynomial reference.degree)
    (index : Fin reference.degree) :
    simpleRootChamberTarget reference squarefree owners ≤
      reference.bezoutStabilityTarget squarefree
        (owners.owner index).box := by
  have commonLe := finitePositiveMinimum_le_of_mem
    (values := simpleRootOwnerTargets reference squarefree owners)
    (value := min
      (reference.bezoutStabilityTarget squarefree
        (owners.owner index).box)
      (reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance)) (by
      rw [simpleRootOwnerTargets, List.mem_ofFn]
      exact ⟨index, rfl⟩)
  exact commonLe.trans (min_le_left _ _)

theorem simpleRootChamberTarget_le_stability
    (reference : CoefficientTable)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (owners : OwnerFamily reference.polynomial reference.degree)
    (index : Fin reference.degree) :
    simpleRootChamberTarget reference squarefree owners ≤
      reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance := by
  have commonLe := finitePositiveMinimum_le_of_mem
    (values := simpleRootOwnerTargets reference squarefree owners)
    (value := min
      (reference.bezoutStabilityTarget squarefree
        (owners.owner index).box)
      (reference.stabilityTarget (owners.owner index).box
        (owners.owner index).clearance)) (by
      rw [simpleRootOwnerTargets, List.mem_ofFn]
      exact ⟨index, rfl⟩)
  exact commonLe.trans (min_le_right _ _)

/-- Finite input certificate for one progressive simple-root chamber.  The
reference polynomial is exact and squarefree, its degree-many owners are
already isolated, and the currently displayed coefficient states have
crossed the single computed chamber target. -/
structure SimpleRootChamber (reference : CoefficientTable) where
  degreeAtLeastTwo : 2 ≤ reference.degree
  squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial
  owners : OwnerFamily reference.polynomial reference.degree
  referenceSmall : CoefficientTable.AllowancesLt reference.entries
    (simpleRootChamberTarget reference squarefree owners)
  referenceMaximality : ∀ {familyCount : Nat}
    (family : Fin familyCount → RFAP.ShrinkingTrack.WindingOneTrack
      reference.polynomial
      (RFAP.GlobalWinding.largeSquareBox reference.polynomial)),
    (∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) →
    familyCount ≤ reference.degree

namespace SimpleRootChamber

abbrev Index {reference : CoefficientTable}
    (_chamber : SimpleRootChamber reference) := Fin reference.degree

def target {reference : CoefficientTable}
    (chamber : SimpleRootChamber reference) : Coordinate :=
  simpleRootChamberTarget reference chamber.squarefree chamber.owners

theorem target_pos {reference : CoefficientTable}
    (chamber : SimpleRootChamber reference) : 0 < chamber.target :=
  simpleRootChamberTarget_pos reference chamber.squarefree chamber.owners

theorem target_le_bezout {reference : CoefficientTable}
    (chamber : SimpleRootChamber reference) (index : chamber.Index) :
    chamber.target ≤ reference.bezoutStabilityTarget chamber.squarefree
      (chamber.owners.owner index).box :=
  simpleRootChamberTarget_le_bezout reference chamber.squarefree
    chamber.owners index

theorem target_le_stability {reference : CoefficientTable}
    (chamber : SimpleRootChamber reference) (index : chamber.Index) :
    chamber.target ≤ reference.stabilityTarget
      (chamber.owners.owner index).box
      (chamber.owners.owner index).clearance :=
  simpleRootChamberTarget_le_stability reference chamber.squarefree
    chamber.owners index

/-- Public chamber constructor from the complete Paper-I isolation result. -/
def ofResult
    (reference : CoefficientTable) (degreeAtLeastTwo : 2 ≤ reference.degree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate reference.polynomial)
    (result : CCL.BoxRFAPBridge.Result reference.polynomial)
    (referenceSmall : CoefficientTable.AllowancesLt reference.entries
      (simpleRootChamberTarget reference squarefree
        (OwnerFamily.ofTableResult reference result))) :
    SimpleRootChamber reference where
  degreeAtLeastTwo := degreeAtLeastTwo
  squarefree := squarefree
  owners := OwnerFamily.ofTableResult reference result
  referenceSmall := referenceSmall
  referenceMaximality := by
    intro familyCount family pairwise
    have bound := result.boxes.maximality family pairwise
    simpa only [reference.polynomial_natDegree] using bound

end SimpleRootChamber

/-! ## Executable chamber-continuation state -/

/-- One finite state of the repeatable simple-root controller.  `budgetBox`
is the retained parent on which the *next* coefficient perturbation was
budgeted; the live owner may already be strictly smaller. -/
structure ChamberContinuationState
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference)
    where
  table : CoefficientTable
  same : CoefficientTable.SameChannels reference.entries table.entries
  chamberSmall : CoefficientTable.AllowancesLt table.entries chamber.target
  family : OwnerFamily table.polynomial reference.degree
  refinesSeed : ∀ index : chamber.Index,
    (family.owner index).box.Refines (chamber.owners.owner index).box
  guardTarget : Coordinate
  guardPositive : 0 < guardTarget
  guardSmall : CoefficientTable.AllowancesLt table.entries guardTarget
  budgetBox : chamber.Index → Box
  ownerRefinesBudget : ∀ index : chamber.Index,
    (family.owner index).box.Refines (budgetBox index)
  stable : ∀ index : chamber.Index,
    table.refinementEvaluationBound guardTarget (budgetBox index) <
      (family.owner index).clearance.bound

namespace ChamberContinuationState

def initial
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference) :
    ChamberContinuationState chamber where
  table := reference
  same := CoefficientTable.sameChannels_refl reference.entries
  chamberSmall := chamber.referenceSmall
  family := chamber.owners
  refinesSeed := fun index =>
    RFAP.Boxes.Box.refines_refl (chamber.owners.owner index).box
  guardTarget := chamber.target
  guardPositive := chamber.target_pos
  guardSmall := chamber.referenceSmall
  budgetBox := fun index => (chamber.owners.owner index).box
  ownerRefinesBudget := fun index =>
    RFAP.Boxes.Box.refines_refl (chamber.owners.owner index).box
  stable := by
    intro index
    have targetLe := chamber.target_le_stability index
    have scaleNonnegative : 0 ≤ reference.refinementEvaluationScale
        (chamber.owners.owner index).box :=
      (reference.refinementEvaluationScale_pos
        (chamber.owners.owner index).box).le
    have localBudget := reference.refinementEvaluationBound_stabilityTarget_lt
      (chamber.owners.owner index).box
      (chamber.owners.owner index).clearance
    rw [reference.refinementEvaluationBound_eq_target_mul_scale] at localBudget ⊢
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      targetLe scaleNonnegative).trans_lt localBudget

theorem table_degree
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) :
    state.table.degree = reference.degree :=
  (CoefficientTable.degree_eq_of_sameChannels state.same).symm

theorem polynomialDegreeAtLeastTwo
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) :
    2 ≤ state.table.polynomial.natDegree := by
  rw [state.table.polynomial_natDegree, state.table_degree]
  exact chamber.degreeAtLeastTwo

theorem polynomialDegreePositive
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) :
    0 < state.table.polynomial.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le state.polynomialDegreeAtLeastTwo

/-- Exact lower bound for the clearance after transporting the next
coefficient reading across the current owner boundary. -/
def transportedClearanceBound
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (index : chamber.Index) :
    Coordinate :=
  ((state.family.owner index).clearance.bound -
      state.table.refinementEvaluationBound state.guardTarget
        (state.budgetBox index)) ^ 2 /
    (4 * RFAP.PolynomialBounds.denseEvalNormMajorant state.table.polynomial
      (state.family.owner index).box)

theorem transportedClearanceBound_pos
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (index : chamber.Index) :
    0 < state.transportedClearanceBound index := by
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct (state.stable index)) 2)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.PolynomialBounds.denseEvalNormMajorant_pos
        state.table.polynomial (state.family.owner index).box))

/-- Pre-reading lower bound for the clearance of the next extracted owner. -/
def predictedOwnerClearance
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (index : chamber.Index)
    (epsilon : Coordinate) : Coordinate :=
  RFAP.NewtonExtraction.predictedExtractionClearanceData
    (state.family.owner index).box
    (RFAP.DerivativeSeparation.approximateMargin chamber.squarefree.right
      (chamber.owners.owner index).box)
    (state.transportedClearanceBound index)
    (reference.admittedExtractionLipschitz chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionTaylor chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionDerivative chamber.target
      (state.family.owner index).box)
    epsilon

theorem predictedOwnerClearance_pos
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (index : chamber.Index)
    {epsilon : Coordinate} (positive : 0 < epsilon) :
    0 < state.predictedOwnerClearance index epsilon := by
  exact RFAP.NewtonExtraction.predictedExtractionClearanceData_pos
    (state.family.owner index).proper
    (RFAP.DerivativeSeparation.approximateMargin_pos
      chamber.squarefree.right (chamber.owners.owner index).box)
    (state.transportedClearanceBound_pos index)
    (reference.admittedExtractionLipschitz_pos chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionTaylor_pos chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionDerivative_pos chamber.target
      (state.family.owner index).box)
    positive

/-- Per-owner guard target which makes the following coefficient
perturbation smaller than the predicted extracted clearance. -/
def nextOwnerGuardTarget
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (index : chamber.Index)
    (epsilon : Coordinate) : Coordinate :=
  state.table.stabilityTargetForBound (state.family.owner index).box
    (state.predictedOwnerClearance index epsilon)

theorem nextOwnerGuardTarget_pos
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (index : chamber.Index)
    {epsilon : Coordinate} (positive : 0 < epsilon) :
    0 < state.nextOwnerGuardTarget index epsilon :=
  state.table.stabilityTargetForBound_pos (state.family.owner index).box
    (state.predictedOwnerClearance_pos index positive)

def nextOwnerGuardTargets
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate) :
    List Coordinate :=
  List.ofFn fun index : chamber.Index =>
    state.nextOwnerGuardTarget index epsilon

def nextGuardTarget
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate) :
    Coordinate :=
  finitePositiveMinimum (state.nextOwnerGuardTargets epsilon)

theorem nextGuardTarget_pos
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) {epsilon : Coordinate}
    (positive : 0 < epsilon) : 0 < state.nextGuardTarget epsilon := by
  apply finitePositiveMinimum_pos
  intro target member
  rw [nextOwnerGuardTargets, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact state.nextOwnerGuardTarget_pos index positive

theorem nextGuardTarget_le_owner
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (index : chamber.Index) :
    state.nextGuardTarget epsilon ≤
      state.nextOwnerGuardTarget index epsilon := by
  apply finitePositiveMinimum_le_of_mem
  rw [nextOwnerGuardTargets, List.mem_ofFn]
  exact ⟨index, rfl⟩

/-- Single simultaneous coefficient request, chosen below the permanent
chamber target, the current transport guard, and every predicted next guard. -/
def coefficientTarget
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate) :
    Coordinate :=
  min chamber.target (min state.guardTarget (state.nextGuardTarget epsilon))

theorem coefficientTarget_pos
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) {epsilon : Coordinate}
    (positive : 0 < epsilon) : 0 < state.coefficientTarget epsilon :=
  lt_min chamber.target_pos
    (lt_min state.guardPositive (state.nextGuardTarget_pos positive))

theorem coefficientTarget_le_chamber
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate) :
    state.coefficientTarget epsilon ≤ chamber.target := min_le_left _ _

theorem coefficientTarget_le_guard
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate) :
    state.coefficientTarget epsilon ≤ state.guardTarget :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem coefficientTarget_le_nextGuard
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate) :
    state.coefficientTarget epsilon ≤ state.nextGuardTarget epsilon :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- The exact simultaneous coefficient reading used by one continuation
step. -/
def nextTable
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) : CoefficientTable :=
  state.table.refine (state.coefficientTarget epsilon)
    (state.coefficientTarget_pos positive)

theorem same_nextTable
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    CoefficientTable.SameChannels state.table.entries
      (state.nextTable epsilon positive).entries :=
  state.table.sameChannels_refine (state.coefficientTarget epsilon)
    (state.coefficientTarget_pos positive)

theorem reference_same_nextTable
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    CoefficientTable.SameChannels reference.entries
      (state.nextTable epsilon positive).entries :=
  CoefficientTable.sameChannels_trans state.same
    (state.same_nextTable epsilon positive)

theorem nextTable_small_coefficientTarget
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    CoefficientTable.AllowancesLt (state.nextTable epsilon positive).entries
      (state.coefficientTarget epsilon) :=
  state.table.refine_allowances_lt (state.coefficientTarget epsilon)
    (state.coefficientTarget_pos positive)

theorem nextTable_chamberSmall
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    CoefficientTable.AllowancesLt (state.nextTable epsilon positive).entries
      chamber.target :=
  (state.nextTable_small_coefficientTarget epsilon positive).mono
    (state.coefficientTarget_le_chamber epsilon)

theorem nextTable_guardSmall
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    CoefficientTable.AllowancesLt (state.nextTable epsilon positive).entries
      state.guardTarget :=
  (state.nextTable_small_coefficientTarget epsilon positive).mono
    (state.coefficientTarget_le_guard epsilon)

theorem nextTable_nextGuardSmall
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    CoefficientTable.AllowancesLt (state.nextTable epsilon positive).entries
      (state.nextGuardTarget epsilon) :=
  (state.nextTable_small_coefficientTarget epsilon positive).mono
    (state.coefficientTarget_le_nextGuard epsilon)

def transferAt
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    CoarseStableChannelReadings state.table
      (state.nextTable epsilon positive) state.guardTarget
      state.guardPositive (state.family.owner index).box
      (state.budgetBox index) where
  same := state.same_nextTable epsilon positive
  leftSmall := state.guardSmall
  rightSmall := state.nextTable_guardSmall epsilon positive
  proper := (state.family.owner index).proper
  refinesBudget := state.ownerRefinesBudget index
  clearance := (state.family.owner index).clearance
  budget_lt := state.stable index

@[simp] theorem transferAt_clearance_bound
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.transferAt epsilon positive index).explicitRightClearance.bound =
      state.transportedClearanceBound index := rfl

theorem nextTableDegreeAtLeastTwo
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    2 ≤ (state.nextTable epsilon positive).polynomial.natDegree := by
  rw [(state.nextTable epsilon positive).polynomial_natDegree,
    ← CoefficientTable.degree_eq_of_sameChannels
      (state.same_nextTable epsilon positive), state.table_degree]
  exact chamber.degreeAtLeastTwo

theorem nextTableDegreePositive
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    0 < (state.nextTable epsilon positive).polynomial.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le
    (state.nextTableDegreeAtLeastTwo epsilon positive)

/-- Robust derivative separation for the next reading, restricted from the
fixed reference owner to the current live owner. -/
def separationAt
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    RFAP.DerivativeSeparation.Certificate
      (state.nextTable epsilon positive).polynomial
      (state.family.owner index).box := by
  let seedBox := (chamber.owners.owner index).box
  let localTarget := reference.bezoutStabilityTarget chamber.squarefree seedBox
  have referenceLocal : CoefficientTable.AllowancesLt reference.entries
      localTarget := chamber.referenceSmall.mono (chamber.target_le_bezout index)
  have nextLocal : CoefficientTable.AllowancesLt
      (state.nextTable epsilon positive).entries localTarget :=
    (state.nextTable_chamberSmall epsilon positive).mono
      (chamber.target_le_bezout index)
  let globalSeparation := reference.robustDerivativeSeparation
    (state.nextTable epsilon positive) chamber.squarefree seedBox
    (state.reference_same_nextTable epsilon positive) referenceLocal nextLocal
  exact globalSeparation.restrict (state.refinesSeed index)

@[simp] theorem separationAt_margin
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.separationAt epsilon positive index).margin =
      RFAP.DerivativeSeparation.approximateMargin chamber.squarefree.right
        (chamber.owners.owner index).box := rfl

def majorantsAt
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    RFAP.NewtonExtraction.ExtractionMajorants
      (state.nextTable epsilon positive).polynomial
      (state.family.owner index).box :=
  reference.admittedExtractionMajorants (state.nextTable epsilon positive)
    chamber.target chamber.target_pos
    (state.reference_same_nextTable epsilon positive) chamber.referenceSmall
    (state.nextTable_chamberSmall epsilon positive)
    (state.family.owner index).box

@[simp] theorem majorantsAt_lipschitz
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.majorantsAt epsilon positive index).lipschitz =
      reference.admittedExtractionLipschitz chamber.target
        (state.family.owner index).box := rfl

@[simp] theorem majorantsAt_taylor
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.majorantsAt epsilon positive index).taylor =
      reference.admittedExtractionTaylor chamber.target
        (state.family.owner index).box := rfl

@[simp] theorem majorantsAt_derivative
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.majorantsAt epsilon positive index).derivative =
      reference.admittedExtractionDerivative chamber.target
        (state.family.owner index).box := rfl

def nextElimination
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    RFAP.AxisSafeCuts.AxisEliminationCertificate
      (state.nextTable epsilon positive).polynomial
      (RFAP.AxisSafeCuts.separatedEliminationDegree
        (state.nextTable epsilon positive).polynomial) :=
  RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
    (state.nextTable epsilon positive).polynomial
    (RFAP.GlobalWinding.isZero_false_of_natDegree_pos
      (state.nextTableDegreePositive epsilon positive))
    (state.nextTableDegreePositive epsilon positive)

def transportedRawStateAt
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    RFAP.RawSubdivision.RawWindingState
      (state.nextTable epsilon positive).polynomial
      (state.family.owner index).box where
  box := (state.family.owner index).box
  refinesAmbient := RFAP.Boxes.Box.refines_refl _
  proper := (state.family.owner index).proper
  clearance := (state.transferAt epsilon positive index).explicitRightClearance
  rawWinding_ne := by
    intro zero
    have transported := (state.transferAt epsilon positive index).rightWinding_eq
    rw [transported, (state.family.owner index).rawWindingFour] at zero
    exact (show (4 : Int) ≠ 0 by decide) zero

@[simp] theorem transportedRawStateAt_box
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.transportedRawStateAt epsilon positive index).box =
      (state.family.owner index).box := rfl

@[simp] theorem transportedRawStateAt_clearance_bound
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.transportedRawStateAt epsilon positive index).clearance.bound =
      state.transportedClearanceBound index :=
  state.transferAt_clearance_bound epsilon positive index

/-- Fully explicit Newton extraction for one owner of the next reading. -/
def extractionAt
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    RFAP.NewtonExtraction.MajorizedSeparatedOutput
      (state.transportedRawStateAt epsilon positive index)
      (state.separationAt epsilon positive index)
      (state.majorantsAt epsilon positive index) epsilon :=
  RFAP.NewtonExtraction.extractSeparatedMajorized
    (state.nextTableDegreeAtLeastTwo epsilon positive)
    (state.transportedRawStateAt epsilon positive index)
    (state.separationAt epsilon positive index)
    (state.majorantsAt epsilon positive index)
    (state.nextElimination epsilon positive) positive

/-- The degree-indexed extracted owner family for the next coefficient
reading. -/
def nextFamily
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    OwnerFamily (state.nextTable epsilon positive).polynomial
      reference.degree where
  owner index :=
    let output := state.extractionAt epsilon positive index
    { box := output.core.box
      proper := output.core.proper
      clearance := output.clearance
      rawWindingFour := output.core.rawWindingFour }
  pairwiseSeparated := by
    intro left right different
    exact RFAP.Boxes.Box.Separated.of_refines
      (state.family.pairwiseSeparated left right different)
      (state.extractionAt epsilon positive left).core.strictCurrent.refines
      (state.extractionAt epsilon positive right).core.strictCurrent.refines

theorem nextFamily_nested
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.nextFamily epsilon positive).owner index).box.Refines
      (state.family.owner index).box :=
  (state.extractionAt epsilon positive index).core.strictCurrent.refines

theorem nextFamily_strict
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.nextFamily epsilon positive).owner index).box.StrictInterior
      (state.family.owner index).box :=
  (state.extractionAt epsilon positive index).core.strictCurrent

theorem nextFamily_accurate
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.nextFamily epsilon positive).owner index).box.diagonalSq ≤
      epsilon ^ 2 :=
  (state.extractionAt epsilon positive index).core.diagonalSq_le

theorem predictedOwnerClearance_le_next
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    state.predictedOwnerClearance index epsilon ≤
      ((state.nextFamily epsilon positive).owner index).clearance.bound := by
  have predicted :=
    (state.extractionAt epsilon positive index).predicted_clearance_le
  rw [RFAP.NewtonExtraction.predictedExtractionClearance_eq_data] at predicted
  simpa only [predictedOwnerClearance, separationAt_margin,
    transferAt_clearance_bound, majorantsAt_lipschitz, majorantsAt_taylor,
    majorantsAt_derivative, transportedRawStateAt_box,
    transportedRawStateAt_clearance_bound, nextFamily] using predicted

theorem nextFamily_stable
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    (state.nextTable epsilon positive).refinementEvaluationBound
        (state.nextGuardTarget epsilon) (state.family.owner index).box <
      ((state.nextFamily epsilon positive).owner index).clearance.bound := by
  have commonLe := state.nextGuardTarget_le_owner epsilon index
  have scaleNonnegative : 0 ≤ state.table.refinementEvaluationScale
      (state.family.owner index).box :=
    (state.table.refinementEvaluationScale_pos
      (state.family.owner index).box).le
  have commonBudgetLe : state.table.refinementEvaluationBound
      (state.nextGuardTarget epsilon) (state.family.owner index).box ≤
      state.table.refinementEvaluationBound
        (state.nextOwnerGuardTarget index epsilon)
        (state.family.owner index).box := by
    rw [state.table.refinementEvaluationBound_eq_target_mul_scale,
      state.table.refinementEvaluationBound_eq_target_mul_scale]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      commonLe scaleNonnegative
  have localBudget :=
    state.table.refinementEvaluationBound_stabilityTargetForBound_lt
      (state.family.owner index).box
      (state.predictedOwnerClearance_pos index positive)
  have currentStable : state.table.refinementEvaluationBound
      (state.nextGuardTarget epsilon) (state.family.owner index).box <
      ((state.nextFamily epsilon positive).owner index).clearance.bound :=
    commonBudgetLe.trans_lt
      (localBudget.trans_le
        (state.predictedOwnerClearance_le_next epsilon positive index))
  rw [← state.table.refinementEvaluationBound_eq_of_sameChannels
    (state.nextTable epsilon positive) (state.same_nextTable epsilon positive)
    (state.nextGuardTarget epsilon) (state.family.owner index).box]
  exact currentStable

/-- One complete executable coefficient/root refinement. -/
def next
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) : ChamberContinuationState chamber where
  table := state.nextTable epsilon positive
  same := state.reference_same_nextTable epsilon positive
  chamberSmall := state.nextTable_chamberSmall epsilon positive
  family := state.nextFamily epsilon positive
  refinesSeed := by
    intro index
    exact (state.nextFamily_nested epsilon positive index).trans
      (state.refinesSeed index)
  guardTarget := state.nextGuardTarget epsilon
  guardPositive := state.nextGuardTarget_pos positive
  guardSmall := state.nextTable_nextGuardSmall epsilon positive
  budgetBox := fun index => (state.family.owner index).box
  ownerRefinesBudget := state.nextFamily_nested epsilon positive
  stable := state.nextFamily_stable epsilon positive

@[simp] theorem next_table
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (state.next epsilon positive).table = state.nextTable epsilon positive := rfl

theorem next_nested
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.next epsilon positive).family.owner index).box.Refines
      (state.family.owner index).box :=
  state.nextFamily_nested epsilon positive index

theorem next_strict
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.next epsilon positive).family.owner index).box.StrictInterior
      (state.family.owner index).box :=
  state.nextFamily_strict epsilon positive index

theorem next_accurate
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (state : ChamberContinuationState chamber) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : chamber.Index) :
    ((state.next epsilon positive).family.owner index).box.diagonalSq ≤
      epsilon ^ 2 :=
  state.nextFamily_accurate epsilon positive index

end ChamberContinuationState

/-! ## Repeatable coefficient/root continuation programs -/

/-- A finite, executable continuation program for all simple root owners of
one progressive monic coefficient table.  A state contains one simultaneous
coefficient reading and one rational owner box for every degree index.  The
single refinement operation advances the coefficient table and every owner
together; the laws state the numerical facts needed by the generic CCL
transducer.

This structure is the exact boundary between the quantitative chamber
argument and the arithmetic output machinery.  In particular, the
`refine_table` field prevents an implementation from silently replacing the
progressive coefficients by an unrelated sequence of rational polynomials. -/
structure RootContinuation (initialTable : CoefficientTable) where
  State : Type
  initial : State
  table : State → CoefficientTable
  initial_table : table initial = initialTable
  table_degree : ∀ state, (table state).degree = initialTable.degree
  degreeAtLeastTwo : 2 ≤ initialTable.degree
  box : State → Fin initialTable.degree → Box
  proper : ∀ state index, (box state index).Proper
  clearance : ∀ state index,
    RFAP.BoxClearance.BoundaryClearance
      (table state).polynomial (box state index)
  rawWindingFour : ∀ state index,
    RFAP.Winding.quadrupledBoxWinding
      (table state).polynomial (box state index) = 4
  refinesInitial : ∀ state index,
    (box state index).Refines (box initial index)
  pairwiseSeparated : ∀ state left right, left ≠ right →
    (box state left).Separated (box state right)
  coefficientTarget : State → Coordinate → Coordinate
  coefficientTarget_pos : ∀ state {epsilon}, 0 < epsilon →
    0 < coefficientTarget state epsilon
  refine : (state : State) → (epsilon : Coordinate) →
    0 < epsilon → State
  refine_table : ∀ state epsilon positive,
    table (refine state epsilon positive) =
      (table state).refine (coefficientTarget state epsilon)
        (coefficientTarget_pos state positive)
  nested : ∀ state epsilon positive index,
    (box (refine state epsilon positive) index).Refines (box state index)
  strict : ∀ state epsilon positive index,
    (box (refine state epsilon positive) index).StrictInterior
      (box state index)
  accurate : ∀ state epsilon positive index,
    (box (refine state epsilon positive) index).diagonalSq ≤ epsilon ^ 2

/-- A finite request history is the small-universe operational state exposed
to the generic CCL process.  Replaying it deterministically reconstructs the
proof-rich chamber state; the coefficient channels themselves remain fixed
parameters rather than data stored inside the process state. -/
inductive ChamberRequestHistory : Type
  | initial
  | refine (previous : ChamberRequestHistory) (epsilon : Coordinate)
      (positive : 0 < epsilon)

/-- Deterministically replay a finite request history through the certified
controller. -/
def SimpleRootChamber.run
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference) :
    ChamberRequestHistory → ChamberContinuationState chamber
  | .initial => ChamberContinuationState.initial chamber
  | .refine previous epsilon positive =>
      (chamber.run previous).next epsilon positive

/-- The executable continuation generated by a finite simple-root chamber.
No later reading is required to provide a newly computed exact squarefree
Bézout identity: the reference identity supplies robust derivative separation
through the chamber allowance, while every other field is recalculated from
finite rational data. -/
def SimpleRootChamber.continuation
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference) :
    RootContinuation reference where
  State := ChamberRequestHistory
  initial := .initial
  table := fun history => (chamber.run history).table
  initial_table := rfl
  table_degree := fun history => (chamber.run history).table_degree
  degreeAtLeastTwo := chamber.degreeAtLeastTwo
  box := fun history index => ((chamber.run history).family.owner index).box
  proper := fun history index =>
    ((chamber.run history).family.owner index).proper
  clearance := fun history index =>
    ((chamber.run history).family.owner index).clearance
  rawWindingFour := fun history index =>
    ((chamber.run history).family.owner index).rawWindingFour
  refinesInitial := fun history index => (chamber.run history).refinesSeed index
  pairwiseSeparated := fun history =>
    (chamber.run history).family.pairwiseSeparated
  coefficientTarget := fun history epsilon =>
    (chamber.run history).coefficientTarget epsilon
  coefficientTarget_pos := fun history _epsilon positive =>
    (chamber.run history).coefficientTarget_pos positive
  refine := fun history epsilon positive =>
    .refine history epsilon positive
  refine_table := by
    intro history epsilon positive
    rfl
  nested := fun history epsilon positive index =>
    (chamber.run history).next_nested epsilon positive index
  strict := fun history epsilon positive index =>
    (chamber.run history).next_strict epsilon positive index
  accurate := fun history epsilon positive index =>
    (chamber.run history).next_accurate epsilon positive index

namespace RootContinuation

abbrev Index {initialTable : CoefficientTable}
    (_continuation : RootContinuation initialTable) :=
  Fin initialTable.degree

theorem degreePositive
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable) :
    0 < initialTable.degree :=
  (by decide : (0 : Nat) < 2).trans_le continuation.degreeAtLeastTwo

theorem polynomialDegreePositive
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (state : continuation.State) :
    0 < (continuation.table state).polynomial.natDegree := by
  rw [(continuation.table state).polynomial_natDegree,
    continuation.table_degree state]
  exact continuation.degreePositive

theorem polynomialDegreeAtLeastTwo
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (state : continuation.State) :
    2 ≤ (continuation.table state).polynomial.natDegree := by
  rw [(continuation.table state).polynomial_natDegree,
    continuation.table_degree state]
  exact continuation.degreeAtLeastTwo

/-- The displayed anchor of every owner is a coefficient-computed residual
sample.  Nonzero winding, rather than an assumed root point, supplies the
bound. -/
theorem anchorResidual_le
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (state : continuation.State) (index : continuation.Index) :
    normSq
        ((continuation.table state).polynomial.eval
          (continuation.box state index).anchor) ≤
      RFAP.LocalExtraction.anchorResidualBound
        (continuation.table state).polynomial
        (continuation.box continuation.initial index)
        (continuation.box state index) := by
  apply RFAP.LocalExtraction.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
    (continuation.table state).polynomial
    (continuation.polynomialDegreePositive state)
    (continuation.refinesInitial state index)
    (continuation.proper state index)
  intro zero
  rw [continuation.rawWindingFour state index] at zero
  exact (show (4 : Int) ≠ 0 by decide) zero

/-- After a request, every owner anchor has residual quadrance at most its
finite Horner-Lipschitz coefficient times the requested squared radius. -/
theorem refinedAnchorResidual_le_requested
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (state : continuation.State) (index : continuation.Index)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    let next := continuation.refine state epsilon positive
    normSq
        ((continuation.table next).polynomial.eval
          (continuation.box next index).anchor) ≤
      RFAP.PolynomialBounds.denseLipschitzBound
          (continuation.table next).polynomial
          (continuation.box continuation.initial index) * epsilon ^ 2 := by
  let next := continuation.refine state epsilon positive
  have residual := continuation.anchorResidual_le next index
  exact residual.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (continuation.accurate state epsilon positive index)
      (RFAP.PolynomialBounds.denseLipschitzBound_pos
        (continuation.table next).polynomial
        (continuation.box continuation.initial index)).le)

/-- One root owner as a progressive squared-error process.  Its possible
values are exactly the rational points in the current certified box, and a
process refinement invokes the common coefficient/root continuation step. -/
def toProcess
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) : CCL.ProgressiveEnclosures.Process where
  State := continuation.State
  ball state :=
    CCL.ArithmeticEnclosures.Ball.ofBox (continuation.box state index)
  Possible state value := (continuation.box state index).Contains value
  witness state :=
    ⟨(continuation.box state index).anchor,
      (continuation.box state index).contains_anchor⟩
  possible_inside := by
    intro state value possible
    exact CCL.ArithmeticEnclosures.Ball.contains_ofBox possible
  refine state target positive :=
    continuation.refine state
      (CCL.BoxedNameProcess.accuracyRadius target)
      (CCL.BoxedNameProcess.accuracyRadius_pos positive)
  refine_persists := by
    intro state target positive value possible
    exact (continuation.nested state
      (CCL.BoxedNameProcess.accuracyRadius target)
      (CCL.BoxedNameProcess.accuracyRadius_pos positive) index).contains
        possible
  accurate := by
    intro state target positive
    exact (continuation.accurate state
      (CCL.BoxedNameProcess.accuracyRadius target)
      (CCL.BoxedNameProcess.accuracyRadius_pos positive) index).trans_lt
        (CCL.BoxedNameProcess.accuracyRadius_sq_lt positive)
  centerBound :=
    (continuation.box continuation.initial index).normSqBound
  centerBound_nonneg :=
    (continuation.box continuation.initial index).normSqBound_nonneg
  center_bounded := by
    intro state
    exact (continuation.box continuation.initial index).normSq_le_normSqBound
      ((continuation.refinesInitial state index).contains
        (continuation.box state index).contains_anchor)

/-- The arithmetic-ready CCL name belonging to one persistent root owner. -/
def rootNameAt
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) : CCL.ProgressiveTransducer.Named :=
  { process := continuation.toProcess index
    state := continuation.initial }

/-- The complete degree-indexed family of arithmetic-ready root names. -/
def rootNames
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable) :
    Fin initialTable.degree → CCL.ProgressiveTransducer.Named :=
  continuation.rootNameAt

theorem rootNameAt_productive
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) (count : Nat) :
    (continuation.rootNameAt index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (continuation.rootNameAt index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (continuation.rootNameAt index).machine count).emitted.length =
        count :=
  (continuation.rootNameAt index).productive count

theorem rootNameAt_exact
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (continuation.toProcess index) continuation.initial
      (CCL.ProgressiveTransducer.advance
        (continuation.rootNameAt index).machine count) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact
    (continuation.rootNameAt index) count

/-- Start the persistent raw-word cursor for one owner. -/
def rootCursorAt
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) :
    CCL.PersistentProgressive.Cursor
      (continuation.toProcess index) continuation.initial :=
  CCL.PersistentProgressive.Cursor.initial
    (continuation.toProcess index) continuation.initial

theorem rootCursorAt_request_extends
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    (continuation.rootCursorAt index).machine.emitted.IsPrefix
      ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.emitted :=
  (continuation.rootCursorAt index).request_extends
    epsilonSq positive count

theorem rootCursorAt_request_length
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.emitted.length = count := by
  have length := (continuation.rootCursorAt index).request_length
    epsilonSq positive count
  have initialLength :
      (continuation.rootCursorAt index).machine.emitted.length = 0 := rfl
  rw [initialLength, Nat.zero_add] at length
  exact length

theorem rootCursorAt_request_chordalSq_le
    {initialTable : CoefficientTable}
    (continuation : RootContinuation initialTable)
    (index : continuation.Index) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat)
    {left right : Gaussian}
    (leftPossible : CCL.ProgressiveMachineSemantics.SemanticMode.possible
      ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.mode left)
    (rightPossible : CCL.ProgressiveMachineSemantics.SemanticMode.possible
      ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.mode right) :
    CCL.Chordal.chordalSq
        (((continuation.rootCursorAt index).request
          epsilonSq positive count).machine.image left)
        (((continuation.rootCursorAt index).request
          epsilonSq positive count).machine.image right) ≤ epsilonSq :=
  (continuation.rootCursorAt index).request_pair_chordalSq_le
    epsilonSq positive count leftPossible rightPossible

end RootContinuation

/-! ## Effective algebraic closure on the certified simple-root locus -/

/-- Finite unique-index ownership of a rational box by one chamber seed. -/
structure ChamberOwnership
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference)
    (box : Box) where
  owner : chamber.Index
  refines : box.Refines (chamber.owners.owner owner).box
  unique : ∀ candidate : chamber.Index,
    box.Refines (chamber.owners.owner candidate).box → candidate = owner

/-- Every live owner of the executable continuation retains its original and
uniquely determined finite owner index. -/
def SimpleRootChamber.ownershipAt
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference)
    (history : ChamberRequestHistory) (index : chamber.Index) :
    ChamberOwnership chamber
      (chamber.continuation.box history index) where
  owner := index
  refines := (chamber.run history).refinesSeed index
  unique := by
    intro candidate candidateRefines
    by_cases equal : candidate = index
    · exact equal
    · have separated := chamber.owners.pairwiseSeparated candidate index equal
      have distinct := separated.points_ne
        (candidateRefines.contains
          (chamber.continuation.box history index).contains_anchor)
        ((chamber.run history).refinesSeed index |>.contains
          (chamber.continuation.box history index).contains_anchor)
      exact (distinct rfl).elim

/-- Headline output.  The `Fin reference.degree` index is the exact finite
root count; `continuation` contains the executable simultaneous coefficient
and owner refinement, while `roots` exposes those same owners as productive
arithmetic-ready CCL names.  Maximality is certified at the chamber's exact
reference reading, from which every later owner keeps a unique identity. -/
structure EffectiveAlgebraicClosure
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference)
    where
  continuation : RootContinuation reference
  roots : Fin reference.degree → CCL.ProgressiveTransducer.Named
  roots_eq : roots = continuation.rootNames
  continuation_eq : continuation = chamber.continuation
  ownership : ∀ history index,
    ChamberOwnership chamber (continuation.box history index)
  referenceMaximality : ∀ {familyCount : Nat}
    (family : Fin familyCount → RFAP.ShrinkingTrack.WindingOneTrack
      reference.polynomial
      (RFAP.GlobalWinding.largeSquareBox reference.polynomial)),
    (∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) →
    familyCount ≤ reference.degree

/-- Effective algebraic closure for a monic progressive polynomial on a
finitely certified simple-root chamber.  The construction performs only
finite coefficient refinements, rational winding transport, bounded safe-cut
searches, and exact rational Newton calculations. -/
def SimpleRootChamber.effectiveAlgebraicClosure
    {reference : CoefficientTable} (chamber : SimpleRootChamber reference) :
    EffectiveAlgebraicClosure chamber where
  continuation := chamber.continuation
  roots := chamber.continuation.rootNames
  roots_eq := rfl
  continuation_eq := rfl
  ownership := chamber.ownershipAt
  referenceMaximality := chamber.referenceMaximality

namespace EffectiveAlgebraicClosure

theorem roots_productive
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (index : Fin reference.degree) (count : Nat) :
    (closure.roots index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (closure.roots index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (closure.roots index).machine count).emitted.length = count := by
  rw [closure.roots_eq]
  exact closure.continuation.rootNameAt_productive index count

theorem roots_exact
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (index : Fin reference.degree) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (closure.continuation.toProcess index) closure.continuation.initial
      (CCL.ProgressiveTransducer.advance
        (closure.roots index).machine count) := by
  rw [closure.roots_eq]
  exact closure.continuation.rootNameAt_exact index count

theorem refined_boxes_strict
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : Fin reference.degree) :
    (closure.continuation.box
        (closure.continuation.refine history epsilon positive) index).StrictInterior
      (closure.continuation.box history index) :=
  closure.continuation.strict history epsilon positive index

theorem refined_boxes_accurate
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (epsilon : Coordinate)
    (positive : 0 < epsilon) (index : Fin reference.degree) :
    (closure.continuation.box
      (closure.continuation.refine history epsilon positive) index).diagonalSq ≤
        epsilon ^ 2 :=
  closure.continuation.accurate history epsilon positive index

theorem refined_boxes_pairwiseSeparated
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (epsilon : Coordinate)
    (positive : 0 < epsilon) (left right : Fin reference.degree)
    (different : left ≠ right) :
    (closure.continuation.box
        (closure.continuation.refine history epsilon positive) left).Separated
      (closure.continuation.box
        (closure.continuation.refine history epsilon positive) right) :=
  closure.continuation.pairwiseSeparated
    (closure.continuation.refine history epsilon positive) left right different

theorem refined_anchor_residual_le
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (history : closure.continuation.State) (index : Fin reference.degree)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    let next := closure.continuation.refine history epsilon positive
    normSq
        ((closure.continuation.table next).polynomial.eval
          (closure.continuation.box next index).anchor) ≤
      RFAP.PolynomialBounds.denseLipschitzBound
          (closure.continuation.table next).polynomial
          (closure.continuation.box closure.continuation.initial index) *
        epsilon ^ 2 :=
  closure.continuation.refinedAnchorResidual_le_requested history index epsilon
    positive

theorem no_degree_succ_reference_family
    {reference : CoefficientTable} {chamber : SimpleRootChamber reference}
    (closure : EffectiveAlgebraicClosure chamber)
    (family : Fin (reference.degree + 1) →
      RFAP.ShrinkingTrack.WindingOneTrack reference.polynomial
        (RFAP.GlobalWinding.largeSquareBox reference.polynomial))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated (family right).initial.box) : False := by
  have impossible := closure.referenceMaximality family pairwise
  omega

end EffectiveAlgebraicClosure

end CCL.ProgressivePolynomialRoots

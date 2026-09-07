import mathlib.Data.ConstructiveList
import mathlib.RFAP.ConstructiveFiniteNorm
import CCL.Calculus.FiniteGaussianPolynomial
import CCL.Progressive.Coherence
import CCL.Transcendental.Output

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace CCL.ProgressiveGaussianIntegration

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := CCL.FiniteGaussianPolynomial.Polynomial
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian

/-- One rational observation checked against a finite Gaussian polynomial. -/
structure LocalObservation (polynomial : Polynomial)
    (allowance : Coordinate) where
  parameter : Coordinate
  integrandReading : Gaussian
  error : Gaussian
  decomposition :
    integrandReading - CCL.FiniteGaussianPolynomial.eval polynomial
      ⟨parameter, 0⟩ = error
  error_le : normSq error <= allowance

/-- One affine complex segment with a Gaussian-polynomial coefficient model. -/
structure CellModel where
  start : Gaussian
  finish : Gaussian
  polynomial : Polynomial
  localAllowance : Coordinate
  localAllowance_nonneg : 0 <= localAllowance
  observations : List (LocalObservation polynomial localAllowance)

namespace CellModel

/-- Finite evidence that a cell uses one displayed Gaussian constant as its
polynomial model.  This is data in `Type`, so it can be consumed by later
constructive refinement builders without eliminating a proposition into
computational data. -/
structure ConstantCertificate (cell : CellModel) where
  coefficient : Gaussian
  polynomial_eq : cell.polynomial =
    CCL.FiniteGaussianPolynomial.constant coefficient

def displacement (cell : CellModel) : Gaussian := cell.finish - cell.start

def integralSample (cell : CellModel) : Gaussian :=
  cell.displacement *
    CCL.FiniteGaussianPolynomial.definiteIntegral cell.polynomial 0 1

def weightedAllowance (cell : CellModel) : Coordinate :=
  normSq cell.displacement * cell.localAllowance

def exact (start finish : Gaussian) (polynomial : Polynomial) : CellModel :=
  { start := start
    finish := finish
    polynomial := polynomial
    localAllowance := 0
    localAllowance_nonneg := le_rfl
    observations := [] }

/-- An exact cell whose polynomial was explicitly supplied as a constant. -/
def exactConstantCertificate (start finish coefficient : Gaussian) :
    ConstantCertificate
      (exact start finish (CCL.FiniteGaussianPolynomial.constant coefficient))
    where
  coefficient := coefficient
  polynomial_eq := rfl

/-- Replace only the displayed local allowance of a cell.  The geometric
segment, polynomial, and hence its rational integral sample are unchanged.
This is useful when a cell is viewed as a finite comparison witness rather
than as its original semantic model. -/
def withAllowance (cell : CellModel) (allowance : Coordinate)
    (allowanceNonnegative : 0 <= allowance) : CellModel :=
  { start := cell.start
    finish := cell.finish
    polynomial := cell.polynomial
    localAllowance := allowance
    localAllowance_nonneg := allowanceNonnegative
    observations := [] }

@[simp] theorem withAllowance_displacement (cell : CellModel)
    (allowance : Coordinate) (allowanceNonnegative : 0 <= allowance) :
    (cell.withAllowance allowance allowanceNonnegative).displacement =
      cell.displacement := rfl

@[simp] theorem withAllowance_integralSample (cell : CellModel)
    (allowance : Coordinate) (allowanceNonnegative : 0 <= allowance) :
    (cell.withAllowance allowance allowanceNonnegative).integralSample =
      cell.integralSample := rfl

theorem exact_integralSample (start finish : Gaussian)
    (polynomial : Polynomial) :
    (exact start finish polynomial).integralSample =
      (finish - start) *
        CCL.FiniteGaussianPolynomial.definiteIntegral polynomial 0 1 := rfl

theorem weightedAllowance_nonneg (cell : CellModel) :
    0 <= cell.weightedAllowance :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (normSq_nonneg cell.displacement) cell.localAllowance_nonneg

theorem weighted_error_le (cell : CellModel) {error : Gaussian}
    (bounded : normSq error <= cell.localAllowance) :
    normSq (cell.displacement * error) <= cell.weightedAllowance := by
  rw [normSq_mul]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bounded
    (normSq_nonneg cell.displacement)

theorem integralSample_eq_zero_of_start_eq_finish (cell : CellModel)
    (equal : cell.start = cell.finish) : cell.integralSample = 0 := by
  unfold integralSample displacement
  rw [equal, RFAP.ConstructiveGaussian.Gaussian.sub_self,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul]

/-- Finite evidence for reversing a local Gaussian-polynomial model. -/
structure ReversalCertificate (cell : CellModel) where
  reversedPolynomial : Polynomial
  integral_eq :
    CCL.FiniteGaussianPolynomial.definiteIntegral reversedPolynomial 0 1 =
      CCL.FiniteGaussianPolynomial.definiteIntegral cell.polynomial 0 1

/-- A Gaussian-constant model is unchanged by parameter reversal. -/
def ReversalCertificate.constant (cell : CellModel) (value : Gaussian)
    (polynomial_eq : cell.polynomial =
      CCL.FiniteGaussianPolynomial.constant value) :
    ReversalCertificate cell where
  reversedPolynomial := CCL.FiniteGaussianPolynomial.constant value
  integral_eq := by rw [polynomial_eq]

def reverse (cell : CellModel) (certificate : ReversalCertificate cell) :
    CellModel :=
  { start := cell.finish
    finish := cell.start
    polynomial := certificate.reversedPolynomial
    localAllowance := cell.localAllowance
    localAllowance_nonneg := cell.localAllowance_nonneg
    observations := [] }

theorem reverse_integralSample (cell : CellModel)
    (certificate : ReversalCertificate cell) :
    (cell.reverse certificate).integralSample = -cell.integralSample := by
  unfold reverse integralSample displacement
  rw [certificate.integral_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im] <;> ring1

end CellModel

structure PathModel where
  cells : List CellModel

namespace PathModel

/-- Cell-for-cell evidence that a complete finite path model is constant on
each displayed affine cell. -/
inductive ConstantCells : List CellModel -> Type
  | nil : ConstantCells []
  | cons {cell : CellModel} {cells : List CellModel}
      (head : cell.ConstantCertificate)
      (tail : ConstantCells cells) : ConstantCells (cell :: cells)

namespace ConstantCells

/-- Constant-cell evidence concatenates in the same order as path models. -/
def append : forall {first second : List CellModel},
    ConstantCells first -> ConstantCells second ->
      ConstantCells (first ++ second)
  | [], _, .nil, secondConstant => secondConstant
  | _ :: _, _, .cons head tail, secondConstant =>
      .cons head (append tail secondConstant)

end ConstantCells

def integralSample (path : PathModel) : Gaussian :=
  path.cells.foldr (fun cell total => cell.integralSample + total) 0

@[simp] theorem singleton_integralSample (cell : CellModel) :
    (PathModel.mk [cell]).integralSample = cell.integralSample := by
  unfold integralSample
  simp only [List.foldr_cons, List.foldr_nil]
  exact RFAP.ConstructiveGaussian.Gaussian.add_zero _

def totalWeightedAllowance (path : PathModel) : Coordinate :=
  path.cells.foldr (fun cell total => cell.weightedAllowance + total) 0

/-- Tail-recursive execution of the same finite weighted-allowance sum.  The
ordinary fold remains the proof-facing definition; explicit large prepared
paths can rewrite to this form before a kernel calculation, avoiding a call
stack proportional to the complete cell list. -/
def tailTotalWeightedAllowance (path : PathModel) : Coordinate :=
  path.cells.foldl (fun total cell => total + cell.weightedAllowance) 0

/-- Map-fused tail accumulator for a finite family of cell-producing data. -/
def tailMappedWeightedAllowance {Data : Type}
    (values : List Data) (model : Data -> CellModel) : Coordinate :=
  values.foldl (fun total value => total + (model value).weightedAllowance) 0

private theorem foldl_weightedAllowance_map {Data : Type}
    (model : Data -> CellModel) :
    forall (values : List Data) (initial : Coordinate),
      (values.map model).foldl
          (fun total cell => total + cell.weightedAllowance) initial =
        values.foldl
          (fun total value => total + (model value).weightedAllowance) initial
  | [], _initial => rfl
  | value :: remaining, initial =>
      foldl_weightedAllowance_map model remaining
        (initial + (model value).weightedAllowance)

/-- Tail allowance of a mapped cell list executes without materializing the
intermediate list. -/
theorem tailTotalWeightedAllowance_map {Data : Type}
    (values : List Data) (model : Data -> CellModel) :
    (PathModel.mk (values.map model)).tailTotalWeightedAllowance =
      tailMappedWeightedAllowance values model := by
  unfold tailTotalWeightedAllowance tailMappedWeightedAllowance
  exact foldl_weightedAllowance_map model values 0

private theorem foldl_mappedWeightedAllowance_eq {Data : Type}
    (model : Data -> CellModel) :
    forall (values : List Data) (initial : Coordinate),
      values.foldl
          (fun total value => total + (model value).weightedAllowance) initial =
        initial + tailMappedWeightedAllowance values model
  | [], initial => by
      unfold tailMappedWeightedAllowance
      simp only [List.foldl_nil]
      exact (_root_.add_zero initial).symm
  | value :: remaining, initial => by
      change
        remaining.foldl
            (fun total value => total + (model value).weightedAllowance)
            (initial + (model value).weightedAllowance) =
          initial +
            remaining.foldl
              (fun total value => total + (model value).weightedAllowance)
              (0 + (model value).weightedAllowance)
      rw [foldl_mappedWeightedAllowance_eq model remaining,
        foldl_mappedWeightedAllowance_eq model remaining]
      ring1

/-- The map-fused tail accumulator distributes over a displayed finite list
concatenation. -/
theorem tailMappedWeightedAllowance_append {Data : Type}
    (first second : List Data) (model : Data -> CellModel) :
    tailMappedWeightedAllowance (first ++ second) model =
      tailMappedWeightedAllowance first model +
        tailMappedWeightedAllowance second model := by
  change
    (first ++ second).foldl
        (fun total value => total + (model value).weightedAllowance) 0 =
      first.foldl
          (fun total value => total + (model value).weightedAllowance) 0 +
        second.foldl
          (fun total value => total + (model value).weightedAllowance) 0
  rw [QuotientFreeList.foldl_append,
    foldl_mappedWeightedAllowance_eq model second,
    foldl_mappedWeightedAllowance_eq model second]
  ring1

private theorem tailMappedWeightedAllowance_cons {Data : Type}
    (value : Data) (remaining : List Data) (model : Data -> CellModel) :
    tailMappedWeightedAllowance (value :: remaining) model =
      (model value).weightedAllowance +
        tailMappedWeightedAllowance remaining model := by
  change
    remaining.foldl
        (fun total value => total + (model value).weightedAllowance)
        (0 + (model value).weightedAllowance) =
      (model value).weightedAllowance +
        remaining.foldl
          (fun total value => total + (model value).weightedAllowance) 0
  rw [foldl_mappedWeightedAllowance_eq model remaining,
    foldl_mappedWeightedAllowance_eq model remaining]
  ring1

/-- Split a displayed finite list into its alternating-position halves.  The
recursion depth is half the input length and does not first demand a complete
length traversal. -/
def alternatingSplit {Data : Type} : List Data -> List Data × List Data
  | [] => ([], [])
  | [value] => ([value], [])
  | first :: second :: remaining =>
      let halves := alternatingSplit remaining
      (first :: halves.1, second :: halves.2)

private theorem alternatingSplit_allowance {Data : Type}
    (model : Data -> CellModel) : forall (values : List Data),
    tailMappedWeightedAllowance (alternatingSplit values).1 model +
        tailMappedWeightedAllowance (alternatingSplit values).2 model =
      tailMappedWeightedAllowance values model
  | [] => by
      simp only [alternatingSplit]
      unfold tailMappedWeightedAllowance
      simp only [List.foldl_nil]
      ring1
  | [value] => by
      simp only [alternatingSplit, tailMappedWeightedAllowance_cons]
      unfold tailMappedWeightedAllowance
      simp only [List.foldl_nil]
      ring1
  | first :: second :: remaining => by
      have tail := alternatingSplit_allowance model remaining
      simp only [alternatingSplit, tailMappedWeightedAllowance_cons]
      calc
        (model first).weightedAllowance +
              tailMappedWeightedAllowance (alternatingSplit remaining).1 model +
            ((model second).weightedAllowance +
              tailMappedWeightedAllowance
                (alternatingSplit remaining).2 model) =
            (model first).weightedAllowance +
              (model second).weightedAllowance +
                (tailMappedWeightedAllowance
                    (alternatingSplit remaining).1 model +
                  tailMappedWeightedAllowance
                    (alternatingSplit remaining).2 model) := by ring1
        _ = (model first).weightedAllowance +
              (model second).weightedAllowance +
                tailMappedWeightedAllowance remaining model := by rw [tail]
        _ = (model first).weightedAllowance +
              ((model second).weightedAllowance +
                tailMappedWeightedAllowance remaining model) := by ring1

/-- Divide-and-conquer execution of a mapped finite allowance sum.  The fuel
controls only evaluation shape: fuel zero falls back to the ordinary fused
tail fold, so every value is total and exact. -/
def balancedMappedWeightedAllowance {Data : Type} :
    Nat -> List Data -> (Data -> CellModel) -> Coordinate
  | 0, values, model => tailMappedWeightedAllowance values model
  | fuel + 1, values, model =>
      let halves := alternatingSplit values
      balancedMappedWeightedAllowance fuel halves.1 model +
        balancedMappedWeightedAllowance fuel halves.2 model

/-- Balanced and tail-recursive mapped allowance executions are equal for
every displayed fuel and finite input. -/
theorem balancedMappedWeightedAllowance_eq {Data : Type}
    (model : Data -> CellModel) : forall (fuel : Nat) (values : List Data),
    balancedMappedWeightedAllowance fuel values model =
      tailMappedWeightedAllowance values model
  | 0, _values => rfl
  | fuel + 1, values => by
      change
        balancedMappedWeightedAllowance fuel
              (alternatingSplit values).1 model +
            balancedMappedWeightedAllowance fuel
              (alternatingSplit values).2 model =
          tailMappedWeightedAllowance values model
      rw [balancedMappedWeightedAllowance_eq model fuel,
        balancedMappedWeightedAllowance_eq model fuel]
      exact alternatingSplit_allowance model values

private theorem foldl_weightedAllowance_eq :
    forall (cells : List CellModel) (initial : Coordinate),
      cells.foldl (fun total cell => total + cell.weightedAllowance) initial =
        initial + (PathModel.mk cells).totalWeightedAllowance
  | [], initial => by
      simp only [List.foldl_nil, totalWeightedAllowance, List.foldr_nil]
      exact (_root_.add_zero initial).symm
  | cell :: remaining, initial => by
      simp only [List.foldl_cons]
      rw [foldl_weightedAllowance_eq remaining
        (initial + cell.weightedAllowance)]
      simp only [totalWeightedAllowance, List.foldr_cons]
      ring1

/-- The tail-recursive allowance accumulator is exactly the original finite
right fold. -/
theorem tailTotalWeightedAllowance_eq (path : PathModel) :
    path.tailTotalWeightedAllowance = path.totalWeightedAllowance := by
  unfold tailTotalWeightedAllowance
  rw [foldl_weightedAllowance_eq]
  exact _root_.zero_add path.totalWeightedAllowance

/-- Finite Cauchy--Schwarz allowance for the displayed sum of cell errors.
The previous recursive triangle estimate doubled the whole tail at every
cell and therefore grew exponentially with subdivision length.  Multiplying
the ordinary finite error sum by the explicit cell count is both constructive
and the quantitatively useful bound. -/
def aggregateAllowance (path : PathModel) : Coordinate :=
  (path.cells.length : Coordinate) * path.totalWeightedAllowance

/-- Stack-safe executable presentation of the exact aggregate allowance. -/
theorem aggregateAllowance_eq_tail (path : PathModel) :
    path.aggregateAllowance =
      (path.cells.length : Coordinate) * path.tailTotalWeightedAllowance := by
  unfold aggregateAllowance
  rw [path.tailTotalWeightedAllowance_eq]

private theorem natCast_nonneg (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

theorem totalWeightedAllowance_nonneg (path : PathModel) :
    0 <= path.totalWeightedAllowance := by
  unfold totalWeightedAllowance
  induction path.cells with
  | nil => exact le_rfl
  | cons cell remaining inductionHypothesis =>
      simp only [List.foldr_cons]
      exact add_nonneg cell.weightedAllowance_nonneg inductionHypothesis

theorem aggregateAllowance_nonneg (path : PathModel) :
    0 <= path.aggregateAllowance := by
  unfold aggregateAllowance
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (natCast_nonneg path.cells.length) path.totalWeightedAllowance_nonneg

/-- Weighted error sum aligned exactly with the displayed cells. -/
def weightedErrorSum : List CellModel -> List Gaussian -> Gaussian
  | cell :: cells, error :: errors =>
      cell.displacement * error + weightedErrorSum cells errors
  | _, _ => 0

/-- The same weighted errors as an explicit finite list, for application of
the finite Gaussian Cauchy--Schwarz theorem. -/
def weightedErrorTerms : List CellModel -> List Gaussian -> List Gaussian
  | cell :: cells, error :: errors =>
      cell.displacement * error :: weightedErrorTerms cells errors
  | _, _ => []

def ErrorsValid : List CellModel -> List Gaussian -> Prop
  | [], [] => True
  | cell :: cells, error :: errors =>
      normSq error <= cell.localAllowance ∧ ErrorsValid cells errors
  | _, _ => False

theorem gaussianSum_weightedErrorTerms (cells : List CellModel)
    (errors : List Gaussian) :
    RFAP.ConstructiveFiniteNorm.gaussianSum
        (weightedErrorTerms cells errors) = weightedErrorSum cells errors := by
  induction cells generalizing errors with
  | nil => cases errors <;> rfl
  | cons cell cells inductionHypothesis =>
      cases errors with
      | nil => rfl
      | cons error errors =>
          simp only [weightedErrorTerms,
            RFAP.ConstructiveFiniteNorm.gaussianSum, weightedErrorSum]
          rw [inductionHypothesis]

theorem weightedErrorTerms_length : forall (cells : List CellModel)
    (errors : List Gaussian), ErrorsValid cells errors ->
      (weightedErrorTerms cells errors).length = cells.length
  | [], [], _ => rfl
  | [], _ :: _, valid => by simp only [ErrorsValid] at valid
  | _ :: _, [], valid => by simp only [ErrorsValid] at valid
  | cell :: cells, error :: errors, valid => by
      rcases valid with ⟨errorBound, remainingValid⟩
      simp only [weightedErrorTerms, List.length_cons]
      exact congrArg Nat.succ
        (weightedErrorTerms_length cells errors remainingValid)

theorem gaussianNormSqSum_weightedErrorTerms_le :
    forall (cells : List CellModel) (errors : List Gaussian),
      ErrorsValid cells errors ->
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
          (weightedErrorTerms cells errors) <=
        (PathModel.mk cells).totalWeightedAllowance
  | [], [], _ => le_rfl
  | [], _ :: _, valid => by simp only [ErrorsValid] at valid
  | _ :: _, [], valid => by simp only [ErrorsValid] at valid
  | cell :: cells, error :: errors, valid => by
      rcases valid with ⟨errorBound, remainingValid⟩
      simp only [weightedErrorTerms,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum,
        totalWeightedAllowance, List.foldr_cons]
      apply add_le_add
      · exact cell.weighted_error_le errorBound
      · exact gaussianNormSqSum_weightedErrorTerms_le cells errors
          remainingValid

theorem weightedErrorSum_le : forall (cells : List CellModel)
    (errors : List Gaussian), ErrorsValid cells errors ->
      normSq (weightedErrorSum cells errors) <=
        (PathModel.mk cells).aggregateAllowance
  | cells, errors, valid => by
      rw [← gaussianSum_weightedErrorTerms cells errors]
      calc
        normSq (RFAP.ConstructiveFiniteNorm.gaussianSum
            (weightedErrorTerms cells errors)) <=
            ((weightedErrorTerms cells errors).length : Coordinate) *
              RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
                (weightedErrorTerms cells errors) :=
          RFAP.ConstructiveFiniteNorm.normSq_gaussianSum_le _
        _ = (cells.length : Coordinate) *
              RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
                (weightedErrorTerms cells errors) := by
          rw [weightedErrorTerms_length cells errors valid]
        _ <= (cells.length : Coordinate) *
              (PathModel.mk cells).totalWeightedAllowance :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (gaussianNormSqSum_weightedErrorTerms_le cells errors valid)
            (natCast_nonneg cells.length)
        _ = (PathModel.mk cells).aggregateAllowance := rfl

/-! ## Constant-cell partition comparison -/

/-- Sum of the displayed affine displacements of a finite cell list. -/
def displacementSum (cells : List CellModel) : Gaussian :=
  cells.foldr (fun cell total => cell.displacement + total) 0

@[simp] theorem displacementSum_nil : displacementSum [] = 0 := rfl

@[simp] theorem displacementSum_cons (cell : CellModel)
    (cells : List CellModel) :
    displacementSum (cell :: cells) =
      cell.displacement + displacementSum cells := rfl

/-- A cell whose polynomial is the displayed constant has exactly the
expected affine-segment integral. -/
theorem CellModel.integralSample_constant (cell : CellModel)
    (coefficient : Gaussian)
    (polynomial_eq : cell.polynomial =
      CCL.FiniteGaussianPolynomial.constant coefficient) :
    cell.integralSample = cell.displacement * coefficient := by
  unfold CellModel.integralSample
  rw [polynomial_eq,
    CCL.FiniteGaussianPolynomial.definiteIntegral_constant]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CellModel.displacement, sub_re, sub_im, mul_re, mul_im,
      zero_re, zero_im, one_re, one_im] <;> ring1

/-- Cellwise evidence that a finite child partition uses constant
coefficients differing from one reference coefficient by the aligned error
list.  The error bounds are the ordinary displayed child allowances. -/
inductive ConstantComparison (reference : Gaussian) :
    List CellModel -> List Gaussian -> Type
  | nil : ConstantComparison reference [] []
  | cons {cell : CellModel} {cells : List CellModel}
      {errors : List Gaussian}
      (coefficient error : Gaussian)
      (polynomial_eq : cell.polynomial =
        CCL.FiniteGaussianPolynomial.constant coefficient)
      (difference_eq : coefficient - reference = error)
      (error_le : normSq error <= cell.localAllowance)
      (remaining : ConstantComparison reference cells errors) :
      ConstantComparison reference (cell :: cells) (error :: errors)

namespace ConstantComparison

theorem errorsValid {reference : Gaussian} :
    forall {cells : List CellModel} {errors : List Gaussian},
      ConstantComparison reference cells errors -> ErrorsValid cells errors
  | [], [], .nil => True.intro
  | _ :: _, _ :: _, .cons _ _ _ _ error_le remaining =>
      ⟨error_le, errorsValid remaining⟩

/-- The integral of a constant child partition is the reference coefficient
times the total displacement plus the explicit weighted error sum. -/
theorem integralSample_eq_reference_add_error {reference : Gaussian} :
    forall {cells : List CellModel} {errors : List Gaussian},
      (comparison : ConstantComparison reference cells errors) ->
      (PathModel.mk cells).integralSample =
        displacementSum cells * reference + weightedErrorSum cells errors
  | cells, errors, comparison => by
      induction comparison with
      | nil =>
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [PathModel.integralSample, List.foldr_nil,
              displacementSum,
              RFAP.ConstructiveGaussian.Gaussian.zero_mul,
              weightedErrorSum, add_re, add_im, zero_re, zero_im] <;> ring1
      | @cons cell cells errors coefficient error polynomial_eq difference_eq
          error_le remaining inductionHypothesis =>
          have coefficientIdentity : coefficient = reference + error := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext
            · have realIdentity := congrArg
                RFAP.ConstructiveGaussian.Gaussian.re difference_eq
              change coefficient.re = reference.re + error.re
              simp only [sub_re] at realIdentity
              rw [← realIdentity]
              ring1
            · have imaginaryIdentity := congrArg
                RFAP.ConstructiveGaussian.Gaussian.im difference_eq
              change coefficient.im = reference.im + error.im
              simp only [sub_im] at imaginaryIdentity
              rw [← imaginaryIdentity]
              ring1
          rw [PathModel.integralSample, List.foldr_cons,
            CellModel.integralSample_constant cell coefficient polynomial_eq]
          change cell.displacement * coefficient +
              (PathModel.mk cells).integralSample =
            displacementSum (cell :: cells) * reference +
              weightedErrorSum (cell :: cells) (error :: errors)
          rw [inductionHypothesis]
          simp only [displacementSum_cons, weightedErrorSum]
          rw [coefficientIdentity]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im] <;> ring1

end ConstantComparison

/-- A finite list of constant child cells partitions one constant parent
cell, with exact displacement conservation and cellwise coefficient errors. -/
structure ConstantPartitionCertificate (parent : CellModel)
    (children : PathModel) where
  reference : Gaussian
  parent_polynomial_eq : parent.polynomial =
    CCL.FiniteGaussianPolynomial.constant reference
  errors : List Gaussian
  comparison : ConstantComparison reference children.cells errors
  displacement_eq : displacementSum children.cells = parent.displacement

namespace ConstantPartitionCertificate

/-- Exact algebraic decomposition of the child-minus-parent integral. -/
theorem integral_difference_eq {parent : CellModel} {children : PathModel}
    (certificate : ConstantPartitionCertificate parent children) :
    children.integralSample - parent.integralSample =
      weightedErrorSum children.cells certificate.errors := by
  rw [certificate.comparison.integralSample_eq_reference_add_error,
    CellModel.integralSample_constant parent certificate.reference
      certificate.parent_polynomial_eq,
    certificate.displacement_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1

/-- The standard finite aggregate allowance bounds the complete discrepancy
between a constant parent cell and its displayed constant child partition. -/
theorem integral_difference_le {parent : CellModel} {children : PathModel}
    (certificate : ConstantPartitionCertificate parent children) :
    normSq (children.integralSample - parent.integralSample) <=
      children.aggregateAllowance := by
  rw [certificate.integral_difference_eq]
  exact PathModel.weightedErrorSum_le children.cells certificate.errors
    certificate.comparison.errorsValid

end ConstantPartitionCertificate

def concat (first second : PathModel) : PathModel :=
  ⟨first.cells ++ second.cells⟩

theorem integralSample_concat (first second : PathModel) :
    (first.concat second).integralSample =
      first.integralSample + second.integralSample := by
  unfold concat integralSample
  rw [QuotientFreeList.foldr_append]
  induction first.cells with
  | nil => exact (RFAP.ConstructiveGaussian.Gaussian.zero_add _).symm
  | cons cell remaining inductionHypothesis =>
      simp only [List.foldr_cons]
      rw [inductionHypothesis]
      exact (RFAP.ConstructiveGaussian.Gaussian.add_assoc _ _ _).symm

@[simp] theorem integralSample_mk_append
    (first second : List CellModel) :
    (PathModel.mk (first ++ second)).integralSample =
      (PathModel.mk first).integralSample +
        (PathModel.mk second).integralSample := by
  exact integralSample_concat (PathModel.mk first) (PathModel.mk second)

/-- Valid aligned error lists concatenate constructively. -/
theorem ErrorsValid.append : forall {firstCells secondCells : List CellModel}
    {firstErrors secondErrors : List Gaussian},
    ErrorsValid firstCells firstErrors ->
      ErrorsValid secondCells secondErrors ->
        ErrorsValid (firstCells ++ secondCells) (firstErrors ++ secondErrors)
  | firstCells, secondCells, firstErrors, secondErrors,
      firstValid, secondValid => by
    induction firstCells generalizing firstErrors with
    | nil =>
        cases firstErrors with
        | nil => exact secondValid
        | cons _ _ => simp only [ErrorsValid] at firstValid
    | cons cell cells inductionHypothesis =>
        cases firstErrors with
        | nil => simp only [ErrorsValid] at firstValid
        | cons error errors =>
            exact ⟨firstValid.1,
              inductionHypothesis errors firstValid.2⟩

/-- Weighted error sums distribute over concatenation when the first pair is
aligned. -/
theorem weightedErrorSum_append : forall
    (firstCells secondCells : List CellModel)
    (firstErrors secondErrors : List Gaussian),
    ErrorsValid firstCells firstErrors ->
    weightedErrorSum (firstCells ++ secondCells)
        (firstErrors ++ secondErrors) =
      weightedErrorSum firstCells firstErrors +
        weightedErrorSum secondCells secondErrors
  | firstCells, secondCells, firstErrors, secondErrors, valid => by
    induction firstCells generalizing firstErrors with
    | nil =>
        cases firstErrors with
        | nil =>
            change weightedErrorSum secondCells secondErrors =
              0 + weightedErrorSum secondCells secondErrors
            exact (RFAP.ConstructiveGaussian.Gaussian.zero_add _).symm
        | cons _ _ => simp only [ErrorsValid] at valid
    | cons cell cells inductionHypothesis =>
        cases firstErrors with
        | nil => simp only [ErrorsValid] at valid
        | cons error errors =>
            simp only [List.cons_append, weightedErrorSum]
            rw [inductionHypothesis errors valid.2]
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [add_re, add_im] <;> ring1

/-- A complete constant path refinement is a finite partition certificate
for each parent cell, with all child blocks concatenated in path order. -/
inductive ConstantPathRefinement :
    List CellModel -> List CellModel -> Type
  | nil : ConstantPathRefinement [] []
  | cons {parent : CellModel} {parents childCells children : List CellModel}
      (head : ConstantPartitionCertificate parent (PathModel.mk childCells))
      (remaining : ConstantPathRefinement parents children) :
      ConstantPathRefinement (parent :: parents) (childCells ++ children)

namespace ConstantPathRefinement

def errors {parents children : List CellModel}
    (refinement : ConstantPathRefinement parents children) : List Gaussian :=
  match refinement with
  | .nil => []
  | .cons head remaining => head.errors ++ remaining.errors

theorem errorsValid : forall {parents children : List CellModel}
    (refinement : ConstantPathRefinement parents children),
    ErrorsValid children refinement.errors
  | parents, children, refinement => by
      induction refinement with
      | nil => exact True.intro
      | cons head remaining inductionHypothesis =>
          exact ErrorsValid.append head.comparison.errorsValid
            inductionHypothesis

/-- Exact whole-path child-minus-parent decomposition into the single aligned
weighted error list. -/
theorem integral_difference_eq : forall {parents children : List CellModel}
    (refinement : ConstantPathRefinement parents children),
    (PathModel.mk children).integralSample -
        (PathModel.mk parents).integralSample =
      weightedErrorSum children refinement.errors
  | parents, children, refinement => by
    induction refinement with
    | nil =>
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [PathModel.integralSample, List.foldr_nil, sub_re, sub_im,
          zero_re, zero_im, weightedErrorSum] <;> ring1
    | @cons parent parents childCells children head remaining
        inductionHypothesis =>
      have childConcat :
          (PathModel.mk (childCells ++ children)).integralSample =
            (PathModel.mk childCells).integralSample +
              (PathModel.mk children).integralSample := by
        exact PathModel.integralSample_concat
          (PathModel.mk childCells) (PathModel.mk children)
      have headDifference := head.integral_difference_eq
      have remainingDifference := inductionHypothesis
      have errorConcat := weightedErrorSum_append childCells children
        head.errors remaining.errors head.comparison.errorsValid
      rw [childConcat]
      change
        ((PathModel.mk childCells).integralSample +
            (PathModel.mk children).integralSample) -
          (parent.integralSample +
            (PathModel.mk parents).integralSample) =
        weightedErrorSum (childCells ++ children)
          (head.errors ++ remaining.errors)
      rw [errorConcat]
      have differenceIdentity :
          ((PathModel.mk childCells).integralSample +
              (PathModel.mk children).integralSample) -
            (parent.integralSample +
              (PathModel.mk parents).integralSample) =
          ((PathModel.mk childCells).integralSample - parent.integralSample) +
            ((PathModel.mk children).integralSample -
              (PathModel.mk parents).integralSample) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, add_re, add_im] <;> ring1
      rw [differenceIdentity, headDifference, remainingDifference]

/-- A complete constant path refinement is bounded directly by the child
path's standard aggregate allowance, without an exponential triangle loss. -/
theorem integral_difference_le {parents children : List CellModel}
    (refinement : ConstantPathRefinement parents children) :
    normSq ((PathModel.mk children).integralSample -
        (PathModel.mk parents).integralSample) <=
      (PathModel.mk children).aggregateAllowance := by
  rw [refinement.integral_difference_eq]
  exact PathModel.weightedErrorSum_le children refinement.errors
    refinement.errorsValid

end ConstantPathRefinement

/-! ## Parent--child comparison allowances

An independently sampled child coefficient cannot in general approach one
fixed rational parent sample using the child's semantic allowance alone.  A
constructive comparison instead pays for the uncertainty of both displayed
models.  The following layer records that honest allowance while retaining
the exact constant-partition algebra above. -/

/-- Squared comparison allowance for one child coefficient against its
parent's constant reference.  The factor two is the Gaussian squared
triangle bound for one parent error and one child error. -/
def parentChildAllowance (parent child : CellModel) : Coordinate :=
  2 * (parent.localAllowance + child.localAllowance)

theorem parentChildAllowance_nonneg (parent child : CellModel) :
    0 <= parentChildAllowance parent child := by
  unfold parentChildAllowance
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg parent.localAllowance_nonneg child.localAllowance_nonneg)

/-- The child cell viewed only as a comparison term against one parent.  Its
integral sample is definitionally unchanged; only its allowance is replaced
by the combined parent--child uncertainty. -/
def comparisonCell (parent child : CellModel) : CellModel :=
  child.withAllowance (parentChildAllowance parent child)
    (parentChildAllowance_nonneg parent child)

@[simp] theorem comparisonCell_integralSample (parent child : CellModel) :
    (comparisonCell parent child).integralSample = child.integralSample := rfl

/-- Apply the combined comparison allowance to a whole child block belonging
to one parent cell. -/
def comparisonBlock (parent : CellModel) (children : PathModel) : PathModel :=
  ⟨children.cells.map (comparisonCell parent)⟩

theorem comparisonBlock_integralSample (parent : CellModel)
    (children : PathModel) :
    (comparisonBlock parent children).integralSample =
      children.integralSample := by
  unfold comparisonBlock PathModel.integralSample
  induction children.cells with
  | nil => rfl
  | cons child remaining inductionHypothesis =>
      simp only [List.map, List.foldr_cons,
        comparisonCell_integralSample, inductionHypothesis]

/-- A constant path refinement whose coefficient comparison pays for both
the parent and child semantic allowances.  Each head certificate is checked
against `comparisonBlock parent childCells`, whose samples and geometry are
identical to the actual child cells. -/
inductive CompatibleConstantPathRefinement :
    List CellModel -> List CellModel -> Type
  | nil : CompatibleConstantPathRefinement [] []
  | cons {parent : CellModel} {parents childCells children : List CellModel}
      (head : ConstantPartitionCertificate parent
        (comparisonBlock parent (PathModel.mk childCells)))
      (remaining : CompatibleConstantPathRefinement parents children) :
      CompatibleConstantPathRefinement (parent :: parents)
        (childCells ++ children)

namespace CompatibleConstantPathRefinement

/-- Every finite constant-cell model refines itself.  The comparison view
pays the ordinary parent--child allowance, while the aligned coefficient
error is exactly zero. -/
def refl : forall {cells : List CellModel},
    ConstantCells cells -> CompatibleConstantPathRefinement cells cells
  | [], .nil => .nil
  | cell :: cells, .cons head tail =>
      @CompatibleConstantPathRefinement.cons cell cells [cell] cells
        { reference := head.coefficient
          parent_polynomial_eq := head.polynomial_eq
          errors := [0]
          comparison := .cons head.coefficient 0
            (by
              change cell.polynomial =
                CCL.FiniteGaussianPolynomial.constant head.coefficient
              exact head.polynomial_eq)
            (RFAP.ConstructiveGaussian.Gaussian.sub_self _)
            (by
              rw [RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
              change 0 <= parentChildAllowance cell cell
              exact parentChildAllowance_nonneg cell cell)
            .nil
          displacement_eq := by
            simp only [comparisonBlock, List.map, displacementSum_cons,
              displacementSum_nil, comparisonCell,
              CellModel.withAllowance_displacement]
            exact RFAP.ConstructiveGaussian.Gaussian.add_zero _ }
        (refl tail)

private theorem child_weightedAllowance_le_comparisonCell
    (parent child : CellModel) :
    child.weightedAllowance <=
      (comparisonCell parent child).weightedAllowance := by
  have allowanceSumNonnegative :
      0 <= parent.localAllowance + child.localAllowance :=
    add_nonneg parent.localAllowance_nonneg child.localAllowance_nonneg
  have childAllowance_le : child.localAllowance <=
      parentChildAllowance parent child := by
    unfold parentChildAllowance
    calc
      child.localAllowance <=
          parent.localAllowance + child.localAllowance :=
        le_add_of_nonneg_left parent.localAllowance_nonneg
      _ <= (parent.localAllowance + child.localAllowance) +
          (parent.localAllowance + child.localAllowance) :=
        le_add_of_nonneg_right allowanceSumNonnegative
      _ = 2 * (parent.localAllowance + child.localAllowance) := by ring1
  unfold CellModel.weightedAllowance comparisonCell CellModel.withAllowance
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    childAllowance_le (normSq_nonneg child.displacement)

private theorem totalWeightedAllowance_append
    (first second : List CellModel) :
    (PathModel.mk (first ++ second)).totalWeightedAllowance =
      (PathModel.mk first).totalWeightedAllowance +
        (PathModel.mk second).totalWeightedAllowance := by
  induction first with
  | nil =>
      simp only [List.nil_append, totalWeightedAllowance, List.foldr_nil]
      rw [_root_.zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append, totalWeightedAllowance, List.foldr_cons]
      change
        (remaining ++ second).foldr
            (fun cell total => cell.weightedAllowance + total) 0 =
          remaining.foldr
              (fun cell total => cell.weightedAllowance + total) 0 +
            second.foldr
              (fun cell total => cell.weightedAllowance + total) 0 at inductionHypothesis
      rw [inductionHypothesis]
      ring1

private theorem totalWeightedAllowance_le_comparisonBlock
    (parent : CellModel) (children : List CellModel) :
    (PathModel.mk children).totalWeightedAllowance <=
      (comparisonBlock parent (PathModel.mk children)).totalWeightedAllowance := by
  induction children with
  | nil => exact le_rfl
  | cons child remaining inductionHypothesis =>
      simp only [totalWeightedAllowance, List.foldr_cons, comparisonBlock,
        List.map_cons]
      exact add_le_add
        (child_weightedAllowance_le_comparisonCell parent child)
        inductionHypothesis

/-- The comparison-only child cells, retaining every actual child integral
sample while displaying the combined parent--child allowances. -/
def comparisonCells : forall {parents children : List CellModel},
    CompatibleConstantPathRefinement parents children -> List CellModel
  | _, _, .nil => []
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children _head remaining =>
      (comparisonBlock parent (PathModel.mk childCells)).cells ++
        comparisonCells remaining

/-- Forgetting which allowances came from the parent gives an ordinary
constant partition refinement of the comparison-only child path. -/
def toConstantPathRefinement : forall {parents children : List CellModel}
    (refinement : CompatibleConstantPathRefinement parents children),
    ConstantPathRefinement parents refinement.comparisonCells
  | _, _, .nil => .nil
  | _, _, .cons head remaining =>
      .cons head (toConstantPathRefinement remaining)

/-- Replacing actual children by their comparison views leaves the complete
rational integral sample unchanged. -/
theorem comparisonCells_integralSample :
    forall {parents children : List CellModel}
      (refinement : CompatibleConstantPathRefinement parents children),
      (PathModel.mk refinement.comparisonCells).integralSample =
        (PathModel.mk children).integralSample
  | _, _, .nil => rfl
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children head remaining => by
      calc
        (PathModel.mk
            ((comparisonBlock parent (PathModel.mk childCells)).cells ++
              remaining.comparisonCells)).integralSample =
            (comparisonBlock parent
                (PathModel.mk childCells)).integralSample +
              (PathModel.mk remaining.comparisonCells).integralSample :=
          PathModel.integralSample_concat
            (comparisonBlock parent (PathModel.mk childCells))
            (PathModel.mk remaining.comparisonCells)
        _ = (PathModel.mk childCells).integralSample +
              (PathModel.mk children).integralSample := by
          rw [comparisonBlock_integralSample,
            comparisonCells_integralSample remaining]
        _ = (PathModel.mk (childCells ++ children)).integralSample :=
          (PathModel.integralSample_concat (PathModel.mk childCells)
            (PathModel.mk children)).symm

@[simp] theorem comparisonCells_length :
    forall {parents children : List CellModel}
      (refinement : CompatibleConstantPathRefinement parents children),
      refinement.comparisonCells.length = children.length
  | _, _, .nil => rfl
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children head remaining => by
      simp only [comparisonCells, List.length_append, comparisonBlock,
        List.length_map, comparisonCells_length remaining]

private theorem refl_comparisonCells_totalWeightedAllowance :
    forall {cells : List CellModel} (constant : ConstantCells cells),
      (PathModel.mk
        (CompatibleConstantPathRefinement.refl constant).comparisonCells).totalWeightedAllowance =
        4 * (PathModel.mk cells).totalWeightedAllowance
  | [], .nil => by
      unfold totalWeightedAllowance
      rfl
  | cell :: cells, .cons head tail => by
      simp only [CompatibleConstantPathRefinement.refl, comparisonCells,
        comparisonBlock, List.map, List.singleton_append]
      change
        (comparisonCell cell cell).weightedAllowance +
            (PathModel.mk
              (CompatibleConstantPathRefinement.refl tail).comparisonCells).totalWeightedAllowance =
          4 * (cell.weightedAllowance +
            (PathModel.mk cells).totalWeightedAllowance)
      rw [refl_comparisonCells_totalWeightedAllowance tail]
      unfold comparisonCell CellModel.withAllowance CellModel.weightedAllowance
        CellModel.displacement parentChildAllowance
      ring1

private theorem children_totalWeightedAllowance_le_comparisonCells :
    forall {parents children : List CellModel}
      (refinement : CompatibleConstantPathRefinement parents children),
      (PathModel.mk children).totalWeightedAllowance <=
        (PathModel.mk refinement.comparisonCells).totalWeightedAllowance
  | _, _, .nil => le_rfl
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children head remaining => by
      change
        (PathModel.mk (childCells ++ children)).totalWeightedAllowance <=
          (PathModel.mk
            ((comparisonBlock parent (PathModel.mk childCells)).cells ++
              remaining.comparisonCells)).totalWeightedAllowance
      rw [show
        (PathModel.mk (childCells ++ children)).totalWeightedAllowance =
          (PathModel.mk childCells).totalWeightedAllowance +
            (PathModel.mk children).totalWeightedAllowance from
        totalWeightedAllowance_append childCells children]
      rw [show
        (PathModel.mk
          ((comparisonBlock parent (PathModel.mk childCells)).cells ++
            remaining.comparisonCells)).totalWeightedAllowance =
          (comparisonBlock parent
              (PathModel.mk childCells)).totalWeightedAllowance +
            (PathModel.mk remaining.comparisonCells).totalWeightedAllowance from
        totalWeightedAllowance_append _ _]
      exact add_le_add
        (totalWeightedAllowance_le_comparisonBlock parent childCells)
        (children_totalWeightedAllowance_le_comparisonCells remaining)

/-- The aggregate allowance actually used to compare a later path with one
displayed parent path. -/
def comparisonAllowance {parents children : List CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    Coordinate :=
  (PathModel.mk refinement.comparisonCells).aggregateAllowance

/-- The canonical self-comparison has exactly four times the original path
allowance.  This gives prepared schedules a uniform reflexive modulus without
storing one certificate at every natural index. -/
theorem comparisonAllowance_refl_eq {cells : List CellModel}
    (constant : ConstantCells cells) :
    (CompatibleConstantPathRefinement.refl constant).comparisonAllowance =
      4 * (PathModel.mk cells).aggregateAllowance := by
  unfold comparisonAllowance aggregateAllowance
  rw [comparisonCells_length,
    refl_comparisonCells_totalWeightedAllowance constant]
  ring1

theorem comparisonAllowance_nonneg {parents children : List CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    0 <= refinement.comparisonAllowance :=
  (PathModel.mk refinement.comparisonCells).aggregateAllowance_nonneg

/-- The comparison allowance dominates the later path's own semantic
allowance.  Thus one self-comparison controls both quantities needed by a
refinement program. -/
theorem childAggregateAllowance_le_comparisonAllowance
    {parents children : List CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    (PathModel.mk children).aggregateAllowance <=
      refinement.comparisonAllowance := by
  unfold PathModel.aggregateAllowance comparisonAllowance
  change (children.length : Coordinate) *
      (PathModel.mk children).totalWeightedAllowance <=
    (refinement.comparisonCells.length : Coordinate) *
      (PathModel.mk refinement.comparisonCells).totalWeightedAllowance
  rw [refinement.comparisonCells_length]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (children_totalWeightedAllowance_le_comparisonCells refinement)
    (natCast_nonneg children.length)

/-- The exact parent--child partition calculation bounds the actual integral
difference by the explicit combined comparison allowance. -/
theorem integral_difference_le {parents children : List CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    normSq ((PathModel.mk children).integralSample -
        (PathModel.mk parents).integralSample) <=
      refinement.comparisonAllowance := by
  have bounded := refinement.toConstantPathRefinement.integral_difference_le
  rw [refinement.comparisonCells_integralSample] at bounded
  exact bounded

end CompatibleConstantPathRefinement

/-- Cellwise finite evidence for reversing a complete displayed path. -/
inductive ReversalCells : List CellModel -> Type
  | nil : ReversalCells []
  | cons {cell : CellModel} {remaining : List CellModel}
      (head : CellModel.ReversalCertificate cell)
      (tail : ReversalCells remaining) : ReversalCells (cell :: remaining)

namespace ReversalCells

def reversed : {cells : List CellModel} -> ReversalCells cells -> List CellModel
  | [], .nil => []
  | _ :: _, .cons head tail =>
      tail.reversed ++ [CellModel.reverse _ head]

theorem integralSample_reversed : forall {cells : List CellModel}
    (certificate : ReversalCells cells),
    (PathModel.mk certificate.reversed).integralSample =
      -(PathModel.mk cells).integralSample
  | [], .nil => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [reversed, integralSample, List.foldr_nil, neg_re, neg_im,
          zero_re, zero_im] <;> ring1
  | cell :: remaining, .cons head tail => by
      change
        (PathModel.mk
          (tail.reversed ++ [CellModel.reverse cell head])).integralSample =
          -(PathModel.mk (cell :: remaining)).integralSample
      rw [show PathModel.mk
          (tail.reversed ++ [CellModel.reverse cell head]) =
          (PathModel.mk tail.reversed).concat
            (PathModel.mk [CellModel.reverse cell head]) from rfl,
        integralSample_concat, integralSample_reversed tail,
        singleton_integralSample, CellModel.reverse_integralSample]
      change
        -(PathModel.mk remaining).integralSample + -cell.integralSample =
          -(cell.integralSample + (PathModel.mk remaining).integralSample)
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, neg_re, neg_im] <;> ring1

end ReversalCells

structure Reversal (path : PathModel) where
  cells : ReversalCells path.cells

def reverse (path : PathModel) (certificate : Reversal path) : PathModel :=
  ⟨certificate.cells.reversed⟩

theorem reverse_integralSample (path : PathModel)
    (certificate : Reversal path) :
    (path.reverse certificate).integralSample = -path.integralSample :=
  certificate.cells.integralSample_reversed

end PathModel

/-- A finite-refinement Gaussian quadrature oracle with an explicit geometric
modulus for both model discrepancy and successive integral samples. -/
structure RefinementProgram where
  model : Nat -> PathModel
  errorScale : Coordinate
  errorScale_nonneg : 0 <= errorScale
  modelAllowance_le : forall index,
    (model index).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale index
  later_close : forall {earlier later : Nat}, earlier <= later ->
    normSq ((model later).integralSample - (model earlier).integralSample) <=
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 <= centerBound
  sample_bounded : forall index,
    normSq (model index).integralSample <= centerBound

/-- A refinement program whose Cauchy estimate is derived from explicit
constant-cell partition certificates rather than accepted as an independent
field.  Every later displayed path must directly refine the earlier path;
the child model allowance then supplies the finite discrepancy bound. -/
structure ConstantRefinementProgram where
  model : Nat -> PathModel
  refinements : forall {earlier later : Nat}, earlier <= later ->
    PathModel.ConstantPathRefinement (model earlier).cells (model later).cells
  errorScale : Coordinate
  errorScale_nonneg : 0 <= errorScale
  modelAllowance_le : forall index,
    (model index).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale index
  centerBound : Coordinate
  centerBound_nonneg : 0 <= centerBound
  sample_bounded : forall index,
    normSq (model index).integralSample <= centerBound

namespace ConstantRefinementProgram

/-- Forget the stronger partition evidence after deriving the required
finite `later_close` estimate. -/
def toRefinementProgram (program : ConstantRefinementProgram) :
    RefinementProgram where
  model := program.model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := by
    intro earlier later order
    calc
      normSq
          ((program.model later).integralSample -
            (program.model earlier).integralSample) <=
        (program.model later).aggregateAllowance :=
        (program.refinements order).integral_difference_le
      _ <= CCL.FiniteGeometric.quarterRadius program.errorScale later :=
        program.modelAllowance_le later
      _ <= CCL.FiniteGeometric.quarterRadius program.errorScale earlier :=
        CCL.FiniteGeometric.quarterRadius_antitone
          program.errorScale_nonneg order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

end ConstantRefinementProgram

/-- A realistic constant-cell refinement program.  Its finite partition
certificate compares each child coefficient with the parent constant using
the combined uncertainty of both semantic models.  The separate comparison
bound is exactly the hypothesis needed for the Cauchy estimate; it does not
pretend that a fixed rational parent sample is accurate at every later child
scale. -/
structure CompatibleConstantRefinementProgram where
  model : Nat -> PathModel
  refinements : forall {earlier later : Nat}, earlier <= later ->
    PathModel.CompatibleConstantPathRefinement
      (model earlier).cells (model later).cells
  errorScale : Coordinate
  errorScale_nonneg : 0 <= errorScale
  modelAllowance_le : forall index,
    (model index).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale index
  comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (refinements order).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 <= centerBound
  sample_bounded : forall index,
    normSq (model index).integralSample <= centerBound

namespace CompatibleConstantRefinementProgram

/-- Derive the ordinary finite-refinement program from compatible parent and
child partition certificates. -/
def toRefinementProgram (program : CompatibleConstantRefinementProgram) :
    RefinementProgram where
  model := program.model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := by
    intro earlier later order
    calc
      normSq
          ((program.model later).integralSample -
            (program.model earlier).integralSample) <=
        (program.refinements order).comparisonAllowance :=
        (program.refinements order).integral_difference_le
      _ <= CCL.FiniteGeometric.quarterRadius program.errorScale earlier :=
        program.comparisonAllowance_le order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

end CompatibleConstantRefinementProgram

/-! ## Consecutive compatible refinements -/

/-- A compatible refinement program presented only one finite step at a time.

The squared comparison error of step `n -> n + 1` decays as `4^-n`.
Finite telescoping then gives the ordinary all-later Cauchy estimate with a
factor-four error scale.  This interface is useful when the child occurrence
is constructed from its immediate prepared parent and no transitivity of
parent--child allowance certificates is available. -/
structure SequentialCompatibleConstantRefinementProgram where
  model : Nat -> PathModel
  steps : forall index,
    PathModel.CompatibleConstantPathRefinement
      (model index).cells (model (index + 1)).cells
  stepScale : Coordinate
  stepScale_nonneg : 0 <= stepScale
  initialAllowance_le :
    (model 0).aggregateAllowance <= 4 * stepScale
  comparisonAllowance_le : forall index,
    (steps index).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius stepScale index

namespace SequentialCompatibleConstantRefinementProgram

/-- The factor-four scale left after summing every displayed finite tail. -/
def errorScale (program : SequentialCompatibleConstantRefinementProgram) :
    Coordinate :=
  4 * program.stepScale

theorem errorScale_nonneg
    (program : SequentialCompatibleConstantRefinementProgram) :
    0 <= program.errorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    program.stepScale_nonneg

private theorem quarterRadius_four_mul_succ (scale : Coordinate)
    (index : Nat) :
    CCL.FiniteGeometric.quarterRadius (4 * scale) (index + 1) =
      CCL.FiniteGeometric.quarterRadius scale index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_succ]
  have quarterFour : (4 : Coordinate) * (1 / 4) = 1 := by decide
  calc
    (4 * scale) * ((1 / 4 : Coordinate) ^ index * (1 / 4)) =
        (scale * (1 / 4 : Coordinate) ^ index) * (4 * (1 / 4)) := by
      ring1
    _ = scale * (1 / 4 : Coordinate) ^ index := by
      rw [quarterFour]
      ring1

private theorem quarterRadius_four_mul (scale : Coordinate) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius (4 * scale) index =
      4 * CCL.FiniteGeometric.quarterRadius scale index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  ring1

/-- Every model allowance is already paid either by the initial bound or by
the preceding parent--child comparison. -/
theorem modelAllowance_le
    (program : SequentialCompatibleConstantRefinementProgram) (index : Nat) :
    (program.model index).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius program.errorScale index := by
  cases index with
  | zero =>
      simpa only [errorScale, CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        pow_zero, RFAP.ConstructiveFraction.mul_one_direct] using
        program.initialAllowance_le
  | succ index =>
      calc
        (program.model (index + 1)).aggregateAllowance <=
            (program.steps index).comparisonAllowance :=
          (program.steps index).childAggregateAllowance_le_comparisonAllowance
        _ <= CCL.FiniteGeometric.quarterRadius program.stepScale index :=
          program.comparisonAllowance_le index
        _ = CCL.FiniteGeometric.quarterRadius program.errorScale
            (index + 1) := by
          exact (quarterRadius_four_mul_succ program.stepScale index).symm

/-- One consecutive model difference has the displayed step modulus. -/
theorem step_difference_le
    (program : SequentialCompatibleConstantRefinementProgram) (index : Nat) :
    normSq
        ((program.model (index + 1)).integralSample -
          (program.model index).integralSample) <=
      CCL.FiniteGeometric.quarterRadius program.stepScale index := by
  exact (program.steps index).integral_difference_le.trans
    (program.comparisonAllowance_le index)

/-- Finite telescoping of consecutive squared errors.  The proof applies the
square-root-free two-term estimate at each displayed step; no completed sum
or infinite-series argument is used. -/
private theorem later_difference_le_extra
    (program : SequentialCompatibleConstantRefinementProgram) :
    forall (extra earlier : Nat),
      normSq
          ((program.model (earlier + extra)).integralSample -
            (program.model earlier).integralSample) <=
        CCL.FiniteGeometric.quarterRadius program.errorScale earlier
  | 0, earlier => by
      simp only [Nat.add_zero,
        RFAP.ConstructiveGaussian.Gaussian.sub_self,
        RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
      exact CCL.FiniteGeometric.quarterRadius_nonneg
        program.errorScale_nonneg earlier
  | extra + 1, earlier => by
      let laterSample := (program.model (earlier + (extra + 1))).integralSample
      let nextSample := (program.model (earlier + 1)).integralSample
      let earlierSample := (program.model earlier).integralSample
      have indexEqual : earlier + (extra + 1) = (earlier + 1) + extra := by
        omega
      have tailBound :
          normSq (laterSample - nextSample) <=
            CCL.FiniteGeometric.quarterRadius program.errorScale
              (earlier + 1) := by
        simpa only [laterSample, nextSample, indexEqual] using
          later_difference_le_extra program extra (earlier + 1)
      have headBound :
          normSq (nextSample - earlierSample) <=
            CCL.FiniteGeometric.quarterRadius program.stepScale earlier := by
        simpa only [nextSample, earlierSample] using
          program.step_difference_le earlier
      have decomposition : laterSample - earlierSample =
          (laterSample - nextSample) + (nextSample - earlierSample) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
      rw [decomposition]
      calc
        normSq
            ((laterSample - nextSample) +
              (nextSample - earlierSample)) <=
            2 * (normSq (laterSample - nextSample) +
              normSq (nextSample - earlierSample)) :=
          RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
        _ <= 2 *
            (CCL.FiniteGeometric.quarterRadius program.errorScale
                (earlier + 1) +
              CCL.FiniteGeometric.quarterRadius program.stepScale earlier) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add tailBound headBound) (by decide)
        _ = CCL.FiniteGeometric.quarterRadius program.errorScale earlier := by
          rw [show program.errorScale = 4 * program.stepScale from rfl,
            quarterRadius_four_mul_succ, quarterRadius_four_mul]
          ring1

/-- Any displayed later sample is close to the earlier one by the derived
factor-four geometric modulus. -/
theorem later_close (program : SequentialCompatibleConstantRefinementProgram)
    {earlier later : Nat} (order : earlier <= later) :
    normSq
        ((program.model later).integralSample -
          (program.model earlier).integralSample) <=
      CCL.FiniteGeometric.quarterRadius program.errorScale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  exact later_difference_le_extra program extra earlier

/-- Canonical squared sample bound derived from the initial model and the
finite telescoping modulus. -/
def centerBound (program : SequentialCompatibleConstantRefinementProgram) :
    Coordinate :=
  2 * (normSq (program.model 0).integralSample + program.errorScale)

theorem centerBound_nonneg
    (program : SequentialCompatibleConstantRefinementProgram) :
    0 <= program.centerBound := by
  unfold centerBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (normSq_nonneg _) program.errorScale_nonneg)

theorem sample_bounded
    (program : SequentialCompatibleConstantRefinementProgram) (index : Nat) :
    normSq (program.model index).integralSample <= program.centerBound := by
  let current := (program.model index).integralSample
  let initial := (program.model 0).integralSample
  have movement : normSq (current - initial) <= program.errorScale :=
    (program.later_close (Nat.zero_le index)).trans
      (CCL.FiniteGeometric.quarterRadius_le_scale
        program.errorScale_nonneg 0)
  have identity : (current - initial) + initial = current := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have sumBound :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two
      (current - initial) initial
  rw [identity] at sumBound
  exact sumBound.trans (by
    apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
      (show (0 : Coordinate) <= 2 by decide)
    calc
      normSq (current - initial) + normSq initial <=
          program.errorScale + normSq initial :=
        add_le_add movement le_rfl
      _ = normSq initial + program.errorScale := by ring1)

/-- Forget the consecutive presentation after deriving every ordinary
refinement-program field by finite algebra. -/
def toRefinementProgram
    (program : SequentialCompatibleConstantRefinementProgram) :
    RefinementProgram where
  model := program.model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := program.later_close
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

end SequentialCompatibleConstantRefinementProgram

namespace RefinementProgram

/-- Replace only the executable presentation of a refinement program's
models.  The supplied pointwise equality keeps every estimate attached to
the original certified models, while allowing finite clients to retain a
call-by-need presentation of the same data. -/
def withEquivalentModels (program : RefinementProgram)
    (models : Nat -> PathModel)
    (models_eq : forall index, models index = program.model index) :
    RefinementProgram where
  model := models
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [models_eq index]
    exact program.modelAllowance_le index
  later_close := by
    intro earlier later order
    rw [models_eq later, models_eq earlier]
    exact program.later_close order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [models_eq index]
    exact program.sample_bounded index

/-- Quarter-power radii are monotone in their displayed finite scale. -/
private theorem quarterRadius_mono_scale {lower upper : Coordinate}
    (bound : lower <= upper) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius lower index <=
      CCL.FiniteGeometric.quarterRadius upper index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct bound
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index)

/-- Retain a refinement program's exact finite models while replacing an
expensive derived error scale by a stored dominating rational.  This is a
cache boundary, not a new estimate: callers must supply the kernel-checked
comparison with the original scale. -/
def withLargerErrorScale (program : RefinementProgram)
    (scale : Coordinate) (scaleNonnegative : 0 <= scale)
    (dominates : program.errorScale <= scale) : RefinementProgram where
  model := program.model
  errorScale := scale
  errorScale_nonneg := scaleNonnegative
  modelAllowance_le := by
    intro index
    exact (program.modelAllowance_le index).trans
      (quarterRadius_mono_scale dominates index)
  later_close := by
    intro earlier later order
    exact (program.later_close order).trans
      (quarterRadius_mono_scale dominates earlier)
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

def approximation (program : RefinementProgram) : Approximation where
  sample index := (program.model index).integralSample
  radiusSq := CCL.FiniteGeometric.quarterRadius program.errorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg program.errorScale_nonneg
  later_close := program.later_close
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow program.errorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge program.errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      program.errorScale program.errorScale_nonneg
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

def output (program : RefinementProgram) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation program.approximation

/-- A single exact finite Gaussian-polynomial segment. -/
def exactPolynomial (start finish : Gaussian) (polynomial : Polynomial) :
    RefinementProgram := by
  let cell := CellModel.exact start finish polynomial
  let path : PathModel := ⟨[cell]⟩
  let sample := path.integralSample
  exact
    { model := fun _ => path
      errorScale := 0
      errorScale_nonneg := le_rfl
      modelAllowance_le := by
        intro index
        change (1 : Coordinate) * (normSq cell.displacement * 0 + 0) <=
          CCL.FiniteGeometric.quarterRadius 0 index
        rw [RFAP.ConstructiveFraction.mul_zero_direct,
          RFAP.ConstructiveFraction.zero_add,
          RFAP.ConstructiveFraction.mul_zero_direct,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          RFAP.ConstructiveFraction.zero_mul_direct]
      later_close := by
        intro earlier later order
        change normSq (sample - sample) <=
          CCL.FiniteGeometric.quarterRadius 0 earlier
        rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          RFAP.ConstructiveFraction.zero_mul_direct]
      centerBound := normSq sample
      centerBound_nonneg := normSq_nonneg sample
      sample_bounded := by intro index; exact le_rfl }

/-- A one-cell exact path carrying one displayed Gaussian rational as its
integral sample.  It is used to turn finite arithmetic samples into ordinary
refinement-program models without postulating a completed value. -/
def exactSamplePath (value : Gaussian) : PathModel :=
  ⟨[CellModel.exact 0 1
    (CCL.FiniteGaussianPolynomial.constant value)]⟩

@[simp] theorem exactSamplePath_integralSample (value : Gaussian) :
    (exactSamplePath value).integralSample = value := by
  unfold exactSamplePath PathModel.integralSample CellModel.exact
    CellModel.integralSample CellModel.displacement
  simp only [List.foldr_cons, List.foldr_nil,
    CCL.FiniteGaussianPolynomial.definiteIntegral_constant]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, mul_re, mul_im, add_re, add_im,
      zero_re, zero_im, one_re, one_im] <;>
    ring1

@[simp] theorem exactSamplePath_aggregateAllowance (value : Gaussian) :
    (exactSamplePath value).aggregateAllowance = 0 := by
  unfold exactSamplePath PathModel.aggregateAllowance
    PathModel.totalWeightedAllowance CellModel.exact CellModel.weightedAllowance
  simp only [List.foldr_cons, List.foldr_nil,
    RFAP.ConstructiveFraction.mul_zero_direct,
    RFAP.ConstructiveFraction.zero_add]

/-- A one-cell exact path whose integral sample is the product of the samples
of two displayed finite paths.  This is an algebraic carrier for products of
persistent integrals; it does not assert that either input path is traversed. -/
def productSamplePath (left right : PathModel) : PathModel :=
  exactSamplePath (left.integralSample * right.integralSample)

@[simp] theorem productSamplePath_integralSample (left right : PathModel) :
    (productSamplePath left right).integralSample =
      left.integralSample * right.integralSample :=
  exactSamplePath_integralSample _

@[simp] theorem productSamplePath_aggregateAllowance
    (left right : PathModel) :
    (productSamplePath left right).aggregateAllowance = 0 :=
  exactSamplePath_aggregateAllowance _

/-- Repackage an arbitrary coherent CCL name as a Gaussian refinement program.
Every displayed model is a one-cell exact carrier for one finite witness of
the original name, and the standard finite sampling modulus supplies all
program bounds. -/
def ofCoherentNamed (value : CoherentNamed) : RefinementProgram := by
  let source := CCL.ProgressiveSampling.approximation value.name
  exact
    { model := fun index => exactSamplePath (source.sample index)
      errorScale := 4
      errorScale_nonneg := by decide
      modelAllowance_le := by
        intro index
        rw [exactSamplePath_aggregateAllowance]
        exact CCL.FiniteGeometric.quarterRadius_nonneg (by decide) index
      later_close := by
        intro earlier later order
        rw [exactSamplePath_integralSample, exactSamplePath_integralSample]
        exact source.later_close order
      centerBound := source.centerBound
      centerBound_nonneg := source.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [exactSamplePath_integralSample]
        exact source.sample_bounded index }

@[simp] theorem ofCoherentNamed_integralSample (value : CoherentNamed)
    (index : Nat) :
    ((ofCoherentNamed value).model index).integralSample =
      (CCL.ProgressiveSampling.approximation value.name).sample index :=
  exactSamplePath_integralSample _

/-- Finite local data for adding two Gaussian refinement programs.  The
caller supplies the actual finite model at every index and checks its exact
path sum and aggregate allowance. -/
structure SumModels (left right : RefinementProgram) where
  model : Nat -> PathModel
  integral_eq : forall index,
    (model index).integralSample =
      (left.model index).integralSample + (right.model index).integralSample
  aggregate_le : forall index,
    (model index).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

/-- Add two persistent Gaussian path integrals using only their displayed
finite sum models. -/
def add (left right : RefinementProgram) (models : SumModels left right) :
    RefinementProgram where
  model := models.model
  errorScale := 2 * (left.errorScale + right.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
  modelAllowance_le := models.aggregate_le
  later_close := by
    intro earlier later order
    rw [models.integral_eq, models.integral_eq]
    have identity :
        ((left.model later).integralSample +
              (right.model later).integralSample) -
            ((left.model earlier).integralSample +
              (right.model earlier).integralSample) =
          ((left.model later).integralSample -
              (left.model earlier).integralSample) +
            ((right.model later).integralSample -
              (right.model earlier).integralSample) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    rw [identity]
    calc
      normSq
          (((left.model later).integralSample -
              (left.model earlier).integralSample) +
            ((right.model later).integralSample -
              (right.model earlier).integralSample)) <=
          2 *
            (normSq ((left.model later).integralSample -
                (left.model earlier).integralSample) +
              normSq ((right.model later).integralSample -
                (right.model earlier).integralSample)) :=
        normSq_add_le_two _ _
      _ <= 2 *
            (CCL.FiniteGeometric.quarterRadius left.errorScale earlier +
              CCL.FiniteGeometric.quarterRadius right.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add (left.later_close order) (right.later_close order))
          (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
            (2 * (left.errorScale + right.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  sample_bounded := by
    intro index
    rw [models.integral_eq]
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.sample_bounded index)
          (right.sample_bounded index)) (by decide))

@[simp] theorem add_integralSample (left right : RefinementProgram)
    (models : SumModels left right) (index : Nat) :
    ((add left right models).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  models.integral_eq index

/-- Multiply two persistent Gaussian integrals by synchronizing their finite
samples and placing each rational product in a one-cell exact model.  The
Cauchy scale is the explicit finite product estimate
`2 * (leftError * rightBound + leftBound * rightError)`. -/
def multiply (left right : RefinementProgram) : RefinementProgram where
  model := fun index => productSamplePath (left.model index) (right.model index)
  errorScale := 2 *
    (left.errorScale * right.centerBound +
      left.centerBound * right.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          left.errorScale_nonneg right.centerBound_nonneg)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          left.centerBound_nonneg right.errorScale_nonneg))
  modelAllowance_le := by
    intro index
    rw [productSamplePath_aggregateAllowance]
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (by decide : (0 : Coordinate) <= 2)
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            left.errorScale_nonneg right.centerBound_nonneg)
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            left.centerBound_nonneg right.errorScale_nonneg))) index
  later_close := by
    intro earlier later order
    let leftLater := (left.model later).integralSample
    let leftEarlier := (left.model earlier).integralSample
    let rightLater := (right.model later).integralSample
    let rightEarlier := (right.model earlier).integralSample
    have productIdentity :
        leftLater * rightLater - leftEarlier * rightEarlier =
          (leftLater - leftEarlier) * rightLater +
            leftEarlier * (rightLater - rightEarlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [leftLater, leftEarlier, rightLater, rightEarlier,
          sub_re, sub_im, mul_re, mul_im, add_re, add_im] <;>
        ring1
    have firstBound :
        normSq (leftLater - leftEarlier) * normSq rightLater <=
          CCL.FiniteGeometric.quarterRadius left.errorScale earlier *
            right.centerBound := by
      calc
        normSq (leftLater - leftEarlier) * normSq rightLater <=
            CCL.FiniteGeometric.quarterRadius left.errorScale earlier *
              normSq rightLater :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (left.later_close order) (normSq_nonneg rightLater)
        _ <= CCL.FiniteGeometric.quarterRadius left.errorScale earlier *
              right.centerBound :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (right.sample_bounded later)
            (CCL.FiniteGeometric.quarterRadius_nonneg
              left.errorScale_nonneg earlier)
    have secondBound :
        normSq leftEarlier * normSq (rightLater - rightEarlier) <=
          left.centerBound *
            CCL.FiniteGeometric.quarterRadius right.errorScale earlier := by
      calc
        normSq leftEarlier * normSq (rightLater - rightEarlier) <=
            normSq leftEarlier *
              CCL.FiniteGeometric.quarterRadius right.errorScale earlier :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (right.later_close order) (normSq_nonneg leftEarlier)
        _ <= left.centerBound *
              CCL.FiniteGeometric.quarterRadius right.errorScale earlier :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (left.sample_bounded earlier)
            (CCL.FiniteGeometric.quarterRadius_nonneg
              right.errorScale_nonneg earlier)
    rw [productSamplePath_integralSample, productSamplePath_integralSample,
      productIdentity]
    calc
      normSq ((leftLater - leftEarlier) * rightLater +
          leftEarlier * (rightLater - rightEarlier)) <=
          2 *
            (normSq ((leftLater - leftEarlier) * rightLater) +
              normSq (leftEarlier * (rightLater - rightEarlier))) :=
        normSq_add_le_two _ _
      _ = 2 *
            (normSq (leftLater - leftEarlier) * normSq rightLater +
              normSq leftEarlier * normSq (rightLater - rightEarlier)) := by
        rw [normSq_mul, normSq_mul]
      _ <= 2 *
            (CCL.FiniteGeometric.quarterRadius left.errorScale earlier *
                right.centerBound +
              left.centerBound *
                CCL.FiniteGeometric.quarterRadius right.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstBound secondBound) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
            (2 *
              (left.errorScale * right.centerBound +
                left.centerBound * right.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct left.centerBound_nonneg
      right.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [productSamplePath_integralSample, normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.sample_bounded index) (right.sample_bounded index)
      (normSq_nonneg (right.model index).integralSample)
      left.centerBound_nonneg

@[simp] theorem multiply_integralSample (left right : RefinementProgram)
    (index : Nat) :
    ((multiply left right).model index).integralSample =
      (left.model index).integralSample *
        (right.model index).integralSample :=
  productSamplePath_integralSample _ _

/-- The finite allowance calculation required to concatenate two displayed
Gaussian path families. -/
structure ConcatenationAllowance (left right : RefinementProgram) where
  aggregate_le : forall index,
    ((left.model index).concat (right.model index)).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

/-- Concatenate two persistent finite paths. -/
def concat (left right : RefinementProgram)
    (allowance : ConcatenationAllowance left right) : RefinementProgram :=
  add left right
    { model := fun index => (left.model index).concat (right.model index)
      integral_eq := by
        intro index
        exact PathModel.integralSample_concat _ _
      aggregate_le := allowance.aggregate_le }

@[simp] theorem concat_model (left right : RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    (concat left right allowance).model index =
      (left.model index).concat (right.model index) :=
  rfl

theorem concat_integralSample (left right : RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    ((concat left right allowance).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  PathModel.integralSample_concat _ _

/-- Explicit finite model data for reversing every displayed path. -/
structure ReversalModels (program : RefinementProgram) where
  model : Nat -> PathModel
  integral_eq : forall index,
    (model index).integralSample = -(program.model index).integralSample
  aggregate_le : forall index,
    (model index).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius program.errorScale index

namespace ReversalModels

/-- Build reversal data from cellwise finite path reversals. -/
def ofPathReversals (program : RefinementProgram)
    (reversals : forall index, PathModel.Reversal (program.model index))
    (aggregate_le : forall index,
      ((program.model index).reverse (reversals index)).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius program.errorScale index) :
    ReversalModels program where
  model := fun index => (program.model index).reverse (reversals index)
  integral_eq := by
    intro index
    exact PathModel.reverse_integralSample _ _
  aggregate_le := aggregate_le

end ReversalModels

/-- Reverse a persistent Gaussian path integral. -/
def reverse (program : RefinementProgram) (models : ReversalModels program) :
    RefinementProgram where
  model := models.model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := models.aggregate_le
  later_close := by
    intro earlier later order
    rw [models.integral_eq, models.integral_eq]
    have identity :
        -(program.model later).integralSample -
            -(program.model earlier).integralSample =
          -((program.model later).integralSample -
            (program.model earlier).integralSample) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, sub_re, sub_im] <;> ring1
    rw [identity, normSq_neg]
    exact program.later_close order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [models.integral_eq, normSq_neg]
    exact program.sample_bounded index

@[simp] theorem reverse_integralSample (program : RefinementProgram)
    (models : ReversalModels program) (index : Nat) :
    ((reverse program models).model index).integralSample =
      -(program.model index).integralSample :=
  models.integral_eq index

/-- Every positive requested error is answered by one explicit finite model. -/
theorem finite_subdivision_accurate (program : RefinementProgram)
    (current : Nat) (target : Coordinate) (positive : 0 < target) :
    let index := program.approximation.refineIndex current target positive
    (program.model index).aggregateAllowance < target := by
  let index := program.approximation.refineIndex current target positive
  exact (program.modelAllowance_le index).trans_lt
    (program.approximation.refineIndex_accurate current target positive)

/-- End-to-end productive CCL contract for the Gaussian quadrature output. -/
theorem output_bitstream_and_error (program : RefinementProgram)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      program.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance refined.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        refined.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance refined.machine count) :=
  CCL.TranscendentalOutput.refined_bitstream_and_error
    program.output.name target positive count

end RefinementProgram

end CCL.ProgressiveGaussianIntegration

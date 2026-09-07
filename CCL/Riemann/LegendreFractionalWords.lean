import CCL.Riemann.LegendreFractionalAction

/-!
# Finite-word Legendre fractional transport

This module folds convention-locked integral matrices and their precisely
indexed denominator preparations.  It keeps the unconditional homogeneous
matrix product separate from stepwise productive division, then proves that a
fully prepared fold agrees with one prepared quotient by the folded matrix.
For period transport it also reverses the generator list while transposing
each homology matrix, and proves that this finite fold is exactly the dual
`periodMatrix` action.
-/

namespace CCL.Riemann.LegendreFractionalWords

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendreFractionalAction

abbrev IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RawPeriodVector := CCL.Riemann.LegendreGaussManin.RawPeriodVector
abbrev VectorEquivalent := CCL.Riemann.LegendreGaussManin.VectorEquivalent
abbrev DenominatorPreparation :=
  CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation

/-! ## Division-free finite matrix words -/

/-- Matrix product for traversal-order steps.  The head acts first, so later
entries multiply on the left. -/
def matrixProduct : List IntegralMatrix -> IntegralMatrix
  | [] => RFAP.ConstructiveFiniteMatrix.identity
  | matrix :: remaining =>
      RFAP.ConstructiveFiniteMatrix.mul (matrixProduct remaining) matrix

/-- Concatenating traversal-order matrix lists applies the first list before
the second, so the second folded matrix occurs on the left. -/
theorem matrixProduct_append (first second : List IntegralMatrix) :
    matrixProduct (first ++ second) =
      RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct second) (matrixProduct first) := by
  induction first with
  | nil =>
      simp only [List.nil_append, matrixProduct]
      exact
        (CCL.Riemann.LegendrePicardLefschetz.mul_identity_int
          (matrixProduct second)).symm
  | cons matrix remaining inductionHypothesis =>
      simp only [List.cons_append, matrixProduct, inductionHypothesis]
      exact RFAP.ConstructiveFiniteMatrix.mul_assoc
        (matrixProduct second) (matrixProduct remaining) matrix

/-- Reverse a traversal list while transposing every matrix.  This is the
finite dual list forced by evaluating periods on the transported homology
basis. -/
def dualMatrices : List IntegralMatrix -> List IntegralMatrix
  | [] => []
  | matrix :: remaining =>
      dualMatrices remaining ++
        [CCL.Riemann.LegendrePicardLefschetz.transpose matrix]

/-- Folding the dual list gives exactly the transpose of the original folded
homology matrix. -/
theorem matrixProduct_dualMatrices (matrices : List IntegralMatrix) :
    matrixProduct (dualMatrices matrices) =
      CCL.Riemann.LegendrePicardLefschetz.transpose
        (matrixProduct matrices) := by
  induction matrices with
  | nil =>
      simp only [dualMatrices, matrixProduct,
        CCL.Riemann.LegendrePicardLefschetz.transpose_identity]
  | cons matrix remaining inductionHypothesis =>
      rw [dualMatrices, matrixProduct_append, inductionHypothesis]
      simp only [matrixProduct,
        CCL.Riemann.LegendrePicardLefschetz.identity_mul_int]
      rw [CCL.Riemann.LegendrePicardLefschetz.transpose_mul]

/-- Apply each matrix in traversal order to a homogeneous vector. -/
def blockAction : List IntegralMatrix -> RawPeriodVector -> RawPeriodVector
  | [], values => values
  | matrix :: remaining, values =>
      blockAction remaining (matrixAction matrix values)

/-- A finite block action is operationally the action of its exact folded
matrix, with the convention-locked multiplication order. -/
def matrixProduct_action : (matrices : List IntegralMatrix) ->
    (values : RawPeriodVector) ->
      VectorEquivalent (matrixAction (matrixProduct matrices) values)
        (blockAction matrices values)
  | [], values => matrixAction_identity values
  | matrix :: remaining, values =>
      VectorEquivalent.trans
        (matrixAction_mul (matrixProduct remaining) matrix values)
        (matrixProduct_action remaining (matrixAction matrix values))

/-- Homogeneous fractional rows of a word agree with stepwise matrix action,
without denominator evidence. -/
def fractionalRows_word (matrices : List IntegralMatrix)
    (tau : CoherentNamed) :
    VectorEquivalent
      (matrixAction (matrixProduct matrices) (fractionalVector tau))
      (blockAction matrices (fractionalVector tau)) :=
  matrixProduct_action matrices (fractionalVector tau)

/-- Exact folded-matrix equality makes two finite words have the same
homogeneous action. -/
def fractionalRows_of_matrixProduct_eq
    {left right : List IntegralMatrix}
    (matrixEq : matrixProduct left = matrixProduct right)
    (tau : CoherentNamed) :
    VectorEquivalent
      (matrixAction (matrixProduct left) (fractionalVector tau))
      (matrixAction (matrixProduct right) (fractionalVector tau)) := by
  rw [matrixEq]
  exact VectorEquivalent.refl _

/-! ## Stepwise productive preparations and append -/

/-- One denominator preparation for every actual intermediate productive
name.  The tail is indexed by the output produced using the head evidence. -/
def StepPreparations (tau : CoherentNamed) :
    List IntegralMatrix -> Type 1
  | [] => ULift Unit
  | matrix :: remaining =>
      Sigma fun head : DenominatorPreparation
        (fractionalDenominator matrix tau) =>
          StepPreparations (fractionalLinear matrix tau head) remaining

/-- Execute a finite word with its precisely indexed step preparations. -/
def stepAction (tau : CoherentNamed) :
    (matrices : List IntegralMatrix) ->
      StepPreparations tau matrices -> CoherentNamed
  | [], _ => tau
  | matrix :: remaining, preparations =>
      stepAction (fractionalLinear matrix tau preparations.1)
        remaining preparations.2

@[simp] theorem stepAction_nil (tau : CoherentNamed)
    (preparations : StepPreparations tau []) :
    stepAction tau [] preparations = tau := rfl

@[simp] theorem stepAction_cons (tau : CoherentNamed)
    (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (preparations : StepPreparations tau (matrix :: remaining)) :
    stepAction tau (matrix :: remaining) preparations =
      stepAction (fractionalLinear matrix tau preparations.1)
        remaining preparations.2 := rfl

/-- Concatenate two already prepared step schedules. -/
def appendPreparations (tau : CoherentNamed)
    (second : List IntegralMatrix) :
    (first : List IntegralMatrix) ->
      (firstPreparations : StepPreparations tau first) ->
      StepPreparations
        (stepAction tau first firstPreparations) second ->
      StepPreparations tau (first ++ second)
  | [], _, secondPreparations => secondPreparations
  | matrix :: remaining, firstPreparations, secondPreparations =>
      ⟨firstPreparations.1,
        appendPreparations
          (fractionalLinear matrix tau firstPreparations.1) second
          remaining firstPreparations.2 secondPreparations⟩

/-- Executing appended preparation schedules is definitionally the same as
executing the first schedule and then the second. -/
theorem stepAction_append (tau : CoherentNamed)
    (second : List IntegralMatrix) :
    (first : List IntegralMatrix) ->
      (firstPreparations : StepPreparations tau first) ->
      (secondPreparations : StepPreparations
        (stepAction tau first firstPreparations) second) ->
      stepAction tau (first ++ second)
          (appendPreparations tau second first firstPreparations
            secondPreparations) =
        stepAction (stepAction tau first firstPreparations) second
          secondPreparations
  | [], _, _ => rfl
  | _matrix :: remaining, firstPreparations, secondPreparations =>
      stepAction_append
        (fractionalLinear _ tau firstPreparations.1) second remaining
        firstPreparations.2 secondPreparations

/-! ## Fold certificates: local and combined preparations -/

/-- Stepwise evidence plus a preparation for the exact matrix product at each
recursive suffix.  The latter is what lets productive composition compare the
step execution with one quotient by the folded matrix. -/
def FoldPreparations (tau : CoherentNamed) :
    List IntegralMatrix -> Type 1
  | [] => DenominatorPreparation
      (fractionalDenominator RFAP.ConstructiveFiniteMatrix.identity tau)
  | matrix :: remaining =>
      Sigma fun head : DenominatorPreparation
        (fractionalDenominator matrix tau) =>
      Sigma fun _tail : FoldPreparations
        (fractionalLinear matrix tau head) remaining =>
        DenominatorPreparation
          (fractionalDenominator (matrixProduct (matrix :: remaining)) tau)

namespace FoldPreparations

/-- Preparation of the single exact folded matrix. -/
def combined {tau : CoherentNamed} :
    (matrices : List IntegralMatrix) ->
      FoldPreparations tau matrices ->
      DenominatorPreparation (fractionalDenominator
        (matrixProduct matrices) tau)
  | [], preparation => preparation
  | _ :: _, preparations => preparations.2.2

/-- Forget the combined preparations while retaining every actual step. -/
def toSteps {tau : CoherentNamed} :
    (matrices : List IntegralMatrix) ->
      FoldPreparations tau matrices -> StepPreparations tau matrices
  | [], _ => ULift.up ()
  | _matrix :: remaining, preparations =>
      ⟨preparations.1,
        toSteps remaining preparations.2.1⟩

end FoldPreparations

/-- Stepwise productive output retained by a full fold preparation. -/
def foldAction (tau : CoherentNamed) (matrices : List IntegralMatrix)
    (preparations : FoldPreparations tau matrices) : CoherentNamed :=
  stepAction tau matrices (FoldPreparations.toSteps matrices preparations)

/-- One quotient by the folded matrix agrees with the fully prepared stepwise
execution. -/
def productOutput_equivalent_foldAction :
    (matrices : List IntegralMatrix) -> (tau : CoherentNamed) ->
      (preparations : FoldPreparations tau matrices) ->
      NamedEquivalent
        (fractionalLinear (matrixProduct matrices) tau
          (FoldPreparations.combined matrices preparations)).name
        (foldAction tau matrices preparations).name
  | [], tau, preparations => by
      change NamedEquivalent
        (fractionalLinear RFAP.ConstructiveFiniteMatrix.identity tau
          preparations).name tau.name
      exact fractionalLinear_identity tau preparations
  | matrix :: remaining, tau, preparations => by
      let head := preparations.1
      let inner := fractionalLinear matrix tau head
      let tail := preparations.2.1
      let combined := preparations.2.2
      let composition : CompositionPreparation
          (matrixProduct remaining) matrix tau :=
        { inner := head
          outer := FoldPreparations.combined remaining tail
          combined := combined }
      have compose := fractionalLinear_mul
        (matrixProduct remaining) matrix tau composition
      have recurse := productOutput_equivalent_foldAction
        remaining inner tail
      change NamedEquivalent
        (fractionalLinear (matrixProduct (matrix :: remaining)) tau
          combined).name (foldAction tau (matrix :: remaining)
            preparations).name
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [composition, matrixProduct,
            CompositionPreparation.combinedOutput,
            CompositionPreparation.nestedOutput,
            CompositionPreparation.innerOutput] using compose)
        (by simpa only [inner, tail, foldAction, StepPreparations,
            FoldPreparations.toSteps, stepAction] using recurse)

/-! ## Matrix-equivalent words and reversal -/

/-- The exact integral matrices carried by a finite three-strand braid word,
retained in traversal order. -/
def braidMatrices (word : CCL.Knot.FiniteBraid.Word 3) :
    List IntegralMatrix :=
  word.map CCL.Riemann.LegendrePicardLefschetz.generatorMatrix

/-- Folding the matrices of a finite braid word is exactly the established
Picard--Lefschetz word matrix. -/
theorem matrixProduct_braidMatrices
    (word : CCL.Knot.FiniteBraid.Word 3) :
    matrixProduct (braidMatrices word) =
      CCL.Riemann.LegendrePicardLefschetz.wordMatrix word := by
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change RFAP.ConstructiveFiniteMatrix.mul
          (matrixProduct (braidMatrices remaining))
          (CCL.Riemann.LegendrePicardLefschetz.generatorMatrix generator) =
        RFAP.ConstructiveFiniteMatrix.mul
          (CCL.Riemann.LegendrePicardLefschetz.wordMatrix remaining)
          (CCL.Riemann.LegendrePicardLefschetz.generatorMatrix generator)
      rw [inductionHypothesis]

/-- Transposed generator matrices in the reverse list order forced by dual
period transport.  The reversal is essential: transposition reverses the
homology matrix product. -/
def periodBraidMatrices (word : CCL.Knot.FiniteBraid.Word 3) :
    List IntegralMatrix :=
  dualMatrices (braidMatrices word)

/-- The finite fold of the reversed transposed generators is exactly the
dual matrix acting on the period column. -/
theorem matrixProduct_periodBraidMatrices
    (word : CCL.Knot.FiniteBraid.Word 3) :
    matrixProduct (periodBraidMatrices word) =
      CCL.Riemann.LegendrePicardLefschetz.periodMatrix word := by
  rw [periodBraidMatrices, matrixProduct_dualMatrices,
    matrixProduct_braidMatrices]
  rfl

/-- For an arbitrary finite braid word, its dual homogeneous period rows are
the stepwise action of the reversed transposed generator list. -/
def periodBraidRows_word (word : CCL.Knot.FiniteBraid.Word 3)
    (tau : CoherentNamed) :
    VectorEquivalent
      (matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word)
        (fractionalVector tau))
      (blockAction (periodBraidMatrices word) (fractionalVector tau)) := by
  rw [← matrixProduct_periodBraidMatrices word]
  exact fractionalRows_word (periodBraidMatrices word) tau

/-- The preparations needed to execute the dual action of every generator
and compare it with the one exact folded period matrix. -/
def PeriodFoldPreparations (word : CCL.Knot.FiniteBraid.Word 3)
    (tau : CoherentNamed) : Type 1 :=
  FoldPreparations tau (periodBraidMatrices word)

/-- Reindex the retained combined preparation by the proved equality between
the finite dual fold and `periodMatrix`. -/
def PeriodFoldPreparations.periodPreparation
    (word : CCL.Knot.FiniteBraid.Word 3) (tau : CoherentNamed)
    (preparations : PeriodFoldPreparations word tau) :
    DenominatorPreparation
      (fractionalDenominator
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau) := by
  rw [← matrixProduct_periodBraidMatrices word]
  exact FoldPreparations.combined (periodBraidMatrices word) preparations

/-- One productive quotient by the exact dual period matrix agrees with the
actual stepwise execution of all reversed transposed generators. -/
def periodOutput_equivalent_foldAction
    (word : CCL.Knot.FiniteBraid.Word 3) (tau : CoherentNamed)
    (preparations : PeriodFoldPreparations word tau) :
    NamedEquivalent
      (fractionalLinear
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau
        (preparations.periodPreparation word tau)).name
      (foldAction tau (periodBraidMatrices word) preparations).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (fractionalLinear_of_matrix_eq
      (matrixProduct_periodBraidMatrices word).symm tau
      (preparations.periodPreparation word tau)
      (FoldPreparations.combined (periodBraidMatrices word) preparations))
    (productOutput_equivalent_foldAction
      (periodBraidMatrices word) tau preparations)

/-- The stepwise productive dual word satisfies the fraction-free quotient
equation for the exact period matrix. -/
def periodFold_denominator_mul
    (word : CCL.Knot.FiniteBraid.Word 3) (tau : CoherentNamed)
    (preparations : PeriodFoldPreparations word tau) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator
          (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau)
        (foldAction tau (periodBraidMatrices word) preparations)).name
      (fractionalNumerator
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau).name := by
  let matrix := CCL.Riemann.LegendrePicardLefschetz.periodMatrix word
  let denominator := fractionalDenominator matrix tau
  let direct := fractionalLinear matrix tau
    (preparations.periodPreparation word tau)
  let folded := foldAction tau (periodBraidMatrices word) preparations
  have directToFold : NamedEquivalent direct.name folded.name := by
    simpa only [matrix, direct, folded] using
      periodOutput_equivalent_foldAction word tau preparations
  have replaceFold : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul denominator folded).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul denominator direct).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      denominator denominator folded direct
      (CCL.OperationalEquivalence.NamedEquivalent.refl denominator.name)
      (CCL.OperationalEquivalence.NamedEquivalent.symm directToFold)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans replaceFold
    (by
      simpa only [matrix, denominator, direct] using
        denominator_mul_fractionalLinear matrix tau
          (preparations.periodPreparation word tau))

/-- Reversing a finite braid word and reversing each of its certified
generator matrices gives a left inverse of the traversal-order matrix fold. -/
theorem braidMatrices_inverse_left
    (word : CCL.Knot.FiniteBraid.Word 3) :
    RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct (braidMatrices word.inverse))
        (matrixProduct (braidMatrices word)) =
      RFAP.ConstructiveFiniteMatrix.identity := by
  rw [matrixProduct_braidMatrices, matrixProduct_braidMatrices]
  exact
    (CCL.Riemann.LegendrePicardLefschetz.wordMatrix_inverse_identities word).1

/-- The same certified generator reversal is also a right inverse. -/
theorem braidMatrices_inverse_right
    (word : CCL.Knot.FiniteBraid.Word 3) :
    RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct (braidMatrices word))
        (matrixProduct (braidMatrices word.inverse)) =
      RFAP.ConstructiveFiniteMatrix.identity := by
  rw [matrixProduct_braidMatrices, matrixProduct_braidMatrices]
  exact
    (CCL.Riemann.LegendrePicardLefschetz.wordMatrix_inverse_identities word).2

/-- Finite braid-word reversal undoes the homogeneous fractional action with
no denominator evidence.  The inverse law is derived from the certified
inverse of every displayed braid generator. -/
def braidWord_reversal_rows (word : CCL.Knot.FiniteBraid.Word 3)
    (tau : CoherentNamed) :
    VectorEquivalent
      (matrixAction (matrixProduct (braidMatrices word.inverse))
        (matrixAction (matrixProduct (braidMatrices word))
          (fractionalVector tau)))
      (fractionalVector tau) :=
  fractionalRows_inverse_of_mul_eq_identity
    (matrixProduct (braidMatrices word.inverse))
    (matrixProduct (braidMatrices word)) tau
    (braidMatrices_inverse_left word)

/-- Independently prepared finite words with the same exact folded matrix
produce operationally equivalent single-product outputs. -/
def productOutput_of_matrixProduct_eq
    {left right : List IntegralMatrix}
    (matrixEq : matrixProduct left = matrixProduct right)
    (tau : CoherentNamed)
    (leftPreparation : DenominatorPreparation
      (fractionalDenominator (matrixProduct left) tau))
    (rightPreparation : DenominatorPreparation
      (fractionalDenominator (matrixProduct right) tau)) :
    NamedEquivalent
      (fractionalLinear (matrixProduct left) tau leftPreparation).name
      (fractionalLinear (matrixProduct right) tau rightPreparation).name :=
  fractionalLinear_of_matrix_eq matrixEq tau
    leftPreparation rightPreparation

/-- A finite reverse word whose folded matrix is a certified left inverse
undoes the forward word at the productive single-product level. -/
def productReversal
    (forward reverse : List IntegralMatrix) (tau : CoherentNamed)
    (preparation : CompositionPreparation
      (matrixProduct reverse) (matrixProduct forward) tau)
    (inverse : RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct reverse) (matrixProduct forward) =
      RFAP.ConstructiveFiniteMatrix.identity) :
    NamedEquivalent preparation.nestedOutput.name tau.name :=
  fractionalLinear_inverse_of_mul_eq_identity
    (matrixProduct reverse) (matrixProduct forward) tau preparation inverse

/-- Productive finite braid-word reversal, with all three denominator
preparations retained at their exact combined and intermediate names. -/
def braidWord_productReversal (word : CCL.Knot.FiniteBraid.Word 3)
    (tau : CoherentNamed)
    (preparation : CompositionPreparation
      (matrixProduct (braidMatrices word.inverse))
      (matrixProduct (braidMatrices word)) tau) :
    NamedEquivalent preparation.nestedOutput.name tau.name :=
  productReversal (braidMatrices word) (braidMatrices word.inverse) tau
    preparation (braidMatrices_inverse_left word)

/-! ## Stepwise productive reversal -/

/-- A shallow carrier for the evidence needed to reverse an actual prepared
finite-word execution.  The reverse fold is indexed by the literal output of
the forward fold, while the composition certificate retains its independently
prepared single-product representatives. -/
structure FoldReversalPreparationsPayload
    (forwardType : Type 1) (forwardOutput : forwardType -> CoherentNamed)
    (reverseType : (forward : forwardType) -> Type 1)
    (compositionType : Type 1) where
  forward : forwardType
  reverse : reverseType forward
  composition : compositionType

/-- Precisely indexed preparations for a stepwise forward word, its stepwise
reverse beginning at the actual forward output, and the certified folded
composition used to prove cancellation. -/
def FoldReversalPreparations (forward reverse : List IntegralMatrix)
    (tau : CoherentNamed) : Type 1 :=
  FoldReversalPreparationsPayload
    (FoldPreparations tau forward)
    (fun preparation => foldAction tau forward preparation)
    (fun preparation => FoldPreparations
      (foldAction tau forward preparation) reverse)
    (CompositionPreparation
      (matrixProduct reverse) (matrixProduct forward) tau)

/-- A stepwise prepared reverse word undoes the actual stepwise prepared
forward word whenever their exact folded matrices are certified inverses.
Every local denominator remains indexed by the concrete intermediate name at
which it is consumed. -/
def foldAction_reversal (forward reverse : List IntegralMatrix)
    (tau : CoherentNamed)
    (preparations : FoldReversalPreparations forward reverse tau)
    (inverse : RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct reverse) (matrixProduct forward) =
      RFAP.ConstructiveFiniteMatrix.identity) :
    NamedEquivalent
      (foldAction
        (foldAction tau forward preparations.forward)
        reverse preparations.reverse).name tau.name := by
  let forwardOutput := foldAction tau forward preparations.forward
  let reverseOutput := foldAction forwardOutput reverse preparations.reverse
  let forwardSingle := fractionalLinear (matrixProduct forward) tau
    (FoldPreparations.combined forward preparations.forward)
  let reverseSingle := fractionalLinear (matrixProduct reverse) forwardOutput
    (FoldPreparations.combined reverse preparations.reverse)
  have forwardSingleToFold : NamedEquivalent forwardSingle.name
      forwardOutput.name := by
    simpa only [forwardSingle, forwardOutput] using
      productOutput_equivalent_foldAction forward tau preparations.forward
  have forwardSingleToComposition : NamedEquivalent forwardSingle.name
      preparations.composition.innerOutput.name := by
    simpa only [forwardSingle, CompositionPreparation.innerOutput] using
      fractionalLinear_preparation_independent (matrixProduct forward) tau
        (FoldPreparations.combined forward preparations.forward)
        preparations.composition.inner
  have forwardFoldToComposition : NamedEquivalent forwardOutput.name
      preparations.composition.innerOutput.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm forwardSingleToFold)
      forwardSingleToComposition
  have reverseSingleToFold : NamedEquivalent reverseSingle.name
      reverseOutput.name := by
    simpa only [reverseSingle, reverseOutput, forwardOutput] using
      productOutput_equivalent_foldAction reverse forwardOutput
        preparations.reverse
  have reverseInputsAgree : NamedEquivalent reverseSingle.name
      preparations.composition.nestedOutput.name := by
    simpa only [reverseSingle, CompositionPreparation.nestedOutput] using
      fractionalLinear_respects (matrixProduct reverse) forwardOutput
        preparations.composition.innerOutput forwardFoldToComposition
        (FoldPreparations.combined reverse preparations.reverse)
        preparations.composition.outer
  have compositionCancels : NamedEquivalent
      preparations.composition.nestedOutput.name tau.name :=
    fractionalLinear_inverse_of_mul_eq_identity
      (matrixProduct reverse) (matrixProduct forward) tau
      preparations.composition inverse
  change NamedEquivalent reverseOutput.name tau.name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm reverseSingleToFold)
    (CCL.OperationalEquivalence.NamedEquivalent.trans reverseInputsAgree
      compositionCancels)

/-- Reversing a finite braid word and every certified generator undoes its
actual stepwise productive fold, not merely the quotient by its folded
matrix. -/
def braidWord_foldReversal (word : CCL.Knot.FiniteBraid.Word 3)
    (tau : CoherentNamed)
    (preparations : FoldReversalPreparations
      (braidMatrices word) (braidMatrices word.inverse) tau) :
    NamedEquivalent
      (foldAction
        (foldAction tau (braidMatrices word) preparations.forward)
        (braidMatrices word.inverse) preparations.reverse).name tau.name :=
  foldAction_reversal (braidMatrices word) (braidMatrices word.inverse) tau
    preparations (braidMatrices_inverse_left word)

/-- The dual period fold of the inverse braid is a left inverse of the dual
period fold of the original braid. -/
theorem periodBraidMatrices_inverse_left
    (word : CCL.Knot.FiniteBraid.Word 3) :
    RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct (periodBraidMatrices word.inverse))
        (matrixProduct (periodBraidMatrices word)) =
      RFAP.ConstructiveFiniteMatrix.identity := by
  rw [matrixProduct_periodBraidMatrices,
    matrixProduct_periodBraidMatrices]
  exact
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix_inverse_identities
      word).2

/-- The corresponding dual period folds are inverse in the other
multiplication order as well. -/
theorem periodBraidMatrices_inverse_right
    (word : CCL.Knot.FiniteBraid.Word 3) :
    RFAP.ConstructiveFiniteMatrix.mul
        (matrixProduct (periodBraidMatrices word))
        (matrixProduct (periodBraidMatrices word.inverse)) =
      RFAP.ConstructiveFiniteMatrix.identity := by
  rw [matrixProduct_periodBraidMatrices,
    matrixProduct_periodBraidMatrices]
  exact
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix_inverse_identities
      word).1

/-- For every finite braid word, a prepared stepwise dual action followed by
the prepared dual action of the inverse word returns the original normalized
period ratio operationally. -/
def periodBraidWord_foldReversal (word : CCL.Knot.FiniteBraid.Word 3)
    (tau : CoherentNamed)
    (preparations : FoldReversalPreparations
      (periodBraidMatrices word) (periodBraidMatrices word.inverse) tau) :
    NamedEquivalent
      (foldAction
        (foldAction tau (periodBraidMatrices word) preparations.forward)
        (periodBraidMatrices word.inverse) preparations.reverse).name
      tau.name :=
  foldAction_reversal (periodBraidMatrices word)
    (periodBraidMatrices word.inverse) tau preparations
    (periodBraidMatrices_inverse_left word)

/-! ## Standard finite words -/

/-- Singleton traversal word for the standard loop around zero. -/
def standardZeroMatrices : List IntegralMatrix :=
  [CCL.Riemann.LegendreMonodromy.zeroMatrix]

/-- Singleton traversal word for the standard loop around one. -/
def standardOneMatrices : List IntegralMatrix :=
  [CCL.Riemann.LegendreMonodromy.oneMatrix]

/-- Singleton traversal word for the standard loop around infinity. -/
def standardInfinityMatrices : List IntegralMatrix :=
  [CCL.Riemann.LegendreMonodromy.infinityMatrix]

@[simp] theorem standardZeroMatrices_product :
    matrixProduct standardZeroMatrices =
      CCL.Riemann.LegendreMonodromy.zeroMatrix := by
  simp only [standardZeroMatrices, matrixProduct,
    CCL.Riemann.LegendrePicardLefschetz.identity_mul_int]

@[simp] theorem standardOneMatrices_product :
    matrixProduct standardOneMatrices =
      CCL.Riemann.LegendreMonodromy.oneMatrix := by
  simp only [standardOneMatrices, matrixProduct,
    CCL.Riemann.LegendrePicardLefschetz.identity_mul_int]

@[simp] theorem standardInfinityMatrices_product :
    matrixProduct standardInfinityMatrices =
      CCL.Riemann.LegendreMonodromy.infinityMatrix := by
  simp only [standardInfinityMatrices, matrixProduct,
    CCL.Riemann.LegendrePicardLefschetz.identity_mul_int]

/-- The generic prepared finite-word fold specializes to the standard
zero-loop quotient `tau / (1 - 2*tau)`. -/
def standardZero_fold_formula (tau : CoherentNamed)
    (preparations : FoldPreparations tau standardZeroMatrices) :
    NamedEquivalent
      (foldAction tau standardZeroMatrices preparations).name
      (zeroTransform preparations.1).name :=
  CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- The generic prepared finite-word fold specializes to the unconditional
affine one-loop formula `2 + tau`; the singleton fold's unit-denominator
preparation is used only to compare with the legacy division-shaped output. -/
def standardOne_fold_formula (tau : CoherentNamed)
    (preparations : FoldPreparations tau standardOneMatrices) :
    NamedEquivalent
      (foldAction tau standardOneMatrices preparations).name
      (oneAffineTransform tau).name := by
  change NamedEquivalent (oneTransform preparations.1).name
    (oneAffineTransform tau).name
  exact oneTransform_equivalent_affine preparations.1

/-- The generic prepared finite-word fold specializes to the standard
infinity quotient `(-2 + tau) / (-3 + 2*tau)`. -/
def standardInfinity_fold_formula (tau : CoherentNamed)
    (preparations : FoldPreparations tau standardInfinityMatrices) :
    NamedEquivalent
      (foldAction tau standardInfinityMatrices preparations).name
      (infinityTransform preparations.1).name :=
  CCL.OperationalEquivalence.NamedEquivalent.refl _

def standardProductMatrices : List IntegralMatrix :=
  [CCL.Riemann.LegendreMonodromy.zeroMatrix,
    CCL.Riemann.LegendreMonodromy.oneMatrix,
    CCL.Riemann.LegendreMonodromy.infinityMatrix]

/-- The traversal-order standard product folds to
`infinity * (one * zero)`, hence exactly the identity. -/
theorem standardProductMatrices_eq_identity :
    matrixProduct standardProductMatrices =
      RFAP.ConstructiveFiniteMatrix.identity := by
  simp only [standardProductMatrices, matrixProduct]
  rw [CCL.Riemann.LegendrePicardLefschetz.identity_mul_int,
    RFAP.ConstructiveFiniteMatrix.mul_assoc,
    CCL.Riemann.LegendreMonodromy.explicit_loop_product_left]

/-- Every fully prepared stepwise execution of the standard product word
returns the source ratio operationally. -/
def standardProduct_fold_identity (tau : CoherentNamed)
    (preparations : FoldPreparations tau standardProductMatrices) :
    NamedEquivalent (foldAction tau standardProductMatrices preparations).name
      tau.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (productOutput_equivalent_foldAction
        standardProductMatrices tau preparations))
    (fractionalLinear_of_matrix_eq_identity
      (matrixProduct standardProductMatrices) tau
      (FoldPreparations.combined standardProductMatrices preparations)
      standardProductMatrices_eq_identity)

end CCL.Riemann.LegendreFractionalWords

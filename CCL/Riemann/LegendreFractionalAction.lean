import CCL.Riemann.LegendreModularMonodromy

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

namespace CCL.Riemann.LegendreFractionalAction

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.LegendreModularMonodromy

abbrev IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RawPeriodVector := CCL.Riemann.LegendreGaussManin.RawPeriodVector
abbrev VectorEquivalent := CCL.Riemann.LegendreGaussManin.VectorEquivalent
abbrev DenominatorPreparation :=
  CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation

/-! ## Convention-locked homogeneous composition -/

/-- The homogeneous fractional rows of `left * right` are obtained by acting
with `right` first and then `left`.  This is the division-free composition law
and fixes the multiplication order used throughout the module. -/
def fractionalRows_mul (left right : IntegralMatrix) (tau : CoherentNamed) :
    VectorEquivalent
      (fun row => fractionalRow
        (RFAP.ConstructiveFiniteMatrix.mul left right) tau row)
      (matrixAction left (fun row => fractionalRow right tau row)) := by
  simpa only [fractionalRow] using
    (matrixAction_mul left right (fractionalVector tau))

/-- Row-zero form of homogeneous composition. -/
def fractionalDenominator_mul (left right : IntegralMatrix)
    (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        (RFAP.ConstructiveFiniteMatrix.mul left right) tau).name
      (matrixAction left (fun row => fractionalRow right tau row) 0).name :=
  fractionalRows_mul left right tau 0

/-- Row-one form of homogeneous composition. -/
def fractionalNumerator_mul (left right : IntegralMatrix)
    (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        (RFAP.ConstructiveFiniteMatrix.mul left right) tau).name
      (matrixAction left (fun row => fractionalRow right tau row) 1).name :=
  fractionalRows_mul left right tau 1

/-- The standard combined path confirms the locked order `one * zero`. -/
theorem standard_combined_order {parameter :
    RFAP.ConstructiveGaussian.Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame) :
    CCL.Riemann.LegendrePicardLefschetz.wordMatrix
        loops.combinedPath.word =
      RFAP.ConstructiveFiniteMatrix.mul
        CCL.Riemann.LegendreMonodromy.oneMatrix
        CCL.Riemann.LegendreMonodromy.zeroMatrix :=
  loops.combinedPath_matrix

/-- The standard infinity path is the certified left inverse of that combined
order. -/
theorem standard_infinity_left_inverse :
    RFAP.ConstructiveFiniteMatrix.mul
        CCL.Riemann.LegendreMonodromy.infinityMatrix
        (RFAP.ConstructiveFiniteMatrix.mul
          CCL.Riemann.LegendreMonodromy.oneMatrix
          CCL.Riemann.LegendreMonodromy.zeroMatrix) =
      RFAP.ConstructiveFiniteMatrix.identity :=
  CCL.Riemann.LegendreMonodromy.explicit_loop_product_left

/-! ## Scaling through one prepared fractional output -/

/-- One matrix action on `(1,tau)` is its denominator times the homogeneous
vector of the prepared productive fractional output. -/
def matrixAction_fractional_scaled (matrix : IntegralMatrix)
    (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    VectorEquivalent
      (matrixAction matrix (fractionalVector tau))
      (scaleVector (fractionalDenominator matrix tau)
        (fractionalVector (fractionalLinear matrix tau preparation))) := by
  intro coordinate
  refine Fin.cases ?_ (fun tail => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) tail) coordinate
  ·
    change NamedEquivalent
      (fractionalDenominator matrix tau).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator matrix tau)
        (CCL.ProgressiveCoherence.CoherentNamed.exact 1)).name
    exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentMul_one_right
        (fractionalDenominator matrix tau))
  ·
    change NamedEquivalent
      (fractionalNumerator matrix tau).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator matrix tau)
        (fractionalLinear matrix tau preparation)).name
    exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (denominator_mul_fractionalLinear matrix tau preparation)

/-- Fraction-free normalized composition with the inner quotient prepared:
the combined homogeneous rows are the right denominator times the outer rows
evaluated at the inner productive output. -/
def fractionalRows_mul_scaled (left right : IntegralMatrix)
    (tau : CoherentNamed)
    (rightPreparation : DenominatorPreparation
      (fractionalDenominator right tau)) :
    VectorEquivalent
      (matrixAction (RFAP.ConstructiveFiniteMatrix.mul left right)
        (fractionalVector tau))
      (scaleVector (fractionalDenominator right tau)
        (matrixAction left
          (fractionalVector
            (fractionalLinear right tau rightPreparation)))) :=
  VectorEquivalent.trans
    (matrixAction_mul left right (fractionalVector tau))
    (VectorEquivalent.trans
      (matrixAction_respects left
        (matrixAction_fractional_scaled right tau rightPreparation))
      (matrixAction_scale left (fractionalDenominator right tau)
        (fractionalVector
          (fractionalLinear right tau rightPreparation))))

/-! ## Precisely indexed productive composition -/

/-- Lightweight dependent carrier for three preparation types.  Keeping this
carrier independent of fractional process expressions prevents generated
structure recursors from unfolding the complete action tree. -/
structure CompositionPreparationPayload (innerType : Type 1)
    (outerType : innerType -> Type 1) (combinedType : Type 1) where
  inner : innerType
  outer : outerType inner
  combined : combinedType

/-- Exact evidence needed to compare one combined quotient with the nested
right-then-left productive action.  None of the three process indices is
silently transported across operational equivalence. -/
def CompositionPreparation (left right : IntegralMatrix)
    (tau : CoherentNamed) : Type 1 :=
  CompositionPreparationPayload
    (DenominatorPreparation (fractionalDenominator right tau))
    (fun inner => DenominatorPreparation
      (fractionalDenominator left (fractionalLinear right tau inner)))
    (DenominatorPreparation
      (fractionalDenominator
        (RFAP.ConstructiveFiniteMatrix.mul left right) tau))

namespace CompositionPreparation

def innerOutput {left right : IntegralMatrix} {tau : CoherentNamed}
    (preparation : CompositionPreparation left right tau) : CoherentNamed :=
  fractionalLinear right tau preparation.inner

def nestedOutput {left right : IntegralMatrix} {tau : CoherentNamed}
    (preparation : CompositionPreparation left right tau) : CoherentNamed :=
  fractionalLinear left preparation.innerOutput preparation.outer

def combinedOutput {left right : IntegralMatrix} {tau : CoherentNamed}
    (preparation : CompositionPreparation left right tau) : CoherentNamed :=
  fractionalLinear (RFAP.ConstructiveFiniteMatrix.mul left right) tau
    preparation.combined

end CompositionPreparation

/-- Productive finite Möbius composition in the convention-locked order:
`T_(left * right)(tau) ~ T_left(T_right(tau))`. -/
def fractionalLinear_mul (left right : IntegralMatrix) (tau : CoherentNamed)
    (preparation : CompositionPreparation left right tau) :
    NamedEquivalent preparation.combinedOutput.name
      preparation.nestedOutput.name := by
  let innerOutput := preparation.innerOutput
  let nestedOutput := preparation.nestedOutput
  let combinedOutput := preparation.combinedOutput
  let rightDenominator := fractionalDenominator right tau
  let outerDenominator := fractionalDenominator left innerOutput
  let outerNumerator := fractionalNumerator left innerOutput
  let combinedDenominator := fractionalDenominator
    (RFAP.ConstructiveFiniteMatrix.mul left right) tau
  let combinedNumerator := fractionalNumerator
    (RFAP.ConstructiveFiniteMatrix.mul left right) tau
  have rows := fractionalRows_mul_scaled left right tau preparation.inner
  have denominatorScaled := rows 0
  change NamedEquivalent combinedDenominator.name
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      rightDenominator outerDenominator).name at denominatorScaled
  have numeratorScaled := rows 1
  change NamedEquivalent combinedNumerator.name
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      rightDenominator outerNumerator).name at numeratorScaled
  have outerEquation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        outerDenominator nestedOutput).name outerNumerator.name := by
    simpa only [innerOutput, nestedOutput, outerDenominator, outerNumerator,
      CompositionPreparation.innerOutput,
      CompositionPreparation.nestedOutput] using
      (denominator_mul_fractionalLinear left
        preparation.innerOutput preparation.outer)
  have combinedNested : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        combinedDenominator nestedOutput).name combinedNumerator.name := by
    apply CCL.OperationalEquivalence.NamedEquivalent.trans
    · exact CCL.TranscendentalCoherence.coherentMul_respects
        combinedDenominator
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          rightDenominator outerDenominator)
        nestedOutput nestedOutput denominatorScaled
        (CCL.OperationalEquivalence.NamedEquivalent.refl nestedOutput.name)
    · apply CCL.OperationalEquivalence.NamedEquivalent.trans
      · simpa only [CCL.ProgressiveCoherence.CoherentNamed.mul] using
          CCL.TranscendentalCoherence.coherentMul_assoc
            rightDenominator outerDenominator nestedOutput
      · apply CCL.OperationalEquivalence.NamedEquivalent.trans
        · exact CCL.TranscendentalCoherence.coherentMul_respects
            rightDenominator rightDenominator
            (CCL.ProgressiveCoherence.CoherentNamed.mul
              outerDenominator nestedOutput)
            outerNumerator
            (CCL.OperationalEquivalence.NamedEquivalent.refl
              rightDenominator.name) outerEquation
        · exact CCL.OperationalEquivalence.NamedEquivalent.symm numeratorScaled
  have preparedNested : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        preparation.combined.prepared nestedOutput).name
      combinedNumerator.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        preparation.combined.prepared combinedDenominator
        nestedOutput nestedOutput
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          preparation.combined.equivalent)
        (CCL.OperationalEquivalence.NamedEquivalent.refl nestedOutput.name))
      combinedNested
  have preparedCombined : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        preparation.combined.prepared combinedOutput).name
      combinedNumerator.name := by
    simpa only [combinedOutput, combinedNumerator,
      CompositionPreparation.combinedOutput] using
      (prepared_denominator_mul_fractionalLinear
        (RFAP.ConstructiveFiniteMatrix.mul left right) tau
        preparation.combined)
  change NamedEquivalent combinedOutput.name nestedOutput.name
  exact CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
    preparation.combined.prepared combinedOutput nestedOutput
    preparation.combined.apart
    (CCL.OperationalEquivalence.NamedEquivalent.trans preparedCombined
      (CCL.OperationalEquivalence.NamedEquivalent.symm preparedNested))

/-- Productive fractional output is independent of which successful
apartification certificate prepared the same exact denominator process. -/
def fractionalLinear_preparation_independent (matrix : IntegralMatrix)
    (tau : CoherentNamed)
    (first second : DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    NamedEquivalent (fractionalLinear matrix tau first).name
      (fractionalLinear matrix tau second).name := by
  let denominator := fractionalDenominator matrix tau
  let numerator := fractionalNumerator matrix tau
  let firstOutput := fractionalLinear matrix tau first
  let secondOutput := fractionalLinear matrix tau second
  have firstScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        first.prepared firstOutput).name numerator.name := by
    simpa only [firstOutput, numerator,
      CCL.ProgressiveCoherence.CoherentNamed.mul] using
      (prepared_denominator_mul_fractionalLinear matrix tau first)
  have secondScaledByFirst : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        first.prepared secondOutput).name numerator.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        first.prepared denominator secondOutput secondOutput
        (CCL.OperationalEquivalence.NamedEquivalent.symm first.equivalent)
        (CCL.OperationalEquivalence.NamedEquivalent.refl secondOutput.name))
      (by simpa only [denominator, numerator, secondOutput,
          CCL.ProgressiveCoherence.CoherentNamed.mul] using
        (denominator_mul_fractionalLinear matrix tau second))
  change NamedEquivalent firstOutput.name secondOutput.name
  exact CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
    first.prepared firstOutput secondOutput first.apart
    (CCL.OperationalEquivalence.NamedEquivalent.trans firstScaled
      (CCL.OperationalEquivalence.NamedEquivalent.symm secondScaledByFirst))

/-- Homogeneous normalized columns respect operational equality of their
`tau` coordinates. -/
def fractionalVector_respects {first second : CoherentNamed}
    (equivalent : NamedEquivalent first.name second.name) :
    VectorEquivalent (fractionalVector first) (fractionalVector second) := by
  intro coordinate
  refine Fin.cases ?_ (fun tail => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) tail) coordinate
  · exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  · change NamedEquivalent
      (fractionalVector first (1 : Fin 2)).name
      (fractionalVector second (1 : Fin 2)).name
    simpa only [fractionalVector_one] using equivalent

/-- Productive fractional action respects an operationally equivalent input,
while retaining independently prepared denominators at the two exact input
processes.  This is the rebasing step needed to compare genuine stepwise word
executions rather than only their single folded-matrix representatives. -/
def fractionalLinear_respects (matrix : IntegralMatrix)
    (first second : CoherentNamed)
    (equivalent : NamedEquivalent first.name second.name)
    (firstPreparation : DenominatorPreparation
      (fractionalDenominator matrix first))
    (secondPreparation : DenominatorPreparation
      (fractionalDenominator matrix second)) :
    NamedEquivalent
      (fractionalLinear matrix first firstPreparation).name
      (fractionalLinear matrix second secondPreparation).name := by
  let firstDenominator := fractionalDenominator matrix first
  let secondDenominator := fractionalDenominator matrix second
  let firstNumerator := fractionalNumerator matrix first
  let secondNumerator := fractionalNumerator matrix second
  let firstOutput := fractionalLinear matrix first firstPreparation
  let secondOutput := fractionalLinear matrix second secondPreparation
  have rows := matrixAction_respects matrix
    (fractionalVector_respects equivalent)
  have denominatorEquivalent : NamedEquivalent firstDenominator.name
      secondDenominator.name := by
    simpa only [firstDenominator, secondDenominator, fractionalDenominator,
      fractionalRow] using rows 0
  have numeratorEquivalent : NamedEquivalent firstNumerator.name
      secondNumerator.name := by
    simpa only [firstNumerator, secondNumerator, fractionalNumerator,
      fractionalRow] using rows 1
  have firstScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        firstPreparation.prepared firstOutput).name firstNumerator.name := by
    simpa only [firstOutput, firstNumerator] using
      (prepared_denominator_mul_fractionalLinear matrix first firstPreparation)
  have secondScaledByFirst : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        firstPreparation.prepared secondOutput).name firstNumerator.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        firstPreparation.prepared firstDenominator secondOutput secondOutput
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          firstPreparation.equivalent)
        (CCL.OperationalEquivalence.NamedEquivalent.refl secondOutput.name))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.TranscendentalCoherence.coherentMul_respects
          firstDenominator secondDenominator secondOutput secondOutput
          denominatorEquivalent
          (CCL.OperationalEquivalence.NamedEquivalent.refl secondOutput.name))
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (by simpa only [secondDenominator, secondNumerator, secondOutput,
              CCL.ProgressiveCoherence.CoherentNamed.mul]
            using
              (denominator_mul_fractionalLinear matrix second
                secondPreparation))
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            numeratorEquivalent)))
  change NamedEquivalent firstOutput.name secondOutput.name
  exact CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
    firstPreparation.prepared firstOutput secondOutput firstPreparation.apart
    (CCL.OperationalEquivalence.NamedEquivalent.trans firstScaled
      (CCL.OperationalEquivalence.NamedEquivalent.symm secondScaledByFirst))

/-- Exact matrix equality transports productive fractional output even when
the two equal matrix expressions were prepared independently. -/
def fractionalLinear_of_matrix_eq {left right : IntegralMatrix}
    (matrixEq : left = right) (tau : CoherentNamed)
    (leftPreparation : DenominatorPreparation
      (fractionalDenominator left tau))
    (rightPreparation : DenominatorPreparation
      (fractionalDenominator right tau)) :
    NamedEquivalent (fractionalLinear left tau leftPreparation).name
      (fractionalLinear right tau rightPreparation).name := by
  subst right
  exact fractionalLinear_preparation_independent left tau
    leftPreparation rightPreparation

/-! ## Identity and certified inverse laws -/

/-- Any matrix proved exactly equal to the identity has productive fractional
action operationally equal to `tau`, while retaining preparation at the
caller's original matrix-indexed denominator. -/
def fractionalLinear_of_matrix_eq_identity (matrix : IntegralMatrix)
    (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau))
    (matrixEq : matrix = RFAP.ConstructiveFiniteMatrix.identity) :
    NamedEquivalent
      (fractionalLinear matrix tau preparation).name tau.name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let output := fractionalLinear matrix tau preparation
  have denominatorOne := matrixAction_identity (fractionalVector tau) 0
  rw [← matrixEq] at denominatorOne
  change NamedEquivalent
    (fractionalDenominator matrix tau).name
    one.name at denominatorOne
  have numeratorTau := matrixAction_identity (fractionalVector tau) 1
  rw [← matrixEq] at numeratorTau
  change NamedEquivalent
    (fractionalNumerator matrix tau).name
    tau.name at numeratorTau
  have onePrepared : NamedEquivalent one.name preparation.prepared.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm denominatorOne)
      preparation.equivalent
  have scaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul one output).name tau.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        one preparation.prepared output output onePrepared
        (CCL.OperationalEquivalence.NamedEquivalent.refl output.name))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [output,
            CCL.ProgressiveCoherence.CoherentNamed.mul] using
          (prepared_denominator_mul_fractionalLinear
            matrix tau preparation))
        numeratorTau)
  change NamedEquivalent output.name tau.name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentMul_one_left output)) scaled

/-- A prepared identity-matrix fractional output is operationally `tau`. -/
def fractionalLinear_identity (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator RFAP.ConstructiveFiniteMatrix.identity tau)) :
    NamedEquivalent
      (fractionalLinear RFAP.ConstructiveFiniteMatrix.identity tau
        preparation).name tau.name :=
  fractionalLinear_of_matrix_eq_identity
    RFAP.ConstructiveFiniteMatrix.identity tau preparation rfl

/-- A certified left inverse undoes the corresponding productive inner action
when all three precisely indexed denominators have been prepared. -/
def fractionalLinear_inverse_of_mul_eq_identity
    (left right : IntegralMatrix) (tau : CoherentNamed)
    (preparation : CompositionPreparation left right tau)
    (inverse : RFAP.ConstructiveFiniteMatrix.mul left right =
      RFAP.ConstructiveFiniteMatrix.identity) :
    NamedEquivalent preparation.nestedOutput.name tau.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (fractionalLinear_mul left right tau preparation))
    (fractionalLinear_of_matrix_eq_identity
      (RFAP.ConstructiveFiniteMatrix.mul left right) tau
      preparation.combined inverse)

/-- If `left * right` is the identity, the corresponding homogeneous nested
action returns `(1,tau)` without any division premise. -/
def fractionalRows_inverse_of_mul_eq_identity
    (left right : IntegralMatrix) (tau : CoherentNamed)
    (inverse : RFAP.ConstructiveFiniteMatrix.mul left right =
      RFAP.ConstructiveFiniteMatrix.identity) :
    VectorEquivalent
      (matrixAction left
        (matrixAction right (fractionalVector tau)))
      (fractionalVector tau) :=
  VectorEquivalent.trans
    (VectorEquivalent.symm
      (matrixAction_mul left right (fractionalVector tau)))
    (by simpa only [inverse] using
      (matrixAction_identity (fractionalVector tau)))

/-- Productive infinity transport undoes the combined zero-then-one action. -/
def standard_infinity_after_combined (tau : CoherentNamed)
    (preparation : CompositionPreparation
      CCL.Riemann.LegendreMonodromy.infinityMatrix
      (RFAP.ConstructiveFiniteMatrix.mul
        CCL.Riemann.LegendreMonodromy.oneMatrix
        CCL.Riemann.LegendreMonodromy.zeroMatrix) tau) :
    NamedEquivalent preparation.nestedOutput.name tau.name :=
  fractionalLinear_inverse_of_mul_eq_identity
    CCL.Riemann.LegendreMonodromy.infinityMatrix
    (RFAP.ConstructiveFiniteMatrix.mul
      CCL.Riemann.LegendreMonodromy.oneMatrix
      CCL.Riemann.LegendreMonodromy.zeroMatrix)
    tau preparation
    CCL.Riemann.LegendreMonodromy.explicit_loop_product_left

/-- Productive combined zero-then-one transport also undoes infinity
transport, using the independently certified reverse multiplication order. -/
def standard_combined_after_infinity (tau : CoherentNamed)
    (preparation : CompositionPreparation
      (RFAP.ConstructiveFiniteMatrix.mul
        CCL.Riemann.LegendreMonodromy.oneMatrix
        CCL.Riemann.LegendreMonodromy.zeroMatrix)
      CCL.Riemann.LegendreMonodromy.infinityMatrix tau) :
    NamedEquivalent preparation.nestedOutput.name tau.name :=
  fractionalLinear_inverse_of_mul_eq_identity
    (RFAP.ConstructiveFiniteMatrix.mul
      CCL.Riemann.LegendreMonodromy.oneMatrix
      CCL.Riemann.LegendreMonodromy.zeroMatrix)
    CCL.Riemann.LegendreMonodromy.infinityMatrix tau preparation
    CCL.Riemann.LegendreMonodromy.explicit_loop_product_right

end CCL.Riemann.LegendreFractionalAction

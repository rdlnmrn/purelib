import CCL.Riemann.PreparedStokes

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace CCL.Riemann.PeriodLinearity

open CCL.Riemann.LiftedPaths

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-! ## Orientation reversal -/

/-- The exact finite data needed to reverse every displayed quadrature model
of one period.  The allowance is checked against the original program's
explicit Cauchy scale. -/
structure ReversalData {sheets : Nat} {cycle : LiftedCycleRefinement sheets}
    (program : PeriodProgram cycle) where
  reversal : forall index,
    CCL.ProgressiveGaussianIntegration.PathModel.Reversal
      (program.integral.model index)
  aggregate_le : forall index,
    ((program.integral.model index).reverse (reversal index)).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius program.integral.errorScale index

namespace ReversalData

def models {sheets : Nat} {cycle : LiftedCycleRefinement sheets}
    {program : PeriodProgram cycle} (data : ReversalData program) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram.ReversalModels
      program.integral :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.ReversalModels.ofPathReversals
    program.integral
    data.reversal data.aggregate_le

/-- The reversed finite period program follows the literally reversed lifted
cycle and retains the same productive refinement machinery. -/
def program {sheets : Nat} {cycle : LiftedCycleRefinement sheets}
    {source : PeriodProgram cycle} (data : ReversalData source) :
    PeriodProgram cycle.reverse :=
  source.reverse data.reversal data.aggregate_le

/-- Reversal negates the period at the operational finite-request layer. -/
def output_equivalent_neg {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} {source : PeriodProgram cycle}
    (data : ReversalData source) :
    NamedEquivalent data.program.output.name
      (CCL.ProgressiveCoherence.CoherentNamed.neg source.output).name := by
  let pair := CCL.Riemann.FiniteBilinear.BoundaryPair.ofProgramReversal
    source.integral data.models
  simpa only [program, PeriodProgram.reverse, models, pair,
    PeriodProgram.output,
    CCL.Riemann.FiniteBilinear.BoundaryPair.ofProgramReversal] using
    pair.reverse_eq_neg

end ReversalData

/-! ## Concatenation -/

/-- Two persistent cycles whose displayed representatives use the same
lifted basepoint at every finite refinement. -/
structure CycleJoin {sheets : Nat}
    (first second : LiftedCycleRefinement sheets) where
  basepoint_eq : forall index,
    (first.liftedPath index).basepoint = (second.liftedPath index).basepoint

namespace CycleJoin

private def appendClosed {sheets : Nat}
    (first second : ClosedLiftedPath sheets)
    (basepoint_eq : first.basepoint = second.basepoint) :
    ClosedLiftedPath sheets := by
  cases first with
  | mk firstBase firstPath =>
      cases second with
      | mk secondBase secondPath =>
          dsimp only at basepoint_eq
          subst secondBase
          exact
            { basepoint := firstBase
              path := firstPath.append secondPath }

private theorem appendFollowed {sheets : Nat}
    (first second : ClosedLiftedPath sheets)
    (basepoint_eq : first.basepoint = second.basepoint)
    {firstModels secondModels : List
      CCL.ProgressiveGaussianIntegration.CellModel}
    (firstFollows : LiftedPath.FollowedBy firstModels first.path)
    (secondFollows : LiftedPath.FollowedBy secondModels second.path) :
    LiftedPath.FollowedBy (firstModels ++ secondModels)
      (appendClosed first second basepoint_eq).path := by
  cases first with
  | mk firstBase firstPath =>
      cases second with
      | mk secondBase secondPath =>
          dsimp only at basepoint_eq
          subst secondBase
          exact LiftedPath.followedBy_append firstFollows secondFollows

/-- Concatenate the two finite closed representatives pointwise. -/
def cycle {sheets : Nat} {first second : LiftedCycleRefinement sheets}
    (join : CycleJoin first second) : LiftedCycleRefinement sheets where
  liftedPath := fun index =>
    appendClosed (first.liftedPath index) (second.liftedPath index)
      (join.basepoint_eq index)

end CycleJoin

/-- Geometric and allowance data for concatenating two actual period
programs. -/
structure ConcatenationData {sheets : Nat}
    {firstCycle secondCycle : LiftedCycleRefinement sheets}
    (first : PeriodProgram firstCycle) (second : PeriodProgram secondCycle)
    where
  join : CycleJoin firstCycle secondCycle
  allowance :
    CCL.ProgressiveGaussianIntegration.RefinementProgram.ConcatenationAllowance
    first.integral second.integral

namespace ConcatenationData

/-- Concatenation follows the concatenated lifted cycle cell by cell. -/
def program {sheets : Nat}
    {firstCycle secondCycle : LiftedCycleRefinement sheets}
    {first : PeriodProgram firstCycle} {second : PeriodProgram secondCycle}
    (data : ConcatenationData first second) : PeriodProgram data.join.cycle := by
  refine
    { integral :=
        CCL.ProgressiveGaussianIntegration.RefinementProgram.concat
          first.integral second.integral
        data.allowance
      follows := ?_ }
  intro index
  exact CycleJoin.appendFollowed
    (firstCycle.liftedPath index) (secondCycle.liftedPath index)
    (data.join.basepoint_eq index) (first.follows index) (second.follows index)

end ConcatenationData

/-- Actual CCL addition of two refinement-program outputs agrees with any
displayed finite sum model whose samples are their exact pointwise sums. -/
def addProgram_output_equivalent (left right : RefinementProgram)
    (models : CCL.ProgressiveGaussianIntegration.RefinementProgram.SumModels
      left right) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        left.output right.output).name
      (CCL.ProgressiveGaussianIntegration.RefinementProgram.add
        left right models).output.name := by
  simpa only [CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveGaussianIntegration.RefinementProgram.output,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.OperationalFieldLaws.addToNamed_equivalent_pointwise
      left.approximation right.approximation
      (CCL.ProgressiveGaussianIntegration.RefinementProgram.add
        left right models).approximation
      (fun index =>
        CCL.ProgressiveGaussianIntegration.RefinementProgram.add_integralSample
        left right models index)

/-- Concatenating two composable finite period programs adds their period
names operationally. -/
def ConcatenationData.output_equivalent_add {sheets : Nat}
    {firstCycle secondCycle : LiftedCycleRefinement sheets}
    {first : PeriodProgram firstCycle} {second : PeriodProgram secondCycle}
    (data : ConcatenationData first second) :
    NamedEquivalent data.program.output.name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        first.output second.output).name := by
  exact CCL.OperationalEquivalence.NamedEquivalent.symm (by
    simpa only [ConcatenationData.program, PeriodProgram.output,
      CCL.ProgressiveGaussianIntegration.RefinementProgram.concat] using
      addProgram_output_equivalent first.integral second.integral
        { model := fun index =>
            (first.integral.model index).concat
              (second.integral.model index)
          integral_eq := fun index =>
            CCL.ProgressiveGaussianIntegration.PathModel.integralSample_concat
              _ _
          aggregate_le := data.allowance.aggregate_le })

/-! ## Explicit integral combinations -/

/-- Repeated operational addition by an explicitly supplied natural
multiplicity. -/
def natMultiple : Nat -> CoherentNamed -> CoherentNamed
  | 0, _ => CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | count + 1, value => CCL.ProgressiveCoherence.CoherentNamed.add value
      (natMultiple count value)

/-- Integer multiplication represented constructively by a finite number of
additions and, for a negative coefficient, one stateful negation. -/
def intMultiple : Int -> CoherentNamed -> CoherentNamed
  | .ofNat count, value => natMultiple count value
  | .negSucc count, value =>
      CCL.ProgressiveCoherence.CoherentNamed.neg
        (natMultiple (count + 1) value)

/-- Recursive addition of a literal finite list of productive names. -/
def sumList : List CoherentNamed -> CoherentNamed
  | [] => CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | value :: remaining =>
      CCL.ProgressiveCoherence.CoherentNamed.add value (sumList remaining)

/-- Finite list concatenation is operational addition of the two finite
sums. -/
def sumList_append (first second : List CoherentNamed) :
    NamedEquivalent (sumList (first ++ second)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumList first) (sumList second)).name := by
  induction first with
  | nil =>
      exact CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.OperationalFieldLaws.coherentAdd_zero_left (sumList second))
  | cons value remaining inductionHypothesis =>
      apply CCL.OperationalEquivalence.NamedEquivalent.trans
      · exact CCL.TranscendentalCoherence.coherentAdd_respects
          value value (sumList (remaining ++ second))
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (sumList remaining) (sumList second))
          (CCL.OperationalEquivalence.NamedEquivalent.refl value.name)
          inductionHypothesis
      · exact CCL.OperationalEquivalence.NamedEquivalent.symm
          (CCL.OperationalFieldLaws.coherentAdd_assoc
            value (sumList remaining) (sumList second))

/-- One basis-cycle period with its displayed integral coefficient. -/
structure IntegralPeriodTerm (sheets : Nat) where
  cycle : LiftedCycleRefinement sheets
  program : PeriodProgram cycle
  coefficient : Int

namespace IntegralPeriodTerm

/-- The corresponding integer multiple of the actual productive period
name. -/
def value {sheets : Nat} (term : IntegralPeriodTerm sheets) : CoherentNamed :=
  intMultiple term.coefficient term.program.output

/-- Coefficient `+1` retains the underlying period operationally. -/
def value_one {sheets : Nat} (cycle : LiftedCycleRefinement sheets)
    (program : PeriodProgram cycle) :
    NamedEquivalent
      (IntegralPeriodTerm.value
        { cycle := cycle, program := program, coefficient := 1 }).name
      program.output.name :=
  CCL.OperationalFieldLaws.coherentAdd_zero_right program.output

/-- Coefficient `-1` is the actual stateful negation of the period. -/
def value_negative_one {sheets : Nat}
    (cycle : LiftedCycleRefinement sheets) (program : PeriodProgram cycle) :
    NamedEquivalent
      (IntegralPeriodTerm.value
        { cycle := cycle, program := program, coefficient := -1 }).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg program.output).name :=
  CCL.Riemann.FiniteBilinear.coherentNeg_respects
    (natMultiple 1 program.output) program.output
    (CCL.OperationalFieldLaws.coherentAdd_zero_right program.output)

end IntegralPeriodTerm

/-- Evaluate an explicit integral combination of finite cycles as the same
finite combination of their period names. -/
def integralCombination {sheets : Nat}
    (terms : List (IntegralPeriodTerm sheets)) : CoherentNamed :=
  sumList (terms.map IntegralPeriodTerm.value)

/-- Appending two displayed integral combinations adds the corresponding
productive period names. -/
def integralCombination_append {sheets : Nat}
    (first second : List (IntegralPeriodTerm sheets)) :
    NamedEquivalent (integralCombination (first ++ second)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (integralCombination first) (integralCombination second)).name := by
  simpa only [integralCombination, List.map_append] using
    sumList_append (first.map IntegralPeriodTerm.value)
      (second.map IntegralPeriodTerm.value)

/-! ## Finite zero laws used by Gauss--Manin reduction -/

/-- Every displayed cellular boundary, containing both orientations of every
lifted edge, contributes operational zero. -/
def cellularBoundary_operational_zero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (pairs : CCL.Riemann.PreparedStokes.CellularEdgePairs curve) :
    NamedEquivalent pairs.boundarySum.name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  pairs.boundarySum_zero

/-- An exact differential around a finitely displayed closed primitive path
contributes operational zero by endpoint telescoping. -/
def exactDifferential_closed_operational_zero
    (boundary : CCL.Riemann.FiniteBilinear.ClosedPrimitiveBoundary) :
    NamedEquivalent boundary.integralSum.name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  boundary.integralSum_zero

end CCL.Riemann.PeriodLinearity

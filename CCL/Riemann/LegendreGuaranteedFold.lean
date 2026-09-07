import CCL.Riemann.LegendrePreparationClosure
import CCL.Riemann.LegendreAutomaticFold

/-!
# Guaranteed preparation of the entire dual word

The original positive enclosure constructs a provider. Fractional composition
preserves that provider, so a finite recursion constructs every local and
combined preparation at the exact intermediate output where it is needed.
-/

namespace CCL.Riemann.LegendreGuaranteedFold

open CCL.Riemann.LegendreFractionalWords
open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendrePreparationClosure

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

def Inverses : List IntegralMatrix → Type
  | [] => Unit
  | matrix :: remaining => RightInverse matrix × Inverses remaining

def appendInverses (first second : List IntegralMatrix)
    (left : Inverses first) (right : Inverses second) : Inverses (first ++ second) :=
  match first with
  | [] => right
  | _ :: remaining => ⟨left.1, appendInverses remaining second left.2 right⟩

def productInverse : (matrices : List IntegralMatrix) →
    Inverses matrices → RightInverse (matrixProduct matrices)
  | [], _ => identityInverse
  | _ :: remaining, ⟨head, tail⟩ => mulInverse (productInverse remaining tail) head

def dualGeneratorInverse (generator : CCL.Knot.FiniteBraid.Generator 3) :
    RightInverse (CCL.Riemann.LegendrePicardLefschetz.transpose
      (CCL.Riemann.LegendrePicardLefschetz.generatorMatrix generator)) where
  inverse := CCL.Riemann.LegendrePicardLefschetz.transpose
    (CCL.Riemann.LegendrePicardLefschetz.generatorMatrix generator.reverse)
  identity := by
    rw [← CCL.Riemann.LegendrePicardLefschetz.transpose_mul,
      (CCL.Riemann.LegendrePicardLefschetz.generator_reverse_matrix generator).1,
      CCL.Riemann.LegendrePicardLefschetz.transpose_identity]

def periodInverses : (word : CCL.Knot.FiniteBraid.Word 3) →
    Inverses (periodBraidMatrices word)
  | [] => ()
  | generator :: remaining =>
      appendInverses (periodBraidMatrices remaining)
        [CCL.Riemann.LegendrePicardLefschetz.transpose
          (CCL.Riemann.LegendrePicardLefschetz.generatorMatrix generator)]
        (periodInverses remaining) ⟨dualGeneratorInverse generator, ()⟩

/-- Retain both the complete preparation and the provider for the actual
final output, allowing further words to continue without new positivity. -/
def Prepared (tau : CoherentNamed) (matrices : List IntegralMatrix) :=
  Sigma fun preparations : FoldPreparations tau matrices =>
    Provider (foldAction tau matrices preparations)

/-- A structurally recursive, search-free construction of the complete
stepwise preparation. All local and combined denominators are generated. -/
def prepare (tau : CoherentNamed) (provider : Provider tau) :
    (matrices : List IntegralMatrix) → Inverses matrices → Prepared tau matrices
  | [], _ => ⟨provider RFAP.ConstructiveFiniteMatrix.identity identityInverse, provider⟩
  | matrix :: remaining, inverses =>
      let head := provider matrix inverses.1
      let tail := prepare (fractionalLinear matrix tau head)
        (after provider matrix inverses.1 head) remaining inverses.2
      let combined := provider (matrixProduct (matrix :: remaining))
        (productInverse (matrix :: remaining) inverses)
      ⟨⟨head, tail.1, combined⟩, tail.2⟩

/-- Every finite dual word is fully prepared from one initial positive
enclosure. The caller supplies no intermediate denominator certificates. -/
def prepareWord {tau : CoherentNamed}
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau)
    (word : CCL.Knot.FiniteBraid.Word 3) : Prepared tau (periodBraidMatrices word) :=
  prepare tau (ofPositiveEnclosure positive) (periodBraidMatrices word) (periodInverses word)

/-- The default single-matrix evaluator and the guaranteed stepwise evaluator
produce operationally equivalent outputs without supplied preparations. -/
def equivalent_single {tau : CoherentNamed}
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau)
    (word : CCL.Knot.FiniteBraid.Word 3) :
    NamedEquivalent
      (CCL.Riemann.LegendreAutomaticTransport.guaranteed positive word).output.name
      (foldAction tau (periodBraidMatrices word) (prepareWord positive word).1).name :=
  (CCL.Riemann.LegendreAutomaticTransport.guaranteed positive word).equivalent_fold
    (prepareWord positive word).1

/-- Equal finite period matrices give equivalent automatically prepared
stepwise outputs, independently of the initial positivity witnesses. -/
def equivalent_words {tau : CoherentNamed}
    (firstPositive secondPositive :
      CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau)
    (firstWord secondWord : CCL.Knot.FiniteBraid.Word 3)
    (equal : CCL.Riemann.LegendrePicardLefschetz.periodMatrix firstWord =
      CCL.Riemann.LegendrePicardLefschetz.periodMatrix secondWord) :
    NamedEquivalent
      (foldAction tau (periodBraidMatrices firstWord) (prepareWord firstPositive firstWord).1).name
      (foldAction tau (periodBraidMatrices secondWord) (prepareWord secondPositive secondWord).1).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (equivalent_single firstPositive firstWord))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      ((CCL.Riemann.LegendreAutomaticTransport.guaranteed firstPositive firstWord).respects_matrix
        (CCL.Riemann.LegendreAutomaticTransport.guaranteed secondPositive secondWord) equal)
      (equivalent_single secondPositive secondWord))

/-- The fully prepared stepwise computations respect finite Artin equivalence
and may use independently discovered initial positive enclosures. -/
def equivalent_braids {tau : CoherentNamed}
    (firstPositive secondPositive :
      CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau)
    (firstWord secondWord : CCL.Knot.FiniteBraid.Word 3)
    (relation : CCL.Knot.ArtinRelations.Equivalent firstWord secondWord) :
    NamedEquivalent
      (foldAction tau (periodBraidMatrices firstWord) (prepareWord firstPositive firstWord).1).name
      (foldAction tau (periodBraidMatrices secondWord) (prepareWord secondPositive secondWord).1).name :=
  equivalent_words firstPositive secondPositive firstWord secondWord
    (CCL.Riemann.LegendrePicardLefschetz.equivalent_periodMatrix_eq relation)

/-- Prepare both executions and the finite composition comparison, reusing
the provider at the actual forward output for the reverse execution. -/
def prepareReversal {tau : CoherentNamed}
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau)
    (word : CCL.Knot.FiniteBraid.Word 3) :
    FoldReversalPreparations (periodBraidMatrices word)
      (periodBraidMatrices word.inverse) tau :=
  let provider := ofPositiveEnclosure positive
  let forward := prepareWord positive word
  let first := matrixProduct (periodBraidMatrices word)
  let second := matrixProduct (periodBraidMatrices word.inverse)
  let firstInverse := productInverse (periodBraidMatrices word) (periodInverses word)
  let secondInverse := productInverse (periodBraidMatrices word.inverse) (periodInverses word.inverse)
  let inner := FoldPreparations.combined (periodBraidMatrices word) forward.1
  { forward := forward.1
    reverse := (prepare (foldAction tau (periodBraidMatrices word) forward.1)
      forward.2 (periodBraidMatrices word.inverse) (periodInverses word.inverse)).1
    composition :=
      { inner := inner
        outer := after provider first firstInverse inner second secondInverse
        combined := provider (RFAP.ConstructiveFiniteMatrix.mul second first)
          (mulInverse secondInverse firstInverse) } }

/-- A fully automatically prepared word followed by its inverse returns the
original ratio. The same initial positivity enclosure prepares both legs. -/
def reversal {tau : CoherentNamed}
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau)
    (word : CCL.Knot.FiniteBraid.Word 3) :
    NamedEquivalent
      (foldAction
        (foldAction tau (periodBraidMatrices word) (prepareReversal positive word).forward)
        (periodBraidMatrices word.inverse) (prepareReversal positive word).reverse).name
      tau.name :=
  periodBraidWord_foldReversal word tau (prepareReversal positive word)

/-- The fully automatic stepwise output satisfies the arbitrary closed-path
dual period theorem. -/
def transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendrePeriodMonodromy.NormalizedData frame)
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure data.ratio)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul (data.periods path 0)
        (foldAction data.ratio (periodBraidMatrices path.word)
          (prepareWord positive path.word).1)).name
      (data.periods path 1).name :=
  data.periodWord_productive_transport path (prepareWord positive path.word).1

end CCL.Riemann.LegendreGuaranteedFold

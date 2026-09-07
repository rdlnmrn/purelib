import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import RFAP.Isolation.GeneralBoxFTA
import RFAP.Rational.OuterWinding
import RFAP.Rational.SignedMultiplicity

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace RFAP.RationalSites

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev PositiveEntry := RFAP.Multiplicity.PositiveEntry
abbrev PositiveContext :=
  RFAP.MultiplicityWinding.PositiveContext
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate
abbrev ReducedPair := RFAP.RationalReduction.ReducedPair

open RFAP.ComputablePolynomial.DensePolynomial

/-- Positive-degree side of a reduced rational function, together with its
complete finite multiplicity preprocessing and coprimality to the opposite
reduced cofactor. -/
structure PositiveSideInput
    (source opposite : GaussianPolynomial) where
  sourceNormalized : source.normalize = source
  preprocessing : RFAP.Factorization.PositivePreprocessing source
  oppositeNonzero : opposite.isZero = false
  sourceOppositeCoprime : CoprimeCertificate source opposite

namespace PositiveSideInput

abbrev entries
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) : List PositiveEntry :=
  input.preprocessing.decomposition.positiveMultiplicityEntries

def contexts
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) :
    List (PositiveContext input.entries) :=
  RFAP.MultiplicityWinding.positiveContexts input.entries

theorem contexts_length
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) :
    input.contexts.length = input.entries.length :=
  RFAP.MultiplicityWinding.positiveContexts_length input.entries

theorem multiplicityDegree
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) :
    RFAP.Multiplicity.positiveDegree input.entries =
      source.natDegree := by
  have degree := input.preprocessing.decomposition.positiveMultiplicityDegree
  simpa only [natDegree_normalize] using degree

theorem entries_pairwise
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) :
    input.entries.Pairwise fun left right =>
      RFAP.Multiplicity.CoprimeRelation
        left.part right.part :=
  input.preprocessing.decomposition.positiveMultiplicityEntries_pairwise

theorem focusFactorization
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) :
    RFAP.Factorization.ProductIdentity source
      context.focus.part.polynomial
      (context.singleCofactor input.preprocessing.decomposition) := by
  have normalized := context.focusFactorization
    input.preprocessing.decomposition rfl
  simpa only [input.sourceNormalized] using normalized

/-- Every basis factor inherits a finite Bézout certificate against the
entire opposite reduced cofactor. -/
def focusOppositeCoprime
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) :
    CoprimeCertificate context.focus.part.polynomial opposite :=
  RFAP.SquarefreeFactors.coprimeLeftFactor
    input.sourceOppositeCoprime context.focus.part.nonzero
    (input.focusFactorization context)

/-- A factor on this side and a factor on the opposite side inherit a
displayed finite Bézout certificate from reduced-cofactor coprimality. -/
def focusFocusCoprime
    {source opposite : GaussianPolynomial}
    (left : PositiveSideInput source opposite)
    (leftContext : PositiveContext left.entries)
    (right : PositiveSideInput opposite source)
    (rightContext : PositiveContext right.entries) :
    CoprimeCertificate leftContext.focus.part.polynomial
      rightContext.focus.part.polynomial := by
  let oppositeLeft :=
    RFAP.SquarefreeFactors.CoprimeCertificate.symm
      (left.focusOppositeCoprime leftContext)
  let rightLeft := RFAP.SquarefreeFactors.coprimeLeftFactor
    oppositeLeft rightContext.focus.part.nonzero
      (right.focusFactorization rightContext)
  exact RFAP.SquarefreeFactors.CoprimeCertificate.symm rightLeft

/-- Same-side pairwise relations are converted back to the complete finite
Bézout data consumed by separation. -/
def focusCoprimeOfRelation
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (left right : PositiveContext input.entries)
    (relation : RFAP.Multiplicity.CoprimeRelation
      left.focus.part right.focus.part) :
    CoprimeCertificate left.focus.part.polynomial
      right.focus.part.polynomial :=
  RFAP.Multiplicity.coprimeCertificateOfRelation
    left.focus.part right.focus.part relation

theorem contexts_pairwise
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) :
    input.contexts.Pairwise fun left right =>
      RFAP.Multiplicity.CoprimeRelation
        left.focus.part right.focus.part :=
  RFAP.MultiplicityWinding.positiveContexts_pairwise
    input.entries_pairwise

/-- Finite lookup of the complete Bézout certificate between any two
distinct focused positions on the same side. -/
def contextCoprime
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (left right : Fin input.contexts.length) (different : left ≠ right) :
    CoprimeCertificate
      (input.contexts.get left).focus.part.polynomial
      (input.contexts.get right).focus.part.polynomial := by
  by_cases ordered : left.val < right.val
  · exact input.focusCoprimeOfRelation _ _
      (QuotientFreeList.pairwise_getElem input.contexts_pairwise
        left.val right.val left.isLt right.isLt ordered)
  · have valuesDifferent : left.val ≠ right.val := by
      intro equal
      exact different (Fin.ext equal)
    have reversed : right.val < left.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered) (Ne.symm valuesDifferent)
    exact input.focusCoprimeOfRelation _ _
      (RFAP.Multiplicity.coprimeRelation_symm
        (QuotientFreeList.pairwise_getElem input.contexts_pairwise
          right.val left.val right.isLt left.isLt reversed))

/-- Exact or shrinking-box observation supplied by one squarefree basis
factor.  The exact constructor is used only when exact evaluation proves a
displayed Gaussian-rational zero. -/
inductive FactorObservation
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) : Type where
  | exact
      (root : RFAP.BoxFTA.ExactRoot
        context.focus.part.polynomial)
      (degree : context.focus.part.polynomial.natDegree = 1)
      (oppositeAtRoot : opposite.eval root.point ≠ 0)
  | higher
      (boxes : RFAP.BoxFTA.Result
        context.focus.part.polynomial)
      (degree : 2 ≤ context.focus.part.polynomial.natDegree)

def observe
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries) :
    FactorObservation input context := by
  let positive := RFAP.BoxFTA.provePositive
    { squarefree := context.focus.part.squarefree
      degreePositive := context.focus.degreePositive }
  cases positive with
  | linear root degree =>
      have alternative := (input.focusOppositeCoprime context).eval_ne_zero
        root.point
      have oppositeAtRoot : opposite.eval root.point ≠ 0 := by
        rcases alternative with focusNonzero | oppositeNonzero
        · exact (focusNonzero root.root).elim
        · exact oppositeNonzero
      exact .exact root degree oppositeAtRoot
  | higher boxes degree => exact .higher boxes degree

theorem exactSourceRoot
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries)
    (root : RFAP.BoxFTA.ExactRoot
      context.focus.part.polynomial) :
    source.eval root.point = 0 := by
  rw [RFAP.SquarefreeFactors.eval_factorization
    (input.focusFactorization context) root.point, root.root, zero_mul]

/-- Build the fully protected signed-multiplicity track input for any track
of a higher-degree basis factor. -/
def higherTrackInput
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries)
    (boxes : RFAP.BoxFTA.Result
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree) :
    RFAP.SignedMultiplicity.TrackSiteInput
      source.normalize opposite :=
  let track := boxes.isolation.trackAt index
  { decomposition := input.preprocessing.decomposition
    pairwise := input.entries_pairwise
    context := context
    oppositeNonzero := input.oppositeNonzero
    focusOppositeCoprime := input.focusOppositeCoprime context
    track := track
    current := track.initial }

/-- Pairwise finite separation for all four combinations of exact rational
sites and higher shrinking-track sites. -/
def ObservationsSeparated
    {leftSource leftOpposite rightSource rightOpposite : GaussianPolynomial}
    {leftInput : PositiveSideInput leftSource leftOpposite}
    {rightInput : PositiveSideInput rightSource rightOpposite}
    {leftContext : PositiveContext leftInput.entries}
    {rightContext : PositiveContext rightInput.entries}
    (left : FactorObservation leftInput leftContext)
    (right : FactorObservation rightInput rightContext) : Type :=
  match left, right with
  | .exact leftRoot _ _, .exact rightRoot _ _ =>
      PLift (leftRoot.point ≠ rightRoot.point)
  | .exact leftRoot _ _, .higher rightBoxes _ =>
      ∀ index : Fin rightContext.focus.part.polynomial.natDegree,
        RFAP.SignedMultiplicity.ExactTrackSeparation
          (exactPolynomial := leftContext.focus.part.polynomial)
          (rightBoxes.isolation.trackAt index)
          (rightBoxes.isolation.trackAt index).initial leftRoot.point
  | .higher leftBoxes _, .exact rightRoot _ _ =>
      ∀ index : Fin leftContext.focus.part.polynomial.natDegree,
        RFAP.SignedMultiplicity.ExactTrackSeparation
          (exactPolynomial := rightContext.focus.part.polynomial)
          (leftBoxes.isolation.trackAt index)
          (leftBoxes.isolation.trackAt index).initial rightRoot.point
  | .higher leftBoxes _, .higher rightBoxes _ =>
      ∀ (leftIndex : Fin leftContext.focus.part.polynomial.natDegree)
        (rightIndex : Fin rightContext.focus.part.polynomial.natDegree),
        RFAP.SignedMultiplicity.TrackPairSeparation
          (leftBoxes.isolation.trackAt leftIndex)
          (leftBoxes.isolation.trackAt leftIndex).initial
          (rightBoxes.isolation.trackAt rightIndex)
          (rightBoxes.isolation.trackAt rightIndex).initial

def separateObservations
    {leftSource leftOpposite rightSource rightOpposite : GaussianPolynomial}
    {leftInput : PositiveSideInput leftSource leftOpposite}
    {rightInput : PositiveSideInput rightSource rightOpposite}
    {leftContext : PositiveContext leftInput.entries}
    {rightContext : PositiveContext rightInput.entries}
    (left : FactorObservation leftInput leftContext)
    (right : FactorObservation rightInput rightContext)
    (coprime : CoprimeCertificate leftContext.focus.part.polynomial
      rightContext.focus.part.polynomial) :
    ObservationsSeparated left right := by
  cases left with
  | exact leftRoot leftDegree _ =>
      cases right with
      | exact rightRoot rightDegree _ =>
          exact ⟨RFAP.SignedMultiplicity.exactPoints_ne coprime
            leftRoot.root rightRoot.root⟩
      | higher rightBoxes rightDegree =>
          intro index
          exact RFAP.SignedMultiplicity.separateExactFromTrack
            rightContext.focus.degreePositive
            (RFAP.SquarefreeFactors.CoprimeCertificate.symm coprime)
            (rightBoxes.isolation.trackAt index)
            (rightBoxes.isolation.trackAt index).initial leftRoot.point
            leftRoot.root
  | higher leftBoxes leftDegree =>
      cases right with
      | exact rightRoot rightDegree _ =>
          intro index
          exact RFAP.SignedMultiplicity.separateExactFromTrack
            leftContext.focus.degreePositive coprime
            (leftBoxes.isolation.trackAt index)
            (leftBoxes.isolation.trackAt index).initial rightRoot.point
            rightRoot.root
      | higher rightBoxes rightDegree =>
          intro leftIndex rightIndex
          exact RFAP.SignedMultiplicity.separateTracks
            leftContext.focus.degreePositive rightContext.focus.degreePositive
            coprime (leftBoxes.isolation.trackAt leftIndex)
            (leftBoxes.isolation.trackAt leftIndex).initial
            (rightBoxes.isolation.trackAt rightIndex)
            (rightBoxes.isolation.trackAt rightIndex).initial

/-- Separation already internal to one squarefree factor: an exact branch
has one displayed rational site, while a higher branch carries a pairwise
separated degree-indexed family. -/
def ObservationInternallySeparated
    {source opposite : GaussianPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation : FactorObservation input context) : Type :=
  match observation with
  | .exact _ _ _ => PUnit
  | .higher boxes _ =>
      PLift (∀ left right : Fin context.focus.part.polynomial.natDegree,
        left ≠ right →
          (boxes.isolation.trackAt left).initial.box.Separated
            (boxes.isolation.trackAt right).initial.box)

def observationInternallySeparated
    {source opposite : GaussianPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation : FactorObservation input context) :
    ObservationInternallySeparated observation := by
  cases observation with
  | exact => exact PUnit.unit
  | higher boxes _ => exact ⟨boxes.isolation.trackAt_pairwiseSeparated⟩

/-- Atomic completeness for one factor.  The linear branch retains its exact
rational evaluation certificate.  For a higher branch, every alternative
winding-one track supported by the isolation partition is constructively
refined into a deterministically selected output owner. -/
def ObservationAtomicMaximality
    {source opposite : GaussianPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation : FactorObservation input context) : Type :=
  match observation with
  | .exact root _ _ =>
      PLift (context.focus.part.polynomial.eval root.point = 0)
  | .higher boxes _ =>
      ∀ (track : RFAP.ShrinkingTrack.WindingOneTrack
          context.focus.part.polynomial
          (RFAP.GlobalWinding.largeSquareBox
            context.focus.part.polynomial)),
        track.initial.box.Refines boxes.isolation.support →
          RFAP.Maximality.OwnerSelection boxes.isolation track

def observationAtomicMaximality
    {source opposite : GaussianPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation : FactorObservation input context) :
    ObservationAtomicMaximality observation := by
  cases observation with
  | exact root => exact ⟨root.root⟩
  | higher boxes => exact boxes.ownership

theorem higherRepresentedSource_eval
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries)
    (boxes : RFAP.BoxFTA.Result
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree)
    (point : Gaussian) :
    ((input.higherTrackInput context boxes index).representedSource).eval point =
      source.eval point := by
  let site := input.higherTrackInput context boxes index
  have factorization := RFAP.SquarefreeFactors.eval_factorization
    site.representedFactorization point
  change source.normalize.eval point = _ at factorization
  rw [eval_normalize] at factorization
  change (RFAP.Multiplicity.polynomialPower
      context.focus.part.polynomial context.focus.multiplicity *
    context.otherPolynomial input.preprocessing.decomposition).eval point =
      source.eval point
  rw [eval_mul]
  exact factorization.symm

theorem higherZeroBoxWinding
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries)
    (boxes : RFAP.BoxFTA.Result
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree) :
    let site := input.higherTrackInput context boxes index
    RFAP.RationalWinding.rationalBoxWinding
        site.representedSource opposite site.state.box =
      context.focus.multiplicity :=
  (input.higherTrackInput context boxes index).representedBoxWinding

theorem higherPoleBoxWinding
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite)
    (context : PositiveContext input.entries)
    (boxes : RFAP.BoxFTA.Result
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree) :
    let site := input.higherTrackInput context boxes index
    RFAP.RationalWinding.rationalBoxWinding
        opposite site.representedSource site.state.box =
      -(context.focus.multiplicity : Int) :=
  (input.higherTrackInput context boxes index).representedPoleBoxWinding

/-- The complete finite family on one positive-degree cofactor.  Every
correctness datum needed by the public RFAP result is retained as a field:
finite context count, weighted degree, internal separation, separation
between distinct factors, and atomic ownership/maximality. -/
structure PositiveFamily
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) where
  observationAt : ∀ index : Fin input.contexts.length,
    FactorObservation input (input.contexts.get index)
  contextCount : input.contexts.length = input.entries.length
  weightedDegree :
    RFAP.Multiplicity.positiveDegree input.entries =
      source.natDegree
  internallySeparated : ∀ index : Fin input.contexts.length,
    ObservationInternallySeparated (observationAt index)
  atomicMaximality : ∀ index : Fin input.contexts.length,
    ObservationAtomicMaximality (observationAt index)
  pairwiseSeparated : ∀ (left right : Fin input.contexts.length),
    left ≠ right →
      ObservationsSeparated (observationAt left) (observationAt right)

def buildFamily
    {source opposite : GaussianPolynomial}
    (input : PositiveSideInput source opposite) : PositiveFamily input where
  observationAt := fun index => input.observe (input.contexts.get index)
  contextCount := input.contexts_length
  weightedDegree := input.multiplicityDegree
  internallySeparated := fun index =>
    observationInternallySeparated
      (input.observe (input.contexts.get index))
  atomicMaximality := fun index =>
    observationAtomicMaximality
      (input.observe (input.contexts.get index))
  pairwiseSeparated := fun left right different =>
    separateObservations
      (input.observe (input.contexts.get left))
      (input.observe (input.contexts.get right))
      (input.contextCoprime left right different)

end PositiveSideInput

/-- A nonzero reduced cofactor has either no finite sites because it is
constant, or the complete positive multiplicity basis above. -/
inductive SideResult (source opposite : GaussianPolynomial) : Type where
  | constant
      (sourceNonzero : source.isZero = false)
      (degreeZero : source.natDegree = 0)
      (oppositeNonzero : opposite.isZero = false)
  | positive (input : PositiveSideInput source opposite)
      (family : PositiveSideInput.PositiveFamily input)

def buildSide
    (source opposite : GaussianPolynomial)
    (sourceNormalized : source.normalize = source)
    (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : CoprimeCertificate source opposite) :
    SideResult source opposite := by
  match preprocessing : RFAP.Factorization.preprocess source with
  | .zero certificate =>
      rw [sourceNonzero] at certificate
      exact Bool.noConfusion certificate
  | .constant _ degreeZero =>
      exact .constant sourceNonzero degreeZero oppositeNonzero
  | .positive positive =>
      let input : PositiveSideInput source opposite :=
        { sourceNormalized := sourceNormalized
          preprocessing := positive
          oppositeNonzero := oppositeNonzero
          sourceOppositeCoprime := coprime }
      exact .positive input input.buildFamily

namespace SideResult

/-- Total signed-multiplicity mass on one side before choosing its sign. -/
def multiplicityDegree
    {source opposite : GaussianPolynomial} :
    SideResult source opposite → Nat
  | .constant _ _ _ => 0
  | .positive input _ =>
      RFAP.Multiplicity.positiveDegree input.entries

theorem multiplicityDegree_eq_natDegree
    {source opposite : GaussianPolynomial}
    (result : SideResult source opposite) :
    result.multiplicityDegree = source.natDegree := by
  cases result with
  | constant _ degreeZero _ => exact degreeZero.symm
  | positive _ family => exact family.weightedDegree

end SideResult

/-- Joint numerator/denominator separation.  Constant sides contribute no
sites; positive sides retain a finite separation witness for every pair of
factor groups across the displayed reduced Bézout identity. -/
def SidesSeparated
    {numerator denominator : GaussianPolynomial}
    (numeratorSites : SideResult numerator denominator)
    (denominatorSites : SideResult denominator numerator) : Type :=
  match numeratorSites, denominatorSites with
  | .positive numeratorInput numeratorFamily,
      .positive denominatorInput denominatorFamily =>
      ∀ (numeratorIndex : Fin numeratorInput.contexts.length)
        (denominatorIndex : Fin denominatorInput.contexts.length),
        PositiveSideInput.ObservationsSeparated
          (numeratorFamily.observationAt numeratorIndex)
          (denominatorFamily.observationAt denominatorIndex)
  | _, _ => PUnit

def separateSides
    {numerator denominator : GaussianPolynomial}
    (numeratorSites : SideResult numerator denominator)
    (denominatorSites : SideResult denominator numerator) :
    SidesSeparated numeratorSites denominatorSites := by
  cases numeratorSites with
  | constant => exact PUnit.unit
  | positive numeratorInput numeratorFamily =>
      cases denominatorSites with
      | constant => exact PUnit.unit
      | positive denominatorInput denominatorFamily =>
          intro numeratorIndex denominatorIndex
          exact PositiveSideInput.separateObservations
            (numeratorFamily.observationAt numeratorIndex)
            (denominatorFamily.observationAt denominatorIndex)
            (numeratorInput.focusFocusCoprime
              (numeratorInput.contexts.get numeratorIndex)
              denominatorInput
              (denominatorInput.contexts.get denominatorIndex))

/-- Complete nonzero-rational-function result after cancellation. -/
structure NonzeroResult
    (numerator denominator : GaussianPolynomial) where
  input : RFAP.RationalFunctionArgumentPrinciple.NonzeroReducedInput
    numerator denominator
  numeratorSites : SideResult input.reduction.numeratorReduced
    input.reduction.denominatorReduced
  denominatorSites : SideResult input.reduction.denominatorReduced
    input.reduction.numeratorReduced
  numeratorMultiplicityDegree :
    numeratorSites.multiplicityDegree =
      input.reduction.numeratorReduced.natDegree
  denominatorMultiplicityDegree :
    denominatorSites.multiplicityDegree =
      input.reduction.denominatorReduced.natDegree
  jointSeparation : SidesSeparated numeratorSites denominatorSites
  outerDegreeDifference :
    RFAP.RationalWinding.rationalBoxWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.outerBox =
      (input.reduction.numeratorReduced.natDegree : Int) -
        input.reduction.denominatorReduced.natDegree

namespace NonzeroResult

theorem outerWinding
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator) :
    RFAP.RationalWinding.rationalQuadrupledWinding
        result.input.reduction.numeratorReduced
        result.input.reduction.denominatorReduced result.input.outerBox =
      (4 : Int) * result.input.reduction.numeratorReduced.natDegree -
        (4 : Int) * result.input.reduction.denominatorReduced.natDegree :=
  result.input.outer_rationalWinding_eq_degreeDifference

theorem outerBoxWinding
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator) :
    RFAP.RationalWinding.rationalBoxWinding
        result.input.reduction.numeratorReduced
        result.input.reduction.denominatorReduced result.input.outerBox =
      (result.input.reduction.numeratorReduced.natDegree : Int) -
        result.input.reduction.denominatorReduced.natDegree :=
  result.outerDegreeDifference

end NonzeroResult

/-- Total RFAP result.  The identically-zero numerator is not assigned a
boundary winding; it is returned explicitly with the displayed denominator
nonzeroness certificate. -/
inductive Result (numerator denominator : GaussianPolynomial) : Type where
  | zeroNumerator
      (numeratorZero : numerator.isZero = true)
      (denominatorNonzero : denominator.isZero = false)
  | nonzero (result : NonzeroResult numerator denominator)

/-- Execute cancellation, preprocessing, and all finite degree branches. -/
def prove
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    Result numerator denominator := by
  if numeratorZero : numerator.isZero = true then
    exact .zeroNumerator numeratorZero denominatorNonzero
  else
    have numeratorNonzero : numerator.isZero = false := by
      simpa using numeratorZero
    let reduction := RFAP.RationalReduction.reduce
      numerator denominator denominatorNonzero
    let input : RFAP.RationalFunctionArgumentPrinciple.NonzeroReducedInput
        numerator denominator :=
      { reduction := reduction
        numeratorReducedNonzero :=
          reduction.numeratorReduced_nonzero numeratorNonzero }
    let numeratorSites := buildSide input.reduction.numeratorReduced
      input.reduction.denominatorReduced
      input.reduction.numeratorReduced_normalized
      input.numeratorReducedNonzero input.denominatorReducedNonzero
      input.reduction.coprime
    let symmetric :=
      RFAP.SquarefreeFactors.CoprimeCertificate.symm
        input.reduction.coprime
    let denominatorSites := buildSide input.reduction.denominatorReduced
      input.reduction.numeratorReduced
      input.reduction.denominatorReduced_normalized
      input.denominatorReducedNonzero input.numeratorReducedNonzero symmetric
    exact .nonzero
      { input := input
        numeratorSites := numeratorSites
        denominatorSites := denominatorSites
        numeratorMultiplicityDegree :=
          numeratorSites.multiplicityDegree_eq_natDegree
        denominatorMultiplicityDegree :=
          denominatorSites.multiplicityDegree_eq_natDegree
        jointSeparation := separateSides numeratorSites denominatorSites
        outerDegreeDifference :=
          input.outer_boxWinding_eq_degreeDifference }

end RFAP.RationalSites

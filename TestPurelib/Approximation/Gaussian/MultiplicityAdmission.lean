module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reality
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.Multiplicity.Site.Realization
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Build
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent
import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Tactic.OperationalEquivalence
import Purelib.Data.List.Map
import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Unit
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Rational.Bezout.GCD
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Hull
import Purelib.System.IO
public import scripts.checkpoint.RootSelection
import scripts.checkpoint.CoherentRootSamples
import Purelib.System.FilePath

/-! # Independent intrinsic multiplicity-site owners at the same positive quadratic root -/

namespace TestPurelib.Approximation.Gaussian.MultiplicityAdmission

open Purelib.RootIsolation.Multiplicity
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Provenance.Algebraic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial (Admission)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic (NonzeroResult)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index.NonzeroResult (RootIndex rootIndices)
open Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent.NonzeroResult
  (RootState rootInitial rootRequest rootMachine rootState_exact rootWord rootBox?)
open Purelib.Data.CCL.Transducer (Machine)
open Purelib.Data.CCL.Progressive
open CoherentRootCheckpoint (State stateReader readStateWith nextState)
open CoherentRoot (CertifiedName)
open Purelib.System.FilePath (join)

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Box

/-- Decide refinement of the fixture's original boxes by their four rational endpoint comparisons. -/
private instance (inner outer : Box) : Decidable (inner.Refines outer) := by
  unfold Box.Refines
  infer_instance

/-- The original nonrational quadratic coefficient table. -/
private def polynomial := Power.Gaussian.rootPolynomial 2 ⟨2, by decide⟩

/-- The independently retained repeated source coefficient table. -/
private def repeated := polynomial * polynomial

/-- The original focused factor's coefficient-computed large-square ambient box. -/
private def ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox polynomial

/-- The original quadratic supplies its actual squarefree and positive-degree input. -/
private def input : FTA.Squarefree.Input polynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨2, by decide⟩
  degreeAtLeastTwo := by
    unfold polynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The actual original separated-axis coefficient certificate retained by each independent track. -/
private def elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  polynomial input.nonzero input.degreePositive

/-- The first original positive local box of the focused quadratic factor. -/
private def firstBox : Box := ⟨1, 3 / 2, -1 / 16, 1 / 16, by decide, by decide⟩

/-- The first actual local state retains its original ambient-line clearances and checked winding. -/
private def firstInitial : State.WindingOne.Basic.WindingOneState polynomial ambient :=
  let left := Line.Bezout.verticalOfCoprime polynomial ambient firstBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial firstBox.xLower)
      (Path.Axis.verticalPathImag polynomial firstBox.xLower) (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime polynomial ambient firstBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial firstBox.xUpper)
      (Path.Axis.verticalPathImag polynomial firstBox.xUpper) (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime polynomial ambient firstBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial firstBox.yLower)
      (Path.Axis.horizontalPathImag polynomial firstBox.yLower) (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime polynomial ambient firstBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial firstBox.yUpper)
      (Path.Axis.horizontalPathImag polynomial firstBox.yUpper) (by decide +kernel) (by decide +kernel))
  have refines : firstBox.Refines ambient := by
    unfold Box.Refines
    constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor <;> decide +kernel
  { box := firstBox
    refinesAmbient := refines
    proper := by constructor <;> decide
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
      (left.restrict refines) (right.restrict refines) (bottom.restrict refines) (top.restrict refines)
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The first independent original total Newton track uses that same checked local state. -/
private def firstTrack : Track.Basic.WindingOneTrack polynomial ambient := Track.Newton.Build.ofInitial
  input.degreeAtLeastTwo input.squarefree elimination firstInitial

/-- The second original positive local box of the focused quadratic factor. -/
private def secondBox : Box := ⟨5 / 4, 10 / 7, -1 / 32, 1 / 32, by decide +kernel, by decide +kernel⟩

/-- The second actual local state retains its original ambient-line clearances and checked winding. -/
private def secondInitial : State.WindingOne.Basic.WindingOneState polynomial ambient :=
  let left := Line.Bezout.verticalOfCoprime polynomial ambient secondBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial secondBox.xLower)
      (Path.Axis.verticalPathImag polynomial secondBox.xLower) (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime polynomial ambient secondBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial secondBox.xUpper)
      (Path.Axis.verticalPathImag polynomial secondBox.xUpper) (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime polynomial ambient secondBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial secondBox.yLower)
      (Path.Axis.horizontalPathImag polynomial secondBox.yLower) (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime polynomial ambient secondBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial secondBox.yUpper)
      (Path.Axis.horizontalPathImag polynomial secondBox.yUpper) (by decide +kernel) (by decide +kernel))
  have refines : secondBox.Refines ambient := by
    unfold Box.Refines
    constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor <;> decide +kernel
  { box := secondBox
    refinesAmbient := refines
    proper := by constructor <;> decide
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
      (left.restrict refines) (right.restrict refines) (bottom.restrict refines) (top.restrict refines)
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The second independent original total Newton track uses that same checked local state. -/
private def secondTrack : Track.Basic.WindingOneTrack polynomial ambient := Track.Newton.Build.ofInitial
  input.degreeAtLeastTwo input.squarefree elimination secondInitial

/-- The same original quadratic coefficient table is one normalized squarefree occurrence. -/
private def factor : Squarefree.Decomposition.Basic.Factor where
  polynomial := polynomial
  normalized := by decide +kernel
  nonzero := input.nonzero
  degreePositive := input.degreePositive
  squarefree := input.squarefree

/-- The original quadratic source retains its complete checked singleton occurrence decomposition. -/
private def firstDecomposition : Squarefree.Decomposition polynomial where
  factors := [factor]
  factorsNonempty := by intro impossible; cases impossible
  evalIdentity := by
    intro point
    simp only [Squarefree.Decomposition.Basic.factorProduct,
      DensePolynomial.eval_mul, DensePolynomial.eval_constant,
      factor, Data.Gaussian.Basic.mul_one, -eq_self]
    rfl
  degreeSum := by decide +kernel

/-- The actual focused occurrence comes from this same original decomposition's finite context list. -/
private def firstContext :=
  (Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts
    firstDecomposition.positiveMultiplicityEntries)[0]'(by decide +kernel)

/-- The actual retained focused factor has the original displayed quadratic coefficients. -/
private theorem firstFocus : firstContext.focus.part.polynomial = polynomial := by decide +kernel

/-- The first original source retains its complete decomposition, focused multiplicity and independent local track. -/
private def firstSite : Multiplicity.Site.Basic.TrackSiteInput polynomial Dense.Gaussian.Unit.unitDenominator where
  decomposition := firstDecomposition
  pairwise := firstDecomposition.positiveMultiplicityEntries_pairwise
  context := firstContext
  oppositeNonzero := by decide +kernel
  focusOppositeCoprime := Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD
    firstContext.focus.part.polynomial Dense.Gaussian.Unit.unitDenominator
    (Dense.Gaussian.GCD.extendedGCD firstContext.focus.part.polynomial Dense.Gaussian.Unit.unitDenominator)
    rfl (by decide +kernel) (by decide +kernel)
  track := by rewrite [firstFocus]; exact firstTrack
  current := by rewrite [firstFocus]; exact firstInitial

/-- The first source's actual realization retains its original cofactor and root cache. -/
private def first := Site.Realization.ofInput firstSite

/-- The original squared source retains both checked occurrences of its same focused factor. -/
private def secondDecomposition : Squarefree.Decomposition repeated where
  factors := [factor, factor]
  factorsNonempty := by intro impossible; cases impossible
  evalIdentity := by
    intro point
    unfold repeated
    simp only [Squarefree.Decomposition.Basic.factorProduct,
      DensePolynomial.eval_mul, DensePolynomial.eval_constant,
      factor, Data.Gaussian.Basic.mul_one, -eq_self]
    rfl
  degreeSum := by decide +kernel

/-- The actual focused occurrence comes from this same original decomposition's finite context list. -/
private def secondContext :=
  (Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts
    secondDecomposition.positiveMultiplicityEntries)[0]'(by decide +kernel)

/-- The actual retained focused factor has the original displayed quadratic coefficients. -/
private theorem secondFocus : secondContext.focus.part.polynomial = polynomial := by decide +kernel

/-- The second original source retains its complete decomposition, focused multiplicity and independent local track. -/
private def secondSite : Multiplicity.Site.Basic.TrackSiteInput repeated Dense.Gaussian.Unit.unitDenominator where
  decomposition := secondDecomposition
  pairwise := secondDecomposition.positiveMultiplicityEntries_pairwise
  context := secondContext
  oppositeNonzero := by decide +kernel
  focusOppositeCoprime := Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD
    secondContext.focus.part.polynomial Dense.Gaussian.Unit.unitDenominator
    (Dense.Gaussian.GCD.extendedGCD secondContext.focus.part.polynomial Dense.Gaussian.Unit.unitDenominator)
    rfl (by decide +kernel) (by decide +kernel)
  track := by rewrite [secondFocus]; exact secondTrack
  current := by rewrite [secondFocus]; exact secondInitial

/-- The second source's actual realization retains its original cofactor and root cache. -/
private def second := Site.Realization.ofInput secondSite

/-- The same original focused polynomial supplies the nested comparison's actual finite squarefree input. -/
private def focusedInput : FTA.Squarefree.Input firstSite.context.focus.part.polynomial where
  squarefree := firstSite.context.focus.part.squarefree
  degreeAtLeastTwo := by
    change 2 ≤ firstContext.focus.part.polynomial.natDegree
    rewrite [firstFocus]
    exact input.degreeAtLeastTwo

/-- The original focused coefficient tables agree while source owners and occurrence counts stay independent. -/
private theorem focusedEq : secondSite.context.focus.part.polynomial = firstSite.context.focus.part.polynomial :=
  secondFocus.trans firstFocus.symm

/-- Print and flush an actual original-owner execution stage. -/
private def progress (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Admit both independent original source owners and retain their same positive-real focused quadratic branches. -/
public def check : IO Unit := do
  progress "multiplicity: retain independent original quadratic and repeated source sites"
  let original := PolynomialRoot.Sidecar.ofRealization first
  let squared := PolynomialRoot.Sidecar.ofRealization second
  unless original.owner.polynomial = polynomial ∧ squared.owner.polynomial = repeated do
    throw (IO.userError "an intrinsic multiplicity owner replaced its original source polynomial")
  unless original.owner.multiplicity = 1 ∧ squared.owner.multiplicity = 2 do
    throw (IO.userError "the independent original source occurrence counts were not preserved")
  let firstReality := first.root.inspectQuadratic 2 0
  let secondReality := second.root.inspectQuadratic 2 0
  match firstReality.outcome, secondReality.outcome with
  | .ready firstRegion, .ready secondRegion =>
      unless firstReality.box.xLower > 0 ∧ secondReality.box.xLower > 0 do
        throw (IO.userError "the independent original multiplicity root branches are not positive")
      let _firstConjugacy := firstRegion.real
      let _secondConjugacy := secondRegion.real
      let _sameOriginalChannels := first.root.equivalent_nested_of_eq focusedInput second.root focusedEq
        (congrArg Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox focusedEq) (by decide +kernel)
      progress "multiplicity: actual independent source multiplicities and positive-real branches retained"
      let Γ : Fin 2 → Annotated := fun index =>
        if index.val = 0 then Annotated.opaque first.root.value else Annotated.opaque second.root.value
      let firstAtom := Admitted.atom Γ ⟨0, by decide⟩ (Algebraic.Sidecar.ofRoot original)
      let secondAtom := Admitted.atom Γ ⟨1, by decide⟩ (Algebraic.Sidecar.ofRoot squared)
      match (firstAtom.pow 2).run, (secondAtom.pow 2).run with
      | .completed firstPower, .completed secondPower =>
          let firstPower := firstPower.materialize
          let secondPower := secondPower.materialize
          let firstReading := firstPower.sidecar.scalar?
          let secondReading := secondPower.sidecar.scalar?
          if presentFirst : firstReading.isSome then
            if presentSecond : secondReading.isSome then
              unless (firstReading.get presentFirst).value = 2 ∧ (secondReading.get presentSecond).value = 2 do
                throw (IO.userError "the independent original focused-factor power equations differ")
              progress "multiplicity: both original admitted power channels read two"
            else throw (IO.userError "the repeated original source lost its focused-factor numerical equation")
          else throw (IO.userError "the original quadratic source lost its numerical equation")
      | _, _ => throw (IO.userError "the independent intrinsic multiplicity admissions failed checked completion")
  | _, _ => throw (IO.userError "an independent original multiplicity branch has a finite reality obligation")

/-- Pay an actual original-channel equality request at independently supplied stage floors.

Optional finite observations retain both original names and exact sampling
indices. The saved comparison is the original complete request, and absent
observations preserve direct sampling of both original channels.
-/
public def checkAgreement {first second : Name.Basic.Named}
    (equivalent : Equivalence.NamedEquivalent first second)
    (leftStart rightStart : Nat) (target : {value : Rational // 0 < value} := ⟨1, by decide⟩)
    (leftSamples : Option (Sequence.SamplePrefix (Name.Sampling.approximation first)) := none)
    (rightSamples : Option (Sequence.SamplePrefix (Name.Sampling.approximation second)) := none)
    (prepared : {request : Equivalence.Comparison
      (Name.Sampling.approximation first) (Name.Sampling.approximation second) leftStart rightStart target.val //
        request = equivalent.compare leftStart rightStart target.val target.property} :=
      ⟨equivalent.compare leftStart rightStart target.val target.property, rfl⟩) : IO Unit := do
  let request := prepared.val
  let left := Name.Sampling.approximation first
  let right := Name.Sampling.approximation second
  let leftValue := match leftSamples with
    | none => left.sample request.leftIndex
    | some retained => retained.sample request.leftIndex
  let rightValue := match rightSamples with
    | none => right.sample request.rightIndex
    | some retained => retained.sample request.rightIndex
  unless request.leftIndex ≥ leftStart ∧ request.rightIndex ≥ rightStart ∧
      Norm.Basic.normSq (leftValue - rightValue) < target.val do
    throw (IO.userError "the actual higher-admission equality did not pay its original-channel request")

/-- Read an equality classification without unfolding the indexed original input owners in an IO match. -/
private def comparisonEqual {first second : CoherentNamed} : Algebraic.Comparison first second → Bool
  | .equal _ => true
  | .distinct _ _ => false

/-- Pay the same original-channel equality request from its retained comparison and root-state banks.

Both genuine whole-channel identities are required for cached named reads.
The ordinary request computes its unchanged named indices once; the same
readers supply their canonical primitive observations in left/right order.
Missing identities or an absent reader preserve the original sampling path.
-/
private def checkComparedAgreement {first second : CoherentNamed} {left : Algebraic.Sidecar first}
    {right : Algebraic.Sidecar second} {firstStart secondStart : Nat}
    (compared : Sidecar.Compared left right firstStart secondStart)
    (equivalent : Equivalence.NamedEquivalent first.name second.name) (leftStart rightStart : Nat)
    (readers : Option ((inputs : Sidecar.Compared.RootInput left ×
      Sidecar.Compared.RootInput right) →
        IO (((index : Nat) → IO (State inputs.1.view.root index)) ×
          ((index : Nat) → IO (State inputs.2.view.root index)))) := none) : IO Unit := do
  match readers with
  | none => checkAgreement equivalent leftStart rightStart
  | some read =>
      match compared.cache with
      | .inr _ => checkAgreement equivalent leftStart rightStart
      | .inl intrinsic =>
          match intrinsic.left.view.channelEq?, intrinsic.right.view.channelEq? with
          | some leftSame, some rightSame => do
              let request := equivalent.compare leftStart rightStart 1 (by decide)
              let states ← read (intrinsic.left, intrinsic.right)
              let leftEntry ← CoherentRootCheckpoint.namedSampleWithView intrinsic.left.view leftSame.down
                states.1 request.leftIndex
              let rightEntry ← CoherentRootCheckpoint.namedSampleWithView intrinsic.right.view rightSame.down
                states.2 request.rightIndex
              let firstSamples := Sequence.SamplePrefix.ofEntries
                (Name.Sampling.approximation first.name) [leftEntry.val]
              let secondSamples := Sequence.SamplePrefix.ofEntries
                (Name.Sampling.approximation second.name) [rightEntry.val]
              checkAgreement equivalent leftStart rightStart (leftSamples := some firstSamples)
                (rightSamples := some secondSamples) (prepared := ⟨request, rfl⟩)
          | _, _ => checkAgreement equivalent leftStart rightStart

/-- Consume an actual computed equality and optionally reuse its same original numerical state banks. -/
private def checkEqualComparison {first second : CoherentNamed} {left : Algebraic.Sidecar first}
    {right : Algebraic.Sidecar second} {firstStart secondStart : Nat}
    (compared : Sidecar.Compared left right firstStart secondStart) (leftStart rightStart : Nat)
    (readers : Option ((inputs : Sidecar.Compared.RootInput left ×
      Sidecar.Compared.RootInput right) →
        IO (((index : Nat) → IO (State inputs.1.view.root index)) ×
          ((index : Nat) → IO (State inputs.2.view.root index)))) := none) : IO Unit :=
  match compared.comparison with
  | .equal equivalent => checkComparedAgreement compared equivalent leftStart rightStart readers
  | .distinct _ _ => throw (IO.userError "the selected original admitted roots were separated")

/-- Inspect the original nested branch's actual paid requests without replacing either root or site owner. -/
private def checkNestedPreparation {firstPolynomial secondPolynomial : CoefficientPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    {firstInput : FTA.Positive.Input.PositiveInput firstPolynomial}
    {secondInput : FTA.Positive.Input.PositiveInput secondPolynomial}
    {firstRoot : CoherentRoot.CertifiedName firstTrack} {secondRoot : CoherentRoot.CertifiedName secondTrack}
    {firstStart secondStart : Nat}
    (prepared : CoherentRoot.CommonSource.PreparedComparison firstInput secondInput
      firstRoot secondRoot firstStart secondStart)
    (request : Option (Nat × Nat × Data.Rat.Fraction.Rational × Nat × Nat) := none) : IO Unit := do
  unless prepared.inspectInitial do
    throw (IO.userError "the nested-root protocol lost its actual checked initial-cache request")
  match prepared.preparation with
  | .nested _ _ _ _ left right _ _ =>
      unless left.index ≥ firstStart ∧ right.index ≥ secondStart ∧
          left.index ≤ left.maxIndex ∧ right.index ≤ right.maxIndex ∧
          left.targetSq = 1 ∧ right.targetSq = 1 ∧
          left.current.box.diagonalSq < left.targetSq ∧ right.current.box.diagonalSq < right.targetSq do
        throw (IO.userError "checked original nesting lost a retained refiner payment, actual cache state or bound")
      if let some actual := request then
        let quarter := actual.2.2.1 / 4
        if positive : 0 < quarter then
          if accurate : left.current.box.diagonalSq < quarter ∧ right.current.box.diagonalSq < quarter then
            have _wholeLeft := left.atRequest_cached quarter positive accurate.1
            have _wholeRight := right.atRequest_cached quarter positive accurate.2
            unless actual.1 ≤ left.index ∧ actual.2.1 ≤ right.index ∧ 1 ≤ left.index ∧
                actual.2.2.2.1 = left.index ∧ actual.2.2.2.2 = right.index do
              throw (IO.userError "the compatible numeric comparison replaced an actual retained paid stage")
          else throw (IO.userError "the retained original cache states did not meet this actual comparison request")
        else throw (IO.userError "the numeric comparison lost its actual positive quarter target")
  | .linear _ _ _ _ _ _ _ _ =>
      throw (IO.userError "the original quadratic focused factors were replaced by linear comparison inputs")
  | .cofactor _ _ _ _ _ _ _ _ _ _ | .enclosing _ _ _ _ _ _ _ _ _ _ _ _ _ _ | .separated _ =>
      throw (IO.userError "the original nested protocol unexpectedly selected a different checked request")
  | .partition _ _ _ =>
      throw (IO.userError "internally checked original nesting rebuilt a common-source partition")

/-- Exercise failed emitted-index coverage when a constant sampler stays at raw stage zero.

The original operational relation legitimately requests later raw stages.
The checked named conversion must retain those payments in its fallback,
while the actual original named samples remain the same exact constant.
-/
private def checkSamplingFallback : IO Unit := do
  let source := Sequence.Constant.constantApproximation 2
  let equivalent := (Equivalence.Equivalent.refl source).withFloors 1 1
  let leftRaw := Equivalence.Sampling.emittedSampleIndex source 0
  let rightRaw := Equivalence.Sampling.emittedSampleIndex source 1
  let paid := equivalent.compare leftRaw rightRaw 1 (by decide)
  let leftIndex := Equivalence.Sampling.comparisonIndex source 0 paid.leftIndex
  let rightIndex := Equivalence.Sampling.comparisonIndex source 1 paid.rightIndex
  unless paid.leftIndex = 1 ∧ paid.rightIndex = 1 ∧ leftRaw = 0 ∧ rightRaw = 0 do
    throw (IO.userError "the constant sampling fallback no longer retains its actual later raw-stage payments")
  if missing : ¬ (paid.leftIndex ≤ Equivalence.Sampling.emittedSampleIndex source leftIndex ∧
      paid.rightIndex ≤ Equivalence.Sampling.emittedSampleIndex source rightIndex) then
    have _wholeFallback :=
      Equivalence.Equivalent.toNamed_true_fallback equivalent 0 1 1 (by decide) missing
    let actual := (equivalent.toNamed true).compare 0 1 1 (by decide)
    let named := Name.Sampling.approximation source.toNamed
    unless actual.leftIndex ≥ leftIndex ∧ actual.rightIndex ≥ rightIndex ∧
        Norm.Basic.normSq (named.sample actual.leftIndex - named.sample actual.rightIndex) < 1 do
      throw (IO.userError "failed coverage did not pay the retained original named fallback request")
  else throw (IO.userError "the intended constant sampler unexpectedly covered the later paid raw indices")

/-- Execute absent, covered and tighter-target difference-bound paths on the actual same original exact channels.

The actual process possibilities establish the retained scalar bound.
Covered requests keep their original floors; uncovered requests consume the
whole original procedure with all its independently computed payment fields.
-/
private def checkDifferenceBounds : IO Unit := do
  let channel := CoherentNamed.Coherence.exact (2 : Data.Gaussian.Basic.Canonical)
  let equivalent := Equivalence.NamedEquivalent.refl channel.name
  let retained : Difference.Bound channel channel := ⟨1, by
    intro value possible
    change ∃ right negative, right = 2 ∧ (∃ left, left = 2 ∧ negative = -left) ∧
      value = right + negative at possible
    rcases possible with ⟨right, negative, rightEq, ⟨left, leftEq, negativeEq⟩, valueEq⟩
    rewrite [valueEq, negativeEq, rightEq, leftEq]
    decide +kernel⟩
  let original := Difference.difference_zero_of_equivalent channel channel equivalent
  let request : Difference.Request channel channel := (retained, fun _ => true)
  let cached := Difference.difference_zero_of_equivalent channel channel equivalent (some request)
  have _default := Difference.difference_zero_of_equivalent_none channel channel equivalent
  have _covered := Difference.difference_zero_of_equivalent_covered
    channel channel equivalent request 2 3 2 (by decide) (by decide) rfl
  let covered := cached.compare 2 3 2 (by decide)
  unless covered.leftIndex = 2 ∧ covered.rightIndex = 3 do
    throw (IO.userError "the covered actual difference bound changed an original requested floor")
  have _fallback := Difference.difference_zero_of_equivalent_fallback
    channel channel equivalent request 2 3 1 (by decide) (by decide)
  let fallback := cached.compare 2 3 1 (by decide)
  let previous := original.compare 2 3 1 (by decide)
  unless fallback.leftIndex = previous.leftIndex ∧ fallback.rightIndex = previous.rightIndex do
    throw (IO.userError "the tighter-target bound failed to consume its actual original fallback payment")
  let unpaid : Difference.Request channel channel := (retained, fun _ => false)
  have _unpaid := Difference.difference_zero_of_equivalent_unpaid
    channel channel equivalent unpaid 2 3 2 (by decide) (by decide)
  let rejected := (Difference.difference_zero_of_equivalent channel channel equivalent (some unpaid)).compare
    2 3 2 (by decide)
  let previousCovered := original.compare 2 3 2 (by decide)
  unless rejected.leftIndex = previousCovered.leftIndex ∧ rejected.rightIndex = previousCovered.rightIndex do
    throw (IO.userError "rejected source floors did not consume the actual original whole comparison")
  let difference := Name.Sampling.approximation (Difference.difference channel channel).name
  unless Norm.Basic.normSq (difference.sample covered.leftIndex) < 2 ∧
      Norm.Basic.normSq (difference.sample fallback.leftIndex) < 1 do
    throw (IO.userError "a bound comparison did not certify the same actual original difference sample")
  progress "multiplicity: difference bound None, covered and full tighter-target fallback requests paid"

/-- Execute checked original nesting at independent multiplicity sites and the actual Sidecar comparison boundary.

Both original root caches and source multiplicities are retained. The internal
checks receive no successful coefficient, ambient, nesting or agreement premise.
Each later request consumes the original paid cache refinements.
-/
public def checkRequests : IO Unit := do
  checkDifferenceBounds
  progress "multiplicity: compute original independent-site identification without a nesting witness"
  let identified := first.compare second 1 2
  checkNestedPreparation identified
  match selected : identified.comparison with
  | .distinct _ =>
      throw (IO.userError "computed original-site identification separated the two positive quadratic branches")
  | .equal equivalent =>
      let comparison := identified.approximation_equivalent equivalent selected
      progress "multiplicity: pay first computed original independent-start comparison request"
      let request := comparison.compare 0 1 4 (by decide)
      checkNestedPreparation identified (some (0, 1, 4, request.leftIndex, request.rightIndex))
      unless request.leftIndex ≥ 0 ∧ request.rightIndex ≥ 1 do
        throw (IO.userError "the original multiplicity comparison lost its independent requested floors")
      let firstSample := first.root.approximation.sample request.leftIndex
      let secondSample := second.root.approximation.sample request.rightIndex
      unless Norm.Basic.normSq (firstSample - secondSample) < 4 do
        throw (IO.userError "the actual original multiplicity comparison observations did not pay their request")
      progress "multiplicity: first actual original comparison observations paid"
      let retry := comparison.compare 1 0 2 (by decide)
      checkNestedPreparation identified (some (1, 0, 2, retry.leftIndex, retry.rightIndex))
      unless retry.leftIndex ≥ 1 ∧ retry.rightIndex ≥ 0 do
        throw (IO.userError "the original multiplicity comparison lost its independent retry floors")
      let firstRetry := first.root.approximation.sample retry.leftIndex
      let secondRetry := second.root.approximation.sample retry.rightIndex
      unless Norm.Basic.normSq (firstRetry - secondRetry) < 2 do
        throw (IO.userError "the actual original multiplicity retry observations did not pay their request")
      progress "multiplicity: retained original caches paid the independent retry"
  progress "multiplicity: consume the same checked nesting through both actual original algebraic Sidecars"
  let firstRoot := PolynomialRoot.Sidecar.ofRealization first
  let secondRoot := PolynomialRoot.Sidecar.ofRealization second
  unless firstRoot.owner.polynomial = polynomial ∧ secondRoot.owner.polynomial = repeated ∧
      firstRoot.owner.multiplicity = 1 ∧ secondRoot.owner.multiplicity = 2 do
    throw (IO.userError "checked nesting replaced an original source parent or repeated multiplicity")
  unless firstRoot.channelEq?.isSome ∧ secondRoot.channelEq?.isSome do
    throw (IO.userError "the original root-sidecar constructors lost their genuine whole-channel identities")
  let operational := firstRoot.transport (Equivalence.NamedEquivalent.refl _)
  unless operational.channelEq?.isNone do
    throw (IO.userError "operational agreement was incorrectly promoted to a whole-channel identity")
  match operational.view? with
  | none => throw (IO.userError "operational transport discarded the original retained root view")
  | some view =>
      unless view.channelEq?.isNone do
        throw (IO.userError "an operational-only root view acquired an unsupported whole-channel identity")
  let original := Algebraic.Sidecar.ofRoot firstRoot
  let squared := Algebraic.Sidecar.ofRoot secondRoot
  let compared := original.compare squared 1 2
  let operationalCompared := (Algebraic.Sidecar.ofRoot operational).compare squared 1 2
  unless operationalCompared.inspectBound ∧ operationalCompared.bound.isNone do
    throw (IO.userError "an operational-only parent supplied an unsupported original-channel bound")
  progress "multiplicity: production comparison retained its original checked common-source result"
  match compared.cache with
  | .inr _ => throw (IO.userError "nested original sites forced the generic full-difference materializer")
  | .inl intrinsic =>
      have _actualProcedure := intrinsic.prepared_eq
      checkNestedPreparation intrinsic.prepared
      unless intrinsic.left.view.channelEq?.isSome ∧ intrinsic.right.view.channelEq?.isSome do
        throw (IO.userError "production root views lost genuine identities before original-channel transport")
  progress "multiplicity: pay the actual production Named comparison at its original starts"
  checkEqualComparison compared 0 1
  checkSamplingFallback
  progress "multiplicity: actual original multiplicities and nested root caches retained at the production boundary"

/-- The distinct displayed squarefree cubic retains the positive quadratic root and the exact root three. -/
private def expandedPolynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[1, -3, -2, 6]⟩

/-- The independent cubic's coefficient-derived original ambient box. -/
private def expandedAmbient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox expandedPolynomial

/-- The displayed cubic is squarefree by its retained original Euclidean result with its derivative. -/
private def expandedInput : FTA.Squarefree.Input expandedPolynomial where
  squarefree := Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD
    expandedPolynomial (Dense.Gaussian.GCD.derivative expandedPolynomial)
    (Dense.Gaussian.GCD.extendedGCD expandedPolynomial (Dense.Gaussian.GCD.derivative expandedPolynomial))
    rfl (by decide +kernel) (by decide +kernel)
  degreeAtLeastTwo := by decide +kernel

/-- The cubic's original separated-axis elimination certificate is computed once for both independent tracks. -/
private def expandedElimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  expandedPolynomial expandedInput.nonzero expandedInput.degreePositive

/-- The two exact cubic seeds select its positive irrational root and its distinct exact root three.

The first box is narrower horizontally and wider vertically than the original
quadratic seed. Neither initial box refines the other, so identification must
compute its actual common-source ownership rather than consume nesting.
-/
private def expandedBox (index : Fin 2) : Box :=
  Fin.cases ⟨5 / 4, 10 / 7, -1 / 8, 1 / 8, by decide +kernel, by decide +kernel⟩
    (fun _ => ⟨23 / 8, 25 / 8, -1 / 16, 1 / 16, by decide +kernel, by decide +kernel⟩) index

/-- The original quadratic seed does not refine the independent equal-root cubic seed. -/
private theorem first_not_refines_expanded : ¬ firstBox.Refines (expandedBox ⟨0, by decide⟩) := by
  decide +kernel

/-- The independent equal-root cubic seed does not refine the original quadratic seed. -/
private theorem expanded_not_refines_first : ¬ (expandedBox ⟨0, by decide⟩).Refines firstBox := by
  decide +kernel

/-- The unchanged two original nonnested boxes determine this exact enclosing hull. -/
private def comparisonHull := Box.Hull.hull firstBox (expandedBox ⟨0, by decide⟩)

/-- The enclosing hull has the same exact outer endpoints selected from both retained seeds. -/
private theorem comparisonHull_endpoints :
    comparisonHull.xLower = 1 ∧ comparisonHull.xUpper = 3 / 2 ∧
      comparisonHull.yLower = -1 / 8 ∧ comparisonHull.yUpper = 1 / 8 := by
  decide +kernel

/-- The actual hull of the original two boxes lies inside the original quadratic ambient. -/
private theorem comparisonHull_refines_first : comparisonHull.Refines ambient := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor <;> decide +kernel

/-- The same actual hull lies inside the original independent cubic ambient. -/
private theorem comparisonHull_refines_expanded : comparisonHull.Refines expandedAmbient := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · constructor <;> decide +kernel

/-- The original finite enclosing box has both strictly positive side lengths. -/
private theorem comparisonHull_proper : comparisonHull.Proper := by
  constructor <;> decide +kernel

/-- The actual original Euclidean cofactor is affine with its retained exact root at three. -/
private def comparisonCofactor := Dense.Gaussian.Roots.Linear.rootData
  (p := (Dense.Gaussian.GCD.extendedGCD polynomial expandedPolynomial).qFactor) (by decide +kernel)

/-- The original affine complement's computed root is genuinely outside the same enclosing hull. -/
private theorem comparisonHull_excludes_cofactor : ¬ comparisonHull.Contains comparisonCofactor.point := by
  decide +kernel

/-- The quadratic's actual finite winding computation on the enclosing hull is four. -/
private theorem comparisonHull_first_winding :
    Winding.Box.Basic.quadrupledBoxWinding polynomial comparisonHull = 4 := by
  decide +kernel

/-- The independent cubic's actual finite winding computation on that same enclosing hull is four. -/
private theorem comparisonHull_expanded_winding :
    Winding.Box.Basic.quadrupledBoxWinding expandedPolynomial comparisonHull = 4 := by
  decide +kernel

/-- Each cubic seed supplies the four checked original ambient-line clearances and unit winding. -/
private def expandedInitial (index : Fin 2) :
    State.WindingOne.Basic.WindingOneState expandedPolynomial expandedAmbient :=
  let box := expandedBox index
  let left := Clearance.Box.Line.Bezout.verticalOfCoprime expandedPolynomial expandedAmbient box.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal expandedPolynomial box.xLower)
      (Path.Axis.verticalPathImag expandedPolynomial box.xLower)
      ((by decide +kernel +revert))
      ((by decide +kernel +revert)))
  let right := Clearance.Box.Line.Bezout.verticalOfCoprime expandedPolynomial expandedAmbient box.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal expandedPolynomial box.xUpper)
      (Path.Axis.verticalPathImag expandedPolynomial box.xUpper)
      ((by decide +kernel +revert))
      ((by decide +kernel +revert)))
  let bottom := Clearance.Box.Line.Bezout.horizontalOfCoprime expandedPolynomial expandedAmbient box.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal expandedPolynomial box.yLower)
      (Path.Axis.horizontalPathImag expandedPolynomial box.yLower)
      ((by decide +kernel +revert))
      ((by decide +kernel +revert)))
  let top := Clearance.Box.Line.Bezout.horizontalOfCoprime expandedPolynomial expandedAmbient box.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal expandedPolynomial box.yUpper)
      (Path.Axis.horizontalPathImag expandedPolynomial box.yUpper)
      ((by decide +kernel +revert))
      ((by decide +kernel +revert)))
  have refines : box.Refines expandedAmbient :=
    (by decide +kernel +revert)
  { box := box
    refinesAmbient := refines
    proper := by
      change box.xLower < box.xUpper ∧ box.yLower < box.yUpper
      decide +kernel +revert
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
      (left.restrict refines) (right.restrict refines) (bottom.restrict refines) (top.restrict refines)
    rawWindingFour := (by decide +kernel +revert)
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- Each actual cubic Newton track retains its own checked original seed and the same cubic coefficient cache. -/
private def expandedTrack (index : Fin 2) : Track.Basic.WindingOneTrack expandedPolynomial expandedAmbient :=
  Track.Newton.Build.ofInitial expandedInput.degreeAtLeastTwo expandedInput.squarefree
    expandedElimination (expandedInitial index)

/-- The displayed cubic is one squarefree multiplicity occurrence, without an irreducibility requirement. -/
private def expandedFactor : Squarefree.Decomposition.Basic.Factor where
  polynomial := expandedPolynomial
  normalized := by decide +kernel
  nonzero := expandedInput.nonzero
  degreePositive := expandedInput.degreePositive
  squarefree := expandedInput.squarefree

/-- The independent cubic retains its complete original singleton squarefree decomposition. -/
private def expandedDecomposition : Squarefree.Decomposition expandedPolynomial where
  factors := [expandedFactor]
  factorsNonempty := by intro impossible; cases impossible
  evalIdentity := by
    intro point
    simp only [Squarefree.Decomposition.Basic.factorProduct,
      DensePolynomial.eval_mul, DensePolynomial.eval_constant,
      expandedFactor, Data.Gaussian.Basic.mul_one, -eq_self]
    rfl
  degreeSum := by decide +kernel

/-- The actual original cubic occurrence comes from its complete retained finite context list. -/
private def expandedContext :=
  (Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts
    expandedDecomposition.positiveMultiplicityEntries)[0]'(by decide +kernel)

/-- The retained focused occurrence has the independent displayed cubic coefficient table. -/
private theorem expandedFocus : expandedContext.focus.part.polynomial = expandedPolynomial := by decide +kernel

/-- Each cubic site retains its original source, occurrence, independently checked track and actual current state. -/
private def expandedSite (index : Fin 2) :
    Multiplicity.Site.Basic.TrackSiteInput expandedPolynomial Dense.Gaussian.Unit.unitDenominator where
  decomposition := expandedDecomposition
  pairwise := expandedDecomposition.positiveMultiplicityEntries_pairwise
  context := expandedContext
  oppositeNonzero := by decide +kernel
  focusOppositeCoprime := Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD
    expandedContext.focus.part.polynomial Dense.Gaussian.Unit.unitDenominator
    (Dense.Gaussian.GCD.extendedGCD expandedContext.focus.part.polynomial Dense.Gaussian.Unit.unitDenominator)
    rfl (by decide +kernel) (by decide +kernel)
  track := by rewrite [expandedFocus]; exact expandedTrack index
  current := by rewrite [expandedFocus]; exact expandedInitial index

/-- The independent cubic realization keeps its actual original parent, root cache and source equation. -/
private def expanded (index : Fin 2) := Site.Realization.ofInput (expandedSite index)

/-- Compare the original positive quadratic and independent nonnested cubic site through the actual classifier.

The supplied owners retain different coefficient polynomials and complete
independent checked boxes. No equality, nesting or successful comparison is
provided to the tactic.
-/
private theorem frontendNonnestedEquality :
    Nonempty (Equivalence.NamedEquivalent first.root.value.name (expanded ⟨0, by decide⟩).root.value.name) := by
  refine ⟨?_⟩
  ccl_equiv [PolynomialRoot.Sidecar.ofRealization first,
    PolynomialRoot.Sidecar.ofRealization (expanded ⟨0, by decide⟩)]

/-- The same quadratic owner and the cubic's independent root-three site retain their actual separation certificate. -/
private theorem frontendIndependentSeparation :
    ¬ Nonempty (Equivalence.NamedEquivalent first.root.value.name
      (expanded ⟨1, by decide⟩).root.value.name) := by
  ccl_equiv [PolynomialRoot.Sidecar.ofRealization first,
    PolynomialRoot.Sidecar.ofRealization (expanded ⟨1, by decide⟩)]

/-- A checked original-state prefix producer for the literal supplied root track.

The pointwise refinement equation identifies the same original Newton
operation. The returned entries keep their exact track parents and complete
states, rather than substituting another isolated or accelerated root.
-/
public abbrev StateRestorer :=
  {p : CoefficientPolynomial} → {ambient : Box} → (label : String) →
    (input : FTA.Squarefree.Input p) → (track : CoherentRoot.WindingOneTrack p ambient) →
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive) →
    (count : Nat) → IO (List (CoherentRoot.StateCache.Entry track))

/-- The first focused site's original refinement is the same retained Newton procedure. -/
private theorem firstSite_refine
    (current : CoherentRoot.WindingOneState firstSite.context.focus.part.polynomial firstSite.ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    firstSite.track.refine current epsilon positive =
      Track.Newton.Refinement.refineState focusedInput.degreeAtLeastTwo focusedInput.squarefree
        focusedInput.elimination current epsilon positive := by
  rfl

/-- The cubic focused factor supplies its original input without changing the site or seed. -/
private def expandedFocusedInput : FTA.Squarefree.Input expandedContext.focus.part.polynomial where
  squarefree := expandedContext.focus.part.squarefree
  degreeAtLeastTwo := by
    rewrite [expandedFocus]
    exact expandedInput.degreeAtLeastTwo

/-- Each original cubic site uses the same retained Newton refinement procedure. -/
private theorem expandedSite_refine (index : Fin 2)
    (current : CoherentRoot.WindingOneState expandedContext.focus.part.polynomial
      (expandedSite index).ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    (expandedSite index).track.refine current epsilon positive =
      Track.Newton.Refinement.refineState expandedFocusedInput.degreeAtLeastTwo expandedFocusedInput.squarefree
        expandedFocusedInput.elimination current epsilon positive := by
  rfl

/-- Read an original realized reference site's view through its same retained state accessor.

Both root getter identities retain the complete original realization. Its
view keeps the original factor, track, root cache and state index; no second
realization or root wrapper is constructed by a numerical read.
-/
private def realizationInputState {source opposite : CoefficientPolynomial}
    {site : Multiplicity.Site.Basic.TrackSiteInput source opposite}
    (realization : Site.Realization site)
    (states : (stage : Nat) → IO (State realization.root stage))
    (original : Sidecar.Compared.RootInput
      (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization realization))) (stage : Nat) :
    IO (State original.view.root stage) :=
  original.stateFromRoot (PolynomialRoot.Sidecar.ofRealization realization) rfl
    (fun actual same view found stage => by
      have read : (ownerView : CertifiedName.View actual.owner.channel) → actual.owner.view? = some ownerView →
          (stage : Nat) → IO (State ownerView.root stage) := by
        cases same
        intro ownerView ownerFound stage
        have sameView : CertifiedName.View.ofRoot realization.root realization.factorInput = ownerView :=
          Option.some.inj ownerFound
        cases sameView
        exact states stage
      exact actual.stateFromView read view found stage) stage

/-- Compare two original root sidecars using their authenticated retained state accessors.

Optional checkpoint controls select exact replay of the ordinary comparison.
Both original root views and their starting floors are retained, and a loader
failure skips the continuation. Without controls the original pure comparison
is consumed directly, including its complete difference fallback.
-/
private def compareSidecars {α : Type} {first second : CoherentNamed}
    (left : Algebraic.Sidecar first)
    (leftStates : (original : Sidecar.Compared.RootInput left) →
      (stage : Nat) → IO (State original.view.root stage))
    (firstStart secondStart : Nat)
    (controls : Option (ClearanceCheckpoint.Control IO × WindingCheckpoint.Control IO × System.FilePath))
    (label : String) (right : Algebraic.Sidecar second)
    (rightStates : (original : Sidecar.Compared.RootInput right) →
      (stage : Nat) → IO (State original.view.root stage))
    (use : {value : Sidecar.Compared left right firstStart secondStart //
      value = left.compare right firstStart secondStart} → IO α) : IO α := do
  match controls with
  | none => use ⟨left.compare right firstStart secondStart, rfl⟩
  | some (columns, winding, directory) =>
      let control : RootRefinementCheckpoint.Control :=
        { savedOnly := columns.savedOnly, inputDigest := winding.inputDigest }
      RootSelectionCheckpoint.compareSidecars left right firstStart secondStart
        (fun inputs => pure (leftStates inputs.1, rightStates inputs.2))
        (fun _ algebra degree => do
          progress "admission comparison: original nonlinear union elimination requested"
          pure (FTA.Squarefree.Input.Elimination.ofInput ⟨algebra.squarefree, degree⟩))
        columns winding control (join directory label) true true true use

/-- Execute computed equality and separation for independent nonnested roots of different displayed squarefree inputs.

No success, common interior, formal coefficient equality or matching owner is
supplied. Both internally computed nonlinear preparations retain the original
sites and paid stages. Equality is consumed on the exact original difference
channel; distinctness supplies its actual positive rational gap and preparation.
The coarse observation mode pays starts zero/one with tolerance64. The optional
saved-state restoration retains its original request and prefix contract.
-/
public def checkIndependent (restore : Option StateRestorer := none)
    (controls : Option (ClearanceCheckpoint.Control IO × WindingCheckpoint.Control IO × System.FilePath) := none)
    (coarse : Bool := false) :
    IO Unit := do
  let banks : Option (List (CoherentRoot.StateCache.Entry firstSite.track) ×
      List (CoherentRoot.StateCache.Entry (expandedSite ⟨0, by decide⟩).track) ×
      List (CoherentRoot.StateCache.Entry (expandedSite ⟨1, by decide⟩).track)) ←
    match restore with
    | none => pure none
    | some restore => do
        let originalSite := expandedSite ⟨0, by decide⟩
        let originalEqual := Site.Realization.ofInput originalSite
        let originalLeft := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization first)
        let originalRight := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization originalEqual)
        let states : ((stage : Nat) → IO (State first.root stage)) ×
            ((stage : Nat) → IO (State originalEqual.root stage)) ← match controls with
          | none => pure ((fun stage => pure ⟨first.root.stateAt stage, rfl⟩),
              fun stage => pure ⟨originalEqual.root.stateAt stage, rfl⟩)
          | some (columns, winding, directory) => do
              let pElimination : Thunk (FTA.Squarefree.Input.Elimination focusedInput) := Thunk.mk fun _ =>
                FTA.Squarefree.Input.Elimination.ofCertificate focusedInput elimination rfl
              let qElimination : Thunk (FTA.Squarefree.Input.Elimination expandedFocusedInput) := Thunk.mk fun _ =>
                FTA.Squarefree.Input.Elimination.ofCertificate expandedFocusedInput expandedElimination rfl
              let left ← stateReader (track := firstSite.track) first.root
                (readStateWith (track := firstSite.track) first.root
                  (nextState (track := firstSite.track) first.root focusedInput pElimination
                    firstSite_refine columns winding (join directory "independent-p")))
              let right ← stateReader (track := originalSite.track) originalEqual.root
                (readStateWith (track := originalSite.track) originalEqual.root
                  (nextState (track := originalSite.track) originalEqual.root expandedFocusedInput qElimination
                    (expandedSite_refine ⟨0, by decide⟩) columns winding (join directory "independent-q-equal")))
              pure (left, right)
        compareSidecars originalLeft (realizationInputState first states.1) 1 2 controls "independent-initial"
          originalRight (realizationInputState originalEqual states.2) fun retained => do
            let originalComparison := retained.val
            unless originalComparison.inspectBound ∧ originalComparison.bound.isSome do
              throw (IO.userError "the actual production request did not retain its original hull-bound inspection")
            match originalComparison.decision with
            | .prepared _ => throw (IO.userError "the original independent request unexpectedly separated equal roots")
            | .excluded zero =>
                let request := zero.compare 2 3 1 (by decide)
                unless request.leftIndex = 2 ∧ request.rightIndex = 3 do
                  throw (IO.userError "the actual covered production request did not retain its \
                    unchanged two/three floors")
                let indices := first.root.differenceStateIndices originalEqual.root request.leftIndex
                unless indices.1 ≥ 1 ∧ indices.2 ≥ 2 do
                  throw (IO.userError "the actual production payment discarded an original raw source floor")
                progress (s!"multiplicity: original named request {request.leftIndex}/{request.rightIndex} " ++
                  s!"demands raw states {indices.1}/{indices.2}")
                let firstBank ← restore "independent-p" focusedInput firstSite.track firstSite_refine (indices.1 + 1)
                progress "multiplicity: original quadratic state prefix restored with exact complete state identities"
                let equalBank ← restore "independent-q-equal" expandedFocusedInput
                  originalSite.track (expandedSite_refine ⟨0, by decide⟩) (indices.2 + 1)
                progress "multiplicity: original nonnested cubic state prefix restored with exact \
                  complete state identities"
                let distinctBank ← restore "independent-q-three" expandedFocusedInput
                  (expandedSite ⟨1, by decide⟩).track (expandedSite_refine ⟨1, by decide⟩) 2
                unless firstBank.length = indices.1 + 1 ∧ equalBank.length = indices.2 + 1 ∧
                    distinctBank.length = 2 do
                  throw (IO.userError "the exact original state-prefix producer lost a demanded ordered entry")
                pure (some (firstBank, equalBank, distinctBank))
  let first := Site.Realization.ofInput firstSite (banks.map fun entries => entries.1)
  let equalRoot := Site.Realization.ofInput (expandedSite ⟨0, by decide⟩)
    (banks.map fun entries => entries.2.1)
  let distinctRoot := Site.Realization.ofInput (expandedSite ⟨1, by decide⟩)
    (banks.map fun entries => entries.2.2)
  have _wholeFirst := Site.Realization.ofInput_cached_eq_default firstSite
    (banks.map fun entries => entries.1)
  have _wholeEqual := Site.Realization.ofInput_cached_eq_default (expandedSite ⟨0, by decide⟩)
    (banks.map fun entries => entries.2.1)
  have _wholeDistinct := Site.Realization.ofInput_cached_eq_default (expandedSite ⟨1, by decide⟩)
    (banks.map fun entries => entries.2.2)
  unless polynomial.normalize.coeffs = [1, 0, -2] ∧
      expandedPolynomial.normalize.coeffs = [1, -3, -2, 6] do
    throw (IO.userError "the independent inputs lost their distinct displayed squarefree coefficient tables")
  unless ¬ firstBox.Refines (expandedBox ⟨0, by decide⟩) ∧
      ¬ (expandedBox ⟨0, by decide⟩).Refines firstBox do
    throw (IO.userError "the independent equal-root fixture no longer exercises nonnested original boxes")
  let _firstNonnested := first_not_refines_expanded
  let _secondNonnested := expanded_not_refines_first
  let leftFloor := if coarse then 0 else 1
  let rightFloor := if coarse then 0 else 2
  progress s!"multiplicity: compute independent nonnested quadratic/cubic equality at starts \
    {leftFloor}/{rightFloor}"
  let originalLeft := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization first)
  let originalRight := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization equalRoot)
  let production := originalLeft.compare originalRight leftFloor rightFloor
  let .inl intrinsic := production.cache |
    throw (IO.userError "the actual original nonnested roots forced full difference materialization")
  have _leftOrigin := intrinsic.left.root_eq
  have _rightOrigin := intrinsic.right.root_eq
  have _actualProcedure := intrinsic.prepared_eq
  have _actualBound := production.bound_computed
  have _actualDecision := production.decision_computed
  unless production.inspectBound ∧ intrinsic.left.view.channelEq?.isSome ∧
      intrinsic.right.view.channelEq?.isSome ∧
      intrinsic.left.root.owner.polynomial = polynomial ∧
      intrinsic.right.root.owner.polynomial = expandedPolynomial ∧
      intrinsic.left.root.owner.multiplicity = 1 ∧ intrinsic.right.root.owner.multiplicity = 1 do
    throw (IO.userError "the production request lost an original parent, multiplicity or whole-channel identity")
  unless Option.map (fun retained : Difference.Request first.root.value equalRoot.root.value => retained.1.val)
      production.bound = some (5 / 16) do
    throw (IO.userError "the retained production bound is not the actual original common hull diagonal")
  let indices := first.root.differenceStateIndices equalRoot.root 2
  let higherRequest := intrinsic.left.view.differenceRequest? intrinsic.right.view
    (indices.1 + 1) (indices.2 + 1)
  unless Option.map (fun retained : Difference.Request first.root.value equalRoot.root.value => retained.2 2)
      higherRequest = some false do
    throw (IO.userError "a hull bound bypassed a higher unpaid original source floor")
  let same := intrinsic.prepared
  match same.preparation with
  | .linear _ _ _ _ _ _ _ _ =>
      throw (IO.userError "the independent nonlinear quadratic/cubic inputs were replaced by linear data")
  | .nested _ _ _ _ _ _ _ _ =>
      throw (IO.userError "different original polynomial inputs incorrectly took the same-index nested branch")
  | .separated _ =>
      throw (IO.userError "the actual overlapping equal roots were incorrectly separated")
  | .cofactor _ _ _ region _ _ right _ _ _ =>
      unless region.localCofactor.isSome ∧ region.index = leftFloor ∧ right.index = rightFloor ∧
          region.current.box.diagonalSq < region.targetSq ∧ right.current.box.diagonalSq < right.targetSq do
        throw (IO.userError "local source comparison lost its actual cofactor cache, paid floor or same state")
      progress "multiplicity: actual local cofactor and original source region retained both paid floor receipts"
  | .enclosing _ _ cofactor _ _ container _ winding _ _ region _ _ _ =>
      unless region.localCofactor.isSome ∧ region.index = 0 ∧ winding = 4 ∧
          region.current.box.diagonalSq < region.targetSq ∧
          container.box.xLower = comparisonHull.xLower ∧ container.box.xUpper = comparisonHull.xUpper ∧
          container.box.yLower = comparisonHull.yLower ∧ container.box.yUpper = comparisonHull.yUpper do
        throw (IO.userError "enclosing comparison lost its actual hull, winding or retained initial cache")
      match cofactor with
      | .inl _ => throw (IO.userError "the displayed original affine complement was replaced by constant data")
      | .inr affine =>
          unless affine.1.point = 3 do
            throw (IO.userError "the checked enclosing complement lost its actual original exact root")
      progress "multiplicity: both original line banks retained the checked common hull and actual winding four"
  | .partition source _ result =>
      unless source.algebra.polynomial.natDegree = 3 ∧ result.left.owner = result.right.owner do
        throw (IO.userError "computed independent equal roots lost their cubic union or same actual source owner")
      unless result.firstRegion.index ≥ leftFloor ∧ result.secondRegion.index ≥ rightFloor ∧
          result.left.index ≥ result.firstRegion.index ∧ result.right.index ≥ result.secondRegion.index do
        throw (IO.userError "computed independent equal roots lost original protection or ownership payments")
      unless result.firstRegion.current.box.diagonalSq < result.firstRegion.targetSq ∧
          result.secondRegion.current.box.diagonalSq < result.secondRegion.targetSq ∧
          result.left.current.box.diagonalSq < result.left.targetSq ∧
          result.right.current.box.diagonalSq < result.right.targetSq do
        throw (IO.userError "actual independent equal-root observations did not meet their retained requests")
      throw (IO.userError "the intended nonnested regression did not exercise its actual checked local cofactor route")
  unless comparisonEqual production.comparison do
    throw (IO.userError "computed independent quadratic/cubic identification separated their positive roots")
  match production.decision with
  | .prepared _ =>
      throw (IO.userError "the production decision separated the same internally identified original roots")
  | .excluded zero =>
      let difference := Difference.difference first.root.value equalRoot.root.value
      let leftStart := if coarse then 0 else 2
      let rightStart := if coarse then 1 else 3
      let accuracy : {value : Rational // 0 < value} :=
        if coarse then ⟨64, by decide +kernel⟩ else ⟨1, by decide +kernel⟩
      progress s!"multiplicity: consume the retained production difference-zero request at starts \
        {leftStart}/{rightStart}, tolerance {IntegrationCheckpoint.fractionText accuracy.val}"
      let request := zero.compare leftStart rightStart accuracy.val accuracy.property
      progress s!"multiplicity: actual difference-zero payment indices {request.leftIndex}/{request.rightIndex}"
      let original := Name.Sampling.approximation difference.name
      let exactZero := Name.Sampling.approximation (Name.Basic.Named.exact 0)
      let starts := if coarse then
        request.leftIndex ≥ leftStart ∧ request.rightIndex ≥ rightStart
      else request.leftIndex = leftStart ∧ request.rightIndex = rightStart
      unless starts ∧
          Norm.Basic.normSq
            (original.sample request.leftIndex - exactZero.sample request.rightIndex) < accuracy.val do
        throw (IO.userError "the actual original quadratic/cubic difference did not pay its exact-zero request")
      match production.decision with
      | .prepared _ => throw (IO.userError "repeated decision projection changed the retained original zero result")
      | .excluded repeated =>
          let reused := repeated.compare leftStart rightStart accuracy.val accuracy.property
          unless reused.leftIndex = request.leftIndex ∧ reused.rightIndex = request.rightIndex do
            throw (IO.userError "the repeated production decision did not reuse its exact original bound request")
      progress "multiplicity: computed original quadratic/cubic agreement paid the exact difference-zero request"
  let distinctLeftFloor := if coarse then 0 else 2
  let distinctRightFloor := if coarse then 0 else 1
  progress s!"multiplicity: compute distinct quadratic/cubic roots at starts \
    {distinctLeftFloor}/{distinctRightFloor}"
  let different := first.compare distinctRoot distinctLeftFloor distinctRightFloor
  match different.preparation with
  | .linear _ _ _ _ _ _ _ _ =>
      throw (IO.userError "the independent nonlinear distinct inputs were replaced by linear data")
  | .nested _ _ _ _ _ _ _ _ =>
      throw (IO.userError "different original polynomial inputs incorrectly took the same-index nested branch")
  | .cofactor _ _ _ _ _ _ _ _ _ _ | .enclosing _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      throw (IO.userError "the separated root-three request was incorrectly identified by a local cofactor")
  | .separated separated =>
      let starts := if coarse then
        separated.leftIndex ≥ distinctLeftFloor ∧ separated.rightIndex ≥ distinctRightFloor
      else separated.leftIndex = distinctLeftFloor ∧ separated.rightIndex = distinctRightFloor
      unless starts ∧ separated.separation.gap > 0 do
        throw (IO.userError "direct cached separation lost either original paid floor or its actual positive gap")
      progress "multiplicity: actual original floor caches supplied the same retained positive coordinate gap"
  | .partition _ _ result =>
      unless result.left.owner ≠ result.right.owner ∧
          result.firstRegion.index ≥ distinctLeftFloor ∧ result.secondRegion.index ≥ distinctRightFloor ∧
          result.left.index ≥ result.firstRegion.index ∧ result.right.index ≥ result.secondRegion.index do
        throw (IO.userError "computed distinct roots lost their actual different owners or original paid starts")
      throw (IO.userError "the intended distinct regression did not exercise actual cached floor separation")
  match different.comparison with
  | .equal _ =>
      throw (IO.userError "computed independent quadratic/cubic identification equated the positive root with three")
  | .distinct separation =>
      let gap := separation.separation.gap
      let prepared := separation.prepareDifference
      let left := first.root.approximation.sample separation.leftIndex
      let right := distinctRoot.root.approximation.sample separation.rightIndex
      unless separation.leftRequestStart ≥ distinctLeftFloor ∧ separation.rightRequestStart ≥ distinctRightFloor ∧
          separation.leftIndex ≥ separation.leftRequestStart ∧
          separation.rightIndex ≥ separation.rightRequestStart ∧
          separation.leftState.box.diagonalSq < separation.leftTargetSq ∧
          separation.rightState.box.diagonalSq < separation.rightTargetSq ∧ gap > 0 ∧
          gap ^ 2 ≤ Norm.Basic.normSq (left - right) ∧
          prepared.apart.certificate.lowerSq = gap ^ 2 / 8 do
        throw (IO.userError "actual distinct-root gap, original cache reads or difference preparation were lost")
      progress
        "multiplicity: computed distinct original roots retain their positive gap and exact difference preparation"

/-- One original dependent root index, its admission, shared state readers and actual stored algebraic Sidecar.

The complete Sidecar equation binds the original result, attachment and site
index; no independently supplied root owner is substituted for that parent.
-/
private abbrev AdmissionEntry {source : CoefficientPolynomial}
    (result : NonzeroResult source) :=
  (index : RootIndex result) ×
    (admission : Admission result index) ×
      Admission.StateReaders IO admission ×
      {sidecar : Algebraic.Sidecar admission.channel //
        sidecar = Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofAdmission admission)}

namespace AdmissionEntry

/-- Read the same original indexed admission retained by this fixture entry. -/
private def admission {source : CoefficientPolynomial}
    {result : NonzeroResult source} (entry : AdmissionEntry result) :
    Admission result entry.1 := entry.2.1

/-- Read the actual stored original Sidecar without another attachment or realization. -/
private def sidecar {source : CoefficientPolynomial}
    {result : NonzeroResult source} (entry : AdmissionEntry result) :
    Algebraic.Sidecar entry.admission.channel := entry.2.2.2.val

/-- Read the same admission's retained view accessors without constructing another state bank. -/
private def states {source : CoefficientPolynomial} {result : NonzeroResult source}
    (entry : AdmissionEntry result) : Admission.StateReaders IO entry.admission := entry.2.2.1

/-- Read the same stored admitted root through its actual original algebraic input view.

The complete root getter and source admission identify the same nominal
parent. Only their getter proofs are transported; the actual cached owner
and its shared state-bank reader supply the unchanged requested stage.
-/
private def stateFromInput {source : CoefficientPolynomial} {result : NonzeroResult source}
    (entry : AdmissionEntry result) (original : Sidecar.Compared.RootInput entry.sidecar) (stage : Nat) :
    IO (State original.view.root stage) := by
  let expected := PolynomialRoot.Sidecar.ofAdmission entry.admission
  have found : entry.sidecar.cached.root? = some expected := by
    have same : entry.sidecar = Algebraic.Sidecar.ofRoot expected := entry.2.2.2.property
    rewrite [same]
    rfl
  exact original.stateFromRoot expected found (fun actual same view viewFound stage => by
    have read : (ownerView : CertifiedName.View actual.owner.channel) → actual.owner.view? = some ownerView →
        (stage : Nat) → IO (State ownerView.root stage) := by
      cases same
      exact entry.states
    exact actual.stateFromView read view viewFound stage) stage

end AdmissionEntry

/-- Construct an actual original indexed admission while keeping its full default readback. -/
public abbrev AdmissionBuilder {source : CoefficientPolynomial} (result : NonzeroResult source) :=
  (index : RootIndex result) → (occurrence count : Nat) →
    (consume : (admission : Admission result index) →
      admission = Admission.ofResult result index → Admission.StateReaders IO admission → IO Unit) → IO Unit

/-- Execute one original indexed root request with its complete returned state and chronological history.

The occurrence and request ordinal select separate saved-work directories.
The original result, dependent root index and initial source process remain
fixed through both success callbacks and consecutive requests.
-/
public abbrev PersistentBuilder {source : CoefficientPolynomial} (result : NonzeroResult source) :=
  {initial : Machine.Snapshot} → (index : RootIndex result) → (occurrence requestOrdinal : Nat) →
    (current : RootState result index) → (history : Machine.History initial) →
    history.current.machine = rootMachine result index current →
    history.current.source = (rootMachine result index (rootInitial result index)).mode.process →
    (epsilon : Rational) → (positive : 0 < epsilon) → (count : Nat) →
    (consume : (next : RootState result index) → next = rootRequest result index current epsilon positive count →
      (retained : Machine.History initial) → retained.current.machine = rootMachine result index next →
        retained.current.source =
          (rootMachine result index (rootInitial result index)).mode.process → IO Unit) → IO Unit

/-- Produce one complete original bank and consume its same retained admission constructor.

The callback keeps the actual result, its original isolation equality and its
cache-consuming admission and persistent-request closures together. Both
actions retain the same nominal result and bounded root indices.
-/
public abbrev BankPreparation (request : Option Rational) :=
  (label : String) → (source : CoefficientPolynomial) →
    (consume : (result : NonzeroResult source) →
      (.nonzero result : CCL.Polynomial.Basic.Result source) =
        CCL.Polynomial.Build.isolate source request →
      AdmissionBuilder result → PersistentBuilder result → IO Unit) → IO Unit

/-- Materialize each original indexed admission once and retain its exact original order.

The supplied original admission constructor may consume exact cached states;
its whole-record equation preserves the default owner and channel. The same
Sidecar assembly then consumes the literal admission returned at that index.
-/
private def admissionEntries {source : CoefficientPolynomial}
    (result : NonzeroResult source)
    (count : Nat)
    (admissions : AdmissionBuilder result)
    (consume : List (AdmissionEntry result) → IO Unit) : IO Unit := do
  let rec retain : List (RootIndex result) → Nat → (List (AdmissionEntry result) → IO Unit) → IO Unit
    | [], _, complete => complete []
    | index :: remaining, occurrence, complete =>
        admissions index occurrence count fun admission _same states => do
          let sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofAdmission admission)
          let entry : AdmissionEntry result := ⟨index, admission, states, ⟨sidecar, rfl⟩⟩
          retain remaining (occurrence + 1) fun tail => complete (entry :: tail)
  retain (rootIndices result) 0 consume

/-- Produce and retain the original complete coefficient-generated root result for one displayed nonzero source. -/
private def produceResult (source : CoefficientPolynomial) (request : Option Rational)
    (produce : IO {result : CCL.Polynomial.Basic.Result source //
      result = CCL.Polynomial.Build.isolate source request}) :
    IO {result : NonzeroResult source //
      (.nonzero result : CCL.Polynomial.Basic.Result source) =
        CCL.Polynomial.Build.isolate source request} := do
  let actual ← produce
  match actual with
  | ⟨.zeroNumerator _ _, _⟩ =>
      throw (IO.userError "a displayed nonzero higher-admission source was classified zero")
  | ⟨.nonzero result, same⟩ => pure ⟨result, same⟩

/-- A selected original admission retains its actual comparison and computed agreement with a separate reference.

The comparison owns both complete Sidecars and its actual common-source
preparation. Its agreement equation is obtained only from that stored outcome.
-/
private abbrev AdmissionSelection {source : CoefficientPolynomial} {channel : CoherentNamed}
    (reference : Algebraic.Sidecar channel)
    (result : NonzeroResult source) (firstStart secondStart : Nat) :=
  (entry : AdmissionEntry result) ×
    (compared : Sidecar.Compared reference entry.sidecar firstStart secondStart) ×
      {equivalent : Equivalence.NamedEquivalent channel.name entry.admission.channel.name //
        compared.comparison = .equal equivalent}

/-- Read whether an actual retained original root owner is a coefficient-produced admission. -/
private def admittedOwner : PolynomialRoot.Owner → Bool
  | .admitted _ => true
  | _ => false

/-- Check that an entry consumes the actual higher-admission view and original source multiplicity. -/
private def checkHigherEntry {source : CoefficientPolynomial}
    {result : NonzeroResult source} (entry : AdmissionEntry result)
    (multiplicity : Nat) : IO Unit := do
  unless entry.admission.view?.isSome ∧ entry.sidecar.scalar?.isNone do
    throw (IO.userError "the intended nonlinear admission bypassed its actual retained higher view")
  let some original := entry.sidecar.cached.root? |
    throw (IO.userError "the original admitted Sidecar lost its complete intrinsic root descriptor")
  unless admittedOwner original.owner ∧ original.owner.polynomial.coeffs = source.coeffs ∧
      original.owner.multiplicity = multiplicity ∧ entry.admission.multiplicity = multiplicity do
    throw (IO.userError "the selected higher admission replaced its original source, index or multiplicity")
  let some view := original.view? |
    throw (IO.userError "the stored admitted owner lost its actual original root certificate")
  unless view.polynomial.natDegree ≥ 2 do
    throw (IO.userError "the higher admission was replaced by an exact scalar or linear root")

/-- Execute consecutive persistent requests at the same retained coefficient-produced admission index.

The second request consumes the first complete numerical/cursor state. Exact
word lengths, the previous prefix and nested numerical boxes are checked on
those actual returned values while the original admission remains retained.
-/
private def checkPersistent {source : CoefficientPolynomial} {result : NonzeroResult source}
    (entry : AdmissionEntry result) (occurrence : Nat) (execute : PersistentBuilder result)
    (multiplicity : Nat := 1) (higher : Bool := true) (label : String := "p") : IO Unit := do
  let initial := rootInitial result entry.1
  let machine := rootMachine result entry.1 initial
  let snapshot := Machine.Snapshot.ofFrame (Cursor.Image.Machine.Frame.ofMachine machine)
    (rootState_exact result entry.1 initial).grammar
  let history := Machine.History.start snapshot
  have cursorEq : history.current.machine = machine :=
    congrArg Machine.Snapshot.machine (Machine.History.start_current snapshot)
  have sourceEq : history.current.source = machine.mode.process :=
    congrArg Machine.Snapshot.source (Machine.History.start_current snapshot)
  progress s!"persistent {label}: BEGIN occurrence {occurrence}, first request epsilon one and three bits"
  execute entry.1 occurrence 0 initial history cursorEq sourceEq 1 (by decide) 3
    fun first _firstEq firstHistory firstMachineEq firstSourceEq => do
      let firstWord := rootWord result entry.1 first
      unless firstWord.length = 3 do
        throw (IO.userError "the first original persistent-root request lost its exact additional bit count")
      progress s!"persistent {label}: occurrence {occurrence}, first complete cursor and numerical state retained"
      execute entry.1 occurrence 1 first firstHistory firstMachineEq firstSourceEq (1 / 2) (by decide) 4
        fun second _secondEq secondHistory _secondMachineEq _secondSourceEq => do
          let secondWord := rootWord result entry.1 second
          unless secondWord.length = 7 ∧ secondWord.take firstWord.length = firstWord ∧
              entry.admission.multiplicity = multiplicity ∧
              secondHistory.snapshots.length > firstHistory.snapshots.length do
            throw (IO.userError "the continued persistent-root request lost its prefix, history or multiplicity")
          match rootBox? result entry.1 first, rootBox? result entry.1 second with
          | some firstBox, some secondBox =>
              unless higher ∧ firstBox.diagonalSq ≤ 1 ∧ secondBox.Refines firstBox ∧
                  secondBox.diagonalSq ≤ (1 / 2 : Rational) ^ 2 do
                throw (IO.userError "the original persistent-root request lost its retained numerical payment")
          | none, none =>
              if higher then
                throw (IO.userError "the actual higher persistent-root request replaced its original winding box")
          | _, _ => throw (IO.userError "consecutive root requests changed the original exact/higher site")
          progress s!"persistent {label}: END occurrence {occurrence}, \
            original site, prefix and both numerical requests retained"

/-- Exercise the original coefficient-produced exact root and its repeated-factor site through consecutive requests.

Each bank has one original root index. Its actual admission and persistent
state retain multiplicities one and two while their chronological cursor
histories preserve the three-bit prefix in the seven-bit result.
-/
public def checkExactPersistentAdmissions (prepare : BankPreparation none) : IO Unit := do
  let linear := Power.Gaussian.rootPolynomial 2 ⟨1, by decide⟩
  for (label, source, multiplicity) in [("linear", linear, 1), ("linear-squared", linear * linear, 2)] do
    prepare label source fun result _same admissions execute => do
      let indices := rootIndices result
      unless indices.length = 1 do
        throw (IO.userError "the original exact-source bank lost its one geometric root site")
      for index in indices do
        admissions index 0 0 fun admission _sameAdmission states => do
          unless admission.view?.isNone do
            throw (IO.userError "the original linear factor was replaced by a higher-degree root view")
          let sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofAdmission admission)
          let entry : AdmissionEntry result := ⟨index, admission, states, ⟨sidecar, rfl⟩⟩
          checkPersistent entry 0 execute multiplicity false label

/-- Check short exact prefixes of the same coefficient-produced quadratic admission bank.

The supplied preparation retains the original complete result and its actual
cache-consuming admission reader. Each bounded root index is consumed at
prefix lengths zero, one and three before its actual higher root samples and
coarse same-owner Named comparisons are paid using whole original admission
equality. The explicit tolerance64 keeps this cache-coverage check separate
from productive-name or unit-tolerance payment.
No independent root or productive-name sampling procedure is substituted.
-/
public def checkRetainedPAdmissions (prepare : BankPreparation (some (1 / 256)))
    (persistent : Bool := false) : IO Unit := do
  let tolerance : {value : Rational // 0 < value} := ⟨Data.Rat.Fraction.Cast.fromInt 64, by
    have positive := Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)
    rewrite [Data.Rat.Fraction.Cast.natCast_eq_fromInt 64] at positive
    exact positive⟩
  progress "retained p: BEGIN original produced bank, request 1/256"
  prepare "p" polynomial fun result _same reader execute => do
    let indices := rootIndices result
    unless indices.length = 2 do
      throw (IO.userError "the original retained p bank lost its two dependent root indices")
    let rec check : List (RootIndex result) → Nat → IO Unit
      | [], _ => pure ()
      | index :: remaining, occurrence => do
          progress s!"retained p: BEGIN occurrence {occurrence}, prefixes zero/one/three"
          reader index occurrence 0 fun empty emptyEq _emptyStates => do
            reader index occurrence 1 fun initial initialEq _initialStates => do
              reader index occurrence 3 fun retained retainedEq states => do
                let sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofAdmission retained)
                let entry : AdmissionEntry result := ⟨index, retained, states, ⟨sidecar, rfl⟩⟩
                checkHigherEntry entry 1
                if persistent then checkPersistent entry occurrence execute
                let some emptyView := empty.view? |
                  throw (IO.userError "the original zero-prefix admission lost its higher root")
                let some initialView := initial.view? |
                  throw (IO.userError "the original one-prefix admission lost its higher root")
                let some retainedView := retained.view? |
                  throw (IO.userError "the original three-prefix admission lost its higher root")
                have emptySame : empty = retained := emptyEq.trans retainedEq.symm
                have initialSame : initial = retained := initialEq.trans retainedEq.symm
                let first := retainedView.root.approximation.sample 0
                let later := retainedView.root.approximation.sample 2
                unless emptyView.root.approximation.sample 0 = first ∧
                    initialView.root.approximation.sample 0 = first ∧
                    retained.multiplicity = 1 ∧ empty.multiplicity = 1 ∧ initial.multiplicity = 1 do
                  throw (IO.userError "the original prefix views lost their same-index channel or multiplicity")
                let numerical := retained.numericalResidual
                unless numerical.1.normalize.coeffs = polynomial.normalize.coeffs ∧
                    numerical.2.source.sample 0 = first ∧ numerical.2.source.sample 2 = later do
                  throw (IO.userError "the actual retained numerical residual replaced its original p root samples")
                progress s!"retained p: occurrence {occurrence}, actual cached samples zero/two read"
                let checkViews (first last : Admission result index) (same : first = last) : IO Unit := do
                  have named : first.channel.name = last.channel.name :=
                    congrArg (fun admission : Admission result index => admission.channel.name) same
                  let equivalent : Equivalence.NamedEquivalent first.channel.name last.channel.name :=
                    Equivalence.NamedEquivalent.transport rfl named
                      (Equivalence.NamedEquivalent.refl first.channel.name)
                  checkAgreement equivalent 0 0 tolerance
                unless emptyView.channelEq?.isSome ∧ initialView.channelEq?.isSome ∧
                    retainedView.channelEq?.isSome ∧ emptyView.root.approximation.radiusSq 0 < 1 ∧
                    initialView.root.approximation.radiusSq 0 < 1 ∧
                    retainedView.root.approximation.radiusSq 0 < 1 do
                  throw (IO.userError "the coarse original p name needs an unprepared future root state")
                progress s!"retained p: occurrence {occurrence}, BEGIN coarse same-owner Named payments, target64"
                checkViews empty retained emptySame
                checkViews initial retained initialSame
                progress (s!"retained p: END occurrence {occurrence}, " ++
                  "same original admission and paid coarse same-owner Named evidence")
                check remaining (occurrence + 1)
    check indices 0
  progress "retained p: both original admissions, prefix views and numerical/Named evidence passed"

/-- Select against a separate certified reference only through internally computed finite comparisons.

Each entry is prepared outside this traversal. The continuation receives its
actual original index, admission, Sidecar and complete successful comparison.
Other branch comparisons supply no caller success or nesting assumption.
-/
private def selectAdmission {source : CoefficientPolynomial} {channel : CoherentNamed}
    (reference : Algebraic.Sidecar channel)
    {result : NonzeroResult source} (firstStart secondStart : Nat)
    (consume : AdmissionSelection reference result firstStart secondStart → IO Unit) :
    List (AdmissionEntry result) → (attempt : Nat := 0) →
      (run : (attempt : Nat) → (entry : AdmissionEntry result) →
        ({value : Sidecar.Compared reference entry.sidecar firstStart secondStart //
          value = reference.compare entry.sidecar firstStart secondStart} → IO Unit) → IO Unit :=
        fun _ entry use => use ⟨reference.compare entry.sidecar firstStart secondStart, rfl⟩) → IO Unit
  | [], _, _ =>
      throw (IO.userError "the original produced admission bank did not match its separate certified reference")
  | entry :: remaining, attempt, run => do
      progress s!"admission selection: attempt {attempt}, starts {firstStart}/{secondStart}; BEGIN original views"
      let firstView := reference.cached.root?.bind (fun root => root.view?)
      let secondView := entry.sidecar.cached.root?.bind (fun root => root.view?)
      match firstView, secondView with
      | some first, some second =>
          let samePolynomial := decide (first.polynomial = second.polynomial)
          let sameAmbient := decide (first.ambient.xLower = second.ambient.xLower) &&
            decide (first.ambient.xUpper = second.ambient.xUpper) &&
            decide (first.ambient.yLower = second.ambient.yLower) &&
            decide (first.ambient.yUpper = second.ambient.yUpper)
          let nested := decide (second.track.initial.box.StrictInterior first.track.initial.box)
          let reverseNested := decide (first.track.initial.box.StrictInterior second.track.initial.box)
          let separated := decide (first.track.initial.box.Separated second.track.initial.box)
          progress s!"admission selection: same polynomial {samePolynomial}, ambient {sameAmbient}"
          progress s!"admission selection: nested {nested}, reverse {reverseNested}, separated {separated}"
          progress s!"admission selection: genuine left channel identity {first.channelEq?.isSome}"
          progress s!"admission selection: genuine right channel identity {second.channelEq?.isSome}"
      | _, _ => progress "admission selection: an original root view is unavailable"
      progress "admission selection: BEGIN actual original Sidecar.compare/cache demand"
      run attempt entry fun retained => do
        let compared := retained.val
        match compared.cache with
        | .inr _ => throw (IO.userError "higher-admission selection forced the generic full difference")
        | .inl _ => progress "admission selection: original intrinsic cache returned"
        progress "admission selection: BEGIN retained actual outcome demand"
        match selected : compared.comparison with
        | .equal equivalent =>
            progress "admission selection: actual equal outcome returned"
            consume ⟨entry, compared, ⟨equivalent, selected⟩⟩
        | .distinct _ _ =>
            progress "admission selection: actual distinct outcome returned"
            selectAdmission reference firstStart secondStart consume remaining (attempt + 1) run

/-- Inspect the same stored common-source preparation and both original admitted source parents. -/
private def checkCommonSource {first second : CoherentNamed} {left : Algebraic.Sidecar first}
    {right : Algebraic.Sidecar second} {firstStart secondStart : Nat}
    (compared : Sidecar.Compared left right firstStart secondStart)
    (leftSource rightSource : CoefficientPolynomial) (leftMultiplicity rightMultiplicity degree : Nat) : IO Unit :=
  match compared.cache with
  | .inr _ => throw (IO.userError "the actual higher admissions forced generic full difference elimination")
  | .inl intrinsic => do
      unless admittedOwner intrinsic.left.root.owner ∧ admittedOwner intrinsic.right.root.owner ∧
          intrinsic.left.root.owner.polynomial.coeffs = leftSource.coeffs ∧
          intrinsic.right.root.owner.polynomial.coeffs = rightSource.coeffs ∧
          intrinsic.left.root.owner.multiplicity = leftMultiplicity ∧
          intrinsic.right.root.owner.multiplicity = rightMultiplicity ∧
          intrinsic.prepared.algebra.polynomial.natDegree = degree do
        throw (IO.userError "comparison discarded an original admitted parent, multiplicity or computed common source")

/-- Pay the stored distinct-root request and inspect its original-channel difference preparation. -/
private def checkDistinctComparison {first second : CoherentNamed} {left : Algebraic.Sidecar first}
    {right : Algebraic.Sidecar second} {firstStart secondStart : Nat}
    (compared : Sidecar.Compared left right firstStart secondStart)
    (readers : Option
      (((original : Sidecar.Compared.RootInput left) → (stage : Nat) → IO (State original.view.root stage)) ×
        ((original : Sidecar.Compared.RootInput right) →
          (stage : Nat) → IO (State original.view.root stage))) :=
      none) : IO Unit := do
  match compared.cache with
  | .inr _ => throw (IO.userError "the actual distinct higher admissions forced generic difference elimination")
  | .inl intrinsic =>
      match intrinsic.prepared.comparison with
      | .equal _ => throw (IO.userError "the actual root-three and quadratic admissions were equated")
      | .distinct separation =>
          let gap := separation.separation.gap
          let read : IO (Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical) := match readers with
            | none => pure (intrinsic.left.view.root.approximation.sample separation.leftIndex,
                intrinsic.right.view.root.approximation.sample separation.rightIndex)
            | some (left, right) => do
                let first ← left intrinsic.left separation.leftIndex
                let second ← right intrinsic.right separation.rightIndex
                return (first.val.box.anchor, second.val.box.anchor)
          let samples ← read
          let firstSample := samples.1
          let secondSample := samples.2
          unless separation.leftRequestStart ≥ firstStart ∧ separation.rightRequestStart ≥ secondStart ∧
              separation.leftIndex ≥ separation.leftRequestStart ∧
              separation.rightIndex ≥ separation.rightRequestStart ∧ gap > 0 ∧
              gap ^ 2 ≤ Norm.Basic.normSq (firstSample - secondSample) do
            throw (IO.userError "the actual distinct admitted roots lost their paid cache reads or positive gap")
          match compared.decision with
          | .excluded _ =>
              throw (IO.userError "actual distinct admitted roots lost their original difference preparation")
          | .prepared prepared =>
              unless prepared.apart.certificate.lowerSq = gap ^ 2 / 8 do
                throw (IO.userError "the original admitted difference did not retain the same computed root gap")
  unless !comparisonEqual compared.comparison do
    throw (IO.userError "the actual distinct higher-admission outcome was replaced")

/-- Exercise higher-admission comparison on actual once-produced polynomial banks and separate certified references.

Each displayed source is isolated once for its own original result/attachment
indices. These banks are separate from the standalone reference tracks. The
actual admitted Sidecars then compare through one retained common source per
pair, including multiplicity two, before an explicit repeated full demand.
An optional producer must identify its complete result with the original
coefficient-first constructor for the actual optional request; checked cold
replay therefore keeps exactly those source parents and indices. None retains
the original producer; an opt-in result supplies its own actual admission owners.
-/
public def checkHigherAdmissions
    (request : Option Rational := none)
    (produce : String → (source : CoefficientPolynomial) →
      IO {result : CCL.Polynomial.Basic.Result source //
        result = CCL.Polynomial.Build.isolate source request} :=
      fun _ source => pure ⟨CCL.Polynomial.Build.isolate source request, rfl⟩)
    (admissions : (label : String) → (source : CoefficientPolynomial) → (result : NonzeroResult source) →
      (.nonzero result : CCL.Polynomial.Basic.Result source) =
        CCL.Polynomial.Build.isolate source request →
      (index : RootIndex result) → (occurrence count : Nat) →
      (consume : (admission : Admission result index) →
        admission = Admission.ofResult result index → Admission.StateReaders IO admission → IO Unit) → IO Unit :=
      fun _ _ result _ index _ _ consume => consume (Admission.ofResult result index) rfl
        (fun view _ stage => pure ⟨view.root.stateAt stage, rfl⟩))
    (prepare : Option (BankPreparation request) := none)
    (comparisons : Option (ClearanceCheckpoint.Control IO × WindingCheckpoint.Control IO × System.FilePath) := none) :
    IO Unit := do
  let withBank (label : String) (source : CoefficientPolynomial) (count : Nat)
      (use : (result : NonzeroResult source) → List (AdmissionEntry result) → IO Unit) : IO Unit := do
    match prepare with
    | none =>
        let produced ← produceResult source request (produce label source)
        admissionEntries produced.val count
          (admissions label source produced.val produced.property) (fun entries => use produced.val entries)
    | some prepared =>
        prepared label source fun result _same reader _execute =>
          admissionEntries result count reader (fun entries => use result entries)
  let pStart : Nat := 2
  let qStart : Nat := 1
  let threeStart : Nat := 3
  let squaredStart : Nat := 3
  progress "higher admissions: construct/store original p=x^2-2 produced bank"
  withBank "p" polynomial (pStart + 1) fun pResult pEntries => do
    unless pEntries.length = 2 do
      throw (IO.userError "the original quadratic produced bank lost its two dependent root indices")
    progress "higher admissions: original p result, dependent indices and actual admissions retained"
    progress "higher admissions: construct/store original q=(x^2-2)(x-3) produced bank"
    withBank "q" expandedPolynomial (max qStart threeStart + 1) fun qResult qEntries => do
      unless qEntries.length = 3 do
        throw (IO.userError "the original cubic produced bank lost its three dependent root indices")
      progress "higher admissions: original q result, dependent indices and actual admissions retained"
      progress "higher admissions: construct/store original p^2 produced bank with multiplicity two"
      withBank "p-squared" repeated (squaredStart + 1) fun squaredResult squaredEntries => do
        unless squaredEntries.length = 2 do
          throw (IO.userError "the original repeated-source bank duplicated its geometric root sites")
        progress "higher admissions: original p^2 result, dependent indices and actual admissions retained"
        let qSite := expandedSite ⟨0, by decide⟩
        let threeSite := expandedSite ⟨1, by decide⟩
        let qRealization := Site.Realization.ofInput qSite
        let threeRealization := Site.Realization.ofInput threeSite
        let referenceP := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization first)
        let referenceQ := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization qRealization)
        let referenceThree := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofRealization threeRealization)
        let referenceStates :
            ((stage : Nat) → IO (State first.root stage)) ×
            ((stage : Nat) → IO (State qRealization.root stage)) ×
            ((stage : Nat) → IO (State threeRealization.root stage)) ← match comparisons with
          | none => pure (
              (fun stage => pure ⟨first.root.stateAt stage, rfl⟩),
                (fun stage => pure ⟨qRealization.root.stateAt stage, rfl⟩),
                fun stage => pure ⟨threeRealization.root.stateAt stage, rfl⟩)
          | some (columns, winding, directory) => do
              let pElimination : Thunk (FTA.Squarefree.Input.Elimination focusedInput) := Thunk.mk fun _ =>
                FTA.Squarefree.Input.Elimination.ofCertificate focusedInput elimination rfl
              let qElimination : Thunk (FTA.Squarefree.Input.Elimination expandedFocusedInput) := Thunk.mk fun _ =>
                FTA.Squarefree.Input.Elimination.ofCertificate expandedFocusedInput expandedElimination rfl
              let pStates ← stateReader (track := firstSite.track) first.root
                (readStateWith (track := firstSite.track) first.root
                (nextState (track := firstSite.track) first.root focusedInput pElimination
                  firstSite_refine columns winding
                  (join directory "reference-p")))
              let qStates ← stateReader (track := qSite.track) qRealization.root
                (readStateWith (track := qSite.track) qRealization.root
                (nextState (track := qSite.track) qRealization.root expandedFocusedInput qElimination
                  (expandedSite_refine ⟨0, by decide⟩)
                  columns winding (join directory "reference-q-equal")))
              let threeStates ← stateReader (track := threeSite.track) threeRealization.root
                (readStateWith (track := threeSite.track) threeRealization.root
                (nextState (track := threeSite.track) threeRealization.root expandedFocusedInput qElimination
                  (expandedSite_refine ⟨1, by decide⟩)
                  columns winding (join directory "reference-q-three")))
              pure (pStates, qStates, threeStates)
        let selectP {otherSource : CoefficientPolynomial} {otherResult : NonzeroResult otherSource}
            (leftStart rightStart : Nat)
            (use : AdmissionSelection referenceP otherResult leftStart rightStart → IO Unit)
            (entries : List (AdmissionEntry otherResult)) : IO Unit :=
          selectAdmission referenceP leftStart rightStart use entries
            (run := fun attempt entry => compareSidecars referenceP (realizationInputState first referenceStates.1)
              leftStart rightStart comparisons s!"select-p-{leftStart}-{rightStart}/attempt-{attempt}"
              entry.sidecar entry.stateFromInput)
        let selectQ (use : AdmissionSelection referenceQ qResult 2 qStart → IO Unit) : IO Unit :=
          selectAdmission referenceQ 2 qStart use qEntries
            (run := fun attempt entry => compareSidecars referenceQ
              (realizationInputState qRealization referenceStates.2.1) 2 qStart comparisons
              s!"select-q/attempt-{attempt}" entry.sidecar entry.stateFromInput)
        let selectThree (use : AdmissionSelection referenceThree qResult 1 threeStart → IO Unit) : IO Unit :=
          selectAdmission referenceThree 1 threeStart use qEntries
            (run := fun attempt entry => compareSidecars referenceThree
              (realizationInputState threeRealization referenceStates.2.2) 1 threeStart comparisons
              s!"select-three/attempt-{attempt}" entry.sidecar entry.stateFromInput)
        progress "higher admissions: select actual indexed admissions against the separate certified reference sites"
        selectP 1 pStart (fun selectedP =>
          selectQ (fun selectedQ =>
            selectThree (fun selectedThree =>
              selectP 2 squaredStart (fun selectedSquared => do
                let left := selectedP.1
                let right := selectedQ.1
                let three := selectedThree.1
                let squared := selectedSquared.1
                checkHigherEntry left 1
                checkHigherEntry right 1
                checkHigherEntry three 1
                checkHigherEntry squared 2
                checkComparedAgreement selectedP.2.1 selectedP.2.2.val 2 3
                  (comparisons.map fun _ inputs =>
                    pure (realizationInputState first referenceStates.1 inputs.1, left.stateFromInput inputs.2))
                checkComparedAgreement selectedQ.2.1 selectedQ.2.2.val 3 2
                  (comparisons.map fun _ inputs =>
                    pure (realizationInputState qRealization referenceStates.2.1 inputs.1,
                      right.stateFromInput inputs.2))
                checkComparedAgreement selectedThree.2.1 selectedThree.2.2.val 1 2
                  (comparisons.map fun _ inputs =>
                    pure (realizationInputState threeRealization referenceStates.2.2 inputs.1,
                      three.stateFromInput inputs.2))
                checkComparedAgreement selectedSquared.2.1 selectedSquared.2.2.val 2 1
                  (comparisons.map fun _ inputs =>
                    pure (realizationInputState first referenceStates.1 inputs.1, squared.stateFromInput inputs.2))
                progress "higher admissions: compare original p/q admitted Sidecars without a supplied equality"
                compareSidecars left.sidecar left.stateFromInput 2 3 comparisons "p-q"
                    right.sidecar right.stateFromInput fun retainedSame => do
                  let same := retainedSame.val
                  checkCommonSource same polynomial expandedPolynomial 1 1 3
                  checkEqualComparison same 3 4
                    (comparisons.map fun _ inputs =>
                      pure (left.stateFromInput inputs.1, right.stateFromInput inputs.2))
                  progress
                    "higher admissions: compare original p/p^2 admitted Sidecars and retain multiplicities one/two"
                  compareSidecars left.sidecar left.stateFromInput 1 2 comparisons "p-p-squared"
                      squared.sidecar squared.stateFromInput fun retainedMultiplicities => do
                    let multiplicities := retainedMultiplicities.val
                    checkCommonSource multiplicities polynomial repeated 1 2 2
                    checkEqualComparison multiplicities 2 3
                      (comparisons.map fun _ inputs =>
                        pure (left.stateFromInput inputs.1, squared.stateFromInput inputs.2))
                    progress
                      "higher admissions: compare actual cubic root three with the original admitted quadratic root"
                    compareSidecars three.sidecar three.stateFromInput 3 2 comparisons "q-three-p"
                        left.sidecar left.stateFromInput fun retainedDifferent => do
                      let different := retainedDifferent.val
                      checkCommonSource different expandedPolynomial polynomial 1 1 3
                      checkDistinctComparison different
                        (comparisons.map fun _ => (three.stateFromInput, left.stateFromInput))
                      progress
                        "higher admissions: all intrinsic requests paid BEFORE explicit full p/q difference demand"
                      let full := same.materialize
                      unless comparisonEqual full.comparison ∧ !full.decision.isPrepared ∧
                          full.difference.polynomial.natDegree > 0 do
                        throw (IO.userError
                          "explicit full admitted comparison lost its original difference/decision result")
                      progress
                        ("higher admissions: first actual full difference demand returned; " ++
                          "force the SAME stored thunk again")
                      let reused := same.materialize
                      unless comparisonEqual reused.comparison ∧ !reused.decision.isPrepared ∧
                          reused.difference.polynomial.coeffs = full.difference.polynomial.coeffs ∧
                          reused.difference.residual.source.sample 0 = full.difference.residual.source.sample 0 do
                        throw (IO.userError
                          "the same retained admitted comparison lost its repeated full materialization")
                      progress
                        "higher admissions: original indices/parents, higher views, multiplicities \
                          and explicit full reuse retained"
              ) squaredEntries
            )
          )
        ) pEntries

end TestPurelib.Approximation.Gaussian.MultiplicityAdmission

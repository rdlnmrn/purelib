module
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Separation
import Purelib.Polynomial.Approximation.Gaussian.Localization

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reality
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Base
import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Computation.Query.History
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Multivariate.Gaussian.Division
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Polynomial.Multivariate.Gaussian.Inverse
import Purelib.Polynomial.Multivariate.PowerReduction
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Root
import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Conjugate
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Dispatch
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.LinearAlgebra.PolynomialMatrix.Pencil
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Approximation.Gaussian.Residual.Conjugation
import Purelib.Polynomial.Approximation.Gaussian.Residual.Power
import Purelib.Polynomial.Approximation.Gaussian.Residual.Origin
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Rational.Bezout.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.System.IO
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import TestPurelib.Polynomial.MultivariateDenotation
import scripts.checkpoint.CoherentRootSamples
import scripts.checkpoint.RootSelection
import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Riemann.RootContinuation.CoherentRoot.Accelerated
import scripts.checkpoint.Integration
import Purelib.System.FilePath
import Purelib.Approximation.Gaussian.Sequence.Process
import TestPurelib.Polynomial.Dense.Gaussian.Path.Pair
import TestPurelib.Polynomial.Dense.Gaussian.Factorization.Origin
import TestPurelib.Approximation.Gaussian.AlgebraicConstruction
import TestPurelib.Riemann.RootStateCache

/-! # Original complex cubic owner and its distinct derived conjugate branch -/

namespace TestPurelib.Approximation.Gaussian.CubicSheets

open TestPurelib.Riemann
open Purelib
open Purelib.Polynomial
open Purelib.Computation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Process.Imaginary
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Geometry.Rational (Box)
open IntegrationCheckpoint (gaussianData fractionData loadJson saveJson)
open CoherentRootCheckpoint (State stateReader readStateWith nextState namedSampleWithStates)
open CoherentRoot (CertifiedName WindingOneTrack)
open Purelib.Data.Json (toJson)
open Purelib.System.FilePath (join)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Box

/-- The actual original coefficient table for the nonrational cubic root. -/
private def polynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩

/-- The small rational upper-half-plane box of the original nonreal cubic branch. -/
private def ambient : Box := ⟨-11 / 16, -9 / 16, 1, 9 / 8, by decide +kernel, by decide +kernel⟩

/-- The original cubic coefficient table supplies its finite squarefree and positive-degree input. -/
private def input : Input polynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨3, by decide⟩
  degreeAtLeastTwo := by
    unfold polynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The existing generic coefficient-derived axis certificate of the same original local polynomial. -/
private def elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  polynomial input.nonzero input.degreePositive

/-- The actual retained clear left line, from its original small coordinate-polynomial Euclidean certificate. -/
private def left := Line.Bezout.verticalOfCoprime polynomial ambient ambient.xLower
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.verticalPathReal polynomial ambient.xLower)
    (Path.Axis.verticalPathImag polynomial ambient.xLower) (by decide +kernel) (by decide +kernel))

/-- The actual retained clear right line, from its original small coordinate-polynomial Euclidean certificate. -/
private def right := Line.Bezout.verticalOfCoprime polynomial ambient ambient.xUpper
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.verticalPathReal polynomial ambient.xUpper)
    (Path.Axis.verticalPathImag polynomial ambient.xUpper) (by decide +kernel) (by decide +kernel))

/-- The actual retained clear bottom line, from its original small coordinate-polynomial Euclidean certificate. -/
private def bottom := Line.Bezout.horizontalOfCoprime polynomial ambient ambient.yLower
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.horizontalPathReal polynomial ambient.yLower)
    (Path.Axis.horizontalPathImag polynomial ambient.yLower) (by decide +kernel) (by decide +kernel))

/-- The actual retained clear top line, from its original small coordinate-polynomial Euclidean certificate. -/
private def top := Line.Bezout.horizontalOfCoprime polynomial ambient ambient.yUpper
  (Dense.Rational.Bezout.certificateOfConstantGCD
    (Path.Axis.horizontalPathReal polynomial ambient.yUpper)
    (Path.Axis.horizontalPathImag polynomial ambient.yUpper) (by decide +kernel) (by decide +kernel))

/-- The kernel-checked local winding-one state retaining all four original line clearances. -/
private def initial : State.WindingOne.Basic.WindingOneState polynomial ambient where
  box := ambient
  refinesAmbient := Box.refines_refl ambient
  proper := by constructor <;> decide
  clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
  rawWindingFour := by decide +kernel
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

/-- The existing total original Newton track starts from the same checked local winding-one state. -/
private def track := Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination initial

/-- The original local root name retains that same polynomial, track and actual numerical root-state cache. -/
private def root := CoherentRoot.certifiedName track input.degreePositive

/-- The actual original local winding owner supplies an intrinsic general algebraic root admission. -/
private def sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root input.toPositive)

/-- The independent original lower-half-plane winding owner's rational box. -/
private def lowerAmbient : Box := ⟨-11 / 16, -9 / 16, -9 / 8, -1, by decide +kernel, by decide +kernel⟩

/-- The independent original lower winding-one state retains its own four exact boundary clearances. -/
private def lowerInitial : State.WindingOne.Basic.WindingOneState polynomial lowerAmbient :=
  let left := Line.Bezout.verticalOfCoprime polynomial lowerAmbient lowerAmbient.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial lowerAmbient.xLower)
      (Path.Axis.verticalPathImag polynomial lowerAmbient.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime polynomial lowerAmbient lowerAmbient.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial lowerAmbient.xUpper)
      (Path.Axis.verticalPathImag polynomial lowerAmbient.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime polynomial lowerAmbient lowerAmbient.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial lowerAmbient.yLower)
      (Path.Axis.horizontalPathImag polynomial lowerAmbient.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime polynomial lowerAmbient lowerAmbient.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial lowerAmbient.yUpper)
      (Path.Axis.horizontalPathImag polynomial lowerAmbient.yUpper)
      (by decide +kernel) (by decide +kernel))
  { box := lowerAmbient
    refinesAmbient := Box.refines_refl lowerAmbient
    proper := by constructor <;> decide
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The independent lower owner uses the original polynomial and its own original Newton track and numerical cache. -/
private def lowerRoot := CoherentRoot.certifiedName
  (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination lowerInitial) input.degreePositive

/-- The independent lower winding owner supplies its own unchanged original general root channel and residual. -/
private def lowerSidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive)

/-- The original cubic owner and its retained residual have no monic-linear scalar reading. -/
private theorem cubicScalarNone {ambient : Box} {track : WindingOneTrack polynomial ambient}
    (original : CertifiedName track) :
    (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated original input.toPositive)).scalar? = none := by
  let isolated := PolynomialRoot.Sidecar.ofIsolated original input.toPositive
  have degree : polynomial.natDegree ≠ 1 := by
    unfold polynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide +kernel
  have noOwner : isolated.scalar? = none := by
    dsimp only [isolated, PolynomialRoot.Sidecar.scalar?, PolynomialRoot.Sidecar.ofIsolated,
      PolynomialRoot.Owner.scalar?]
    rewrite [dif_neg degree]
    rfl
  have noResidual : isolated.residualCertificate.2.scalar? = none :=
    Polynomial.Approximation.Gaussian.Residual.scalar?_of_degree_ne_one _ (by
      rewrite [PolynomialRoot.Sidecar.ofIsolated_residual_polynomial]
      exact degree)
  change (match isolated.scalar? with
    | some reading => some reading
    | none => isolated.residualCertificate.2.scalar?) = none
  rewrite [noOwner, noResidual]
  rfl

/-- Run one bounded word tick at the original admitted nonquadratic cubic root. -/
public def checkBoundedWord : IO Unit := do
  let _nonScalar := cubicScalarNone root
  let word := [Purelib.LinearAlgebra.Matrix.Multiplication.identity]
  let cursor := Fold.Algebraic.Cursor.initial sidecar word
  let work := Fold.Algebraic.Execution.Work.active cursor
  match (Fold.Algebraic.Execution.attempt work 1).val.val with
  | (0, .exhausted _ _ _ _) => pure ()
  | _ => throw (IO.userError "one cubic word tick did not retain its unfinished original work")

/-- The original upper root's initial box lies strictly above the real axis. -/
private theorem upperBoxAbove : 0 < track.initial.box.yLower := by
  change (0 : Rational) < 1
  decide +kernel

/-- The independent lower root's original initial box lies strictly below the real axis. -/
private theorem lowerBoxBelow :
    (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination lowerInitial).initial.box.yUpper <
      0 := by
  change (-1 : Rational) < 0
  decide +kernel

/-- The independent lower root's initial box also fails the upper-half-plane test. -/
private theorem lowerBoxNotAbove :
    ¬ 0 < (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree
      elimination lowerInitial).initial.box.yLower := by
  change ¬ (0 : Rational) < -9 / 8
  decide +kernel

example : Separation.inspectRootBox track = .above upperBoxAbove :=
  Separation.inspectRootBox_above track upperBoxAbove

example : Separation.inspectRootBox
    (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination lowerInitial) =
      .below lowerBoxNotAbove lowerBoxBelow :=
  Separation.inspectRootBox_below _ lowerBoxNotAbove lowerBoxBelow

example {value : Canonical} (possible : root.value.name.process.Possible root.value.name.state value) :
    (1 : Rational) ^ 2 ≤ value.im ^ 2 := by
  have bound := (Separation.ofRootAbove root upperBoxAbove).squared_lower possible
  change (1 : Rational) ^ 2 ≤ value.im ^ 2 at bound
  exact bound

example {value : Canonical} (possible : lowerRoot.value.name.process.Possible lowerRoot.value.name.state value) :
    (1 : Rational) ^ 2 ≤ value.im ^ 2 := by
  have bound := (Separation.ofRootBelow lowerRoot lowerBoxBelow).squared_lower possible
  change (1 : Rational) ^ 2 ≤ value.im ^ 2 at bound
  exact bound

example (prepared : Division.Prepared (Separation.conjugateDifference root.value))
    {value : Canonical} (possible : root.value.name.process.Possible
      (Separation.ofConjugatePrepared prepared).2.val.state value) :
    (Separation.ofConjugatePrepared prepared).2.val.gap ^ 2 ≤ value.im ^ 2 :=
  (Separation.ofConjugatePrepared prepared).2.val.squared_lower possible

/-- The root view obtained from the retained upper owner, including its original transport. -/
private def upperView := (CertifiedName.View.ofRoot root input.toPositive).transport
  (Equivalence.NamedEquivalent.refl _) (some ⟨rfl⟩)

/-- The retained upper owner projects precisely its original root view. -/
private theorem upperViewFound :
    (PolynomialRoot.Sidecar.ofIsolated root input.toPositive).view? = some upperView := rfl

/-- The provider inspection retains the same upper view and its positive original box. -/
private theorem upperInspection :
    Provenance.inspectRoot (PolynomialRoot.Sidecar.ofIsolated root input.toPositive) =
      .inr ⟨⟨upperView, upperViewFound⟩, .above upperBoxAbove⟩ := by
  change (.inr ⟨⟨upperView, upperViewFound⟩, Separation.inspectRootBox track⟩ :
    Provenance.RootInspection (PolynomialRoot.Sidecar.ofIsolated root input.toPositive)) = _
  rewrite [Separation.inspectRootBox_above track upperBoxAbove]
  rfl

example : ∃ provider, Provenance.infer (some (.algebraic sidecar)) = .provider provider := by
  have prepared : ∃ provider, Provenance.inspectedRootProvider
      (PolynomialRoot.Sidecar.ofIsolated root input.toPositive) = .inl provider := by
    cases selected : Provenance.inspectedRootProvider
        (PolynomialRoot.Sidecar.ofIsolated root input.toPositive) with
    | inl provider => exact ⟨provider, rfl⟩
    | inr reason =>
      have unresolved := reason.property.2
      have same := reason.property.1.trans upperInspection
      rewrite [same] at unresolved
      exact False.elim unresolved
  obtain ⟨provider, selected⟩ := prepared
  exact ⟨provider, Provenance.infer_algebraic_rootProvider sidecar (cubicScalarNone root)
    (PolynomialRoot.Sidecar.ofIsolated root input.toPositive) rfl provider selected⟩

/-- The lower owner projects its own original root view and channel transport. -/
private def lowerView := (CertifiedName.View.ofRoot lowerRoot input.toPositive).transport
  (Equivalence.NamedEquivalent.refl _) (some ⟨rfl⟩)

/-- The retained lower owner projects precisely its independent root view. -/
private theorem lowerViewFound :
    (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive).view? = some lowerView := rfl

/-- The provider inspection retains the lower view and its negative original box. -/
private theorem lowerInspection :
    Provenance.inspectRoot (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive) =
      .inr ⟨⟨lowerView, lowerViewFound⟩, .below lowerBoxNotAbove lowerBoxBelow⟩ := by
  change (.inr ⟨⟨lowerView, lowerViewFound⟩, Separation.inspectRootBox
    (Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree elimination lowerInitial)⟩ :
      Provenance.RootInspection (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive)) = _
  rewrite [Separation.inspectRootBox_below _ lowerBoxNotAbove lowerBoxBelow]
  rfl

example : ∃ provider, Provenance.infer (some (.algebraic lowerSidecar)) = .provider provider := by
  have prepared : ∃ provider, Provenance.inspectedRootProvider
      (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive) = .inl provider := by
    cases selected : Provenance.inspectedRootProvider
        (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive) with
    | inl provider => exact ⟨provider, rfl⟩
    | inr reason =>
      have unresolved := reason.property.2
      have same := reason.property.1.trans lowerInspection
      rewrite [same] at unresolved
      exact False.elim unresolved
  obtain ⟨provider, selected⟩ := prepared
  exact ⟨provider, Provenance.infer_algebraic_rootProvider lowerSidecar (cubicScalarNone lowerRoot)
    (PolynomialRoot.Sidecar.ofIsolated lowerRoot input.toPositive) rfl provider selected⟩

/-- The input annotation keeps the exact original local root channel without performing arithmetic sidecar work. -/
private def environment : Fin 1 → Annotated := fun _ => Annotated.opaque root.value

/-- Print and flush one native original-owner construction checkpoint. -/
private def progress (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Every actual retained original upper-root observation has imaginary coordinate at least one. -/
private theorem upper_sign (index : Nat) : 1 ≤ (root.approximation.sample index).im :=
  (root.sample_initial_inside index).2.2.1

/-- The actual conjugation residual reads the conjugate of that same retained original root-cache observation. -/
private theorem conjugate_sample (index : Nat) :
    sidecar.conj.residual.source.sample index = (root.approximation.sample index).conj := by
  change sidecar.residual.conj.source.sample index = _
  rewrite [Polynomial.Approximation.Gaussian.Residual.conj_sample]
  exact congrArg Data.Gaussian.Basic.conj
    (PolynomialRoot.Sidecar.ofIsolated_residual_sample root input.toPositive index)

/-- Every actual retained derived conjugate observation has imaginary coordinate at most minus one. -/
private theorem lower_sign (index : Nat) : (sidecar.conj.residual.source.sample index).im ≤ -1 := by
  rewrite [conjugate_sample]
  change -(root.approximation.sample index).im ≤ -(1 : Data.Rat.Fraction.Rational)
  exact Data.Rat.Fraction.Order.Arithmetic.neg_le_neg_direct (upper_sign index)

/-- Check the retained original upper root's exact cache-reader control without producing a refinement. -/
public def checkInitialCache : IO Unit := do
  RootStateCache.checkSeededReader root
  progress "cubic sheets: supplied completed state bank retained across repeated replay reads"
  RootStateCache.checkSidecarReaderFailure root input
  progress "cubic sheets: original algebraic comparison preserves bank-loader failure and skips all later requests"
  RootStateCache.checkGlobalPreparationFailure root input
  progress "cubic sheets: original global preparation preserves source-loader failure and skips later reads"
  RootStateCache.checkInitialHits root
  RootStateCache.checkNamedInitial root 2 (by decide +kernel) input.toPositive
  RootStateCache.checkNamedReaderFailure root 6 input.toPositive
  progress "cubic sheets: original named indices reuse primitive states and preserve reader failures"
  have valueEq : polynomial.eval (-1) = -3 := by
    unfold polynomial
    exact (Power.Gaussian.rootPolynomial_eval 2 (-1) ⟨3, by decide⟩).trans (by decide +kernel)
  RootStateCache.checkPointReaderFailure root (-1) (-3) valueEq (by decide +kernel) 3
  let cofactor : CoherentRoot.GaussianPolynomial := Dense.Basic.DensePolynomial.constant 1
  let coprime := Coprime.Operations.CoprimeCertificate.constantRight input.nonzero
  have factorization : Factorization.Identity.ProductIdentity polynomial polynomial cofactor := by decide +kernel
  let requested : CoherentRoot.FactorRegion.LocalCofactor cofactor track.initial.box :=
    .inl ⟨1, ⟨by decide +kernel, by decide +kernel⟩⟩
  RootStateCache.checkSourceRegion root polynomial cofactor input.nonzero factorization coprime requested
  progress "cubic sheets: complete cached source region and original global-reader failure preserved"
  progress "cubic sheets: original point-separation maximum-stage request and reader failure preserved"
  progress "cubic sheets: original initial cache and exact successor-reader failure preserved"

/-- Admit the actual upper cubic owner, retain its conjugation operation and compare the distinct original channels. -/
public def check : IO Unit := do
  checkInitialCache
  progress "cubic sheets: original initial state repeated hits and missing successor retain the same cache"
  progress "cubic sheets: retain original upper winding owner and its actual conjugation channel"
  let observed := root.approximation.sample 0
  unless observed.im ≥ 1 ∧ (sidecar.conj.residual.source.sample 0).im ≤ -1 do
    throw (IO.userError "the actual original cubic branch observations violate their retained sign certificates")
  let _upperSign := upper_sign
  let _lowerSign := lower_sign
  let atom := Admitted.atom environment ⟨0, by decide⟩ sidecar
  match atom.run with
  | .completed upper =>
      let upper := upper.materialize
      TestPurelib.Approximation.Gaussian.AlgebraicConstruction.checkZeroPower upper.sidecar (upper.sidecar.pow 0)
      TestPurelib.Approximation.Gaussian.AlgebraicConstruction.checkZeroPower upper.sidecar (upper.pow 0).sidecar
      progress "cubic sheets: zero power retained its original opaque root and constant-one program"
      let lower := upper.conj
      progress "cubic sheets: original checked construction retained the actual conjugation operation"
      let same := upper.sidecar.compareInitial upper.sidecar
      match same.outcome with
      | .distinct _ _ _ _ _ => throw (IO.userError "the original self-difference was incorrectly separated")
      | .inconclusive _ _ => progress "cubic sheets: original self-difference retains its typed finite obligation"
      let compared := upper.sidecar.compareInitial lower.sidecar
      match compared.outcome with
      | .inconclusive _ _ =>
          throw (IO.userError "the original conjugate cubic difference has a finite separation obligation")
      | .distinct _ prepared _ _ different =>
          let _apart := prepared
          let _different := different
          let originalDifference := compared.initial.ball.center
          unless normSq originalDifference > 0 do
            throw (IO.userError "the actual retained original cubic difference lost its positive head")
          progress "cubic sheets: actual original difference and computed separation prove distinctness"
          let cube := lower.pow 3
          let reading := cube.sidecar.scalar?
          if present : reading.isSome then
            unless (reading.get present).value = 2 do
              throw (IO.userError "the retained conjugate cubic power equation was read incorrectly")
            progress "cubic sheets: original conjugated branch cube retains exact reading two"
          else throw (IO.userError "the original conjugate branch lost its checked cubic equation")
  | _ => throw (IO.userError "the original intrinsic complex cubic admission did not complete")

/-- Read the actual retained arithmetic pencil and direct negative-child cache of a complete difference.

The reader consumes the production arithmetic record and its cached pencil;
it computes no second elimination or replacement difference program.
-/
private def differenceCache {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Approximation.Gaussian.Residual polynomial channel}
    (cached : Algebraic.Cached origin polynomial residual) : Option (Nat × Nat × Nat × Bool) :=
  match cached with
  | .arithmetic (firstPolynomial := firstPolynomial) (secondPolynomial := secondPolynomial) .add _ right result =>
      let checked := result.elimination.pencil.construction.checked?.isSome
      let negative := match right with
        | .neg _ => true
        | _ => false
      some (firstPolynomial.natDegree, secondPolynomial.natDegree,
        result.elimination.pencil.degree, checked && negative)
  | _ => none

/-- Run the complete production classifier on the original upper root and its actual conjugation operation.

The comparison retains both original sidecars, their unchanged channels and
its explicitly materialized arithmetic difference, direct negative child and
checked compact pencil. Every read consumes that same stored comparison and
numerical cache.
-/
public def checkGeneralDistinct : IO Unit := do
  progress "general cubic sheets: begin complete original upper/conjugate comparison"
  let original := sidecar
  let conjugated := original.conj
  let compared := original.compare conjugated
  match compared.cache with
  | .inl _ => throw (IO.userError "actual conjugation manufactured an intrinsic root owner")
  | .inr _ => pure ()
  let materialized := compared.materialize
  unless differenceCache materialized.difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "general cubic comparison did not consume its actual checked original difference pencil")
  progress "general cubic sheets: original negation and checked degree-nine difference cache retained"
  match compared.comparison with
  | .equal _ => throw (IO.userError "the original different conjugate sheets were classified equal")
  | .distinct _ _ =>
      unless normSq (materialized.difference.residual.source.sample 0) > 0 do
        throw (IO.userError "the actual original conjugate difference lost its positive sample")
      progress "general cubic sheets: complete original classifier certified distinct channels"

/-- Compare two independently retained original cubic winding owners on their different sheets.

The lower input uses its own exact initial box, clearances, track and root
cache rather than the upper input's conjugation operation. Intrinsic comparison
retains one computed original-root gap before the separate explicit complete
difference check. Neither stage receives a supplied distinctness witness or
selected output branch.
-/
public def checkGeneralIndependent : IO Unit := do
  progress "general independent cubics: begin complete original upper/lower owner comparison"
  let original := sidecar
  let independent := lowerSidecar
  let compared := original.compare independent 1 2
  match compared.cache with
  | .inr _ => throw (IO.userError "independent original cubic roots forced the general difference classifier")
  | .inl intrinsic =>
      match intrinsic.prepared.comparison with
      | .equal _ => throw (IO.userError "independent original cubic roots lost their computed distinct sheets")
      | .distinct separation =>
          let gap := separation.separation.gap
          let left := intrinsic.left.view.root.approximation.sample separation.leftIndex
          let right := intrinsic.right.view.root.approximation.sample separation.rightIndex
          unless separation.leftIndex ≥ 1 ∧ separation.rightIndex ≥ 2 ∧ gap > 0 ∧
              gap ^ 2 ≤ normSq (left - right) do
            throw (IO.userError "independent original cubic roots lost their retained paid starts or gap")
          match compared.decision with
          | .excluded _ => throw (IO.userError "independent original cubic roots lost their direct prepared difference")
          | .prepared prepared =>
              unless prepared.apart.certificate.lowerSq = gap ^ 2 / 8 do
                throw (IO.userError "the original intrinsic decision did not consume the retained pair gap")
  let materialized := compared.materialize
  unless differenceCache materialized.difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "independent cubic comparison replaced its original compact difference cache")
  match compared.comparison with
  | .equal _ => throw (IO.userError "the independent original upper/lower cubic owners were classified equal")
  | .distinct _ _ =>
      unless normSq (materialized.difference.residual.source.sample 0) > 0 do
        throw (IO.userError "the independent original cubic difference lost its positive sample")
      progress "general independent cubics: complete original classifier certified distinct original owners"

/-- Read the actual compiler policy and atom leaf route of every retained arithmetic node. -/
private def deferredAtoms {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Basic.Expr arity} → {annotation : Annotated} →
    Basic.Construction environment expression annotation → Bool
  | _, _, .atom _ _ _ | _, _, .rational _ _ _ => true
  | _, _, .root _ _ _ _ => false
  | _, _, .neg _ child _ | _, _, .addNeg _ child _ | _, _, .subSelf _ child _ => deferredAtoms child
  | _, _, .add _ _ _ first second eager _ | _, _, .sub _ _ _ first second eager _ |
    _, _, .mul _ _ _ first second eager _ => !eager && deferredAtoms first && deferredAtoms second
  | _, _, .square _ child eager _ => !eager && deferredAtoms child

/-- Compile a displayed finite coefficient polynomial by Horner arithmetic at its original atom. -/
private def polynomialExpression {arity : Nat} (atom : Basic.Expr arity)
    (coefficients : List Data.Gaussian.Basic.Canonical) : Basic.Expr arity :=
  let rec loop (remaining : List Data.Gaussian.Basic.Canonical) (previous : Basic.Expr arity) :
      Basic.Expr arity :=
    match remaining with
    | [] => previous
    | first :: tail => loop tail (.add (.mul previous atom) (.rational first))
  match coefficients with
  | [] => .rational 0
  | first :: remaining => loop remaining (.rational first)

/-- Inspect the actual algebraic cache constructor while retaining all of its original indices. -/
private def rationalCache {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Approximation.Gaussian.Residual polynomial channel}
    (cached : Algebraic.Cached origin polynomial residual) : Bool :=
  match cached with
  | .rational _ => true
  | _ => false

/-- Inspect a supported base completion at its original construction, channel and expression indices. -/
private def supportedBaseCache {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    {channel : CoherentNamed} (construction : Construction environment expression channel) : Bool :=
  match construction with
  | .base cached (.supported _ _ _ _ _ _) _ =>
      (Base.Slots.missing cached.compiled.bindings cached.slots cached.required).isEmpty &&
        deferredAtoms cached.compiled.construction
  | _ => false

/-- Check every surviving quotient and remainder term of an actual retained coefficient division. -/
private def checkDivisionTerms {size : Nat} (source : Multivariate.Sparse Canonical size)
    (index : Fin size) (annihilator : CoefficientPolynomial)
    (attempt : Multivariate.Sparse.DivisionAt source index annihilator) : IO Unit := do
  unless attempt.quotient.terms.all (fun term => decide (term.monomial.exponentAt index < attempt.bound)) do
    throw (IO.userError "retained quotient escaped its original input exponent ceiling")
  unless (attempt.quotient.terms ++ attempt.remainder.terms).all (fun term =>
      source.terms.any (fun original =>
        decide (term.monomial.withExponentAt index 0 = original.monomial.withExponentAt index 0))) do
    throw (IO.userError "canonical division changed an unrelated original variable exponent")
  if annihilator.isZero then
    unless attempt.quotient.terms.isEmpty = true ∧ attempt.remainder.terms = source.terms do
      throw (IO.userError "zero-divisor coefficient division changed its original remainder")
  else
    unless attempt.remainder.terms.all (fun term => decide (term.monomial.exponentAt index < annihilator.natDegree)) do
      throw (IO.userError "retained remainder escaped its original nonzero annihilator degree")
    if annihilator.natDegree = 0 then
      unless attempt.remainder.terms.isEmpty do
        throw (IO.userError "a nonzero constant divisor left a surviving remainder term")
  match attempt.reconstruction with
  | .isTrue _ => pure ()
  | .isFalse _ => throw (IO.userError "retained fixture division failed exact whole coefficient reconstruction")

/-- Exercise zero and constant division edges at the same original normalized binding coordinate. -/
private def checkDivisionEdges {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (source : Multivariate.Gaussian.Normalized bindings original) (index : Fin size)
    (annihilator : CoefficientPolynomial) : IO Unit := do
  let one := Dense.Basic.DensePolynomial.constant (1 : Canonical)
  let constant := Multivariate.Sparse.DivisionAt.prepare source.form index one
  checkDivisionTerms source.form index one constant
  unless constant.quotient.terms = source.form.terms ∧ constant.remainder.terms.isEmpty = true do
    throw (IO.userError "division by one did not return the complete original form as its quotient")
  let zero := Multivariate.Sparse.DivisionAt.prepare source.form index 0
  checkDivisionTerms source.form index 0 zero
  let cancelled := source.form.sub source.form
  let empty := Multivariate.Sparse.DivisionAt.prepare cancelled index annihilator
  checkDivisionTerms cancelled index annihilator empty
  unless empty.quotient.terms.isEmpty && empty.remainder.terms.isEmpty do
    throw (IO.userError "zero input retained a spurious quotient or remainder term")

/-- Check actual canonical survivors against the retained predecessor's complete product lookup. -/
private def checkLookup {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (input : Multivariate.Gaussian.Normalized bindings original) (index : Fin size)
    (powers : List (Multivariate.Monomial.PowerEntry (bindings index)))
    (terms : List (Multivariate.Term Canonical size)) : IO Unit := do
  let cached := input.denotation.replacementLookup index powers
  for term in terms do
    unless (cached term.monomial).isSome do
      throw (IO.userError "a surviving reduction monomial missed its retained original product lookup")
    unless input.form.terms.any (fun original =>
        decide (term.monomial.withExponentAt index 0 = original.monomial.withExponentAt index 0)) do
      throw (IO.userError "a surviving reduction monomial lost its original other-coordinate owner")

/-- Consume the saved next normalization and retained pure/general coefficient caches of an actual history step. -/
private def checkReductionCaches {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (step : Query.History.Step (Base.Reduction bindings original)
      (Multivariate.Gaussian.Normalized bindings original)) : IO Unit := by
  cases step with
  | mk request next =>
      cases request with
      | mk index sidecar inspection input coefficients _ powers _ =>
          cases inspection with
          | mk form _ =>
              unfold Base.PowerInspection.Coefficients at coefficients
              cases form with
              | recognized _ _ => exact do
                  unless next.form.terms = coefficients.val.terms do
                    throw (IO.userError "saved pure reduction did not consume its retained complete coefficient form")
                  checkLookup input index powers coefficients.val.terms
                  unless coefficients.val.terms.all (fun term =>
                      decide (term.monomial.exponentAt index < sidecar.polynomial.natDegree)) do
                    throw (IO.userError "pure reduction left a surviving exponent above the original degree")
                  for term in coefficients.val.terms do
                    unless (next.denotation.findMonomial term.monomial).isSome do
                      throw (IO.userError "saved pure output discarded its retained complete monomial cache")
              | other _ => exact do
                  unless next.form.terms = coefficients.remainder.terms do
                    throw (IO.userError "saved general reduction did not consume its retained whole remainder form")
                  checkDivisionTerms input.form index sidecar.polynomial coefficients
                  checkLookup input index powers (coefficients.quotient.terms ++ coefficients.remainder.terms)
                  for term in coefficients.remainder.terms do
                    unless (next.denotation.findMonomial term.monomial).isSome do
                      throw (IO.userError "saved general output discarded its retained complete monomial cache")

/-- Inspect actual retained exact-first caches and their comparison on the original source channel. -/
private def checkExactFirst {arity : Nat} (environment : Fin arity → Annotated) (expression : Basic.Expr arity)
    (general : Bool) (rootIndex : Fin arity) (expected : Canonical := 3) : IO Unit := do
  let cached := Base.Cached.ofExpression environment expression
  unless deferredAtoms cached.compiled.construction do
    throw (IO.userError "exact-first compilation eagerly constructed generic composite evidence or a fresh root")
  match Base.Certificate.existing cached with
  | some certificate@(.exact _ _ reduced _ value same) =>
      if exact : value = expected then
        let comparison : Equivalence.NamedEquivalent cached.channel.name (Coherence.exact expected).name :=
          exact ▸ (reduced.polynomial.rational value same).equivalent
        let _originalChannel := cached.compiled.channel_eq
        let _operationalComparison := comparison
        unless (Base.Slots.missing cached.compiled.bindings cached.slots cached.required).isEmpty do
          throw (IO.userError "an eliminated original opaque variable still requested an admission")
        for step in reduced.history.steps do
          unless (Basic.Binding.read cached.compiled.bindings step.request.index).leaf = .atom rootIndex do
            throw (IO.userError "equation reduction replaced the original bounded root binding key")
          checkReductionCaches step
        match reduced.history.steps with
        | [] => throw (IO.userError "the fixture skipped its actual retained original equation reduction")
        | first :: _ => checkDivisionEdges first.request.input first.request.index first.request.sidecar.polynomial
        let usedGeneral := reduced.history.steps.any fun step =>
          match step.request.inspection.form with
          | .recognized _ _ => false
          | .other _ => true
        unless usedGeneral = general do
          throw (IO.userError "the actual retained equation path disagrees with its pure/general reduction test")
        let materialized := certificate.materialize
        unless rationalCache materialized.val.cached do
          throw (IO.userError "constant coefficient success constructed a generic eliminant fallback")
      else throw (IO.userError "original equation reduction did not obtain its expected exact coefficient")
  | _ => throw (IO.userError "partial original equations failed to settle the exact coefficient before admission")

/-- Cancel original cubic equations before opaque admissions, including a non-pure displayed annihilator. -/
public def checkPartialSlots : IO Unit := do
  let alpha : Basic.Expr 2 := .atom ⟨0, by decide⟩
  let analytic : Basic.Expr 2 := .atom ⟨1, by decide⟩
  let pureEnvironment : Fin 2 → Annotated := fun index =>
    if index.val = 0 then Annotated.algebraic sidecar else Annotated.opaque (Coherence.exact 7)
  let cube : Basic.Expr 2 := .mul (.mul alpha alpha) alpha
  let identity : Basic.Expr 2 := .sub cube (.rational 2)
  checkExactFirst pureEnvironment (.add (.mul analytic identity) (.rational 3)) false 0
  let product : Basic.Expr 2 := .mul (.add (.rational 1) alpha)
    (.add (.sub (.mul alpha alpha) alpha) (.rational 1))
  checkExactFirst pureEnvironment product false 0
  checkExactFirst pureEnvironment identity false 0 0
  let shifted := sidecar.add (Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 1))
  let shiftedEnvironment : Fin 2 → Annotated := fun index =>
    if index.val = 0 then Annotated.algebraic shifted else Annotated.opaque (Coherence.exact 7)
  let displayed := polynomialExpression alpha shifted.polynomial.coeffs
  checkExactFirst shiftedEnvironment (.add (.mul analytic displayed) (.rational 3)) true 0
  let surviving : Basic.Expr 2 := .add (.mul analytic identity) (.add alpha (.rational 3))
  match Expr.attempt pureEnvironment (.base surviving) with
  | .completed output =>
      unless supportedBaseCache output.construction do
        throw (IO.userError "surviving root fallback did not consume its actual supported deferred base cache")
  | _ => throw (IO.userError "eliminated opaque evidence blocked the supported original-root fallback")
  let eventualZero : Expr 2 := .mul (.inverse (Expr.rational 0)) (.base identity)
  match Expr.attempt pureEnvironment eventualZero with
  | .invalid first =>
      match first.denominator.1 with
      | .base (.rational value) =>
          unless value = 0 ∧ first.prefix.isEmpty do
            throw (IO.userError "eventual zero discarded its original first undefined inverse occurrence")
      | _ => throw (IO.userError "eventual zero replaced its original undefined denominator")
  | _ => throw (IO.userError "eventual zero hid the original first inverse-zero obstruction")
  let unresolvedFirst : Expr 2 := .mul (.inverse (Expr.atom (1 : Fin 2))) (.base identity)
  match Expr.attempt pureEnvironment unresolvedFirst with
  | .pending first =>
      match first.binding.leaf with
      | .atom index =>
          unless index.val = 1 ∧ first.unvisited.length = 1 do
            throw (IO.userError "eventual zero bypassed its original first unresolved inverse admission")
      | _ => throw (IO.userError "the unresolved inverse lost its original opaque atom owner")
  | _ => throw (IO.userError "eventual zero bypassed its original first unresolved inverse")
  progress "partial cubic equations: exact coefficient caches retain original channels and ordered inverse obligations"

/-- Inspect the retained unit attempt at its complete original base-construction indices. -/
private def checkUnitBaseCache {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {channel : CoherentNamed}
    (construction : Construction environment expression channel) : IO Unit :=
  match construction with
  | .base _ _ (some checked, _) => do
      match checked.2.val with
      | some run => unless run.2.val.1.length = 1 ∧ run.2.val.2.isSome do
          throw (IO.userError "the exact inverse lost its retained first original generator attempt")
      | none => throw (IO.userError "the exact inverse discarded its actual coordinate/GCD check")
  | _ => throw (IO.userError "the exact inverse lost its original base construction/check cache")

/-- Read the branch of an actual finite geometric observation without reducing its source program. -/
private def geometricPrepared {source : Geometric.GeometricApproximation} {channel : CoherentNamed}
    {equivalent : Equivalence.NamedEquivalent channel.name source.toApproximation.toNamed}
    {state : Geometric.Preparation.State source} {ball : Enclosure.Ball}
    {readback : Geometric.Preparation.Readback source state ball} :
    Geometric.Preparation.Outcome source channel equivalent state ball readback → Bool
  | .prepared _ _ _ => true
  | .inconclusive _ => false

/-- Inspect the selected inverse and a demanded inverse of its retained output at complete construction indices.

The second guard consumes the actual normalized inverse output and original
selected generator. Its shared denominator preparation retains the failed
first head and actual successful two-advance follow-up.
-/
private def checkUnitInverseCache {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {channel : CoherentNamed}
    (construction : Construction environment expression channel) : IO Unit :=
  match expression, channel, construction with
  | _, _, .inverseGenerator child _ cache retained => do
      unless retained.reciprocal.isNone do
        throw (IO.userError "building an inverse eagerly prepared its unrequested reciprocal output")
      let certificate := cache.2.2.2
      unless certificate.coprime.result.gcd.natDegree = 0 ∧
          certificate.inversePolynomial.eval 0 = (1 / 3 : Data.Gaussian.Basic.Canonical) ∧
          certificate.inversePolynomial.eval 1 = (1 / 3 : Data.Gaussian.Basic.Canonical) ∧
          certificate.inversePolynomial.eval 2 = (1 : Data.Gaussian.Basic.Canonical) do
        throw (IO.userError
          "the retained cubic inverse did not consume the expected original scaled Bezout coefficient")
      unless certificate.request.isNone ∧ certificate.observation.isNone do
        throw (IO.userError "the separated original cubic head paid the inflated unit-product comparison")
      match certificate.initial.outcome with
      | .prepared _ _ _ =>
          unless certificate.initial.ball.center = (⟨5 / 16, 1⟩ : Canonical) ∧
              certificate.initial.ball.radiusSq = (1 / 4 : Data.Rat.Fraction.Rational) do
            throw (IO.userError "the cubic inverse head lost its actual cached dense/root observation")
      | .inconclusive _ =>
          throw (IO.userError "the small original cubic denominator head did not certify its exact margin")
      checkUnitBaseCache child
      progress "selected cubic inverse: demand actual retained inverse-output normalization"
      let normalized := certificate.normalizeOutput
      progress "selected cubic inverse: request exact inverse of that actual prior inverse"
      let secondAttempt := normalized.inverseAt certificate.index certificate.generator
      match secondAttempt with
      | .ready second _ _ =>
          unless second.index.val = certificate.index.val ∧ second.coprime.result.gcd.natDegree = 0 do
            throw (IO.userError "the prior-inverse guard replaced the original selected slot or constant-GCD cache")
          unless second.request.isNone ∧ second.observation.isNone do
            throw (IO.userError "the prior inverse paid a factor comparison after bounded geometric preparation")
          if geometricPrepared second.initial.outcome then
            throw (IO.userError "the prior-inverse denominator lost its actual failed first geometric head")
          match second.followup with
          | some later =>
              let retainedState : {state : Geometric.Preparation.State second.source //
                state = second.initial.state.advance.advance} := later.1
              unless retainedState.val.nextIndex = 2 do
                throw (IO.userError "the prior-inverse follow-up lost its actual two-request retry index")
              let geometricIndex : Nat := retainedState.val.source
              unless geometricIndex = 1 do
                throw (IO.userError "the prior-inverse follow-up lost its actual geometric source index")
              unless geometricPrepared later.2.val.outcome do
                throw (IO.userError "the actual prior-inverse follow-up did not retain its successful preparation")
              progress
                s!"selected cubic inverse: prior-inverse denominator geometric index {geometricIndex}, retry 2"
          | none => throw (IO.userError "the prior-inverse denominator discarded its actual retained follow-up")
      | _ =>
          throw (IO.userError "the actual normalized prior inverse did not return an exact original unit certificate")
  | _, _, _ => throw (IO.userError "the original cubic denominator did not take the exact constant-GCD construction")

/-- Inspect the actual demanded reciprocal receipt at complete original construction indices. -/
private def checkReciprocalCache {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {channel : CoherentNamed}
    (construction : Construction environment expression channel) : IO Unit :=
  match expression, channel, construction with
  | _, _, .inverseGenerator _ _ _ retained => do
      let some receipt := retained.reciprocal |
        throw (IO.userError "the reciprocal decision discarded its actual demanded preparation receipt")
      let attempt := receipt.val
      unless attempt.observation.isNone do
        throw (IO.userError "the bounded original cubic reciprocal head paid the inflated factor comparison")
      if geometricPrepared attempt.initial.outcome then
        throw (IO.userError "the reciprocal request lost its actual original failed head")
      match attempt.followup with
      | some later =>
          unless later.1.val.nextIndex = 2 do
            throw (IO.userError "the reciprocal follow-up lost its exact original two-request retry index")
          let geometricIndex : Nat := later.1.val.source
          unless geometricIndex = 1 do
            throw (IO.userError "the reciprocal follow-up lost its actual original geometric source index")
          progress
            s!"selected cubic inverse: reciprocal geometric index {geometricIndex}, retry {later.1.val.nextIndex}"
          unless geometricPrepared later.2.val.outcome do
            throw (IO.userError "the original cubic reciprocal follow-up did not certify its finite margin")
      | none => throw (IO.userError "the reciprocal request lost its original failed head or actual follow-up")
  | _, _, _ => throw (IO.userError "the reciprocal decision discarded its retained actual preparation receipt")

/-- Inspect the original failed coordinate attempt at its complete construction indices. -/
private def checkCommonInverseCache {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {channel : CoherentNamed}
    (construction : Construction environment expression channel) : IO Unit :=
  match construction with
  | .base cached _ (some checked, _) => do
      match checked.2.val with
      | some run =>
          unless run.2.val.2.isNone do
            throw (IO.userError "a nonconstant gcd was treated as a selected-generator inverse certificate")
          unless !run.2.val.1.isEmpty ∧ run.2.val.1.map (fun attempt => attempt.1.val) =
              List.ofFn (fun index : Fin cached.compiled.bindings.length => index.val) do
            throw (IO.userError "nonconstant-GCD fallback lost its original ordered unresolved attempts")
          for attempt in run.2.val.1 do
            match attempt.2 with
            | .inspected _ _ (.commonDivisor _ _ _ _ _ _ _ _ _ _ common) =>
                unless common.result.gcd.natDegree > 0 do
                  throw (IO.userError "nonconstant-GCD fallback discarded its actual positive-degree gcd")
            | _ => throw (IO.userError "nonconstant-GCD fallback replaced an original unresolved attempt")
      | none => throw (IO.userError "exact zero fallback lost its original retained generator inspection")
  | _ => throw (IO.userError "exact zero fallback discarded its actual base check/cache")

/-- Exercise the constant-GCD inverse before generic elimination and retain its original ordered failed attempt on
exact zero. -/
public def checkSelectedInverse : IO Unit := do
  let alpha : Basic.Expr 1 := .atom ⟨0, by decide⟩
  let denominator : Basic.Expr 1 := .add alpha (.rational 1)
  let admittedEnvironment : Fin 1 → Annotated := fun _ => Annotated.algebraic sidecar
  progress "selected cubic inverse: request actual original selected-unit completion"
  match Expr.attempt admittedEnvironment (.inverse (.base denominator)) with
  | .completed output =>
      progress "selected cubic inverse: original selected-unit completion returned"
      unless output.cached.isNone do
        throw (IO.userError "the exact selected-generator inverse forced a generic Sidecar")
      checkUnitInverseCache output.construction
      progress "selected cubic inverse: request actual reciprocal-output decision"
      let finished := output.finish
      unless finished.completed.cached.isNone ∧ finished.decision.isPrepared do
        throw (IO.userError "exact reciprocal acquisition materialized an eliminant or lost its nonzero preparation")
      checkReciprocalCache finished.completed.construction
      progress "selected cubic inverse: actual reciprocal-output decision retained"
      let repeated := finished.completed.finish
      checkReciprocalCache repeated.completed.construction
      unless repeated.completed.cached.isNone ∧ repeated.decision.isPrepared do
        throw (IO.userError "a repeated reciprocal request lost its actual cached preparation")
      progress "selected cubic inverse: repeated output decision reused retained receipt"
      progress "selected cubic inverse: request explicit full Sidecar materialization"
      let full := output.materialize
      unless full.sidecar.polynomial.natDegree > 0 do
        throw (IO.userError "explicit full reciprocal materialization failed to retain its original Sidecar")
      progress "selected cubic inverse: explicit full Sidecar materialization returned"
  | _ => throw (IO.userError "the original cubic denominator inverse did not complete")
  let cube : Basic.Expr 1 := .mul (.mul alpha alpha) alpha
  let zero : Basic.Expr 1 := .sub cube (.rational 2)
  match Expr.attempt admittedEnvironment (.inverse (.base zero)) with
  | .invalid first =>
      let child := first.denominator.2.1
      unless child.cached.isSome do
        throw (IO.userError "nonconstant-GCD fallback discarded its actual materialized zero evidence")
      checkCommonInverseCache child.construction
  | _ => throw (IO.userError "the original cubic exact-zero inverse lost its typed source obstruction")
  progress "selected cubic inverse: exact coordinates/Bezout/product caches and full materialization boundary retained"

/-- Count actual retained exact reciprocal nodes and reject any implicit generic inverse materialization. -/
private def exactInverseNodes {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Expr arity} → {channel : CoherentNamed} → Construction environment expression channel → Nat × Bool
  | _, _, .base _ _ _ => (0, true)
  | _, _, .neg child _ _ | _, _, .conj child _ _ | _, _, .pow child _ _ _ => exactInverseNodes child
  | _, _, .add first _ second _ _ _ | _, _, .sub first _ second _ _ | _, _, .mul first _ second _ _ =>
      let left := exactInverseNodes first
      let right := exactInverseNodes second
      (left.1 + right.1, left.2 && right.2)
  | _, _, .inverse _ _ _ _ _ _ => (0, false)
  | _, _, .inverseGenerator child _ _ _ =>
      let retained := exactInverseNodes child
      (retained.1 + 1, retained.2)

/-- Count the actual demanded reciprocal receipts stored in the unchanged original construction tree. -/
private def demandedReciprocals {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Expr arity} → {channel : CoherentNamed} → Construction environment expression channel → Nat
  | _, _, .base _ _ _ => 0
  | _, _, .neg child _ _ | _, _, .conj child _ _ | _, _, .pow child _ _ _ => demandedReciprocals child
  | _, _, .add first _ second _ _ _ | _, _, .sub first _ second _ _ | _, _, .mul first _ second _ _ =>
      demandedReciprocals first + demandedReciprocals second
  | _, _, .inverse child _ _ _ _ _ => demandedReciprocals child
  | _, _, .inverseGenerator child _ _ retained =>
      demandedReciprocals child + if retained.reciprocal.isSome then 1 else 0

/-- Repeat the actual already stored child guard before any structural reciprocal refinement.

The original whole-result laws identify both returned constructions. The
executable assertions consume the returned values and check that a stored
request is reused without producing another structural preparation request.
-/
private def checkRepeatedInverseGuard {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {channel : CoherentNamed} (construction : Construction environment expression channel)
    (coherent : construction.CacheCoherent) : IO Unit :=
  match expression, channel, construction, coherent with
  | _, _, .inverseGenerator original stored _ _, coherent => do
      let child : Construction.Result environment _ :=
        ⟨_, original, ⟨stored, coherent.1, coherent.2.1⟩⟩
      if existing : child.construction.inverseChecked = true then
        let refined := child.prepareDenominator
        have _wholeRefinement := child.prepareDenominator_checked existing
        unless refined.2.isNone do
          throw (IO.userError "a repeated guard rebuilt structural denominator preparation")
        let repeated := refined.1.checkInverse refined.2
        have _wholeGuard := child.checkInverse_retained none existing
        unless repeated.1.construction.inverseChecked ∧ repeated.2.isSome do
          throw (IO.userError "a repeated guard discarded its actual stored request or exact selected inverse")
      else throw (IO.userError "the completed exact reciprocal discarded its actual child guard cache")
  | _, _, _, _ => throw (IO.userError "the compound reuse check lost its actual exact reciprocal constructor")

/-- Check that an actual sum denominator retains its one combined attempt and both demanded child receipts. -/
private def checkCachedSumDenominator {arity : Nat} {environment : Fin arity → Annotated} :
    {expression : Expr arity} → {channel : CoherentNamed} →
    Construction environment expression channel → IO Unit
  | _, _, .add first _ second _ _ (some attempt) => do
      unless attempt.prepared.isSome ∧ first.cachedSource.isSome ∧ second.cachedSource.isSome do
        throw (IO.userError "the sum denominator discarded its successful cached attempt or a child observation")
      unless demandedReciprocals first > 0 ∧ demandedReciprocals second > 0 do
        throw (IO.userError "the sum denominator lost an actual demanded original reciprocal receipt")
      let some left := first.cachedSource | throw (IO.userError "the first sum source cache disappeared")
      let some right := second.cachedSource | throw (IO.userError "the second sum source cache disappeared")
      unless attempt.sources.1.ball.center = left.ball.center ∧ attempt.sources.1.ball.radiusSq = left.ball.radiusSq ∧
          attempt.sources.2.ball.center = right.ball.center ∧ attempt.sources.2.ball.radiusSq = right.ball.radiusSq do
        throw (IO.userError "the retained sum attempt used a different actual child enclosure")
  | _, _, _ => throw (IO.userError "the checked sum denominator lost its retained finite attempt")

/-- Inspect a nonbase reciprocal's actual original table, interpreted generator parents and retained inverse chain. -/
private def checkCompoundInverse {arity : Nat} {environment : Fin arity → Annotated}
    {expression : Expr arity} {channel : CoherentNamed} (construction : Construction environment expression channel)
    (depth minimumInverses : Nat) (alternate : Option Nat := none) (requirePrepared : Bool := false)
    (requireCachedSum : Bool := false) : IO Unit :=
  match expression, channel, construction with
  | _, _, .inverseGenerator original _ inverseCache retained => do
      if requireCachedSum then checkCachedSumDenominator original
      unless inverseCache.2.2.2.coprime.result.gcd.natDegree = 0 do
        throw (IO.userError "compound inverse lost its actual original unit GCD cache")
      let some source := retained.source |
        throw (IO.userError "compound inverse lost its exact original coordinate/source view")
      let input := source.input
      if requirePrepared then
        let certificate := inverseCache.2.2.2
        match requested : certificate.request with
        | none => throw (IO.userError "the structural inverse guard discarded its actual supplied preparation")
        | some prepared =>
            have _wholePreparation := certificate.preparation_eq_of_supplied prepared requested
            unless certificate.followup.isNone ∧ certificate.observation.isNone ∧
                certificate.prepared.apart.certificate.lowerSq = prepared.apart.certificate.lowerSq do
              throw (IO.userError "the supplied denominator preparation was replaced by a fresh head or factor scan")
            let initialIndex : Nat := certificate.initial.state.source
            unless initialIndex = 0 ∧ certificate.initial.state.nextIndex = 0 do
              throw (IO.userError "the supplied route changed its actual original initial source owner")
        unless demandedReciprocals construction ≥ minimumInverses - 1 do
          throw (IO.userError "structural preparation discarded a demanded original child reciprocal receipt")
      unless !input.bindings.isEmpty do
        throw (IO.userError "compound inverse invented an empty original generator table")
      for index in List.ofFn (fun index : Fin input.bindings.length => index) do
        match (Basic.Binding.read input.bindings index).leaf with
        | .atom original => unless original.val = 0 do
            throw (IO.userError "compound inverse replaced its actual original cubic leaf")
        | .root _ _ => throw (IO.userError "compound inverse replaced an original admitted atom by another root")
        unless (input.depths index = depth ∨ alternate = some (input.depths index)) ∧ (input.generator index).isSome do
          throw (IO.userError "compound inverse lost an actual interpreted generator or supplied Sidecar parent")
      if let some additional := alternate then
        let indices := List.ofFn (fun index : Fin input.bindings.length => index)
        unless indices.any (fun index => input.depths index == depth) ∧
            indices.any (fun index => input.depths index == additional) do
          throw (IO.userError "operational double-conjugate alignment discarded an actual original input history")
      unless retained.polynomial.polynomial.isNone do
        throw (IO.userError "compound inverse eagerly normalized its still unrequested reciprocal output")
      let nodes := exactInverseNodes construction
      unless nodes.1 ≥ minimumInverses ∧ nodes.2 do
        throw (IO.userError "compound exact propagation materialized an earlier inverse or lost its original child")
  | _, _, _ => throw (IO.userError "nonbase same-generator reciprocal fell back to generic elimination")

/-- Execute one nonbase reciprocal before any explicit full Sidecar boundary. -/
private def runCompoundInverse (label : String) (expression : Expr 1) (depth minimumInverses : Nat)
    (materialize : Bool := false) (alternate : Option Nat := none) (requirePrepared : Bool := false)
    (requireCachedSum : Bool := false) : IO Unit := do
  let original := sidecar
  let admitted : Fin 1 → Annotated := fun _ => Annotated.algebraic original
  progress s!"compound cubic inverse: {label}, request original exact chain"
  match expression.attempt admitted with
  | .completed output =>
      unless output.cached.isNone do
        throw (IO.userError "compound exact reciprocal eagerly materialized a composite Sidecar")
      checkCompoundInverse output.construction depth minimumInverses alternate requirePrepared requireCachedSum
      checkRepeatedInverseGuard output.construction output.coherent
      if materialize then
        progress s!"compound cubic inverse: {label}, request explicit full materialization"
        let full := output.materialize
        unless full.sidecar.polynomial.natDegree > 0 do
          throw (IO.userError "explicit compound materialization lost its actual full Sidecar")
      progress s!"compound cubic inverse: {label}, complete retained exact chain"
  | _ => throw (IO.userError "nonzero same-generator compound reciprocal failed to complete")

/-- The original mixed environment retains one admitted cubic and one same-channel opaque exact scalar. -/
private def compoundInputs (index : Fin 2) : Annotated :=
  Data.Fin.cases (Annotated.algebraic sidecar) (fun _ => Annotated.opaque (Coherence.exact 7)) index

/-- Supply intrinsic evidence for the same two original mixed-environment channels. -/
private def compoundAdmissions (index : Fin 2) : Algebraic.Sidecar (compoundInputs index).channel :=
  Data.Fin.casesDependent (motive := fun index => Algebraic.Sidecar (compoundInputs index).channel)
    sidecar (fun _ => Algebraic.Sidecar.ofRational (RationalSidecar.exact 7)) index

/-- The ordered names of every original compound-inverse acceptance case. -/
public def compoundInverseCases : List String :=
  ["prior-inverse", "negation", "addition", "subtraction", "product", "power",
    "conjugation", "double-conjugation", "conjugated-sum", "mixed-double-conjugation",
    "ordered-invalid", "retry"]

/-- Execute one original compound-inverse case at its same source owners and exact checked grammar.

Selection changes only which independent acceptance request is executed. The
complete case retains its original cache, failure, retry and materialization
assertions, and an unknown name is rejected before any case executes.
-/
public def checkCompoundInverseCase (name : String) : IO Unit := do
  let alpha : Expr 1 := Expr.atom ⟨0, by decide⟩
  let first : Expr 1 := .inverse (.add alpha (Expr.rational 1))
  match name with
  | "prior-inverse" =>
      runCompoundInverse "inverse of prior inverse" (.inverse first) 0 2 true none true
  | "negation" =>
      runCompoundInverse "negation of prior inverse" (.inverse (.neg first)) 0 2
  | "addition" =>
      runCompoundInverse "sum of prior inverse" (.inverse (.add first (Expr.rational 2))) 0 2
  | "subtraction" =>
      runCompoundInverse "difference of prior inverse" (.inverse (.sub first (Expr.rational 2))) 0 2
  | "product" =>
      runCompoundInverse "product of prior inverses" (.inverse (.mul first first)) 0 3 false none true
  | "power" =>
      runCompoundInverse "power of prior inverse" (.inverse (.pow first 2)) 0 2 false none true
  | "conjugation" =>
      runCompoundInverse "conjugate of prior inverse" (.inverse (.conj first)) 1 2 false none true
  | "double-conjugation" =>
      runCompoundInverse "double conjugate of prior inverse" (.inverse (.conj (.conj first))) 2 2 false none true
  | "conjugated-sum" =>
      runCompoundInverse "sum of conjugated prior inverses"
        (.inverse (.add (.conj first) (.conj first))) 1 3 false none true true
  | "mixed-double-conjugation" =>
      runCompoundInverse "original plus actual double conjugate" (.inverse (.add first (.conj (.conj first))))
        0 3 false (some 2) true true
  | "ordered-invalid" => do
      let invalid : Expr 1 := .add (.inverse (Expr.rational 0)) (.inverse first)
      let admitted : Fin 1 → Annotated := fun _ => Annotated.algebraic sidecar
      match invalid.attempt admitted with
      | .invalid failure =>
          unless failure.prefix.isEmpty do
            throw (IO.userError "compound exact work changed the original left-first invalidity prefix")
          match failure.denominator.1 with
          | .base (.rational value) => unless value = 0 do
              throw (IO.userError "compound exact work changed the original first zero denominator")
          | _ => throw (IO.userError "compound exact work replaced the original first invalid syntax")
      | _ => throw (IO.userError "compound exact work bypassed an earlier original zero inverse")
  | "retry" => do
      let alpha : Expr 2 := Expr.atom (0 : Fin 2)
      let first : Expr 2 := .inverse (.add alpha (Expr.rational 1))
      let suspended : Expr 2 := .add first (.inverse (Expr.atom (1 : Fin 2)))
      match suspended.attempt compoundInputs with
      | .pending request =>
          unless request.unvisited.isEmpty ∧ request.unresolved.length = 1 do
            throw (IO.userError "compound suspension lost its original unresolved occurrence order")
          match request.prefix with
          | [retained] =>
              unless retained.2.cached.isNone do
                throw (IO.userError "compound suspension materialized its completed exact prefix")
              checkCompoundInverse retained.2.construction 0 1
          | _ => throw (IO.userError "compound suspension lost its actual completed prior-inverse prefix")
          let some evidence := request.fromAtoms compoundAdmissions |
            throw (IO.userError "original scalar evidence could not attach to its same pending source owner")
          match request.resume evidence with
          | .completed output =>
              unless output.cached.isNone ∧ (exactInverseNodes output.construction).1 ≥ 1 do
                throw (IO.userError "compound retry replaced or materialized its actual retained exact prefix")
          | _ => throw (IO.userError "compound retry failed after supplying its actual original missing evidence")
      | _ => throw (IO.userError "compound evaluation discarded its original pending right admission")
  | _ => throw (IO.userError s!"unknown compound-inverse case: {name}")

/-- Exercise actual prior-inverse coordinates through every same-generator checked arithmetic operation.

Each reciprocal pays its demanded original ordered guard once, before any
composite elimination. Products, powers and conjugates consume actual child
reciprocal receipts, and a repeated guard reuses its same retained request.
Conjugation retains the actual interpreted generator,
including a literal twice-conjugated channel. The same native fixture checks
ordered failures, suspension/resumption with an existing exact prefix and the
explicit full materialization boundary for a true prior-inverse chain.
-/
public def checkCompoundInverses : IO Unit := do
  for name in compoundInverseCases do
    checkCompoundInverseCase name
  progress "compound cubic inverses: cached coordinates, actual conjugate owners, ordered failures and retry retained"

/-- Complete original repeated-cubic cancellation through the production finite-expression compiler.

The same original opaque cubic atom occurs twice in the actual total source
syntax. Its existing compiler checks formal cancellation before elimination,
retains the original subtraction channel and supplies no caller-provided zero
hypothesis. Checked inversion retains that exact first zero denominator.
-/
public def checkFormalZero : IO Unit := do
  TestPurelib.Polynomial.MultivariateDenotation.checkCachedComparisons
  checkSelectedInverse
  checkPartialSlots
  progress "formal cubic zero: compile actual original repeated-owner subtraction"
  let expression : Expr 1 := .base (.sub (.atom ⟨0, by decide⟩) (.atom ⟨0, by decide⟩))
  match expression.check environment with
  | .finished finished =>
      match finished.decision with
      | .prepared _ => throw (IO.userError "the original formal cubic cancellation was classified nonzero")
      | .excluded _ => pure ()
      let materialized := finished.materialize
      unless materialized.sidecar.residual.source.sample 0 = 0 do
        throw (IO.userError "the original cancellation lost its exact retained zero reading")
      progress "formal cubic zero: complete production decision certified its original zero channel"
  | _ => throw (IO.userError "the original formal cubic cancellation did not complete")
  match Expr.check environment (.inverse expression) with
  | .invalid first =>
      match first.denominator.1 with
      | .base (.sub (.atom firstIndex) (.atom secondIndex)) =>
          unless firstIndex.val = 0 ∧ secondIndex.val = 0 ∧ first.prefix.isEmpty do
            throw (IO.userError "the exact zero reciprocal lost its original ordered denominator occurrence")
      | _ => throw (IO.userError "the original zero reciprocal denominator syntax was replaced")
      progress "formal cubic zero: checked inversion retained its original exact zero obstruction"
  | _ => throw (IO.userError "the original formal zero reciprocal did not retain its exact obstruction")

/-- Retain the actual finished coefficient-zero construction on the same original upper-root difference.

The completed subtraction keeps both original child constructions and caches.
Finishing preserves the original coefficient inspection and bounded zero
occurrence alongside the exact decision consumed by subsequent readers.
-/
private def checkFinishedZero : IO Unit := do
  match (Admitted.atom environment ⟨0, by decide⟩ sidecar).run with
  | .completed upper =>
      let finished := (upper.sub upper).finish
      match finished.resolved with
      | some receipt => do
          match receipt.resolved with
          | .coefficient inspection completion =>
              match completion with
              | .zero _ _ occurrence _ _ _ _ =>
                  let entry := inspection.preparation.decomposition.positiveMultiplicityEntries.get occurrence.index
                  unless entry.part.polynomial.eval 0 = 0 do
                    throw (IO.userError "finished original difference discarded its actual zero factor occurrence")
              | _ => throw (IO.userError "finished original difference lost its computed coefficient-zero construction")
          | _ => throw (IO.userError "finished original difference discarded its actual coefficient inspection")
          unless !finished.decision.isPrepared && receipt.completed.sidecar.residual.source.sample 0 = 0 do
            throw (IO.userError "finished original difference changed its stored zero decision or original source")
      | none => throw (IO.userError "finished original difference did not retain a full coefficient-resolution receipt")
      progress "finished cubic zero: original completed difference and coefficient inspection retained"
  | _ => throw (IO.userError "the original upper cubic input failed intrinsic checked completion")

/-- Run the complete production exact-zero classifier on the original cubic owner against itself.

This supplies no equality or successful zero hypothesis to the classifier.
Intrinsic comparison uses the same original root/cache before the explicit
complete difference check consumes its retained direct-negation cache.
-/
public def checkGeneralZero : IO Unit := do
  progress "general cubic zero: begin complete original self-difference comparison"
  let original := sidecar
  let compared := original.compare original 2 1
  match compared.cache with
  | .inr _ => throw (IO.userError "the original self-root comparison forced the general difference classifier")
  | .inl intrinsic =>
      match intrinsic.prepared.comparison with
      | .distinct _ => throw (IO.userError "the original self-root comparison lost its actual equality outcome")
      | .equal _ => pure ()
  match compared.comparison with
  | .distinct _ _ => throw (IO.userError "the intrinsic original self-root comparison was classified distinct")
  | .equal equivalent =>
      let request := equivalent.compare 1 2 4 (by decide)
      let actual := Name.Sampling.approximation root.value.name
      unless request.leftIndex ≥ 1 ∧ request.rightIndex ≥ 2 ∧
          normSq (actual.sample request.leftIndex - actual.sample request.rightIndex) < 4 do
        throw (IO.userError "the intrinsic original root equality did not pay its actual original-channel request")
  let materialized := compared.materialize
  unless differenceCache materialized.difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "general cubic zero did not retain its actual checked original difference cache")
  match materialized.resolved with
  | .coefficient inspected completion =>
      match completion with
      | .zero _ _ occurrence _ _ _ _ =>
          let entry := inspected.preparation.decomposition.positiveMultiplicityEntries.get occurrence.index
          unless entry.part.polynomial.eval 0 = 0 do
            throw (IO.userError "general cubic zero lost its actual original factor occurrence")
          progress s!"general cubic zero: retained original factor occurrence {occurrence.index.val} \
            at degree {entry.part.polynomial.natDegree}"
      | _ => throw (IO.userError "general cubic zero did not consume its retained coefficient zero certificate")
  | _ => throw (IO.userError "general cubic zero lost its retained original coefficient decision")
  match compared.comparison with
  | .equal _ => progress "general cubic zero: complete original classifier certified operational equality"
  | .distinct _ _ => throw (IO.userError "the actual original self-difference was classified nonzero")
  checkFinishedZero

/-- Execute the actual complete original comparison's returned independent-start request without formal cancellation. -/
public def checkGeneralZeroRequest : IO Unit := do
  let original := sidecar
  let compared := original.compare original
  let materialized := compared.materialize
  unless differenceCache materialized.difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "general zero request lost its same original self-difference cache")
  match compared.comparison with
  | .equal equivalent =>
      progress "general cubic zero request: original classifier complete; pay starts 3/7 target 1/16"
      let paid := equivalent.compare 3 7 (1/16) (by decide)
      unless 3 ≤ paid.leftIndex ∧ 7 ≤ paid.rightIndex do
        throw (IO.userError "general zero request changed an original independent start")
      progress s!"general cubic zero request: returned original indices {paid.leftIndex}/{paid.rightIndex}"
      let first := (Name.Sampling.approximation root.value.name).sample paid.leftIndex
      let second := (Name.Sampling.approximation root.value.name).sample paid.rightIndex
      unless normSq (first - second) < (1/16 : Data.Rat.Fraction.Rational) do
        throw (IO.userError "general zero request failed its original numerical tail comparison")
      progress "general cubic zero request: actual original returned samples paid the unchanged request"
  | .distinct _ _ => throw (IO.userError "the actual original self-difference was classified nonzero")

/-- Consume the original upper-root comparison through checked saved states at its computed primitive indices.

The complete original classifier pays the unchanged independent starts and
tolerance before the original sampling trajectory determines either primitive
index. Saved entries retain the same root, track, Newton targets and scalar
observations. The transported payment keeps its original indices and bounds.
-/
public def checkCachedGeneralZeroRequest (directory : System.FilePath)
    (savedOnly interrupt : Bool) (readSamples : Bool := true) : IO Unit := do
  let original := sidecar
  let compared := original.compare original
  let materialized := compared.materialize
  unless differenceCache materialized.difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "saved general zero request lost its original self-difference cache")
  match compared.comparison with
  | .distinct _ _ => throw (IO.userError "the actual original self-difference was classified nonzero")
  | .equal equivalent =>
      let paid := equivalent.compare 3 7 (1/16) (by decide)
      unless paid.leftIndex = 13 ∧ paid.rightIndex = 13 do
        throw (IO.userError "saved general zero request changed its original returned indices")
      let leftPrimitive : Nat := Process.Sampling.stateAt root.approximation.toProcess
        (show Nat from 0) paid.leftIndex
      let rightPrimitive : Nat := Process.Sampling.stateAt root.approximation.toProcess
        (show Nat from 0) paid.rightIndex
      unless initial.box.diagonalSq = (1/32 : Data.Rat.Fraction.Rational) do
        throw (IO.userError "saved general zero request changed the original initial diagonal")
      progress s!"saved general cubic request: starts 3/7 target 1/16 named \
        {paid.leftIndex}/{paid.rightIndex} computed primitive {leftPrimitive}/{rightPrimitive}"
      let request := Data.Json.mkObj
        [("protocol", toJson "original-upper-cubic-named-request-v1"),
         ("polynomial", toJson (polynomial.coeffs.map gaussianData)),
         ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
         ("initialDiagonal", toJson (fractionData initial.box.diagonalSq)),
         ("leftStart", toJson (3 : Nat)), ("rightStart", toJson (7 : Nat)),
         ("target", toJson (fractionData (1/16))),
         ("leftIndex", toJson paid.leftIndex), ("rightIndex", toJson paid.rightIndex),
         ("leftPrimitive", toJson leftPrimitive), ("rightPrimitive", toJson rightPrimitive)]
      IO.FS.createDirAll directory
      let path := join directory "named-request.json"
      if ← path.pathExists then
        let stored : Data.Json ← loadJson path
        unless stored == request do
          throw (IO.userError "saved original named request differs from its retained exact inputs and indices")
      else saveJson path request
      if !readSamples then return
      let columns : ClearanceCheckpoint.Control IO :=
        { savedOnly := savedOnly
          afterSave := if interrupt then
            throw (IO.userError "interruption after an original upper-root column atomic save")
          else pure () }
      let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
      let retainedElimination := Thunk.mk fun _ => Input.Elimination.ofCertificate input elimination rfl
      let entries ← CoherentRootCheckpoint.samplePrefix root input retainedElimination (fun _ _ _ => rfl)
        columns winding directory (max leftPrimitive rightPrimitive)
      let samples := root.approximationSamples entries
      let named := Name.Sampling.approximation samples.view.toNamed
      let cachedPaid := paid.withSamples named named
        (root.approximationSamples_named entries) (root.approximationSamples_named entries)
      unless cachedPaid.leftIndex = paid.leftIndex ∧ cachedPaid.rightIndex = paid.rightIndex do
        throw (IO.userError "saved sample transport changed an original paid comparison index")
      let first := named.sample cachedPaid.leftIndex
      let second := named.sample cachedPaid.rightIndex
      unless normSq (first - second) < (1/16 : Data.Rat.Fraction.Rational) do
        throw (IO.userError "saved actual original samples failed their unchanged comparison request")
      let retried := named.sample cachedPaid.leftIndex
      unless retried = first do
        throw (IO.userError "saved original named sample retry changed its scalar observation")
      let observed := Data.Json.mkObj
        [("request", request), ("first", toJson (gaussianData first)),
         ("second", toJson (gaussianData second)), ("retry", toJson (gaussianData retried))]
      let resultPath := join directory "named-observations.json"
      if ← resultPath.pathExists then
        let stored : Data.Json ← loadJson resultPath
        unless stored == observed do
          throw (IO.userError "saved original named observations differ from their exact checked replay")
      else saveJson resultPath observed
      progress "saved general cubic request: actual original samples and retry consumed the same paid comparison"

/-- Pay the unchanged independent starts on a numerical name compared with the retained original owner. -/
private def dyadicPayment {numericalTrack : Track.Basic.WindingOneTrack polynomial ambient}
    (numerical : CoherentRoot.CertifiedName numericalTrack)
    (agreement : Equivalence.NamedEquivalent root.value.name numerical.value.name)
    (original : Equivalence.NamedEquivalent root.value.name root.value.name) :=
  (agreement.symm.trans (original.trans agreement)).compare 3 7 (1 / 16) (by decide)

/-- Execute the original zero classification and external request on a compared loaded dyadic source.

The original classifier retains its degree-nine difference and exact zero
occurrence. Its equality is composed with the actual original-to-new root
comparison. The resulting starts and tolerance are unchanged; only their
computed new-policy primitive demands determine the finite loaded prefix.
-/
public def checkDyadicGeneralZeroRequest (directory : System.FilePath) (savedOnly interrupt : Bool) : IO Unit := do
  let original := sidecar
  let compared := original.compare original
  let materialized := compared.materialize
  unless differenceCache materialized.difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "dyadic general zero request lost the original self-difference cache")
  match compared.comparison with
  | .distinct _ _ => throw (IO.userError "the actual original self-difference was classified nonzero")
  | .equal equivalent =>
      let directory := join directory "dyadic-general-zero-v1"
      let states := join directory "states"
      let columns : ClearanceCheckpoint.Control IO :=
        { savedOnly := savedOnly
          afterSave := if interrupt then
            throw (IO.userError "interruption after a compared dyadic upper-root column atomic save")
          else pure () }
      let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
      CoherentRootCheckpoint.dyadicFromOriginal root input
        (Input.Elimination.ofCertificate input elimination rfl) columns winding savedOnly states 1
          fun seeded sameOriginal => do
        let agreement : Equivalence.NamedEquivalent root.value.name seeded.root.value.name :=
          sameOriginal ▸ seeded.comparison
        let planned := dyadicPayment seeded.root agreement equivalent
        let leftDemand : Nat := Process.Sampling.stateAt seeded.root.approximation.toProcess
          (show Nat from 0) planned.leftIndex
        let rightDemand : Nat := Process.Sampling.stateAt seeded.root.approximation.toProcess
          (show Nat from 0) planned.rightIndex
        let demand := max leftDemand rightDemand
        progress s!"dyadic general cubic request: starts 3/7 target 1/16 named \
          {planned.leftIndex}/{planned.rightIndex} computed primitive {leftDemand}/{rightDemand}"
        let loaded ← CoherentRootCheckpoint.extendDyadicRefinements input seeded.elimination
          track.initial columns winding savedOnly states seeded.loaded (demand - seeded.last)
        let prepared := CoherentRoot.Accelerated.fromInitial input root seeded.elimination
          (seeded.last + (demand - seeded.last))
          (seeded.first_covered.trans (Nat.le_add_right _ _)) loaded
        let paid := dyadicPayment prepared.root prepared.comparison equivalent
        let leftPrimitive : Nat := Process.Sampling.stateAt prepared.root.approximation.toProcess
          (show Nat from 0) paid.leftIndex
        let rightPrimitive : Nat := Process.Sampling.stateAt prepared.root.approximation.toProcess
          (show Nat from 0) paid.rightIndex
        unless 3 ≤ paid.leftIndex ∧ 7 ≤ paid.rightIndex ∧
            leftPrimitive ≤ prepared.last ∧ rightPrimitive ≤ prepared.last do
          throw (IO.userError "the actual dyadic comparison demand exceeds its loaded prefix or changed a start")
        unless initial.box.diagonalSq = (1 / 32 : Data.Rat.Fraction.Rational) do
          throw (IO.userError "the compared numerical policy changed the original upper cubic initial box")
        let request := Data.Json.mkObj
          [("protocol", toJson "compared-upper-cubic-named-request-dyadic-v1"),
           ("polynomial", toJson (polynomial.coeffs.map gaussianData)),
           ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
           ("initialDiagonal", toJson (fractionData initial.box.diagonalSq)),
           ("leftStart", toJson (3 : Nat)), ("rightStart", toJson (7 : Nat)),
           ("target", toJson (fractionData (1 / 16))),
           ("leftIndex", toJson paid.leftIndex), ("rightIndex", toJson paid.rightIndex),
           ("leftPrimitive", toJson leftPrimitive), ("rightPrimitive", toJson rightPrimitive),
           ("loadedLast", toJson prepared.last)]
        let path := join directory "named-request.json"
        if ← path.pathExists then
          let stored : Data.Json ← loadJson path
          unless stored == request do
            throw (IO.userError "the compared named cubic request differs from its original exact inputs")
        else if savedOnly then
          throw (IO.userError "missing compared named cubic request; header generation forbidden")
        else saveJson path request
        let named := Name.Sampling.approximation prepared.root.value.name
        let first := named.sample paid.leftIndex
        let second := named.sample paid.rightIndex
        unless normSq (first - second) < (1 / 16 : Data.Rat.Fraction.Rational) do
          throw (IO.userError "the compared dyadic samples failed the unchanged original tolerance")
        let retried := named.sample paid.leftIndex
        unless retried = first do
          throw (IO.userError "the compared named cubic sample retry changed its actual observation")
        let observed := Data.Json.mkObj
          [("request", request), ("first", toJson (gaussianData first)),
           ("second", toJson (gaussianData second)), ("retry", toJson (gaussianData retried))]
        let resultPath := join directory "named-observations.json"
        if ← resultPath.pathExists then
          let stored : Data.Json ← loadJson resultPath
          unless stored == observed do
            throw (IO.userError "the compared cubic observations differ from their exact checked replay")
        else if savedOnly then
          throw (IO.userError "missing compared cubic observations; ordinary output generation forbidden")
        else saveJson resultPath observed
        progress "dyadic general cubic request: original zero classifier, compared samples and retry retained"

/-- Measure complete original edge construction on the actual self-difference's localization factors. -/
public def checkLineCache : IO Unit := do
  let original := sidecar
  let difference := original.sub original
  unless differenceCache difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "edge phase lost its actual original self-difference cache")
  TestPurelib.Polynomial.Dense.Gaussian.Path.Pair.profile difference.polynomial difference.residual.degreePositive

/-- Inspect retained origin data on the actual cubic owner and its original general self-difference polynomial. -/
public def checkOriginCache : IO Unit := do
  let original := sidecar
  TestPurelib.Polynomial.Dense.Gaussian.Factorization.Origin.profile original.polynomial
    (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos original.residual.degreePositive)
  let difference := original.sub original
  unless differenceCache difference.cached = some (3, 3, 9, true) do
    throw (IO.userError "origin phase lost its actual original self-difference cache")
  TestPurelib.Polynomial.Dense.Gaussian.Factorization.Origin.profile difference.polynomial
    (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos difference.residual.degreePositive)
  let initial := difference.inspectInitial
  let inspected := Polynomial.Approximation.Gaussian.Residual.Origin.inspect difference.residual initial
  match inspected.outcome with
  | .zero _ _ occurrence _ _ _ =>
      let entry := inspected.preparation.decomposition.positiveMultiplicityEntries.get occurrence.index
      unless entry.part.polynomial.eval 0 = 0 do
        throw (IO.userError "coefficient inspection lost its original exact root occurrence")
      progress "original self-difference: coefficient inspection built its actual original-source zero certificate"
  | .prepared _ _ _ => throw (IO.userError "original self-difference coefficient inspection was incorrectly nonzero")
  | .inconclusive _ _ => throw (IO.userError "original self-difference coefficient inspection remained inconclusive")

/-- Every actual conjugated original cubic sample stays in the reflected original spatial region. -/
private theorem conjugateInside (index : Nat) : ambient.conj.Contains (sidecar.conj.residual.source.sample index) := by
  have same : sidecar.residual.source.sample index = root.approximation.sample index :=
    (Algebraic.Sidecar.ofRoot_sample _ index).trans (PolynomialRoot.Sidecar.ofIsolated_residual_sample _ _ index)
  rewrite [Algebraic.Sidecar.conj_sample, same]
  exact (root.sample_inside index).conj

/-- Each reflected original cached state refines the same reflected source ambient box. -/
private theorem conjugateStateRefines (index : Nat) : (root.stateAt index).box.conj.Refines ambient.conj :=
  (root.stateAt index).refinesAmbient.conj

/-- Inspect the actual direct conjugation constructor with all original cache indices generalized. -/
private def conjugationCache {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {residual : Approximation.Gaussian.Residual polynomial channel}
    (cached : Algebraic.Cached origin polynomial residual) : Bool :=
  match cached with
  | .conj _ => true
  | _ => false

/-- Same-index checked readings of the original conjugated upper and independent lower channels. -/
private abbrev ConjugateObservations :=
  ((index : Nat) → IO {reading : Sequence.SamplePrefix.Entry
    (Name.Sampling.approximation (CoherentNamed.conj root.value).name) // reading.index = index}) ×
  ((index : Nat) → IO {reading : Sequence.SamplePrefix.Entry
    (Name.Sampling.approximation lowerRoot.value.name) // reading.index = index})

/-- Read an isolated input's original view through the same retained raw-state bank.

Both root getter identities retain the original complete isolated owner.
Its transported view keeps the same track and stage, so the supplied state
accessor serves the actual comparison view without reconstructing a root.
-/
private def isolatedInputState {polynomial : CoefficientPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (input : FTA.Positive.Input.PositiveInput polynomial) (states : (index : Nat) → IO (State root index))
    (original : Algebraic.Sidecar.Compared.RootInput
      (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root input))) (index : Nat) :
    IO (State original.view.root index) :=
  original.stateFromRoot (PolynomialRoot.Sidecar.ofIsolated root input) rfl
    (fun actual same view found index => by
      have read : (ownerView : CertifiedName.View actual.owner.channel) → actual.owner.view? = some ownerView →
          (index : Nat) → IO (State ownerView.root index) := by
        cases same
        intro ownerView ownerFound index
        have sameView : CertifiedName.View.ofRoot root input = ownerView := Option.some.inj ownerFound
        cases sameView
        exact states index
      exact actual.stateFromView read view found index) index

/-- The same selected and upper state banks with both original independent comparison actions.

Each action returns the entire ordinary comparison at its original floors
and request bits. The retained readers also supply the later exact gap check.
-/
private abbrev ConjugateComparisons (identified : Algebraic.Sidecar (CoherentNamed.conj root.value)) : Type 2 :=
  ((original : Algebraic.Sidecar.Compared.RootInput identified) →
    (index : Nat) → IO (State original.view.root index)) ×
  ((index : Nat) → IO (State root index)) ×
  (({value : Algebraic.Sidecar.Compared identified lowerSidecar 1 2 //
      value = identified.compare lowerSidecar 1 2} → IO Unit) → IO Unit) ×
  (({value : Algebraic.Sidecar.Compared identified sidecar 2 1 //
      value = identified.compare sidecar 2 1} → IO Unit) → IO Unit)

/-- Compare a complete original conjugation identification with both independent cubic sheets.

The retained sidecar agrees with the complete original identification, including
its selected occurrence and child caches. One computed intrinsic comparison
establishes exchange with the original lower owner, and another retains positive
separation from the original upper sheet. The same retained agreement pays both
the coarse and unit tolerances at the original independent starts. Supplied
observations retain those same named indices and original scalar identities.
Supplied comparison actions retain whole ordinary-comparison equalities and
share their actual selected/upper state banks with the gap check.
-/
private def checkSelectedConjugate
    (selected : {identified : Algebraic.Sidecar (CoherentNamed.conj root.value) //
      identified = sidecar.conj.identify}) (observations : Option ConjugateObservations := none)
    (comparisons : Option (ConjugateComparisons selected.val) := none) : IO Unit := do
  let conjugated := sidecar.conj
  let identified := selected.val
  match identified with
  | ⟨_, _, _, .selected child _ _ _ retained _ _⟩ =>
      unless retained.owner.polynomial.coeffs = conjugated.polynomial.coeffs do
        throw (IO.userError "nonreal cubic result selection lost its complete conjugated annihilator")
      unless conjugationCache child do
        throw (IO.userError "nonreal cubic result selection replaced its actual conjugation child cache")
  | _ => throw (IO.userError "nonreal cubic conjugation did not retain its computed original result selection")
  progress "nonreal cubic conjugation: retained computed selection and actual original child cache"
  let lowerComparison :
      ({value : Algebraic.Sidecar.Compared identified lowerSidecar 1 2 //
        value = identified.compare lowerSidecar 1 2} → IO Unit) → IO Unit := match comparisons with
    | none => fun use => use ⟨identified.compare lowerSidecar 1 2, rfl⟩
    | some (_, _, lower, _) => lower
  let upperComparison :
      ({value : Algebraic.Sidecar.Compared identified sidecar 2 1 //
        value = identified.compare sidecar 2 1} → IO Unit) → IO Unit := match comparisons with
    | none => fun use => use ⟨identified.compare sidecar 2 1, rfl⟩
    | some (_, _, _, upper) => upper
  lowerComparison fun retained => do
    let exchanged := retained.val
    match exchanged.cache with
    | .inr _ => throw (IO.userError "identified nonreal conjugation forced complete difference elimination")
    | .inl intrinsic =>
        match intrinsic.prepared.comparison with
        | .equal _ => pure ()
        | .distinct _ => throw (IO.userError "the actual conjugate did not select the independent lower sheet")
    match exchanged.comparison with
    | .distinct _ _ => throw (IO.userError "the identified conjugate and independent lower owner were separated")
    | .equal agreement =>
        let targets : List {value : Rational // 0 < value} := [⟨4, by decide⟩, ⟨1, by decide⟩]
        for target in targets do
          let paid := agreement.compare 2 1 target.val target.property
          progress s!"nonreal cubic conjugation: pay original request at indices {paid.leftIndex}/{paid.rightIndex}"
          let read : IO (Canonical × Canonical) :=
            match observations with
            | none => do
                let first := (Name.Sampling.approximation (CoherentNamed.conj root.value).name).sample paid.leftIndex
                let second := (Name.Sampling.approximation lowerRoot.value.name).sample paid.rightIndex
                return (first, second)
            | some (left, right) => do
                let first ← left paid.leftIndex
                let second ← right paid.rightIndex
                return (first.val.value, second.val.value)
          let readings ← read
          let first := readings.1
          let second := readings.2
          unless 2 ≤ paid.leftIndex ∧ 1 ≤ paid.rightIndex ∧ normSq (first - second) < target.val do
            throw (IO.userError "computed lower-sheet identification lost its actual conjugated-channel payment")
    upperComparison fun retained => do
      let separated := retained.val
      match separated.cache with
      | .inr _ => throw (IO.userError "identified conjugate-to-upper comparison forced complete elimination")
      | .inl intrinsic =>
          match intrinsic.prepared.comparison with
          | .equal _ => throw (IO.userError "actual upper and lower cubic sheets were merged")
          | .distinct separation =>
              let gap := separation.separation.gap
              let read : IO (Canonical × Canonical) := match comparisons with
                | none => pure (intrinsic.left.view.root.approximation.sample separation.leftIndex,
                    intrinsic.right.view.root.approximation.sample separation.rightIndex)
                | some (selectedStates, upperStates, _, _) => do
                    let first ← selectedStates intrinsic.left separation.leftIndex
                    let second ← isolatedInputState root input.toPositive upperStates intrinsic.right
                      separation.rightIndex
                    return (first.val.box.anchor, second.val.box.anchor)
              let readings ← read
              let first := readings.1
              let second := readings.2
              unless 2 ≤ separation.leftIndex ∧ 1 ≤ separation.rightIndex ∧ 0 < gap ∧
                  gap ^ 2 ≤ normSq (first - second) do
                throw (IO.userError "nonreal conjugation lost its paid positive original-sheet gap")
              match separated.decision with
              | .excluded _ => throw (IO.userError "different cubic sheets lost their prepared actual difference")
              | .prepared prepared =>
                  unless prepared.apart.certificate.lowerSq = gap ^ 2 / 8 do
                    throw (IO.userError "nonreal conjugation did not consume its same stored pair gap")
      progress "nonreal cubic conjugation: identified lower result exchanges independent sheets and retains their gap"

/-- Restore the original conjugation selection through checked original primitive source states.

The original factor and root-pair caches compute the unchanged anchor request.
Its scalar comes from the original state reader, and the resulting selection
gives exactly the original identified sidecar. Separate policies control missing
source work and preparation/locator work. Saved-only failures retain the existing
reader's unresolved request; no replacement root is selected. The continuation
also receives the selected view's accessor into that same factor state bank. -/
private def withCachedConjugateSelection (directory : System.FilePath)
    (sourceSavedOnly preparationSavedOnly : Bool)
    (use : (identified : {identified : Algebraic.Sidecar (CoherentNamed.conj root.value) //
      identified = sidecar.conj.identify}) → ((index : Nat) → IO (State root index)) →
      ((original : Algebraic.Sidecar.Compared.RootInput identified.val) →
        (index : Nat) → IO (State original.view.root index)) → IO Unit) : IO Unit := do
  progress "nonreal cubic selection: prepare original conjugation localization"
  let conjugated := sidecar.conj
  let columns : ClearanceCheckpoint.Control IO := { savedOnly := preparationSavedOnly }
  let winding : WindingCheckpoint.Control IO := { savedOnly := preparationSavedOnly }
  let refinement ← RootRefinementCheckpoint.Control.create preparationSavedOnly
  RootSelectionCheckpoint.Multiplicity.prepare conjugated.residual columns winding refinement
    (join directory "prepared-factors") fun retained => do
    let preparation := retained.val
    let retainedElimination := Thunk.mk fun _ => Input.Elimination.ofCertificate input elimination rfl
    let upperStates ← stateReader root (readStateWith root
      (nextState root input retainedElimination (fun _ _ _ => rfl)
        { savedOnly := sourceSavedOnly } { savedOnly := sourceSavedOnly } directory))
    progress "nonreal cubic selection: retain original factor and root-pair caches"
    let states ← RootSelectionCheckpoint.Multiplicity.stateReaders preparation.roots
      (fun index => Polynomial.Approximation.Gaussian.Localization.Preparation.factor_eq_ofResidual
        conjugated.polynomial conjugated.residual.degreePositive conjugated.residual.source
        conjugated.residual.scale conjugated.residual.scale_nonnegative conjugated.residual.bound
        preparation retained.property index) columns winding (join directory "prepared-locator")
    let factorPairs := preparation.factorPairs
    preparation.roots.pairsWithStates factorPairs states fun rootPairs => do
      RootSelectionCheckpoint.Multiplicity.select preparation
        (fun request => RootSelectionCheckpoint.Multiplicity.nearbyPrepared conjugated.residual preparation
          retained.property request (fun index => do
          progress s!"nonreal cubic selection: restore original primitive source index {index}"
          let current ← upperStates index
          let value := current.val.box.anchor
          have sample : value = root.approximation.sample index :=
            (congrArg (fun state : CoherentRoot.WindingOneState polynomial ambient => state.box.anchor)
              current.property).trans (root.sample_stateAt index).symm
          have actual : preparation.source.sample index = (root.approximation.sample index).conj :=
            (congrArg (fun source : Geometric.GeometricApproximation => source.sample index)
              preparation.source_eq).trans (conjugate_sample index)
          return ⟨value.conj, (congrArg Data.Gaussian.Basic.conj sample).trans actual.symm⟩)
            columns winding (join directory "prepared-locator") (some states))
        (fun selected => do
          let identified := conjugated.withSelection preparation selected.val selected.property
          have original : identified = conjugated.identify := by
            have noChild : sidecar.cached.scalar? = none := by
              change sidecar.scalar? = none
              exact cubicScalarNone root
            have noScalar : conjugated.cached.scalar? = none := by
              change sidecar.conj.cached.scalar? = none
              rewrite [Algebraic.Sidecar.conj_cached]
              exact Algebraic.Cached.scalar?_conj_of_none _ noChild
            have noRoot : conjugated.cached.root? = none := rfl
            rewrite [Algebraic.Sidecar.identify_none]
            rewrite [noRoot, noScalar]
            rewrite [← retained.property]
            change conjugated.withSelection preparation selected.val _ =
              conjugated.withSelection preparation preparation.select rfl
            rcases selected with ⟨value, selectedEq⟩
            cases selectedEq
            rfl
          unless selected.val.multiplicity = 1 ∧ selected.val.factorPolynomial.natDegree = 3 do
            throw (IO.userError "cached conjugation selection changed its original cubic factor or multiplicity")
          match identified with
          | ⟨_, _, _, .selected child _ _ _ retained _ _⟩ =>
              unless retained.owner.polynomial.coeffs = conjugated.polynomial.coeffs ∧ conjugationCache child do
                throw (IO.userError "cached conjugation selection replaced its original annihilator or child cache")
          | _ => throw (IO.userError "cached conjugation selection lost its original selected result")
          progress "nonreal cubic selection: complete original identification retained from checked source states"
          let selectedStates (original : Algebraic.Sidecar.Compared.RootInput identified) (index : Nat) :
              IO (State original.view.root index) :=
            original.stateFromRoot (PolynomialRoot.Sidecar.ofSelection conjugated.residual preparation selected.val)
              (Algebraic.Sidecar.withSelection_root conjugated preparation selected.val selected.property)
              (fun actual same view found index => by
                have read : (ownerView : CertifiedName.View actual.owner.channel) →
                    actual.owner.view? = some ownerView → (index : Nat) → IO (State ownerView.root index) := by
                  cases same
                  exact fun ownerView ownerFound index =>
                    selected.val.stateFromView states ownerView ownerFound index
                exact actual.stateFromView read view found index) index
          use ⟨identified, original⟩ upperStates selectedStates)
        ⟨factorPairs, rfl⟩ rootPairs

/-- Check the original conjugation selection using its retained preparation and primitive states.

Separate saved-only policies govern original source work and factor/locator
work. The complete selected sidecar agrees with the original identification;
this component stops before the independent-sheet comparison requests.
-/
public def checkCachedConjugateSelection (directory : System.FilePath)
    (sourceSavedOnly : Bool := true) (preparationSavedOnly : Bool := false) : IO Unit :=
  withCachedConjugateSelection directory sourceSavedOnly preparationSavedOnly (fun _ _ _ => pure ())

/-- Check nonreal conjugation against both independent original cubic sheets.

An optional checkpoint directory restores the complete original selection and
passes that actual sidecar to both comparisons. The same lower-sheet agreement
pays the original coarse and unit requests; upper-sheet separation retains its
original starts and positive gap. The source policy also governs named readings
from the retained upper and independent lower banks. Both comparison
classifications use exact replay of their ordinary preparation, and gap
readings consume those same banks. Agreement indices retain the original
procedure and the original coarse and unit requests.
-/
public def checkConjugateIdentification (directory : Option System.FilePath := none)
    (sourceSavedOnly : Bool := true) (preparationSavedOnly : Bool := false) : IO Unit := do
  let conjugated := sidecar.conj
  let reflected := ambient.conj
  unless reflected.xLower = lowerAmbient.xLower ∧ reflected.xUpper = lowerAmbient.xUpper ∧
      reflected.yLower = lowerAmbient.yLower ∧ reflected.yUpper = lowerAmbient.yUpper ∧
      reflected.Contains (conjugated.residual.source.sample 0) do
    throw (IO.userError "nonreal cubic conjugation lost its original reflected region and actual cache sample")
  match directory with
  | none =>
      progress "nonreal cubic conjugation: compute original residual localization and selected occurrence"
      checkSelectedConjugate ⟨conjugated.identify, rfl⟩
  | some directory =>
      withCachedConjugateSelection directory sourceSavedOnly preparationSavedOnly
          fun selected upperStates selectedStates => do
        let retainedElimination := Thunk.mk fun _ => Input.Elimination.ofCertificate input elimination rfl
        let lowerStates ← stateReader lowerRoot (readStateWith lowerRoot
          (nextState lowerRoot input retainedElimination (fun _ _ _ => rfl)
            { savedOnly := sourceSavedOnly } { savedOnly := sourceSavedOnly }
            (join directory "lower-observations")))
        let observations : ConjugateObservations :=
          (fun index => do
            let reading ← namedSampleWithStates root upperStates index
            have actual : reading.val.value = (Name.Sampling.approximation root.value.name).sample index :=
              reading.val.value_eq.trans
                (congrArg (fun stage => (Name.Sampling.approximation root.value.name).sample stage) reading.property)
            return ⟨⟨index, reading.val.value.conj,
              (congrArg Data.Gaussian.Basic.conj actual).trans (CoherentNamed.conj_sample root.value index).symm⟩,
                rfl⟩,
          fun index => namedSampleWithStates lowerRoot lowerStates index)
        let columns : ClearanceCheckpoint.Control IO := { savedOnly := preparationSavedOnly }
        let winding : WindingCheckpoint.Control IO := { savedOnly := preparationSavedOnly }
        let control ← RootRefinementCheckpoint.Control.create preparationSavedOnly
        let comparisons : ConjugateComparisons selected.val :=
          (selectedStates, upperStates,
            fun use => RootSelectionCheckpoint.compareSidecars selected.val lowerSidecar 1 2
              (fun inputs => pure (selectedStates inputs.1,
                fun index => isolatedInputState lowerRoot input.toPositive lowerStates inputs.2 index))
              (fun _ algebra degree => pure (Input.Elimination.ofInput ⟨algebra.squarefree, degree⟩))
              columns winding control (join directory "independent-lower-comparison") true true true use,
            fun use => RootSelectionCheckpoint.compareSidecars selected.val sidecar 2 1
              (fun inputs => pure (selectedStates inputs.1,
                fun index => isolatedInputState root input.toPositive upperStates inputs.2 index))
              (fun _ algebra degree => pure (Input.Elimination.ofInput ⟨algebra.squarefree, degree⟩))
              columns winding control (join directory "independent-upper-comparison") true true true use)
        checkSelectedConjugate selected (some observations) (some comparisons)

end TestPurelib.Approximation.Gaussian.CubicSheets

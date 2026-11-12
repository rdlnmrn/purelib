module
import Purelib.RootIsolation.FTA.Squarefree.Prepare

import scripts.checkpoint.CoherentRootSamples
import Purelib.Approximation.Gaussian.Sequence.SamplePrefix.Addition
import Purelib.System.FilePath
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import scripts.checkpoint.Integration

public import Purelib.Polynomial.Approximation.Gaussian.Residual.EvenQuartic
public import Purelib.Polynomial.Approximation.Gaussian.Residual.QuadraticSum
import Purelib.Polynomial.Approximation.Gaussian.Residual.Conjugation
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
import Purelib.Riemann.RootContinuation.CoherentRoot.Reality
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Rational.Bezout.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.System.IO
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
import Purelib.Riemann.RootContinuation.CoherentRoot.PointComparison
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource

/-! # The original positive sqrt-two plus sqrt-three channel and an independent local quartic owner -/

namespace TestPurelib.Approximation.Gaussian.QuarticAdmission

open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.System.FilePath (join)
open Purelib.Data.Json (toJson)
open IntegrationCheckpoint (fractionData gaussianData)
open Purelib.Polynomial.Clearance.Box
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Approximation
open Purelib.Data.Gaussian

/-- The original square-root-of-two coefficient table. -/
private def firstPolynomial := Power.Gaussian.rootPolynomial 2 ⟨2, by decide⟩

/-- The original square-root-of-three coefficient table. -/
private def secondPolynomial := Power.Gaussian.rootPolynomial 3 ⟨2, by decide⟩

/-- The independently admitted quartic's original real coefficient table. -/
private def quarticPolynomial := EvenQuartic.polynomial 10 1

/-- The actual local positive box of the first quadratic root. -/
private def firstBox : Box := ⟨11 / 8, 23 / 16, -1 / 64, 1 / 64, by decide +kernel, by decide +kernel⟩

/-- The actual local positive box of the second quadratic root. -/
private def secondBox : Box := ⟨27 / 16, 7 / 4, -1 / 64, 1 / 64, by decide +kernel, by decide +kernel⟩

/-- The independent original quartic owner retains this strictly positive local box. -/
private def quarticBox : Box := ⟨3, 13 / 4, -1 / 16, 1 / 16, by decide +kernel, by decide +kernel⟩

/-- The displayed sum box adds the same four original quadratic box endpoints. -/
private def sumBox : Box := ⟨firstBox.xLower + secondBox.xLower, firstBox.xUpper + secondBox.xUpper,
  firstBox.yLower + secondBox.yLower, firstBox.yUpper + secondBox.yUpper,
  Order.Arithmetic.add_le_add_direct firstBox.x_valid secondBox.x_valid,
  Order.Arithmetic.add_le_add_direct firstBox.y_valid secondBox.y_valid⟩

/-- The same original first coefficient table has its actual finite squarefree input. -/
private def firstInput : Input firstPolynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨2, by decide⟩
  degreeAtLeastTwo := by
    unfold firstPolynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The generic separated-axis certificate consumes the original first coefficients. -/
private def firstElimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  firstPolynomial firstInput.nonzero firstInput.degreePositive

/-- The actual first local state retains four original small Euclidean clearances and checked winding. -/
private def firstInitial : State.WindingOne.Basic.WindingOneState firstPolynomial firstBox :=
  let left := Line.Bezout.verticalOfCoprime firstPolynomial firstBox firstBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal firstPolynomial firstBox.xLower)
      (Path.Axis.verticalPathImag firstPolynomial firstBox.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime firstPolynomial firstBox firstBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal firstPolynomial firstBox.xUpper)
      (Path.Axis.verticalPathImag firstPolynomial firstBox.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime firstPolynomial firstBox firstBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal firstPolynomial firstBox.yLower)
      (Path.Axis.horizontalPathImag firstPolynomial firstBox.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime firstPolynomial firstBox firstBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal firstPolynomial firstBox.yUpper)
      (Path.Axis.horizontalPathImag firstPolynomial firstBox.yUpper)
      (by decide +kernel) (by decide +kernel))
  { box := firstBox
    refinesAmbient := Box.refines_refl firstBox
    proper := by constructor <;> decide +kernel
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The original generic Newton track retains this same first local polynomial and winding state. -/
private def firstTrack := Track.Newton.Build.ofInitial
  firstInput.degreeAtLeastTwo firstInput.squarefree firstElimination firstInitial

/-- The original first numerical channel retains its same actual root-state cache. -/
private def firstRoot := CoherentRoot.certifiedName firstTrack firstInput.degreePositive

/-- Intrinsic finite admission consumes the same original first winding owner and numerical cache. -/
private def firstSidecar := Algebraic.Sidecar.ofRoot
  (PolynomialRoot.Sidecar.ofIsolated firstRoot firstInput.toPositive)

/-- The first admitted sidecar retains its same actual original quadratic polynomial. -/
private theorem firstSidecar_polynomial : firstSidecar.polynomial = firstPolynomial :=
  (Algebraic.Sidecar.ofRoot_polynomial _).trans (PolynomialRoot.Sidecar.ofIsolated_residual_polynomial _ _)

/-- Every first admitted residual sample reads that same original root-state cache. -/
private theorem firstSidecar_sample (index : Nat) :
    firstSidecar.residual.source.sample index = firstRoot.approximation.sample index :=
  (Algebraic.Sidecar.ofRoot_sample _ index).trans (PolynomialRoot.Sidecar.ofIsolated_residual_sample _ _ index)

/-- The same original second coefficient table has its actual finite squarefree input. -/
private def secondInput : Input secondPolynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨2, by decide⟩
  degreeAtLeastTwo := by
    unfold secondPolynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The generic separated-axis certificate consumes the original second coefficients. -/
private def secondElimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  secondPolynomial secondInput.nonzero secondInput.degreePositive

/-- The actual second local state retains four original small Euclidean clearances and checked winding. -/
private def secondInitial : State.WindingOne.Basic.WindingOneState secondPolynomial secondBox :=
  let left := Line.Bezout.verticalOfCoprime secondPolynomial secondBox secondBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal secondPolynomial secondBox.xLower)
      (Path.Axis.verticalPathImag secondPolynomial secondBox.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime secondPolynomial secondBox secondBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal secondPolynomial secondBox.xUpper)
      (Path.Axis.verticalPathImag secondPolynomial secondBox.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime secondPolynomial secondBox secondBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal secondPolynomial secondBox.yLower)
      (Path.Axis.horizontalPathImag secondPolynomial secondBox.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime secondPolynomial secondBox secondBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal secondPolynomial secondBox.yUpper)
      (Path.Axis.horizontalPathImag secondPolynomial secondBox.yUpper)
      (by decide +kernel) (by decide +kernel))
  { box := secondBox
    refinesAmbient := Box.refines_refl secondBox
    proper := by constructor <;> decide +kernel
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The original generic Newton track retains this same second local polynomial and winding state. -/
private def secondTrack := Track.Newton.Build.ofInitial
  secondInput.degreeAtLeastTwo secondInput.squarefree secondElimination secondInitial

/-- The original second numerical channel retains its same actual root-state cache. -/
private def secondRoot := CoherentRoot.certifiedName secondTrack secondInput.degreePositive

/-- Intrinsic finite admission consumes the same original second winding owner and numerical cache. -/
private def secondSidecar := Algebraic.Sidecar.ofRoot
  (PolynomialRoot.Sidecar.ofIsolated secondRoot secondInput.toPositive)

/-- The second admitted sidecar retains its same actual original quadratic polynomial. -/
private theorem secondSidecar_polynomial : secondSidecar.polynomial = secondPolynomial :=
  (Algebraic.Sidecar.ofRoot_polynomial _).trans (PolynomialRoot.Sidecar.ofIsolated_residual_polynomial _ _)

/-- Every second admitted residual sample reads that same original root-state cache. -/
private theorem secondSidecar_sample (index : Nat) :
    secondSidecar.residual.source.sample index = secondRoot.approximation.sample index :=
  (Algebraic.Sidecar.ofRoot_sample _ index).trans (PolynomialRoot.Sidecar.ofIsolated_residual_sample _ _ index)

/-- The same original quartic coefficient table has its actual finite squarefree input. -/
private def quarticInput : Input quarticPolynomial where
  squarefree := Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD quarticPolynomial
    (Dense.Gaussian.GCD.derivative quarticPolynomial)
    (Dense.Gaussian.GCD.extendedGCD quarticPolynomial (Dense.Gaussian.GCD.derivative quarticPolynomial))
    rfl (by decide +kernel) (by decide +kernel)
  degreeAtLeastTwo := by decide +kernel

/-- The generic separated-axis certificate consumes the original quartic coefficients. -/
private def quarticElimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  quarticPolynomial quarticInput.nonzero quarticInput.degreePositive

/-- The actual quartic local state retains four original small Euclidean clearances and checked winding. -/
private def quarticInitial : State.WindingOne.Basic.WindingOneState quarticPolynomial quarticBox :=
  let left := Line.Bezout.verticalOfCoprime quarticPolynomial quarticBox quarticBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal quarticPolynomial quarticBox.xLower)
      (Path.Axis.verticalPathImag quarticPolynomial quarticBox.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime quarticPolynomial quarticBox quarticBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal quarticPolynomial quarticBox.xUpper)
      (Path.Axis.verticalPathImag quarticPolynomial quarticBox.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime quarticPolynomial quarticBox quarticBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal quarticPolynomial quarticBox.yLower)
      (Path.Axis.horizontalPathImag quarticPolynomial quarticBox.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime quarticPolynomial quarticBox quarticBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal quarticPolynomial quarticBox.yUpper)
      (Path.Axis.horizontalPathImag quarticPolynomial quarticBox.yUpper)
      (by decide +kernel) (by decide +kernel))
  { box := quarticBox
    refinesAmbient := Box.refines_refl quarticBox
    proper := by constructor <;> decide +kernel
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The original generic Newton track retains this same quartic local polynomial and winding state. -/
private def quarticTrack := Track.Newton.Build.ofInitial
  quarticInput.degreeAtLeastTwo quarticInput.squarefree quarticElimination quarticInitial

/-- The original quartic numerical channel retains its same actual root-state cache. -/
private def quarticRoot := CoherentRoot.certifiedName quarticTrack quarticInput.degreePositive

/-- Intrinsic finite admission consumes the same original quartic winding owner and numerical cache. -/
private def quarticSidecar := Algebraic.Sidecar.ofRoot
  (PolynomialRoot.Sidecar.ofIsolated quarticRoot quarticInput.toPositive)

/-- The independent other positive quartic branch lies strictly below the original sum branch. -/
private def smallQuarticBox : Box := ⟨1 / 4, 3 / 8, -1 / 128, 1 / 128, by decide +kernel, by decide +kernel⟩

/-- The other positive quartic root has its own checked original winding state. -/
private def smallQuarticInitial : State.WindingOne.Basic.WindingOneState quarticPolynomial smallQuarticBox :=
  let left := Line.Bezout.verticalOfCoprime quarticPolynomial smallQuarticBox smallQuarticBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal quarticPolynomial smallQuarticBox.xLower)
      (Path.Axis.verticalPathImag quarticPolynomial smallQuarticBox.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime quarticPolynomial smallQuarticBox smallQuarticBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal quarticPolynomial smallQuarticBox.xUpper)
      (Path.Axis.verticalPathImag quarticPolynomial smallQuarticBox.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime quarticPolynomial smallQuarticBox smallQuarticBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal quarticPolynomial smallQuarticBox.yLower)
      (Path.Axis.horizontalPathImag quarticPolynomial smallQuarticBox.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime quarticPolynomial smallQuarticBox smallQuarticBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal quarticPolynomial smallQuarticBox.yUpper)
      (Path.Axis.horizontalPathImag quarticPolynomial smallQuarticBox.yUpper)
      (by decide +kernel) (by decide +kernel))
  { box := smallQuarticBox
    refinesAmbient := Box.refines_refl smallQuarticBox
    proper := by constructor <;> decide +kernel
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The original generic Newton track retains this same quartic local polynomial and winding state. -/
private def smallQuarticTrack := Track.Newton.Build.ofInitial
  quarticInput.degreeAtLeastTwo quarticInput.squarefree quarticElimination smallQuarticInitial

/-- The original quartic numerical channel retains its same actual root-state cache. -/
private def smallQuarticRoot := CoherentRoot.certifiedName smallQuarticTrack quarticInput.degreePositive

/-- Intrinsic finite admission consumes the same original quartic winding owner and numerical cache. -/
private def smallQuarticSidecar := Algebraic.Sidecar.ofRoot
  (PolynomialRoot.Sidecar.ofIsolated smallQuarticRoot quarticInput.toPositive)

/-- The independent correlated input has its own displayed square-root-of-eight polynomial. -/
private def eightPolynomial := Power.Gaussian.rootPolynomial 8 ⟨2, by decide⟩

/-- The independent square-root-of-eight owner retains this positive original ambient box. -/
private def eightBox : Box := ⟨11 / 4, 23 / 8, -1 / 64, 1 / 64, by decide +kernel, by decide +kernel⟩

/-- The same original eight coefficient table has its actual finite squarefree input. -/
private def eightInput : Input eightPolynomial where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) ⟨2, by decide⟩
  degreeAtLeastTwo := by
    unfold eightPolynomial
    rewrite [Power.Gaussian.rootPolynomial_degree]
    decide

/-- The generic separated-axis certificate consumes the original eight coefficients. -/
private def eightElimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
  eightPolynomial eightInput.nonzero eightInput.degreePositive

/-- The actual eight local state retains four original small Euclidean clearances and checked winding. -/
private def eightInitial : State.WindingOne.Basic.WindingOneState eightPolynomial eightBox :=
  let left := Line.Bezout.verticalOfCoprime eightPolynomial eightBox eightBox.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal eightPolynomial eightBox.xLower)
      (Path.Axis.verticalPathImag eightPolynomial eightBox.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime eightPolynomial eightBox eightBox.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal eightPolynomial eightBox.xUpper)
      (Path.Axis.verticalPathImag eightPolynomial eightBox.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime eightPolynomial eightBox eightBox.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal eightPolynomial eightBox.yLower)
      (Path.Axis.horizontalPathImag eightPolynomial eightBox.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime eightPolynomial eightBox eightBox.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal eightPolynomial eightBox.yUpper)
      (Path.Axis.horizontalPathImag eightPolynomial eightBox.yUpper)
      (by decide +kernel) (by decide +kernel))
  { box := eightBox
    refinesAmbient := Box.refines_refl eightBox
    proper := by constructor <;> decide +kernel
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
    rawWindingFour := by decide +kernel
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The original generic Newton track retains this same eight local polynomial and winding state. -/
private def eightTrack := Track.Newton.Build.ofInitial
  eightInput.degreeAtLeastTwo eightInput.squarefree eightElimination eightInitial

/-- The original eight numerical channel retains its same actual root-state cache. -/
private def eightRoot := CoherentRoot.certifiedName eightTrack eightInput.degreePositive

/-- Intrinsic finite admission consumes the same original eight winding owner and numerical cache. -/
private def eightSidecar := Algebraic.Sidecar.ofRoot
  (PolynomialRoot.Sidecar.ofIsolated eightRoot eightInput.toPositive)

/-- The eight admitted sidecar retains its same actual original quadratic polynomial. -/
private theorem eightSidecar_polynomial : eightSidecar.polynomial = eightPolynomial :=
  (Algebraic.Sidecar.ofRoot_polynomial _).trans (PolynomialRoot.Sidecar.ofIsolated_residual_polynomial _ _)

/-- Every eight admitted residual sample reads that same original root-state cache. -/
private theorem eightSidecar_sample (index : Nat) :
    eightSidecar.residual.source.sample index = eightRoot.approximation.sample index :=
  (Algebraic.Sidecar.ofRoot_sample _ index).trans (PolynomialRoot.Sidecar.ofIsolated_residual_sample _ _ index)

/-- The sum certificate retains both original positive quadratic numerical owners and their cofactor caches. -/
private def sumCertificate := Gaussian.Residual.QuadraticSum.ofResiduals
  firstRoot.residualCertificate secondRoot.residualCertificate

/-- The default production arithmetic reads those same original root sidecars. -/
private def sumSidecar := firstSidecar.add secondSidecar

/-- Both actual original root channels remain in the checked-expression environment. -/
private def environment : Fin 2 → Annotated := fun index =>
  if index.val = 0 then Annotated.opaque firstRoot.value else Annotated.opaque secondRoot.value

/-- The same actual original sum program has the coefficient-computed quartic residual. -/
private def sumResidual := sumCertificate.residualCertificate

/-- Every retained sum sample reads both same-index original root caches inside their original summed box. -/
private theorem sumInside (index : Nat) : sumBox.Contains (sumResidual.source.sample index) := by
  rewrite [sumResidual, sumCertificate.residualCertificate_sample]
  change sumBox.Contains (firstRoot.approximation.sample index + secondRoot.approximation.sample index)
  have first := firstRoot.sample_inside index
  have second := secondRoot.sample_inside index
  exact ⟨Order.Arithmetic.add_le_add_direct first.1 second.1,
    Order.Arithmetic.add_le_add_direct first.2.1 second.2.1,
    Order.Arithmetic.add_le_add_direct first.2.2.1 second.2.2.1,
    Order.Arithmetic.add_le_add_direct first.2.2.2 second.2.2.2⟩

/-- The independently isolated quartic consumes its same actual original numerical residual. -/
private def quarticResidual : Gaussian.Residual quarticPolynomial quarticRoot.value :=
  quarticRoot.residualCertificate

/-- Every retained quartic sample stays inside its original positive winding-one box. -/
private theorem quarticInside (index : Nat) : quarticBox.Contains (quarticResidual.source.sample index) :=
  quarticRoot.sample_inside index

/-- The computed original-tail gap proves equality of the unchanged sum channel and independent quartic channel.

No successful attempt or comparison bound is supplied. The actual inspection
computes its box interval, and the only unresolved branch contradicts that
same exact positive endpoint calculation.
-/
private def agreement : Equivalence.NamedEquivalent
    (CoherentNamed.add firstRoot.value secondRoot.value).name quarticRoot.value.name :=
  match Gaussian.Residual.EvenQuartic.inspect sumResidual quarticResidual sumBox quarticBox 0
      (fun index _ => sumInside index) (fun index _ => quarticInside index) with
  | .ready certificate _ _ => certificate.equivalent
  | .unresolved attempt firstBox_eq secondBox_eq failed =>
      have positive : 0 < attempt.factorBounds.lower := by
        rewrite [attempt.factorBounds_eq, firstBox_eq, secondBox_eq]
        decide +kernel
      (failed positive).elim

/-- Conjugation leaves the independent original quartic's actual real coefficient table unchanged. -/
private theorem quarticConjugate_eq : Dense.Gaussian.Conjugation.conjugate quarticPolynomial = quarticPolynomial :=
  by decide +kernel

/-- Conjugating the independent owner retains its same original sample cache and numerical residual. -/
private def quarticConjugateResidual : Gaussian.Residual quarticPolynomial
    (CoherentNamed.conj quarticRoot.value) :=
  Eq.mp (congrArg (fun polynomial => Gaussian.Residual polynomial
    (CoherentNamed.conj quarticRoot.value)) quarticConjugate_eq) quarticResidual.conj

/-- Every conjugated original quartic sample remains in that same symmetric positive box. -/
private theorem quarticConjugateInside (index : Nat) :
    quarticBox.Contains (quarticConjugateResidual.source.sample index) := by
  change quarticBox.Contains (quarticRoot.approximation.sample index).conj
  have reflected := (quarticInside index).conj
  have same : quarticBox.conj = quarticBox := by
    apply Box.ext <;> decide +kernel
  rewrite [same] at reflected
  exact reflected

/-- One wider actual box gives a retained finite inconclusive sufficient comparison. -/
private def wide : Box := ⟨0, 4, -4, 4, by decide, by decide⟩

/-- Both original sum tails also remain inside this same wider attempted box. -/
private theorem sumWide (index : Nat) : wide.Contains (sumResidual.source.sample index) :=
  (show sumBox.Refines wide from by
    constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor <;> decide +kernel).contains (sumInside index)

/-- The original independent quartic tail also remains inside the same wider attempted box. -/
private theorem quarticWide (index : Nat) : wide.Contains (quarticResidual.source.sample index) :=
  (show quarticBox.Refines wide from by
    constructor
    · decide +kernel
    · constructor
      · decide +kernel
      · constructor <;> decide +kernel).contains (quarticInside index)

/-- Read the actual original sum program directly from its retained specialized arithmetic child cache. -/
private def quadraticSample? {channel : CoherentNamed} {origin : Algebraic.Origin channel}
    {polynomial} {residual : Gaussian.Residual polynomial channel}
    (cache : Algebraic.Cached origin polynomial residual) : Option Data.Gaussian.Basic.Canonical :=
  match cache with
  | .quadraticSum _ _ _ _ _ _ retained => some (retained.result.sample 0)
  | _ => none

/-- Print and flush one finite native original-owner checkpoint. -/
private def progress (message : String) : IO Unit := do
  System.IO.println message
  (← IO.getStdout).flush

/-- Construct the original positive owners and retain their computed local quartic comparison. -/
public def check : IO Unit := do
  progress "quartic: retain both original positive quadratic winding owners"
  match (firstRoot.inspectQuadratic 2 0).outcome, (secondRoot.inspectQuadratic 3 0).outcome with
  | .ready _, .ready _ => pure ()
  | _, _ => throw (IO.userError "an original quadratic reality certificate has a finite unresolved condition")
  unless 0 < (firstRoot.approximation.sample 0).re do
    throw (IO.userError "the original first positive box sample lost its positive real coordinate")
  progress "quartic: compute same original two-owner arithmetic residual"
  let originalSum := sumCertificate
  unless originalSum.result.sample 0 =
      firstRoot.approximation.sample 0 + secondRoot.approximation.sample 0 do
    throw (IO.userError "the original sum residual lost its actual two-owner same-index sample")
  let production := sumSidecar
  unless production.polynomial.coeffs = quarticPolynomial.coeffs do
    throw (IO.userError "the automatic original quadratic sum did not consume its computed quartic certificate")
  match quadraticSample? production.cached with
  | some retained =>
      unless retained = originalSum.result.sample 0 do
        throw (IO.userError "the original production sum cache read different original samples")
  | none => throw (IO.userError "the original sum lost its retained specialized child caches")
  match ((Admitted.atom environment ⟨0, by decide⟩ firstSidecar).add
      (Admitted.atom environment ⟨1, by decide⟩ secondSidecar)).run with
  | .completed completed =>
      let completed := completed.materialize
      unless completed.sidecar.polynomial.coeffs = quarticPolynomial.coeffs do
        throw (IO.userError "checked original sum completion lost the automatic retained quartic evidence")
      match quadraticSample? completed.sidecar.cached with
      | some retained =>
          unless retained = originalSum.result.sample 0 do
            throw (IO.userError "the checked original sum cache lost its actual original child samples")
      | none => throw (IO.userError "checked original sum completion lost its retained original quadratic child caches")
  | _ => throw (IO.userError "the two admitted original quadratic owners did not complete their checked sum")
  progress "quartic: automatic production sum retained both original admitted child caches"
  progress "quartic: retain independent original positive quartic winding owner"
  let originalQuartic := quarticRoot
  unless originalQuartic.approximation.sample 0 = (originalQuartic.stateAt 0).box.anchor do
    throw (IO.userError "the independent original quartic sample lost its actual cache readback")
  let reality := Gaussian.Residual.EvenQuartic.inspect quarticResidual quarticConjugateResidual
    quarticBox quarticBox 0 (fun index _ => quarticInside index) (fun index _ => quarticConjugateInside index)
  match reality with
  | .unresolved _ _ _ _ => throw (IO.userError "the independent original quartic reality gap remains unresolved")
  | .ready _ _ _ => progress "quartic: actual original independent branch conjugacy certificate retained"
  let inconclusive := Gaussian.Residual.EvenQuartic.inspect sumResidual quarticResidual
    wide wide 0 (fun index _ => sumWide index) (fun index _ => quarticWide index)
  match inconclusive with
  | .ready _ _ _ => throw (IO.userError "the original wide sufficient comparison unexpectedly separated")
  | .unresolved attempted _ _ _ =>
      unless attempted.floor = 0 do throw (IO.userError "the unresolved original comparison lost its attempted floor")
      progress "quartic: actual inconclusive gap attempt retains original programs, boxes and floor"
  let comparison := Gaussian.Residual.EvenQuartic.inspect sumResidual quarticResidual
    sumBox quarticBox 0 (fun index _ => sumInside index) (fun index _ => quarticInside index)
  match comparison with
  | .unresolved _ _ _ _ => throw (IO.userError "the original quartic factor gap remains a finite local obligation")
  | .ready certificate _ _ =>
      unless 0 < certificate.factorBounds.lower do
        throw (IO.userError "the retained original divided-difference gap lost its positive computed endpoint")
      progress "quartic: actual positive box gap and both original residual caches retained"

/-- Pay independent original-name comparison requests and read their same retained numerical observations. -/
public def checkRequests : IO Unit := do
  progress "quartic requests: compute original-channel comparison from independent starts zero and one"
  let first := agreement.compare 0 1 1 (by decide)
  unless 0 ≤ first.leftIndex ∧ 1 ≤ first.rightIndex do
    throw (IO.userError "the original quartic comparison lost an independent starting index")
  progress s!"quartic requests: first paid indices {first.leftIndex}, {first.rightIndex}"
  progress "quartic requests: read original positive quadratic-sum observation"
  let left := (Name.Sampling.approximation
    (CoherentNamed.add firstRoot.value secondRoot.value).name).sample first.leftIndex
  progress s!"quartic requests: actual sum observation signs {decide (left.re < 0)}, {decide (left.im < 0)}"
  progress "quartic requests: read independently owned positive quartic observation"
  let right := (Name.Sampling.approximation quarticRoot.value.name).sample first.rightIndex
  progress s!"quartic requests: actual quartic observation signs {decide (right.re < 0)}, {decide (right.im < 0)}"
  unless Norm.Basic.normSq (left - right) < 1 do
    throw (IO.userError "the actual paid original quartic observations violated their computed comparison")
  progress "quartic requests: actual first original observations meet the paid bound"
  let retry := agreement.compare 1 0 1 (by decide)
  unless 1 ≤ retry.leftIndex ∧ 0 ≤ retry.rightIndex do
    throw (IO.userError "the original quartic retry lost its independent swapped starts")
  progress s!"quartic requests: retry paid indices {retry.leftIndex}, {retry.rightIndex}"
  let nextLeft := (Name.Sampling.approximation
    (CoherentNamed.add firstRoot.value secondRoot.value).name).sample retry.leftIndex
  progress s!"quartic requests: actual retry sum signs {decide (nextLeft.re < 0)}, {decide (nextLeft.im < 0)}"
  let nextRight := (Name.Sampling.approximation quarticRoot.value.name).sample retry.rightIndex
  progress s!"quartic requests: actual retry quartic signs {decide (nextRight.re < 0)}, {decide (nextRight.im < 0)}"
  unless Norm.Basic.normSq (nextLeft - nextRight) < 1 do
    throw (IO.userError "the actual cached original quartic retry observations violated their computed comparison")
  progress "quartic requests: actual cached original retry observations meet the paid bound"

/-- Saved input execution views read the same original quadratic-sum name at every named sample index. -/
private theorem savedSum_sample (firstEntries : List (CoherentRoot.StateCache.Entry firstTrack))
    (secondEntries : List (CoherentRoot.StateCache.Entry secondTrack)) (index : Nat) :
    (Name.Sampling.approximation ((firstRoot.approximationSamples firstEntries).view.toNamed.add
      (secondRoot.approximationSamples secondEntries).view.toNamed)).sample index =
      (Name.Sampling.approximation (CoherentNamed.add firstRoot.value secondRoot.value).name).sample index :=
  firstRoot.approximationSamples_add secondRoot firstEntries secondEntries index

/-- Restore the original paid quadratic and quartic states and consume them in the actual independent comparison.

Both original names, comparison starts, computed paid indices and retry order
are retained. Original process trajectories compute the primitive sample
indices. Saved state entries feed the production algebraic sum cache and the
exact original named observations through checked execution views.
-/
public def checkCachedRequests (directory : System.FilePath) (savedOnly interrupt : Bool) : IO Unit := do
  let first := agreement.compare 0 1 1 (by decide)
  let retry := agreement.compare 1 0 1 (by decide)
  let lastLeft := max first.leftIndex retry.leftIndex
  let lastRight := max first.rightIndex retry.rightIndex
  let pair : Nat × Nat := Process.Sampling.stateAt
    (Process.add firstRoot.approximation.toProcess secondRoot.approximation.toProcess)
    (show Nat × Nat from (0, 0)) lastLeft
  let quarticIndex : Nat := Process.Sampling.stateAt quarticRoot.approximation.toProcess (show Nat from 0) lastRight
  let columns : ClearanceCheckpoint.Control IO :=
    { savedOnly := savedOnly
      afterSave := if interrupt then
        throw (IO.userError "interruption after original quartic-comparison root-column atomic save")
      else pure () }
  let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
  let productionIndex := max pair.1 pair.2
  let firstLast := productionIndex
  let secondLast := productionIndex
  let quarticLast := quarticIndex
  progress s!"quartic saved requests: actual primitive floors {firstLast}, {secondLast}, {quarticLast}"
  let firstCached := Thunk.mk fun _ => Input.Elimination.ofCertificate firstInput firstElimination rfl
  let secondCached := Thunk.mk fun _ => Input.Elimination.ofCertificate secondInput secondElimination rfl
  let quarticCached := Thunk.mk fun _ => Input.Elimination.ofCertificate quarticInput quarticElimination rfl
  let firstEntries ← CoherentRootCheckpoint.samplePrefix firstRoot firstInput firstCached (fun _ _ _ => rfl)
    columns winding (Purelib.System.FilePath.join directory "sqrt-two") firstLast
  let secondEntries ← CoherentRootCheckpoint.samplePrefix secondRoot secondInput secondCached (fun _ _ _ => rfl)
    columns winding (Purelib.System.FilePath.join directory "sqrt-three") secondLast
  let quarticEntries ← CoherentRootCheckpoint.samplePrefix quarticRoot quarticInput quarticCached (fun _ _ _ => rfl)
    columns winding (Purelib.System.FilePath.join directory "positive-quartic") quarticLast
  let firstRetained := firstSidecar.withRootSamples firstRoot firstEntries (fun index =>
    (firstSidecar_sample index).symm)
  let secondRetained := secondSidecar.withRootSamples secondRoot secondEntries (fun index =>
    (secondSidecar_sample index).symm)
  let productionSum := firstRetained.add secondRetained
  let productionSample := productionSum.residual.source.sample productionIndex
  progress s!"quartic saved requests: production sum real sign {decide (productionSample.re < 0)}"
  let savedSum := (firstRoot.approximationSamples firstEntries).view.toNamed.add
    (secondRoot.approximationSamples secondEntries).view.toNamed
  let savedQuartic := (quarticRoot.approximationSamples quarticEntries).view.toNamed
  let retainedAgreement := agreement.withSamples (Name.Sampling.approximation savedSum)
    (Name.Sampling.approximation savedQuartic) (savedSum_sample firstEntries secondEntries)
    (quarticRoot.approximationSamples_named quarticEntries)
  let retainedFirst := retainedAgreement.compare 0 1 1 (by decide)
  let retainedRetry := retainedAgreement.compare 1 0 1 (by decide)
  unless retainedFirst.leftIndex = first.leftIndex ∧ retainedFirst.rightIndex = first.rightIndex ∧
      retainedRetry.leftIndex = retry.leftIndex ∧ retainedRetry.rightIndex = retry.rightIndex do
    throw (IO.userError "saved scalar readback altered original paid comparison indices or retry order")
  let left := (Name.Sampling.approximation savedSum).sample first.leftIndex
  let right := (Name.Sampling.approximation savedQuartic).sample first.rightIndex
  unless Norm.Basic.normSq (left - right) < 1 do
    throw (IO.userError "the actual saved original quartic observations violated their original paid bound")
  progress "quartic saved requests: actual original first observations meet the paid bound"
  let nextLeft := (Name.Sampling.approximation savedSum).sample retry.leftIndex
  let nextRight := (Name.Sampling.approximation savedQuartic).sample retry.rightIndex
  unless Norm.Basic.normSq (nextLeft - nextRight) < 1 do
    throw (IO.userError "the actual saved original quartic retry violated its original paid bound")
  progress "quartic saved requests: actual retained original retry observations meet the paid bound"

/-- Inspect the actual selected cache, its original displayed residual and its paid original source anchor. -/
private def checkSelectionCache {channel : CoherentNamed}
    (original identified : Algebraic.Sidecar channel) : IO Unit := do
  match identified with
  | ⟨_, _, _,
      .selected (polynomial := displayed) (residual := retained) _ preparation selection _ root _ _⟩ =>
      unless displayed.coeffs = original.polynomial.coeffs ∧
          root.owner.polynomial.coeffs = original.polynomial.coeffs ∧
          retained.source.sample 0 = original.residual.source.sample 0 do
        throw (IO.userError "result selection lost its complete original annihilator or numerical child cache")
      unless root.owner.multiplicity = selection.multiplicity ∧
          root.residualCertificate.1.coeffs = selection.factorPolynomial.coeffs ∧
          selection.occurrence.toFin.val = selection.anchor.nearby.owner.val do
        throw (IO.userError "result selection changed its original factor, multiplicity or bounded occurrence")
      let gap := selection.rootPairs.gap
      let source := preparation.source.toApproximation
      let candidate := preparation.roots.candidates selection.anchor.nearby.owner
      unless 0 < gap ∧ source.radiusSq selection.anchor.index < gap / 16 ∧
          Data.Gaussian.Norm.Basic.normSq
            (candidate.sample selection.anchor.nearby.index - source.sample selection.anchor.index) < gap / 16 do
        throw (IO.userError "result selection did not retain its actual paid source anchor and same-candidate bound")
  | _ => throw (IO.userError "an unidentified arithmetic output did not retain its computed original selection")

/-- Compare actual identified inputs and pay an original-channel request from their one computed intrinsic result. -/
private def checkIdentifiedEqual {first second : CoherentNamed}
    (left : Algebraic.Sidecar first) (right : Algebraic.Sidecar second) : IO Unit := do
  let compared := left.compare right 1 2
  match compared.cache with
  | .inr _ => throw (IO.userError "an identified mixed-root result forced the complete difference eliminant")
  | .inl intrinsic =>
      match intrinsic.prepared.comparison with
      | .distinct _ => throw (IO.userError "the computed original selected roots unexpectedly have a positive gap")
      | .equal _ => pure ()
  match compared.comparison with
  | .distinct _ _ => throw (IO.userError "identified equal arithmetic channels were classified distinct")
  | .equal agreement =>
      let paid := agreement.compare 2 1 1 (by decide)
      let firstSample := (Name.Sampling.approximation first.name).sample paid.leftIndex
      let secondSample := (Name.Sampling.approximation second.name).sample paid.rightIndex
      unless 2 ≤ paid.leftIndex ∧ 1 ≤ paid.rightIndex ∧
          Data.Gaussian.Norm.Basic.normSq (firstSample - secondSample) < 1 do
        throw (IO.userError "the computed selected equality lost its actual original-channel request payment")

/-- Identify the actual positive quadratic sum with an independent quartic root and separate its other positive root.

The production result computes and retains its own coefficient localization
and selected occurrence. Both comparisons use actual original owner tracks,
independent nonzero starts and computed outcomes; neither receives a selected
branch, supplied equality or successful-search hypothesis.
-/
public def checkIdentification : IO Unit := do
  progress "quartic identification: compute original residual localization and selected occurrence"
  let original := sumSidecar
  let identified := original.identify
  checkSelectionCache original identified
  progress "quartic identification: retained original operation, selected factor and paid anchor"
  unless quarticBox.xLower = 3 ∧ quarticBox.xUpper < 4 ∧
      (sumResidual.source.sample 0).re > 3 do
    throw (IO.userError "the independent positive quartic box lost its original three-to-four region")
  checkIdentifiedEqual identified quarticSidecar
  match identified.decide with
  | .excluded _ => throw (IO.userError "the selected positive quartic lost its retained nonzero decision")
  | .prepared prepared =>
      unless 0 < prepared.apart.certificate.lowerSq do
        throw (IO.userError "the selected positive quartic decision lost its actual positive lower bound")
  let other := identified.compare smallQuarticSidecar 2 1
  match other.cache with
  | .inr _ => throw (IO.userError "the other positive quartic root forced complete difference elimination")
  | .inl intrinsic =>
      match intrinsic.prepared.comparison with
      | .equal _ => throw (IO.userError "the two different positive quartic roots were merged")
      | .distinct separation =>
          let gap := separation.separation.gap
          let first := intrinsic.left.view.root.approximation.sample separation.leftIndex
          let second := intrinsic.right.view.root.approximation.sample separation.rightIndex
          unless 2 ≤ separation.leftIndex ∧ 1 ≤ separation.rightIndex ∧ 0 < gap ∧
              gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (first - second) do
            throw (IO.userError "the other positive quartic root lost its actual paid positive separation")
          match other.decision with
          | .excluded _ => throw (IO.userError "the different positive quartic roots lost their prepared difference")
          | .prepared prepared =>
              unless prepared.apart.certificate.lowerSq = gap ^ 2 do
                throw (IO.userError "the distinct quartic result did not consume its retained pair gap")
  progress "quartic identification: original sum equals the large positive root and separates the other positive root"

/-- Check actual retained point-comparison floors without reducing its dependent outcome inside an IO branch. -/
private def pointPaid {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {root : CoherentRoot.CertifiedName track}
    {point : Canonical} {start : Nat} (comparison : CoherentRoot.PointComparison root point start) : Bool :=
  match comparison with
  | .nonroot separation => decide (start ≤ separation.index)
  | .root _ refinement _ _ => decide (start ≤ refinement.index ∧ 0 < refinement.targetSq)

/-- Inspect the actual stored coefficient bank, ordered attempts and original selected-root request. -/
private def checkPointInspection {channel : CoherentNamed} {root : PolynomialRoot.Sidecar channel}
    (inspection : PolynomialRoot.Sidecar.PointInspection root) (start : Nat) (expected : Canonical) : IO Unit := do
  unless inspection.start = start do
    throw (IO.userError "exact selected-point inspection lost its original requested floor")
  match inspection.result with
  | none => throw (IO.userError "the selected nonlinear root lost its actual root View")
  | some retained =>
      let candidates := retained.candidates
      let attempts := retained.attempts
      let remaining := retained.remaining
      unless !attempts.isEmpty ∧ candidates.length ≤ retained.budget ∧
          (attempts.map fun entry => entry.1.point) ++ (remaining.map fun candidate => candidate.point) =
            (candidates.map fun candidate => candidate.point) do
        throw (IO.userError "exact candidate inspection lost original duplicate order, \
          attempted data or remaining suffix")
      for entry in attempts do
        unless pointPaid entry.2 do
          throw (IO.userError "an exact-candidate attempt discarded its actual original paid request")
      match retained.reading with
      | none => throw (IO.userError "the selected rational value had no actual checked equal candidate")
      | some reading =>
          unless reading.value = expected do
            throw (IO.userError "the computed candidate comparison selected a different exact value")

/-- Reuse the same retained selected-point receipt in the original production scalar and decision readers. -/
private def checkExactSelected {channel : CoherentNamed} (identified : Algebraic.Sidecar channel)
    (start : Nat) (expected : Canonical) : IO Unit := do
  match identified with
  | ⟨_, _, _, .selected _ _ _ _ root _ (some inspection)⟩ =>
      checkPointInspection inspection start expected
      unless root.owner.multiplicity = 2 ∧ root.owner.polynomial.natDegree = 4 ∧
          root.residualCertificate.1.natDegree = 2 do
        throw (IO.userError "exact reading replaced the original selected owner, repeated annihilator or multiplicity")
  | _ => throw (IO.userError "the exact selected result did not retain its original checked inspection")
  match found : identified.scalar? with
  | none => throw (IO.userError "the production scalar reader ignored its retained checked point result")
  | some reading =>
      have _decision := Algebraic.Sidecar.decide_of_scalar identified reading found
      unless reading.value = expected do
        throw (IO.userError "the production scalar reader changed the actual exact candidate")
      let paid := reading.equivalent.compare 1 2 1 (by decide)
      let first := (Name.Sampling.approximation channel.name).sample paid.leftIndex
      let second := (Name.Sampling.approximation
        (CoherentNamed.Coherence.exact reading.value).name).sample paid.rightIndex
      unless 1 ≤ paid.leftIndex ∧ 2 ≤ paid.rightIndex ∧ Data.Gaussian.Norm.Basic.normSq (first - second) < 1 do
        throw (IO.userError "the retained exact reading did not pay its actual original-channel request")
      match identified.decide with
      | .excluded _ => throw (IO.userError "a retained nonzero exact selected value was classified zero")
      | .prepared prepared =>
          unless 0 < prepared.apart.certificate.lowerSq do
            throw (IO.userError "the actual scalar decision lost its certified positive denominator bound")
      let repeated := identified.inspectExact (some (start + 1))
      match repeated with
      | ⟨_, _, _, .selected _ _ _ _ _ _ (some inspection)⟩ => checkPointInspection inspection start expected
      | _ => throw (IO.userError "repeated exact inspection discarded the original actual request receipt")
      match repeated.scalar? with
      | none => throw (IO.userError "repeated scalar readback lost its stored exact result")
      | some repeatedReading =>
          let repeatedPaid := repeatedReading.equivalent.compare 1 2 1 (by decide)
          unless repeatedReading.value = reading.value ∧ repeatedPaid.leftIndex = paid.leftIndex ∧
              repeatedPaid.rightIndex = paid.rightIndex do
            throw (IO.userError "repeated exact readback rebuilt a different value or request payment")

/-- Derive the correlation of independent square-root owners and the exact value of their actual product.

The independent square-root-of-eight track is compared with the identified
original doubled square-root-of-two operation. Their actual product retains
its full repeated annihilator, selected multiplicity and original input
caches. Coefficient-produced candidates and their original paid point
comparisons are stored in that same selected cache. The production scalar and
decision readers consume the checked equality and its actual request payment.
-/
public def checkCorrelation : IO Unit := do
  progress "quadratic correlation: identify the original doubled square-root channel"
  let doubled := ((Algebraic.Sidecar.ofRational (Rational.Basic.RationalSidecar.exact 2)).mul firstSidecar).identify
  checkIdentifiedEqual doubled eightSidecar
  progress "quadratic correlation: identify the original independent product channel"
  let original := firstSidecar.mul eightSidecar
  let identified := original.identify (some 2)
  checkSelectionCache original identified
  checkExactSelected identified 2 4
  match identified.cached.root? with
  | none => throw (IO.userError "the independent product lost its actual selected root owner")
  | some stored =>
      unless original.polynomial.natDegree = 4 ∧ stored.owner.multiplicity = 2 ∧
          stored.residualCertificate.1.natDegree = 2 do
        throw (IO.userError "the correlated product lost its complete repeated annihilator or selected multiplicity")
      unless (identified.scalar?.map fun reading => reading.value) = some 4 do
        throw (IO.userError "the actual selected cache lost its coefficient-computed exact value")
  progress "quadratic correlation: independent beta equals twice alpha and their actual product equals four"
/-- Compute the original quartic box-gap comparison for supplied numerical roots in the same three owner boxes.

The original coefficients, independent quartic owner and positive divided-
difference gap are unchanged. Each actual residual reads its supplied root;
no equality with another track's same-index observations is assumed.
-/
private def agreementFor
    {leftTrack : CoherentRoot.WindingOneTrack firstPolynomial firstBox}
    {rightTrack : CoherentRoot.WindingOneTrack secondPolynomial secondBox}
    {independentTrack : CoherentRoot.WindingOneTrack quarticPolynomial quarticBox}
    (left : CoherentRoot.CertifiedName leftTrack) (right : CoherentRoot.CertifiedName rightTrack)
    (independent : CoherentRoot.CertifiedName independentTrack) :
    Equivalence.NamedEquivalent (CoherentNamed.add left.value right.value).name independent.value.name := by
  let sum := Gaussian.Residual.QuadraticSum.ofResiduals left.residualCertificate right.residualCertificate
  have inside (index : Nat) : sumBox.Contains (sum.residualCertificate.source.sample index) := by
    rewrite [sum.residualCertificate_sample]
    have first := left.sample_inside index
    have second := right.sample_inside index
    exact ⟨Order.Arithmetic.add_le_add_direct first.1 second.1,
      Order.Arithmetic.add_le_add_direct first.2.1 second.2.1,
      Order.Arithmetic.add_le_add_direct first.2.2.1 second.2.2.1,
      Order.Arithmetic.add_le_add_direct first.2.2.2 second.2.2.2⟩
  exact match Gaussian.Residual.EvenQuartic.inspect sum.residualCertificate
      independent.residualCertificate sumBox quarticBox 0 (fun index _ => inside index)
      (fun index _ => independent.sample_inside index) with
    | .ready certificate _ _ => certificate.equivalent
    | .unresolved attempt firstBox_eq secondBox_eq failed =>
        have positive : 0 < attempt.factorBounds.lower := by
          rewrite [attempt.factorBounds_eq, firstBox_eq, secondBox_eq]
          decide +kernel
        (failed positive).elim

/-- Bind one distinct dyadic request or exact observation while preserving saved-only header requirements. -/
private def persistDyadic (savedOnly : Bool) (path : System.FilePath) (value : Data.Json) : IO Unit := do
  if ← path.pathExists then
    unless (← IntegrationCheckpoint.loadJson path) == value do
      throw (IO.userError "compared dyadic quartic request or observation changed on reload")
  else
    if savedOnly then
      throw (IO.userError "missing compared dyadic quartic request or observation")
    IntegrationCheckpoint.saveJson path value

/-- The complete original three-polynomial request under a distinct loaded dyadic protocol. -/
private def dyadicRequest : Data.Json := Data.Json.mkObj
  [("protocol", toJson "original-quartic-compared-dyadic-v1"),
   ("firstPolynomial", toJson (firstPolynomial.coeffs.map gaussianData)),
   ("secondPolynomial", toJson (secondPolynomial.coeffs.map gaussianData)),
   ("quarticPolynomial", toJson (quarticPolynomial.coeffs.map gaussianData)),
   ("firstBox", toJson ([firstBox.xLower, firstBox.xUpper, firstBox.yLower, firstBox.yUpper].map
     fractionData)),
   ("secondBox", toJson ([secondBox.xLower, secondBox.xUpper, secondBox.yLower, secondBox.yUpper].map
     fractionData)),
   ("quarticBox", toJson ([quarticBox.xLower, quarticBox.xUpper, quarticBox.yLower, quarticBox.yUpper].map
     fractionData)),
   ("firstStarts", toJson [0, 1]), ("retryStarts", toJson [1, 0]),
   ("targetSq", toJson (fractionData 1))]

section

-- Keep the same closed original owners opaque while elaborating dependent loaded-prefix types.
attribute [local irreducible] firstInput secondInput quarticInput firstTrack secondTrack quarticTrack
  firstRoot secondRoot quarticRoot

/-- Compute the exact primitive demand of both requested observations and the retained production sum.

Each actual named request is mapped separately through its original process.
The production sum consumes both loaded root samples at their shared maximum;
no monotonicity inference about unobserved process indices is needed.
-/
private def dyadicSampleDemand
    (first : CoherentRoot.Accelerated.Initial firstInput firstTrack)
    (second : CoherentRoot.Accelerated.Initial secondInput secondTrack)
    (independent : CoherentRoot.Accelerated.Initial quarticInput quarticTrack)
    (paid retry : Nat × Nat) : Nat × Nat :=
  let process := Process.add first.root.approximation.toProcess second.root.approximation.toProcess
  let firstPair : Nat × Nat := Process.Sampling.stateAt process (show Nat × Nat from (0, 0)) paid.1
  let retryPair : Nat × Nat := Process.Sampling.stateAt process (show Nat × Nat from (0, 0)) retry.1
  let productionIndex := Nat.max (Nat.max firstPair.1 retryPair.1) (Nat.max firstPair.2 retryPair.2)
  let independentIndex : Nat := Nat.max
    (Process.Sampling.stateAt independent.root.approximation.toProcess (show Nat from 0) paid.2)
    (Process.Sampling.stateAt independent.root.approximation.toProcess (show Nat from 0) retry.2)
  (productionIndex, independentIndex)

/-- Consume actual covered observations and retain both original-to-loaded channel comparisons. -/
private def recordDyadicRequests (savedOnly : Bool) (rootDirectory : System.FilePath)
    (firstComplete : CoherentRoot.Accelerated.Initial firstInput firstTrack)
    (secondComplete : CoherentRoot.Accelerated.Initial secondInput secondTrack)
    (independentComplete : CoherentRoot.Accelerated.Initial quarticInput quarticTrack)
    (firstOriginal : firstComplete.original = firstRoot) (secondOriginal : secondComplete.original = secondRoot)
    (independentOriginal : independentComplete.original = quarticRoot)
    (paidIndices retryIndices : Nat × Nat) : IO Unit := do
  let actual := agreementFor firstComplete.root secondComplete.root independentComplete.root
  let actualPaid := actual.compare 0 1 1 (by decide)
  let actualRetry := actual.compare 1 0 1 (by decide)
  unless actualPaid.leftIndex = paidIndices.1 ∧ actualPaid.rightIndex = paidIndices.2 ∧
      actualRetry.leftIndex = retryIndices.1 ∧ actualRetry.rightIndex = retryIndices.2 do
    throw (IO.userError "extending the same dyadic policy changed the planned comparison indices")
  let actualDemand := dyadicSampleDemand firstComplete secondComplete independentComplete
    (actualPaid.leftIndex, actualPaid.rightIndex) (actualRetry.leftIndex, actualRetry.rightIndex)
  unless actualDemand.1 ≤ firstComplete.last ∧ actualDemand.1 ≤ secondComplete.last ∧
      actualDemand.2 ≤ independentComplete.last do
    throw (IO.userError "actual compared dyadic observation exceeds its loaded primitive prefix")
  let productionIndex := actualDemand.1
  let production := firstComplete.algebraic.add secondComplete.algebraic
  unless production.polynomial.coeffs = quarticPolynomial.coeffs do
    throw (IO.userError "compared dyadic production sum lost the original quartic polynomial")
  let productionSample := production.residual.source.sample productionIndex
  let numericSum := CoherentNamed.add firstComplete.root.value secondComplete.root.value
  let numericQuartic := independentComplete.root.value
  let firstComparison : Equivalence.NamedEquivalent firstRoot.value.name firstComplete.root.value.name :=
    firstOriginal ▸ firstComplete.comparison
  let secondComparison : Equivalence.NamedEquivalent secondRoot.value.name secondComplete.root.value.name :=
    secondOriginal ▸ secondComplete.comparison
  let independentComparison : Equivalence.NamedEquivalent quarticRoot.value.name independentComplete.root.value.name :=
    independentOriginal ▸ independentComplete.comparison
  let originalSumComparison := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    firstRoot.value firstComplete.root.value secondRoot.value secondComplete.root.value
    firstComparison secondComparison
  let originalAgreement := originalSumComparison.trans (actual.trans independentComparison.symm)
  let originalPaid := originalAgreement.compare 0 1 1 (by decide)
  let originalRetry := originalAgreement.compare 1 0 1 (by decide)
  let left := (Name.Sampling.approximation numericSum.name).sample actualPaid.leftIndex
  let right := (Name.Sampling.approximation numericQuartic.name).sample actualPaid.rightIndex
  let nextLeft := (Name.Sampling.approximation numericSum.name).sample actualRetry.leftIndex
  let nextRight := (Name.Sampling.approximation numericQuartic.name).sample actualRetry.rightIndex
  unless 0 ≤ actualPaid.leftIndex ∧ 1 ≤ actualPaid.rightIndex ∧ 1 ≤ actualRetry.leftIndex ∧
      0 ≤ actualRetry.rightIndex ∧ Norm.Basic.normSq (left - right) < 1 ∧
      Norm.Basic.normSq (nextLeft - nextRight) < 1 do
    throw (IO.userError "actual compared dyadic quartic observations violated the original requests")
  let observations := Data.Json.mkObj
    [("request", dyadicRequest), ("firstIndices", toJson [actualPaid.leftIndex, actualPaid.rightIndex]),
     ("retryIndices", toJson [actualRetry.leftIndex, actualRetry.rightIndex]),
     ("originalFirstIndices", toJson [originalPaid.leftIndex, originalPaid.rightIndex]),
     ("originalRetryIndices", toJson [originalRetry.leftIndex, originalRetry.rightIndex]),
     ("primitiveFloors", toJson [firstComplete.last, secondComplete.last, independentComplete.last]),
     ("left", toJson (gaussianData left)),
     ("right", toJson (gaussianData right)),
     ("retryLeft", toJson (gaussianData nextLeft)),
     ("retryRight", toJson (gaussianData nextRight)),
     ("production", toJson (gaussianData productionSample))]
  persistDyadic savedOnly (join rootDirectory "observations.json") observations
  progress "quartic dyadic requests: actual original-domain observations and retry meet the paid bound"

/-- Extend only missing retained refinements through the actual finite comparison demand. -/
private def finishDyadicAt (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (savedOnly : Bool) (rootDirectory : System.FilePath)
    (first : CoherentRoot.Accelerated.Initial firstInput firstTrack)
    (second : CoherentRoot.Accelerated.Initial secondInput secondTrack)
    (independent : CoherentRoot.Accelerated.Initial quarticInput quarticTrack)
    (paidIndices retryIndices demand : Nat × Nat) : IO Unit := do
  let firstDirectory := join rootDirectory "sqrt-two"
  let secondDirectory := join rootDirectory "sqrt-three"
  let independentDirectory := join rootDirectory "positive-quartic"
  -- Match the retained Nat.max bounds without reducing the whole demand through generic maxOfLe.
  let firstLast := Nat.max first.last demand.1
  let secondLast := Nat.max second.last demand.1
  let independentLast := Nat.max independent.last demand.2
  progress s!"quartic dyadic requests: actual primitive floors {firstLast}, {secondLast}, {independentLast}"
  let firstLoaded ← CoherentRootCheckpoint.extendDyadicRefinements firstInput first.elimination
    firstTrack.initial columns winding savedOnly firstDirectory first.loaded (firstLast - first.last)
  let secondLoaded ← CoherentRootCheckpoint.extendDyadicRefinements secondInput second.elimination
    secondTrack.initial columns winding savedOnly secondDirectory second.loaded
    (secondLast - second.last)
  let independentLoaded ← CoherentRootCheckpoint.extendDyadicRefinements quarticInput independent.elimination
    quarticTrack.initial columns winding savedOnly independentDirectory
    independent.loaded
    (independentLast - independent.last)
  have firstOrder : first.last ≤ firstLast := Data.Nat.Order.le_max_left _ _
  have secondOrder : second.last ≤ secondLast := Data.Nat.Order.le_max_left _ _
  have independentOrder : independent.last ≤ independentLast := Data.Nat.Order.le_max_left _ _
  let firstExact : CoherentRoot.Accelerated.RefinementPrefix
      (CoherentRoot.Accelerated.dyadicTrack firstInput first.elimination.certificate firstTrack.initial) 0 firstLast :=
    Eq.mp (congrArg (fun count : Nat => CoherentRoot.Accelerated.RefinementPrefix
      (CoherentRoot.Accelerated.dyadicTrack firstInput first.elimination.certificate firstTrack.initial) 0 count)
      (Data.Nat.Subtraction.add_sub_of_le firstOrder)) firstLoaded
  let firstComplete := CoherentRoot.Accelerated.fromInitial firstInput firstRoot first.elimination
    firstLast (first.first_covered.trans firstOrder) firstExact
  let secondExact : CoherentRoot.Accelerated.RefinementPrefix
      (CoherentRoot.Accelerated.dyadicTrack secondInput second.elimination.certificate secondTrack.initial)
      0 secondLast :=
    Eq.mp (congrArg (fun count : Nat => CoherentRoot.Accelerated.RefinementPrefix
      (CoherentRoot.Accelerated.dyadicTrack secondInput second.elimination.certificate secondTrack.initial) 0 count)
      (Data.Nat.Subtraction.add_sub_of_le secondOrder)) secondLoaded
  let secondComplete := CoherentRoot.Accelerated.fromInitial secondInput secondRoot second.elimination
    secondLast (second.first_covered.trans secondOrder)
    secondExact
  let independentExact : CoherentRoot.Accelerated.RefinementPrefix
      (CoherentRoot.Accelerated.dyadicTrack quarticInput independent.elimination.certificate quarticTrack.initial) 0
      independentLast :=
    Eq.mp (congrArg (fun count : Nat => CoherentRoot.Accelerated.RefinementPrefix
      (CoherentRoot.Accelerated.dyadicTrack quarticInput independent.elimination.certificate quarticTrack.initial)
      0 count)
      (Data.Nat.Subtraction.add_sub_of_le independentOrder)) independentLoaded
  let independentComplete := CoherentRoot.Accelerated.fromInitial quarticInput quarticRoot independent.elimination
    independentLast (independent.first_covered.trans independentOrder)
    independentExact
  have firstOriginal : firstComplete.original = firstRoot :=
    CoherentRoot.Accelerated.fromInitial_original firstInput firstRoot first.elimination
      firstLast (first.first_covered.trans firstOrder) firstExact
  have secondOriginal : secondComplete.original = secondRoot :=
    CoherentRoot.Accelerated.fromInitial_original secondInput secondRoot second.elimination
      secondLast (second.first_covered.trans secondOrder) secondExact
  have independentOriginal : independentComplete.original = quarticRoot :=
    CoherentRoot.Accelerated.fromInitial_original quarticInput quarticRoot independent.elimination
      independentLast (independent.first_covered.trans independentOrder) independentExact
  recordDyadicRequests savedOnly rootDirectory firstComplete secondComplete independentComplete
    firstOriginal secondOriginal independentOriginal
    paidIndices retryIndices

/-- Plan finite first and retry indices before invoking the dependent cache-loading action. -/
private def finishDyadicRequests (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (savedOnly : Bool) (rootDirectory : System.FilePath)
    (first : CoherentRoot.Accelerated.Initial firstInput firstTrack)
    (second : CoherentRoot.Accelerated.Initial secondInput secondTrack)
    (independent : CoherentRoot.Accelerated.Initial quarticInput quarticTrack) : IO Unit :=
  let planned := agreementFor first.root second.root independent.root
  let paid := planned.compare 0 1 1 (by decide)
  let retry := planned.compare 1 0 1 (by decide)
  let paidIndices := (paid.leftIndex, paid.rightIndex)
  let retryIndices := (retry.leftIndex, retry.rightIndex)
  let demand := dyadicSampleDemand first second independent paidIndices retryIndices
  finishDyadicAt columns winding savedOnly rootDirectory first second independent paidIndices retryIndices demand

/-- Execute the unchanged independent requests using compared loaded dyadic programs on the original three owners.

The original Newton names remain the retained parents of explicit same-initial
comparisons. Actual observations use the new loaded programs. A first finite
prefix supplies state one for those comparisons, then only missing refinement
suffixes are restored through the computed primitive sample indices. The
original external starts, target, retry order and positive local boxes stay fixed.
-/
public def checkDyadicCachedRequests (directory : System.FilePath) (savedOnly interrupt : Bool) : IO Unit := do
  let columns : ClearanceCheckpoint.Control IO :=
    { savedOnly := savedOnly
      afterSave := if interrupt then
        throw (IO.userError "interruption after compared dyadic quartic root-column atomic save")
      else pure () }
  let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
  let rootDirectory := join directory "compared-dyadic-v1"
  IO.FS.createDirAll rootDirectory
  persistDyadic savedOnly (join rootDirectory "request.json") dyadicRequest
  let firstDirectory := join rootDirectory "sqrt-two"
  let secondDirectory := join rootDirectory "sqrt-three"
  let independentDirectory := join rootDirectory "positive-quartic"
  CoherentRootCheckpoint.dyadicFromOriginal firstRoot firstInput
    (Input.Elimination.ofCertificate firstInput firstElimination rfl) columns winding savedOnly
      firstDirectory 1 fun first _ => do
    CoherentRootCheckpoint.dyadicFromOriginal secondRoot secondInput
      (Input.Elimination.ofCertificate secondInput secondElimination rfl) columns winding savedOnly
        secondDirectory 1 fun second _ => do
      CoherentRootCheckpoint.dyadicFromOriginal quarticRoot quarticInput
        (Input.Elimination.ofCertificate quarticInput quarticElimination rfl) columns winding
          savedOnly independentDirectory 1 fun independent _ => do
        finishDyadicRequests columns winding savedOnly rootDirectory first second independent

end

end TestPurelib.Approximation.Gaussian.QuarticAdmission

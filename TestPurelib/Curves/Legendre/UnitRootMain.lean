module

import Purelib.System.IO
import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Cells
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Program
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Circuit
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Data.Rat.Interval.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Native cofactor refinement, continuation comparisons and shared waist differential readings -/

namespace TestPurelib.Curves.Legendre.UnitRootMain

open Purelib

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Periods.Jets.Specification
open Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel

/-- Flush one finite construction marker so a slow native stage remains identifiable. -/
private def progress (message : String) : IO Unit := do
  System.IO.println message
  (← IO.getStdout).flush

/-- The original maximal-variation corner of the selected spatial collision square. -/
private def corner (site : Fin 2) : Canonical := Degeneration.criticalValue site + ⟨1 / 2, 1 / 2⟩

/-- Each selected original corner is admitted by its same computed spatial square. -/
private theorem corner_inside (site : Fin 2) : (Degeneration.spatialBox site).Contains (corner site) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Execute actual refinements and the retained comparison, checking its two original sampled root names. -/
private def check (site : Fin 2) : IO Unit := do
  let point := corner site
  let retained := Degeneration.UnitRoot.owner site point (corner_inside site)
  let state := CoherentRoot.state retained.track 1
  let reading := state.box.anchor
  if !(decide ((Degeneration.UnitRoot.box site).Contains reading ∧
      (1 / 4 : Rat.Fraction.Rational) ≤ Gaussian.Norm.Basic.normSq reading)) then
    throw (IO.userError "computed unit-root sample violates its signed-box or lower-norm certificate")
  let residual := Gaussian.Norm.Basic.normSq (reading * reading - (Degeneration.unitPolynomial site).eval point)
  System.IO.println
    (s!"site {site.val}: sample ({reading.re.num}/{reading.re.den}, {reading.im.num}/{reading.im.den}); "
    ++ s!"squared residual {residual.num}/{residual.den}")
  let continued := Degeneration.UnitRoot.Transport.fromSource site point (corner_inside site)
  let continuedReading := (CoherentRoot.state continued.track 1).box.anchor
  if !(decide ((Degeneration.UnitRoot.box site).Contains continuedReading ∧
      (1 / 4 : Rat.Fraction.Rational) ≤ Gaussian.Norm.Basic.normSq continuedReading)) then
    throw (IO.userError "actual reference continuation violates the signed root-box certificate")
  let agreement := Degeneration.UnitRoot.Transport.fromSource_agrees site point (corner_inside site)
  let compared := agreement.compare 0 0 (1 / 16) (by decide +kernel)
  let leftName := ownerRootName continued.parameterNonzero continued
  let rightName := ownerRootName retained.parameterNonzero retained
  let leftReading := (Sampling.approximation leftName).sample compared.leftIndex
  let rightReading := (Sampling.approximation rightName).sample compared.rightIndex
  if !(decide (Gaussian.Norm.Basic.normSq (leftReading - rightReading) < (1 / 16 : Rat.Fraction.Rational))) then
    throw (IO.userError "retained continuation comparison fails at its actual sample indices")
  System.IO.println
    s!"site {site.val}: actual continuation comparison indices {compared.leftIndex}, {compared.rightIndex}"

/-- A regular original waist parameter one eighth beyond its labelled collision. -/
private def waistParameter (site : Fin 2) : Canonical := Degeneration.criticalValue site + (1 / 8 : Canonical)

/-- Both chosen original waist parameters are regular. -/
private theorem waist_regular (site : Fin 2) : waistParameter site ≠ Degeneration.criticalValue site := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Both chosen original waist parameters obey the original intrinsic squared-distance bound. -/
private theorem waist_bound (site : Fin 2) :
    Gaussian.Norm.Basic.normSq (waistParameter site - Degeneration.criticalValue site) ≤
      (1 / 16 : Rat.Fraction.Rational) := by
  rcases Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Execute both original value-row cells with one cached cofactor reading at the original moving branch. -/
private def checkWaist (site : Fin 2) : IO Unit := do
  let parameter := waistParameter site
  let span : Rat.Interval.Bounds := ⟨0, 1, by decide +kernel⟩
  let lift := Waist.lift site parameter (Waist.direction .first span.lower) (waist_regular site) (waist_bound site)
  let firstBudget := Waist.Differential.Bounds.Data.build site parameter (valueSpecification parameter 0)
  let first := Waist.Differential.Cells.Model.build firstBudget (valueSpecification_denominatorPairs parameter 0) lift 0
  let secondBudget := Waist.Differential.Bounds.Data.build site parameter (valueSpecification parameter 1)
  let second := first.reweight secondBudget (valueSpecification_denominatorPairs parameter 1)
  if !(decide (first.centerRoot = second.centerRoot ∧
      first.rootBox.xLower = second.rootBox.xLower ∧ first.rootBox.xUpper = second.rootBox.xUpper ∧
      first.rootBox.yLower = second.rootBox.yLower ∧ first.rootBox.yUpper = second.rootBox.yUpper ∧
      (1 / 16 : Rat.Fraction.Rational) ≤ Gaussian.Norm.Basic.normSq first.centerRoot ∧
      first.cell.integralSample = first.center ∧ second.cell.integralSample = second.center ∧
      second.center = parameter * first.center ∧ first.cell.observations.length = 1 ∧
      second.cell.observations.length = 1)) then
    throw (IO.userError "actual waist cells fail their shared root, original differential or integral-sample laws")
  System.IO.println (s!"site {site.val}: shared waist root ({first.centerRoot.re.num}/{first.centerRoot.re.den}, "
    ++ s!"{first.centerRoot.im.num}/{first.centerRoot.im.den}); original row samples "
    ++ s!"({first.center.re.num}/{first.center.re.den}, {first.center.im.num}/{first.center.im.den}) and "
    ++ s!"({second.center.re.num}/{second.center.re.den}, {second.center.im.num}/{second.center.im.den})")
  have signed : lift.unitOwner.track.initial.box.Refines (Degeneration.UnitRoot.box site) := by
    rewrite [lift.unitOwner_eq, Degeneration.UnitRoot.owner_initial_box]
    exact Purelib.Geometry.Rational.Box.refines_refl _
  let accuracy : Rat.Fraction.Rational := 1 / 64
  let refined := Refinement.Cell.build firstBudget (valueSpecification_denominatorPairs parameter 0)
    lift signed accuracy (by decide +kernel)
  let split := Refinement.Split.build refined
  let paired := split.reweight secondBudget (valueSpecification_denominatorPairs parameter 1)
  let difference := Gaussian.Norm.Basic.normSq (split.children.integralSample - refined.model.integralSample)
  let compared := CompatibleConstantPathRefinement.comparisonAllowance split.compatible
  let residual := Gaussian.Norm.Basic.normSq (refined.reading.centerRoot * refined.reading.centerRoot -
    Waist.cofactor site parameter .first (waist_regular site) (waist_bound site) span.lower)
  if !(decide (residual < accuracy ∧ split.left.allowance = refined.allowance / 4 ∧
      split.right.allowance = refined.allowance / 4 ∧ difference ≤ compared ∧
      split.left.reading.centerRoot = paired.left.reading.centerRoot ∧
      split.right.reading.centerRoot = paired.right.reading.centerRoot)) then
    throw (IO.userError "actual waist refinement fails its residual, quarter allowance or shared-reading comparison")
  System.IO.println (s!"site {site.val}: paid root residual {residual.num}/{residual.den}; "
    ++ s!"actual split sample difference {difference.num}/{difference.den} below its comparison allowance")
  let original := Refinement.Piece.ofCell refined
  let layer0 := Refinement.Layer.ofPiece original
  let steps0 : Refinement.Steps layer0.pieces := .cons split .nil
  let layer1 := layer0.next steps0
  let steps1 := Refinement.Steps.build layer1.pieces
  let layer2 := layer1.next steps1
  let comparison := CompatibleConstantPathRefinement.comparisonAllowance (layer1.compatible steps1)
  let intrinsic := Refinement.Piece.ofQuarter firstBudget
    (valueSpecification_denominatorPairs parameter 0)
    .first (waist_regular site) (waist_bound site) accuracy (by decide +kernel)
  let cached := intrinsic.cached.stage 2
  if !(decide (layer1.pieces.length = 2 ∧ layer2.pieces.length = 4 ∧
      layer1.model.aggregateAllowance ≤ refined.allowance / 4 ∧
      layer2.model.aggregateAllowance ≤ refined.allowance / 16 ∧
      comparison ≤ refined.allowance ∧
      cached.sample = layer2.model.integralSample ∧ cached.allowance = layer2.model.aggregateAllowance ∧
      original.program.errorScale = 16 * refined.allowance ∧
      Gaussian.Norm.Basic.normSq (layer2.model.integralSample - layer0.model.integralSample) ≤
        original.program.errorScale)) then
    throw (IO.userError "whole waist layers fail their counts, contracted allowances or integral cache")
  System.IO.println
    s!"site {site.val}: actual whole-quarter integral layers 1, 2, 4; cache and shrinking allowances agree"

/-- Compare the two original cached cubic names at an actual curved-circuit seam. -/
private def checkSeam (label : String) (left right : Named) (agreement : NamedEquivalent left right) : IO Unit := do
  let compared := agreement.compare 0 0 (1 / 16) (by decide +kernel)
  let leftReading := (Sampling.approximation left).sample compared.leftIndex
  let rightReading := (Sampling.approximation right).sample compared.rightIndex
  if !(decide (Gaussian.Norm.Basic.normSq (leftReading - rightReading) < (1 / 16 : Rat.Fraction.Rational))) then
    throw (IO.userError s!"original circuit seam {label} fails at its actual comparison indices")
  System.IO.println s!"circuit seam {label}: original comparison indices {compared.leftIndex}, {compared.rightIndex}"

/-- Execute the integral cache on the exact retained four-quarter geometric circuit and check its operational seams. -/
private def checkCircuit (site : Fin 2) : IO Unit := do
  let parameter := waistParameter site
  progress s!"site {site.val}: preparing original curved circuit"
  let circuit := Waist.Banks.Circuit.build site parameter (waist_regular site) (waist_bound site)
  progress (s!"site {site.val}: actual cofactor preparation depths "
    ++ s!"{circuit.first.transport.prepared.depth}, {circuit.second.transport.prepared.depth}, "
    ++ s!"{circuit.third.transport.prepared.depth}, {circuit.fourth.transport.prepared.depth}")
  let data := Waist.Differential.Bounds.Data.build site parameter (valueSpecification parameter 0)
  let accuracy : Rat.Fraction.Rational := 1 / 64
  let firstIndex := CertifiedSquareRoot.residualIndex circuit.first.source.unitOwner.track
    accuracy (by decide +kernel)
  let secondIndex := CertifiedSquareRoot.residualIndex circuit.second.source.unitOwner.track
    accuracy (by decide +kernel)
  let thirdIndex := CertifiedSquareRoot.residualIndex circuit.third.source.unitOwner.track
    accuracy (by decide +kernel)
  let fourthIndex := CertifiedSquareRoot.residualIndex circuit.fourth.source.unitOwner.track
    accuracy (by decide +kernel)
  progress s!"site {site.val}: actual source residual indices {firstIndex}, {secondIndex}, {thirdIndex}, {fourthIndex}"
  let integral := Waist.Differential.Circuit.Integral.build data (valueSpecification_denominatorPairs parameter 0)
    circuit accuracy (by decide +kernel)
  progress s!"site {site.val}: original four source cells prepared"
  let original := integral.program.model 0
  let refined := integral.program.model 1
  let cached := integral.cached.stage 1
  let quarters := integral.cells
  let quarterSum :=
    (((quarters.piece .first).layerAt 1).model.integralSample +
      ((quarters.piece .second).layerAt 1).model.integralSample) +
    (((quarters.piece .third).layerAt 1).model.integralSample +
      ((quarters.piece .fourth).layerAt 1).model.integralSample)
  if !(decide (original.cells.length = 4 ∧ refined.cells.length = 8 ∧
      refined.integralSample = quarterSum ∧ cached.sample = refined.integralSample ∧
      cached.allowance = refined.aggregateAllowance ∧
      refined.aggregateAllowance ≤ original.aggregateAllowance / 4 ∧
      Gaussian.Norm.Basic.normSq (refined.integralSample - original.integralSample) ≤ integral.program.errorScale)) then
    throw (IO.userError ("actual four-quarter circuit fails its ordered samples, finite comparison bounds "
      ++ "or original cache"))
  checkSeam s!"{site.val}: first-second" circuit.first.target.value.name circuit.second.source.value.name
    circuit.first_second
  checkSeam s!"{site.val}: second-third" circuit.second.target.value.name circuit.third.source.value.name
    circuit.second_third
  checkSeam s!"{site.val}: third-fourth" circuit.third.target.value.name circuit.fourth.source.value.name
    circuit.third_fourth
  checkSeam s!"{site.val}: fourth-first" circuit.fourth.target.value.name circuit.first.source.value.name
    circuit.fourth_first
  System.IO.println (s!"site {site.val}: original curved circuit integral layers 4, 8; "
    ++ "ordered quarter samples, cache and seams agree")

end TestPurelib.Curves.Legendre.UnitRootMain

open TestPurelib.Curves.Legendre

/-- Check both original cofactor patches and quarter integrals, with an optional full-circuit runtime diagnostic.

The `--circuit` argument additionally executes the four retained geometric
legs, source cells, integral cache and operational seams at both sites.
-/
public def main (arguments : List String) : IO Unit := do
  UnitRootMain.check 0
  UnitRootMain.check 1
  UnitRootMain.checkWaist 0
  UnitRootMain.checkWaist 1
  if arguments.contains "--circuit" then
    UnitRootMain.checkCircuit 0
    UnitRootMain.checkCircuit 1

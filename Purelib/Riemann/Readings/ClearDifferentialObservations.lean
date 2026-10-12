module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Diagnostics
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation
import Purelib.Curves.Hyperelliptic.Sheets.Basic
public import Purelib.Curves.Hyperelliptic.Sheets.Construction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
public import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

@[expose] public section

/-!
# Automatic differential observations on clear lifted segments

Branch-cut clearance proves `f(x) != 0` at every rational unit-interval
sample.  The finite square-root sheet constructor then supplies `y`, its
apartness, and `y^2 = f(x)`.  This module packages one actual rational witness
of `x^k/y` as a Gaussian-constant local polynomial observation.  Sheet-switch
cells have zero displacement and need no integrand observation.
-/

namespace Purelib.Riemann.Readings.ClearDifferentialObservations

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data
/-- The exact rational coordinate type. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The canonical Gaussian rational scalar type. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Polynomial in
/-- Dense polynomials with Gaussian rational coefficients. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Geometry in
/-- A rational rectangular box. -/
abbrev Box := Rational.Box
section
open Purelib.Integration
/-- A finite polynomial integration cell model. -/
abbrev CellModel := Polynomial.Gaussian.Cell.Basic.CellModel
/-- A polynomial cell's local integrand observation and discrepancy certificate. -/
abbrev LocalObservation :=
  Polynomial.Gaussian.Cell.Basic.LocalObservation
end

open Purelib.Riemann in
/-- A retained square-root continuation owner. -/
abbrev Owner := Topology.SquareRootContinuationChain.Owner

open Purelib.Curves in
open Purelib.Geometry in
set_option genInjectivity false in
/-- An integration cell certified against one lifted differential edge.

The record identifies the exact endpoints and retains every algebraic observation certificate for the chosen
differential and lifted cell. -/
structure CertifiedCell {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential :
      Hyperelliptic.Differentials.Basic.Differential genus)
    {start finish : Path.Gaussian.Lifted.Basic.LiftedPoint 2} (liftedCell : Path.Gaussian.Lifted.Basic.LiftedCell start
      finish) where
  /-- The retained finite integration model. -/ model : CellModel
  /-- The model begins at the lifted edge's initial coordinate. -/ start_eq : model.start = start.coordinate
  /-- The model ends at the lifted edge's final coordinate. -/ finish_eq : model.finish = finish.coordinate
  /-- The algebraic certificates for the model's actual observation list. -/ observations :
    Hyperelliptic.Integration.Algebraic.Observation.Basis.ObservationCertificates curve differential liftedCell model
    model.observations

constructive_injectivity CertifiedCell

section
open Purelib.Approximation
/-- Select the explicit rational witness of a coherent coefficient's initial state. -/
def initialReading (value : Gaussian.Name.Coherent.CoherentNamed) : Gaussian :=
  (value.name.process.witness value.name.state).val

/-- The selected initial reading is admitted by the coefficient's finite initial state. -/
theorem initialReading_possible
    (value : Gaussian.Name.Coherent.CoherentNamed) :
    value.name.process.Possible value.name.state (initialReading value) :=
  (value.name.process.witness value.name.state).property

end

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Certify a constant-polynomial differential observation on a clear segment.

At the displayed unit-interval parameter, construct the selected square-root sheet and retain an admitted Gaussian
reading of the differential with zero local polynomial discrepancy. -/
def clearSample {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (sheet : Fin 2) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    CertifiedCell curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet segment) := by
  let point := segment.pointAt parameter
  let radicandNonzero := segment.pointAt_eval_ne_zero parameter inside
  let sheetValue := Hyperelliptic.Sheets.Basic.AlgebraicSheetValue.automatic curve point
    radicandNonzero sheet
  let coefficient := Hyperelliptic.Differentials.Value.differentialValue differential point sheetValue.value
    sheetValue.apart
  let state := coefficient.name.state
  let reading := initialReading coefficient
  let polynomial := Ascending.Gaussian.Basic.constant reading
  let observation : LocalObservation polynomial 0 :=
    { parameter := parameter
      integrandReading := reading
      error := 0
      decomposition := by
        dsimp only [polynomial]
        rw [Ascending.Gaussian.Evaluation.eval_constant]
        change reading - reading = 0
        exact Gaussian.Basic.sub_self reading
      error_le := by
        change Gaussian.Norm.Basic.normSq (0 : Gaussian) <= 0
        exact le_rfl }
  let model : CellModel :=
    { start := start
      finish := finish
      polynomial := polynomial
      localAllowance := 0
      localAllowance_nonneg := le_rfl
      observations := [observation] }
  let algebraic : Hyperelliptic.Integration.Algebraic.Observation.Basis.AlgebraicObservation curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet segment)
      model observation := by
    refine
      { point := point
        point_eq := rfl
        sheetValue := sheetValue
        chosenSheet_eq := ?_
        readingState := state
        readingPossible := ?_ }
    · change sheet = sheet
      rfl
    · change coefficient.name.process.Possible state reading
      exact initialReading_possible coefficient
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .cons algebraic (.nil) }

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Certify a differential observation using a retained same-owner continuation chain.

Its endpoint equation identifies the radicand at the displayed segment parameter and preserves the chain's selected
square-root sheet. -/
def continuedSample {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (chain : Topology.SquareRootContinuationChain.SeededChain
      source sourceNonzero)
    (endpoint_eq : chain.endpoint.parameter =
      curve.polynomial.eval (segment.pointAt parameter)) :
    CertifiedCell curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet
        chain.sheet segment) := by
  let point := segment.pointAt parameter
  let radicandNonzero := segment.pointAt_eval_ne_zero parameter inside
  let sheetValue := chain.algebraicSheetValue curve point source
    sourceNonzero endpoint_eq
  let coefficient := Hyperelliptic.Differentials.Value.differentialValue differential point sheetValue.value
    sheetValue.apart
  let state := coefficient.name.state
  let reading := initialReading coefficient
  let polynomial := Ascending.Gaussian.Basic.constant reading
  let observation : LocalObservation polynomial 0 :=
    { parameter := parameter
      integrandReading := reading
      error := 0
      decomposition := by
        dsimp only [polynomial]
        rw [Ascending.Gaussian.Evaluation.eval_constant]
        change reading - reading = 0
        exact Gaussian.Basic.sub_self reading
      error_le := by
        change Gaussian.Norm.Basic.normSq (0 : Gaussian) <= 0
        exact le_rfl }
  let model : CellModel :=
    { start := start
      finish := finish
      polynomial := polynomial
      localAllowance := 0
      localAllowance_nonneg := le_rfl
      observations := [observation] }
  let algebraic : Hyperelliptic.Integration.Algebraic.Observation.Basis.AlgebraicObservation curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet
        chain.sheet segment) model observation := by
    refine
      { point := point
        point_eq := rfl
        sheetValue := sheetValue
        chosenSheet_eq := ?_
        readingState := state
        readingPossible := ?_ }
    · change chain.sheet = chain.sheet
      rfl
    · change coefficient.name.process.Possible state reading
      exact initialReading_possible coefficient
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .cons algebraic (.nil) }

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
/-- Certify a differential reading at the computed endpoint of a clear-segment subdivision.

Use the subdivision's retained seeded continuation chain and exact endpoint equation. -/
def continuedEndpointSample {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (sheet : Fin 2)
    (subdivision : Branches.ClearSheetContinuation.Subdivision
      segment within left leftInside
        (Topology.SquareRootContinuationChain.Owner.independent
          (segment.pointAt_eval_ne_zero left leftInside) sheet)) :
    CertifiedCell curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet segment) := by
  let chain := subdivision.seeded sheet
  have endpoint_eq : chain.endpoint.parameter =
      curve.polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter) := by
    exact subdivision.toChain_endpoint_parameter
  exact continuedSample curve differential segment
    subdivision.endpoint.parameter subdivision.endpoint.inside
    (segment.pointAt_eval_ne_zero left leftInside) chain endpoint_eq

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Certify an endpoint differential reading from an inherited square-root owner.

The owner is indexed by the polynomial at the segment endpoint, preserving the transported root while constructing the
constant local observation. -/
def inheritedEndpointSample {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (sheet : Fin 2)
    (owner : Owner (curve.polynomial.eval finish)) :
    CertifiedCell curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet segment) := by
  let radicandNonzero := segment.finish_eval_ne_zero
  let root := owner.certificate radicandNonzero
  let sheetValue : Hyperelliptic.Sheets.Basic.AlgebraicSheetValue curve finish :=
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        Gaussian.Equivalence.NamedEquivalent.trans root.square
          (Gaussian.Equivalence.NamedEquivalent.symm
            (Approximation.Gaussian.Evaluation.Horner.polynomialEval_exact
              curve.polynomial finish)) }
  let coefficient := Hyperelliptic.Differentials.Value.differentialValue differential finish sheetValue.value
    sheetValue.apart
  let state := coefficient.name.state
  let reading := initialReading coefficient
  let polynomial := Ascending.Gaussian.Basic.constant reading
  let observation : LocalObservation polynomial 0 :=
    { parameter := 1
      integrandReading := reading
      error := 0
      decomposition := by
        dsimp only [polynomial]
        rw [Ascending.Gaussian.Evaluation.eval_constant]
        exact Gaussian.Basic.sub_self reading
      error_le := by
        change Gaussian.Norm.Basic.normSq (0 : Gaussian) <= 0
        exact le_rfl }
  let model : CellModel :=
    { start := start
      finish := finish
      polynomial := polynomial
      localAllowance := 0
      localAllowance_nonneg := le_rfl
      observations := [observation] }
  let algebraic : Hyperelliptic.Integration.Algebraic.Observation.Basis.AlgebraicObservation curve differential
      (Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet segment)
      model observation := by
    refine
      { point := finish
        point_eq := ?_
        sheetValue := sheetValue
        chosenSheet_eq := rfl
        readingState := state
        readingPossible := ?_ }
    · apply Gaussian.Basic.ext <;>
        simp only [Cell.Basic.CellModel.observationPoint, model,
          Polynomial.Gaussian.Cell.Basic.CellModel.displacement,
          Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
    · change coefficient.name.process.Possible state reading
      exact initialReading_possible coefficient
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .cons algebraic (.nil) }

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Certified integration cells aligned with a retained clear-segment subdivision.

The ordered cell list carries differential and sheet certificates for the exact lifted geometric path. -/
structure CertifiedSubdivision {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision : Branches.ClearSheetContinuation.Subdivision
      segment within left leftInside owner) where
  /-- The ordered list of retained integration cell models. -/ cells : List CellModel
  /-- The cell certificates along the subdivision's actual lifted path. -/ certificates :
    Hyperelliptic.Integration.Algebraic.Diagnostics.Basis.PathCertificates curve differential cells
    (Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet sheet
      subdivision.toClearPath)

constructive_injectivity CertifiedSubdivision

section
open Purelib.Riemann
open Purelib.Curves
open Purelib.Polynomial
/-- Build algebraic cell certificates along the existing owner-transport subdivision.

Each step reuses its transported endpoint owner and recursively retains the same ordered tail. -/
def certifySubdivision {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2) :
    (subdivision : Branches.ClearSheetContinuation.Subdivision
      segment within left leftInside owner) →
      CertifiedSubdivision curve differential sheet subdivision
  | .stop _ _ _ =>
      { cells := []
        certificates := .nil _ }
  | .next left leftInside owner right rightInside small remaining => by
      let restricted :=
        segment.restrict within left right leftInside rightInside
      let head := inheritedEndpointSample curve differential restricted sheet
        (Branches.ClearSheetContinuation.advance segment within
          left right leftInside rightInside owner small)
      let tail := certifySubdivision curve differential sheet remaining
      exact
        { cells := head.model :: tail.cells
          certificates := .cons head.start_eq head.finish_eq
            head.observations tail.certificates }

/-- The certified cell list has exactly one cell per subdivision step. -/
@[simp] theorem certifySubdivision_cellCount {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left))}
    (sheet : Fin 2)
    (subdivision : Branches.ClearSheetContinuation.Subdivision
      segment within left leftInside owner) :
    (certifySubdivision curve differential sheet subdivision).cells.length =
      subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Polynomial in
/-- Certify the exact zero-displacement model for a sheet-switch edge.

The model has equal endpoints and an empty observation list, so no quotient sample is required. -/
def switch {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (coordinate : Gaussian)
    (sheet : Fin 2) :
    CertifiedCell curve differential (Hyperelliptic.Branches.BranchCutLifts.switchCell coordinate sheet) := by
  let model : CellModel := Polynomial.Gaussian.Cell.Basic.CellModel.exact
    coordinate coordinate Ascending.Gaussian.Basic.zero
  exact
    { model := model
      start_eq := rfl
      finish_eq := rfl
      observations := .nil }

end Purelib.Riemann.Readings.ClearDifferentialObservations

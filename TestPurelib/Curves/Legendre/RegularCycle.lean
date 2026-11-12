module

import Purelib.Examples.Curves.Legendre.RegularCycle.Periods
import Purelib.Data.Gaussian.Basic

/-!
# Actual six-channel programs on both regular Legendre sheets

Every stage selects an original Newton request, caches the four original
six-channel side models, and constructs the retained programs. Their
sample and coherence conclusions come from the polynomial telescope.
-/

namespace TestPurelib.Curves.Legendre.RegularCycle

open Purelib
open Purelib.Examples.Curves.Legendre.RegularCycle
open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Approximation.Rational
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
open Purelib.Examples.Curves.Legendre

attribute [local irreducible] patch

/-- The original regular-chart source cache for the selected sheet. -/
private def cache (sheet : Fin 2) : Cache (patch sheet) := Cache.ofPatch (patch sheet)

/-- The exact positive stage targets used to refine the original source model. -/
private def targets (index : Nat) : Rational := Geometric.Basic.quarterRadius 1 index

/-- The original source request selected at every retained stage. -/
private def sources (sheet : Fin 2) : Sources (cache sheet) (fun index => index) targets :=
  fun index => (cache sheet).request index (targets index) (Geometric.Basic.quarterRadius_pos (by decide) index)

/-- The six actual programs consume the same retained original side caches at each stage. -/
private def programs (sheet : Fin 2) : Programs (sources sheet) :=
  Programs.build (stageCells (sources sheet))

example (sheet coordinate : Fin 2) (index : Nat) :
    (((programs sheet).value coordinate).model index).integralSample = 0 :=
  (programs sheet).value_integralSample_zero coordinate index

example (sheet coordinate : Fin 2) (index : Nat) :
    (((programs sheet).first coordinate).model index).integralSample = 0 :=
  (programs sheet).first_integralSample_zero coordinate index

example (sheet coordinate : Fin 2) (index : Nat) :
    (((programs sheet).second coordinate).model index).integralSample = 0 :=
  (programs sheet).second_integralSample_zero coordinate index

example (sheet coordinate : Fin 2) (index : Nat) :
    LiftedPath.FollowedBy (((programs sheet).value coordinate).model index).cells
      (loop sheet).path := (programs sheet).value_follows coordinate index

example (sheet coordinate : Fin 2) (earlier later : Nat) (order : earlier ≤ later) :
    Canonical.normSq
      ((((programs sheet).second coordinate).model later).integralSample -
        (((programs sheet).second coordinate).model earlier).integralSample) ≤
      Geometric.Basic.quarterRadius ((programs sheet).second coordinate).errorScale earlier :=
  ((programs sheet).second coordinate).later_close order

/-- The original six-request-before-model schedule on either independently retained root sheet. -/
private def schedule (sheet : Fin 2) : Schedule sheet := Schedule.build sheet

example (sheet : Fin 2) (index : Nat) (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1) :
    let query := (schedule sheet).lowerQuery index
    let observed := query.observe Frame.frame input lower upper
    let original := ((schedule sheet).sides index).lower
    Canonical.normSq observed.valueZero.observation.error ≤
        original.models.valueZero.model.localAllowance ∧
      Canonical.normSq observed.valueOne.observation.error ≤
        original.models.valueOne.model.localAllowance ∧
      Canonical.normSq observed.firstZero.observation.error ≤
        original.models.firstZero.model.localAllowance ∧
      Canonical.normSq observed.firstOne.observation.error ≤
        original.models.firstOne.model.localAllowance ∧
      Canonical.normSq observed.secondZero.observation.error ≤
        original.models.secondZero.model.localAllowance ∧
      Canonical.normSq observed.secondOne.observation.error ≤
        original.models.secondOne.model.localAllowance := by
  let observed := ((schedule sheet).lowerQuery index).observe Frame.frame input lower upper
  exact ⟨observed.valueZero.observation.error_le, observed.valueOne.observation.error_le,
    observed.firstZero.observation.error_le, observed.firstOne.observation.error_le,
    observed.secondZero.observation.error_le, observed.secondOne.observation.error_le⟩

example (sheet : Fin 2) (index : Nat) :
    ((schedule sheet).requests index).stage ≤ ((schedule sheet).sources index).selection.stage :=
  (schedule sheet).stage_paid index

example (sheet : Fin 2) (index : Nat) :
    ((schedule sheet).plans index).stage ≤ ((schedule sheet).sources index).selection.stage :=
  (schedule sheet).endpoint_stage_paid index

example (sheet : Fin 2) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Integration.Polynomial.Gaussian.Path.Basic.PathModel.mk
        ((schedule sheet).stages index).sources.zero).integralSample ≤ Geometric.Basic.quarterRadius 1 index :=
  ((schedule sheet).stages index).zero_error_le

example (sheet : Fin 2) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Integration.Polynomial.Gaussian.Path.Basic.PathModel.mk
        ((schedule sheet).stages index).sources.one).integralSample ≤ Geometric.Basic.quarterRadius 1 index :=
  ((schedule sheet).stages index).one_error_le

example (sheet : Fin 2) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (Integration.Polynomial.Gaussian.Path.Basic.PathModel.mk
        ((schedule sheet).stages index).sources.scalar).integralSample ≤ Geometric.Basic.quarterRadius 1 index :=
  ((schedule sheet).stages index).scalar_error_le

example (sheet : Fin 2) (index : Nat) :
    ((schedule sheet).sources index).model.residual.eval (0 : Canonical) = 1 :=
  (schedule sheet).residual_at_zero index

example (sheet : Fin 2) : (schedule sheet).jet.cycle = cycle sheet := (schedule sheet).jet_cycle

example (sheet : Fin 2) (index : Nat) :
    ((schedule sheet).jet.source.stages index).sources = ((schedule sheet).programs.cells index).sourcePath :=
  (schedule sheet).jet_stage index

example (sheet coordinate : Fin 2) (index : Nat) :
    Jets.UniformPathCertificates (Fibre.frameCurve Frame.frame)
      (Specification.valueSpecification 2 coordinate)
      (((schedule sheet).jet.value coordinate).integral.model index).cells
      ((schedule sheet).jet.cycle.liftedPath index).path :=
  ((schedule sheet).jet.value coordinate).certificates index

example (sheet coordinate : Fin 2) (index : Nat) :
    (((schedule sheet).jet.value coordinate).integral.model index).integralSample = 0 := by
  rewrite [(schedule sheet).jet_value_integral coordinate]
  exact (schedule sheet).programs.value_integralSample_zero coordinate index

example (sheet coordinate : Fin 2) (index : Nat) :
    Jets.UniformPathCertificates (Fibre.frameCurve Frame.frame)
      (Specification.firstDerivativeSpecification 2 coordinate)
      (((schedule sheet).jet.first coordinate).integral.model index).cells
      ((schedule sheet).jet.cycle.liftedPath index).path :=
  ((schedule sheet).jet.first coordinate).certificates index

example (sheet coordinate : Fin 2) (index : Nat) :
    (((schedule sheet).jet.first coordinate).integral.model index).integralSample = 0 := by
  rewrite [(schedule sheet).jet_first_integral coordinate]
  exact (schedule sheet).programs.first_integralSample_zero coordinate index

example (sheet coordinate : Fin 2) (index : Nat) :
    Jets.UniformPathCertificates (Fibre.frameCurve Frame.frame)
      (Specification.secondDerivativeSpecification 2 coordinate)
      (((schedule sheet).jet.second coordinate).integral.model index).cells
      ((schedule sheet).jet.cycle.liftedPath index).path :=
  ((schedule sheet).jet.second coordinate).certificates index

example (sheet coordinate : Fin 2) (index : Nat) :
    (((schedule sheet).jet.second coordinate).integral.model index).integralSample = 0 := by
  rewrite [(schedule sheet).jet_second_integral coordinate]
  exact (schedule sheet).programs.second_integralSample_zero coordinate index

example (sheet : Fin 2) : RootBranch (lowerLeftRoot sheet) (Vertices.build sheet).lowerLeft.sample :=
  RootBranch.ofOwnerEq (lowerLeftRoot sheet) (Vertices.build sheet).lowerLeft.sample
    (congrArg (fun sample => sample.owner) (Vertices.build_lowerLeft_sample sheet)).symm

example (sheet : Fin 2) : RootBranch (lowerRightRoot sheet) (Vertices.build sheet).lowerRight.sample :=
  RootBranch.ofOwnerEq (lowerRightRoot sheet) (Vertices.build sheet).lowerRight.sample
    (congrArg (fun sample => sample.owner) (Vertices.build_lowerRight_sample sheet)).symm

example (sheet : Fin 2) : RootBranch (upperRightRoot sheet) (Vertices.build sheet).upperRight.sample :=
  RootBranch.ofOwnerEq (upperRightRoot sheet) (Vertices.build sheet).upperRight.sample
    (congrArg (fun sample => sample.owner) (Vertices.build_upperRight_sample sheet)).symm

example (sheet : Fin 2) : RootBranch (upperLeftRoot sheet) (Vertices.build sheet).upperLeft.sample :=
  RootBranch.ofOwnerEq (upperLeftRoot sheet) (Vertices.build sheet).upperLeft.sample
    (congrArg (fun sample => sample.owner) (Vertices.build_upperLeft_sample sheet)).symm

end TestPurelib.Curves.Legendre.RegularCycle

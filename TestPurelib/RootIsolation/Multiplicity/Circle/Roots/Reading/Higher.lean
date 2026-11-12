module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Higher
public import scripts.checkpoint.Circle
import Purelib.Polynomial.Dense.Map.Basic
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Actual exterior higher roots through their retained source schedule

The same original higher argument supplies its radius, separated ordered
samples and strict radial owners. One original formal tower over Gaussian
coefficients is read from a prepaid source schedule and its checked original
source expansion. Root coordinates remain elements of that same formal
algebra; their actual endpoint readings satisfy the original exterior bounds.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Higher

open Purelib
open Purelib.System.FilePath (join)
open Data (Json)
open Data.Json (toJson)
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Bounds.RootRadius.Box (largeSquareBox)
open Polynomial.Dense.Roots (Tower)
open Polynomial.Dense.Roots.Tower.Reading (Parameters Request Sources)
open Polynomial.Clearance.Circle (Certificate)
open RootIsolation.FTA.Squarefree
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots.Reading (Higher)
open Algebra.Ring (GaussianReading)
open IntegrationCheckpoint
open RootRefinementCheckpoint

/-- The original identity reading preserves the complete same original coefficient table. -/
private theorem identity_source (polynomial : CoefficientPolynomial) :
    polynomial = Polynomial.Dense.Map.map GaussianReading.identity.read polynomial :=
  (Polynomial.Dense.Map.map_id polynomial).symm

/-- Read the same original exterior higher owners using one original formal tower and paid source expansion.

The source-normalization proof concerns the same supplied coefficient table.
Every request is computed before scheduled continuation, while checked saved
samples and divisions retain their original constructor equations. No model,
root coordinates or radial payment is supplied independently.
-/
public def run {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) {clearance : Certificate polynomial}
    (locations : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared))
    (argument : CenterProduct.Approximation locations) (normalized : polynomial.normalize = polynomial)
    (control : Control) (directory : System.FilePath) : CircleCheckpoint.Execution Json := do
  have leadingNonzero : polynomial.leadingCoeff ≠ 0 := DensePolynomial.leadingCoeff_ne_zero input.nonzero
  let leadingInverse := polynomial.leadingCoeff⁻¹
  let tower := Tower.prepare polynomial normalized leadingInverse (Canonical.mul_inv_cancel _ leadingNonzero)
  have radiusNonnegative : 0 ≤ argument.request.radius := by
    rewrite [argument.request.radius_eq]
    exact (largeSquareBox polynomial).normSqBound_nonneg
  let parameters := Parameters.prepare tower Norm.weight 1 argument.request.radius (by decide) radiusNonnegative
  let budget := Request.prepare parameters 1 (by decide)
  have leading : Tower.Leading tower id polynomial.leadingCoeff :=
    Tower.Leading.ofSource tower id polynomial.leadingCoeff normalized rfl rfl rfl (fun _ _ => rfl)
  let initial := GaussianReading.identity
  have sourceEq : polynomial = Polynomial.Dense.Map.map initial.read polynomial := identity_source polynomial
  let request := Sources.Radial.prepare budget.budget leading argument.request.gaps.bound
    locations.request.collar.width argument.request.gaps.positive locations.request.collar.positive
  CircleCheckpoint.request control directory (Json.mkObj
    [("format", toJson "original-higher-root-reading-v1"),
     ("coefficients", toJson (polynomial.coeffs.map gaussianData)),
     ("radius", toJson (fractionData argument.request.radius)), ("target", toJson (fractionData 1)),
     ("initialTolerance", toJson (fractionData budget.tolerance)),
     ("separation", toJson (fractionData argument.request.gaps.bound)),
     ("collar", toJson (fractionData locations.request.collar.width)),
     ("inverseNorm", toJson (fractionData request.inverseNorm)),
     ("rootBound", toJson (fractionData request.rootBound)), ("cap", toJson (fractionData request.radial.cap))])
  profile directory "higher original formal tower and prepaid source schedule ready"
  let count := Higher.targets_count argument budget.budget leading request initial sourceEq
  let samples ← CircleCheckpoint.sourceSamples prepared locations argument request.sources.schedule.val
    request.sources.schedule.property count control directory
  let higher := Higher.ofSamples argument budget.budget leading initial rfl sourceEq (le_refl _)
    request rfl samples.val samples.property
  have same : higher = Higher.prepare argument budget.budget leading initial rfl sourceEq (le_refl _) :=
    Higher.ofSamples_eq_prepare argument budget.budget leading initial rfl sourceEq (le_refl _)
      request rfl samples.val samples.property
  let endpoint := higher.model.realization.finalReading
  have errorPaid : endpoint.error < 1 := higher.error_lt budget.positive
  have gainEq : endpoint.gain = parameters.finalGain := higher.final_gain
  unless decide (endpoint.error < 1) && decide (endpoint.gain = parameters.finalGain) do
    throw (IO.userError "the actual original higher endpoint lost its paid error or fixed gain")
  let mut roots : List Json := []
  for index in List.ofFn (fun index : Fin tower.blocks.length => index) do
    let localIndex := higher.localIndex index
    let original := argument.request.trackIndex localIndex
    let point := endpoint.read (tower.blocks[index.val]'index.isLt).point
    let quadrance := Norm.Basic.normSq point
    if exterior : locations.insideAt original = false then
      have radial : higher.request.originalRadial.floor ≤ quadrance := higher.outside index exterior
      unless decide (higher.request.originalRadial.floor ≤ quadrance) && decide (1 < quadrance) do
        throw (IO.userError "an actual original formal-root reading lost its same indexed exterior owner")
      roots := roots ++ [Json.mkObj
        [("index", toJson index.val), ("sampleIndex", toJson localIndex.val),
         ("trackIndex", toJson original.val), ("inside", toJson (locations.insideAt original)),
         ("quadrance", toJson (fractionData quadrance))]]
    else
      throw (IO.userError "the exterior higher fixture has an original interior label")
  let result := Json.mkObj
    [("format", toJson "original-higher-root-reading-v1"), ("roots", toJson roots),
     ("degree", toJson polynomial.natDegree), ("layers", toJson parameters.layers),
     ("radius", toJson (fractionData argument.request.radius)),
     ("gain", toJson (fractionData endpoint.gain)), ("error", toJson (fractionData endpoint.error)),
     ("target", toJson (fractionData 1)), ("floor", toJson (fractionData higher.request.originalRadial.floor)),
     ("ceiling", toJson (fractionData higher.request.originalRadial.ceiling)),
     ("sourceInitial", toJson (fractionData request.sources.schedule.val.initial))]
  saveJson (join directory (.mk "result.json")) result
  profile directory "higher original formal-root reading and indexed radial bounds ready"
  return result

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Higher

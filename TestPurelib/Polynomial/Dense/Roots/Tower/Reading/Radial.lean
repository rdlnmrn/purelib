module

import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled.Radial
import Purelib.Data.Gaussian.Field

/-!
# Paid radial transfer with an actual nonzero terminal correction

The original linear adjunction reads its formal root as one half while
the retained candidate is fifty-one hundredths. The actual original
expansion pays a radial cap fixed before this candidate was observed.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Tower.Reading.Radial

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Request Sources Sampled)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- The actual original source has its single exact root at one half. -/
private def source : DensePolynomial Canonical := ⟨[1, -1/2]⟩

/-- The original automatic constructor retains its actual linear companion and synthetic quotient. -/
private def tower : Tower Canonical inferInstance inferInstance source :=
  Tower.prepare source (by decide +kernel) 1 (by decide +kernel)

/-- All original finite reading data are prepared with unit gain and unit quadrance radius. -/
private def parameters : Parameters tower Norm.weight 1 1 :=
  Parameters.prepare tower Norm.weight 1 1 (by decide +kernel) (by decide +kernel)

/-- The actual source-fixed root total is one half before observing a candidate. -/
private theorem root_total : parameters.rootBoundTotal = 1/2 := by decide +kernel

/-- The original backward budget leaves the stricter radial cap active at its same terminal source. -/
private def readingRequest : Request parameters 32 := Request.prepare parameters 32 (by decide +kernel)

/-- The radial cap uses the same original parameter total and positive half-width collar. -/
private def radial : Norm.Radial.Request 1 parameters.rootBoundTotal 1 (1/2) :=
  Norm.Radial.Request.prepare 1 parameters.rootBoundTotal 1 (1/2) (by decide +kernel)
    parameters.rootBoundTotal_nonnegative (by decide +kernel) (by decide +kernel)

/-- The independently calculated fixed radial cap is one over one hundred twenty-eight. -/
private theorem radial_data : radial.cap = 1/128 ∧ radial.ceiling = 3/4 := by decide +kernel

/-- The original scalar-leading invariant follows from this same normalized monic linear source. -/
private theorem leading : Tower.Leading tower id 1 :=
  Tower.Leading.ofSource tower id 1 (by decide +kernel) (by decide +kernel) rfl rfl (fun _ _ => rfl)

/-- The same backward source schedule is prepared using the fixed radial cap. -/
private def sources : Sources readingRequest.budget leading 1 radial.cap :=
  Sources.prepare readingRequest.budget leading 1 radial.cap (by decide +kernel) radial.cap_positive

/-- The retained candidate differs from the actual original linear root. -/
private def candidate : Canonical := ⟨51/100, 0⟩

/-- One original synthetic division retains the actual candidate residual and quotient. -/
private def expansion : Interpolation.Expansion source [candidate] :=
  Interpolation.Expansion.prepare source [candidate]

/-- The original source schedule computes the same explicit one-entry target list. -/
private theorem source_targets : sources.targets = [1/128] := by decide +kernel

/-- The retained original head remainder has its independently calculated positive quadrance. -/
private theorem residual_readback : Norm.Basic.normSq expansion.first.remainder = 1/10000 := by decide +kernel

/-- This actual original division pays its one precomputed source target. -/
private theorem paid : expansion.Pays sources.targets := by
  rewrite [source_targets]
  apply Interpolation.Expansion.Pays.cons
  · change Norm.Basic.normSq expansion.first.remainder ≤ 1/128
    rewrite [residual_readback]
    decide +kernel
  · exact .nil

/-- The original retained candidate satisfies the fixed unit quadrance radius. -/
private theorem candidate_bounded : Norm.Basic.normSq candidate ≤ 1 := by decide +kernel

/-- Every original node in the same singleton list satisfies that source-fixed radius. -/
private theorem singleton_bound (value : Canonical → Rational) (candidate : Canonical) (bound : Rational)
    (bounded : value candidate ≤ bound) : ∀ point ∈ [candidate], value point ≤ bound := by
  intro point member
  cases member with
  | head => exact bounded
  | tail _ member => cases member

/-- The same scalar candidate bound applies at every original singleton-node occurrence. -/
private theorem nodes_bounded : ∀ point ∈ [candidate], Norm.Basic.normSq point ≤ 1 :=
  singleton_bound Norm.Basic.normSq candidate 1 candidate_bounded

/-- The automatic original construction reads its same one-root tower from this paid expansion. -/
private def sampled : Sampled readingRequest.budget GaussianReading.identity rfl [candidate] (radial.cap * 1) :=
  sources.realize GaussianReading.identity rfl source (Purelib.Polynomial.Dense.Map.map_id source).symm
    [candidate] expansion nodes_bounded paid

/-- The indexed matched readback keeps the original root position and candidate position. -/
private theorem indexed_displacement :
    Norm.Basic.normSq (sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point -
      candidate) ≤ radial.cap * 1 := sampled.matched.get ⟨0, by decide +kernel⟩

/-- The original terminal root reading includes the actual nonzero linear residual correction. -/
private theorem terminal_correction :
    sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point = ⟨1/2, 0⟩ ∧
      Norm.Basic.normSq (sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point -
        candidate) = 1/10000 := by decide +kernel

/-- The new all-input composition puts that corrected original formal-root reading below the fixed inside ceiling. -/
private theorem inside_transfer :
    Norm.Basic.normSq (sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point) ≤
      radial.ceiling :=
  sampled.inside radial ⟨0, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)

end TestPurelib.Polynomial.Dense.Roots.Tower.Reading.Radial

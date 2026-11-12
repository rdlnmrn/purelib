module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Exact
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Higher
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Original factor observations at their paid formal readings

The original exact or higher observation selects its existing association
payload. Both branches consume the same source-fixed bound cache and tower
budget. Their original root coordinates and retained geometric labels give
quantitative bounds on the actual final formal-root readings.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower (Leading)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Budget Realization)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Algebra.Ring (Weight GaussianReading)

universe u

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {context : PositiveContext input.entries} {clearance : Certificate context.focus.part.polynomial}
variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {formal : DensePolynomial K}
variable {tower : Tower K ring equality formal} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius} {embed : Canonical → K}

/-- The original observation selects its exact or higher association payload without copying either cache.

The bound cache remains indexed by the same observation, locations and
argument. In the higher branch its original radius equation transports the
fixed parameter bound; the exact branch retains the original exact root.
-/
@[expose] def Factor (observation : FactorObservation input context) (locations : Locations clearance observation)
    (argument : ObservationArgument observation locations) (bounds : Bounds observation locations argument)
    (budget : Budget parameters target tolerance)
    (leading : Leading tower embed context.focus.part.polynomial.leadingCoeff)
    (reading : GaussianReading parent embed) (gainEq : reading.gain = gain)
    (sourceEq : context.focus.part.polynomial = Map.map reading.read formal) (radiusBound : bounds.radius ≤ radius) :=
  match observation with
  | .exact root _ _ => Exact budget leading reading gainEq root
  | .higher _ _ => Higher argument budget leading reading gainEq sourceEq (by
      have same : bounds.radius = argument.request.radius := bounds.radius_eq
      exact same ▸ radiusBound)

namespace Factor

variable {observation : FactorObservation input context} {locations : Locations clearance observation}
variable {argument : ObservationArgument observation locations} {bounds : Bounds observation locations argument}
variable {budget : Budget parameters target tolerance}
variable {leading : Leading tower embed context.focus.part.polynomial.leadingCoeff}
variable {reading : GaussianReading parent embed} {gainEq : reading.gain = gain}
variable {sourceEq : context.focus.part.polynomial = Map.map reading.read formal} {radiusBound : bounds.radius ≤ radius}

/-- Construct the original selected association from its same bound cache and fixed formal budget.

The exact branch passes the retained ceiling directly as its point norm.
The higher branch invokes its original association once on the same argument
and transported original radius bound.
-/
@[expose] def prepare (observation : FactorObservation input context) (locations : Locations clearance observation)
    (argument : ObservationArgument observation locations) (bounds : Bounds observation locations argument)
    (budget : Budget parameters target tolerance)
    (leading : Leading tower embed context.focus.part.polynomial.leadingCoeff)
    (reading : GaussianReading parent embed) (gainEq : reading.gain = gain)
    (sourceEq : context.focus.part.polynomial = Map.map reading.read formal)
    (degreeEq : formal.natDegree = context.focus.part.polynomial.natDegree) (radiusBound : bounds.radius ≤ radius) :
    Factor observation locations argument bounds budget leading reading gainEq sourceEq radiusBound :=
  match observation with
  | .exact root degree _ =>
      have pointBound : Norm.Basic.normSq root.point ≤ radius :=
        have below := add_le_add_right_direct (by decide : (0 : Rational) ≤ 1) (Norm.Basic.normSq root.point)
        have same : bounds.radius = 1 + Norm.Basic.normSq root.point := bounds.radius_eq
        by
          rewrite [zero_add] at below
          exact below.trans (same ▸ radiusBound)
      Exact.ofNorm budget leading reading gainEq root (degreeEq.trans degree) degree sourceEq
        bounds.ceiling bounds.ceiling_eq pointBound
  | .higher _ _ => Higher.prepare argument budget leading reading gainEq sourceEq (by
      have same : bounds.radius = argument.request.radius := bounds.radius_eq
      exact same ▸ radiusBound)

/-- Project the actual original tower realization from the selected retained payload. -/
@[expose] def realization : (retained : Factor observation locations argument bounds budget leading reading gainEq
    sourceEq radiusBound) → Realization budget reading gainEq :=
  match observation with
  | .exact _ _ _ => fun retained => retained.sampled.realization
  | .higher _ _ => fun retained => retained.model.realization

/-- Preserve the same original natural root occurrence at its Gaussian factor degree. -/
@[expose] def localIndex (degreeEq : formal.natDegree = context.focus.part.polynomial.natDegree)
    (index : Fin tower.blocks.length) : Fin context.focus.part.polynomial.natDegree :=
  ⟨index.val, (tower.blocks_length.trans degreeEq) ▸ index.isLt⟩

/-- The selected original association keeps the final gain fixed before observation. -/
theorem final_gain (retained : Factor observation locations argument bounds budget leading reading gainEq
    sourceEq radiusBound) : retained.realization.finalReading.gain = parameters.finalGain :=
  retained.realization.final_gain

/-- A paid initial error gives the requested endpoint bound for the same actual selected association. -/
theorem error_le (retained : Factor observation locations argument bounds budget leading reading gainEq
    sourceEq radiusBound) (paid : reading.error ≤ tolerance) : retained.realization.finalReading.error ≤ target :=
  retained.realization.error_le paid

/-- A strictly paid initial error gives the strict endpoint bound for the same actual selected association. -/
theorem error_lt (retained : Factor observation locations argument bounds budget leading reading gainEq
    sourceEq radiusBound) (paid : reading.error < tolerance) : retained.realization.finalReading.error < target :=
  retained.realization.error_lt paid

/-- Each original inside label bounds its same actual formal-root reading by the retained physical ceiling. -/
theorem inside (retained : Factor observation locations argument bounds budget leading reading gainEq
    sourceEq radiusBound) (degreeEq : formal.natDegree = context.focus.part.polynomial.natDegree)
    (index : Fin tower.blocks.length)
    (label : Locations.insideAt observation locations (localIndex degreeEq index) = true) :
    Norm.Basic.normSq (retained.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤
      bounds.ceiling := by
  cases observation with
  | exact root degree oppositeRoot =>
      change Norm.Basic.normSq
        (retained.sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤ bounds.ceiling
      exact ((retained.normSq_root index).trans (retained.pointNorm_eq.trans bounds.ceiling_eq.symm)).le
  | higher boxes degree =>
      change HigherLocations.insideAt locations
        (argument.request.trackIndex (Higher.localIndex retained index)) = true at label
      have original := Higher.inside retained index label
      change Norm.Basic.normSq
        (retained.model.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤ bounds.ceiling
      have same : retained.request.originalRadial.ceiling = bounds.ceiling :=
        retained.request.originalRadial.ceiling_eq.trans
          ((congrArg (fun half : Rational => max 0 (1 - half))
            retained.request.originalRadial.halfWidth_eq).trans bounds.ceiling_eq.symm)
      exact same ▸ original

/-- Each original outside label bounds its same actual formal-root reading by the retained physical floor. -/
theorem outside (retained : Factor observation locations argument bounds budget leading reading gainEq
    sourceEq radiusBound) (degreeEq : formal.natDegree = context.focus.part.polynomial.natDegree)
    (index : Fin tower.blocks.length)
    (label : Locations.insideAt observation locations (localIndex degreeEq index) = false) :
    bounds.floor ≤ Norm.Basic.normSq
      (retained.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) := by
  cases observation with
  | exact root degree oppositeRoot =>
      change bounds.floor ≤ Norm.Basic.normSq
        (retained.sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point)
      exact ((bounds.floor_eq.trans retained.pointNorm_eq.symm).trans (retained.normSq_root index).symm).le
  | higher boxes degree =>
      change HigherLocations.insideAt locations
        (argument.request.trackIndex (Higher.localIndex retained index)) = false at label
      have original := Higher.outside retained index label
      change bounds.floor ≤ Norm.Basic.normSq
        (retained.model.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point)
      have same : retained.request.originalRadial.floor = bounds.floor :=
        retained.request.originalRadial.floor_eq.trans
          ((congrArg (fun half : Rational => 1 + half)
            retained.request.originalRadial.halfWidth_eq).trans bounds.floor_eq.symm)
      exact same ▸ original

end Factor

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

end

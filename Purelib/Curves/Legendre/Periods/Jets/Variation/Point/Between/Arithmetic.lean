module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Between
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Rows
import Purelib.Data.Fin
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Data.Rat.Fraction.Order.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original-box row factors for retained two-absolute-time arithmetic

One nominal retained cache keeps the complete original requestBetween
result and its whole factory identity. Its two independent residual/spread
requests, scalar core, arithmetic factory and new paid Reobservations remain
the same values. Their laws justify the same original-box row ceilings.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational.Box.Square
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

variable {parameter point firstOffset lastOffset : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point}
    (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)

attribute [local irreducible] BetweenRequest.Result in
set_option genInjectivity false in
/-- The complete original two-root request result retained with its whole original factory equation.

Both Steps and requests stay original indices. The stored raw result keeps
both independently paid root observations, the same scalar core, arithmetic
factory and new Reobservations without replacing either Step observation.
-/
structure BetweenRequest where
  /-- The same complete original request result, with all five dependent caches. -/
  val : BetweenRequest.Result first last unit nonzero spatial
  /-- The whole retained result is the original request factory on these exact inputs. -/
  property : val = requestBetween first last unit nonzero spatial

constructive_injectivity BetweenRequest

namespace BetweenRequest

/-- Execute the original two-root request factory once and retain its whole result and factory law. -/
def build (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest) :
    BetweenRequest first last unit nonzero spatial :=
  let retained := requestBetween first last unit nonzero spatial
  ⟨retained, rfl⟩

variable {first last unit nonzero spatial} (retained : BetweenRequest first last unit nonzero spatial)

/-- The complete stored five-field result is its original request factory on the same retained inputs. -/
theorem cache_eq : retained.val = requestBetween first last unit nonzero spatial := retained.property

/-- Read the SAME original scalar Taylor cache at the difference of its two absolute offsets. -/
@[expose] def core : BetweenCore first last unit := retained.val.2.2.1.val

/-- The scalar cache keeps its exact original factory on both actual retained paid root observations. -/
theorem core_eq : retained.core = betweenOfObservations first last unit
    (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) rfl retained.val.1.2.val retained.val.2.1.2.val :=
  retained.val.2.2.1.property

/-- The whole retained core request is the original local difference-fourth AccuracyRequest. -/
theorem accuracy_eq : retained.core.accuracy = Sampling.incrementRequest (lastOffset - firstOffset) nonzero :=
  AccuracyRequest.eq_of_tolerance_eq retained.core.accuracy_eq

/-- A genuinely paid model allowance transports only along exact equality of the same whole common request.

No Reading, request or evaluator is retagged. This is scalar transport of
an original inequality after the core factory proves its literal request.
-/
theorem allowancePaid (amount : Rational)
    (paid : amount ≤ (spatial.minimum (Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance) :
    amount ≤ (spatial.minimum retained.core.accuracy).tolerance :=
  paid.trans_eq (congrArg AccuracyRequest.tolerance
    (congrArg (fun accuracy : AccuracyRequest => spatial.minimum accuracy) retained.accuracy_eq)).symm

/-- Read the SAME actual inverse/cubic evaluator bank without repeating its original arithmetic factory. -/
@[expose] def arithmetic : Arithmetic.Observations retained.core := retained.val.2.2.2.1.val

/-- The whole original evaluator bank retains the exact same actual scalar core factory. -/
theorem arithmetic_eq : retained.arithmetic = Arithmetic.request retained.core := retained.val.2.2.2.1.property

/-- Read the genuinely new independently paid arithmetic reobservations on those same scalar/root owners. -/
@[expose] def paid : Arithmetic.Reobservations retained.arithmetic spatial := retained.val.2.2.2.2

/-- The same actual four-row numerical certificates obey the original fixed physical box and seed floor.

The original core factory is consumed only as an exact proof transport.
Both input Steps, both actual root observations and every paid arithmetic
reading remain retained. The ceiling is computed from the original patch,
independently of either absolute offset or their local difference.
-/
theorem row_factor_le (order coordinate : Fin 2) (inside : patch.box.Contains point) :
    (retained.paid.rowCertificate order coordinate).factor ≤ Joint.rowCeiling patch 0 order coordinate := by
  have sourceFloor := (congrArg (fun core : BetweenCore first last unit => core.clearance.sourceFloor)
    retained.core_eq).trans (betweenOfObservations_sourceFloor first last unit
      (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) rfl retained.val.1.2.val retained.val.2.1.2.val)
  have targetFloor := (congrArg (fun core : BetweenCore first last unit => core.clearance.targetFloor)
    retained.core_eq).trans (betweenOfObservations_targetFloor first last unit
      (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) rfl retained.val.1.2.val retained.val.2.1.2.val)
  have sumFloor := (congrArg (fun core : BetweenCore first last unit => core.clearance.sumFloor)
    retained.core_eq).trans (betweenOfObservations_sumFloor first last unit
      (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) rfl retained.val.1.2.val retained.val.2.1.2.val)
  let bounded := fun degree : Fin 2 =>
    (retained.paid.rowCertificate degree coordinate).factor ≤ Joint.rowCeiling patch 0 degree coordinate
  have value : bounded 0 := by
    have original := retained.arithmetic.value_factor_le coordinate inside
    have ceiling : Arithmetic.valueCeiling (parameter + firstOffset) (lastOffset - firstOffset) coordinate
        patch.box retained.core.clearance.sourceFloor retained.core.clearance.targetFloor
          retained.core.clearance.sumFloor = Joint.valueCeiling patch 0 coordinate := by
      rewrite [sourceFloor, targetFloor, sumFloor]
      exact Arithmetic.valueCeiling_parameters (parameter + firstOffset) (lastOffset - firstOffset)
        parameter 0 coordinate patch.box patch.rootLower patch.rootLower (4 * patch.rootLower)
    exact (retained.paid.valueCertificate_factor_eq coordinate).trans_le (original.trans_eq ceiling)
  have first : bounded 1 := by
    have sourceLower : patch.rootLower ≤ Norm.Basic.normSq retained.core.sourceSample.reading :=
      sourceFloor.symm.trans_le retained.core.clearance.source_normSq_lower
    have targetLower : patch.rootLower ≤ Norm.Basic.normSq retained.core.targetSample.reading :=
      targetFloor.symm.trans_le retained.core.clearance.target_normSq_lower
    have sourceInverse : (Joint.inverseBox patch).Contains retained.core.sourceSample.reading⁻¹ :=
      Centered.normBox_contains (Order.Field.inv_pos_direct patch.rootLower_positive).le
        (Norm.Reciprocal.normSq_le patch.rootLower_positive sourceLower)
    have targetInverse : (Joint.inverseBox patch).Contains retained.core.targetSample.reading⁻¹ :=
      Centered.normBox_contains (Order.Field.inv_pos_direct patch.rootLower_positive).le
        (Norm.Reciprocal.normSq_le patch.rootLower_positive targetLower)
    have original := retained.arithmetic.first_factor_le coordinate inside sourceInverse targetInverse
    have ceiling : Arithmetic.firstCeiling (parameter + firstOffset) (lastOffset - firstOffset) coordinate
        patch.box (Joint.inverseBox patch) retained.core.clearance.sourceFloor retained.core.clearance.targetFloor
          retained.core.clearance.sumFloor = Joint.firstCeiling patch 0 coordinate := by
      rewrite [sourceFloor, targetFloor, sumFloor]
      exact Arithmetic.firstCeiling_parameters (parameter + firstOffset) (lastOffset - firstOffset)
        parameter 0 coordinate patch.box (Joint.inverseBox patch) patch.rootLower patch.rootLower (4 * patch.rootLower)
    exact (retained.paid.firstCertificate_factor_eq coordinate).trans_le (original.trans_eq ceiling)
  exact Data.Fin.casesDependent (motive := bounded) value
    (Data.Fin.casesDependent (motive := fun degree : Fin 1 => bounded degree.succ)
      first (fun degree => Fin.elim0 degree)) order

end BetweenRequest

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

end

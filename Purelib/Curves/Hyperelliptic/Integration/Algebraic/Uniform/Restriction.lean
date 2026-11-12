module

import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction

/-! # Uniform child queries retaining the original parent observations

An existing polynomial restriction cache supplies the actual physical child
model. Each child query transports one original parent query at its mapped
parameter, keeping the same integrand reading, residual, algebraic sheet,
coefficient interpretation and process state. No query is resampled.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets

open Purelib
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel LocalObservation)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {start finish childStart childFinish : LiftedPoint 2}
    {lifted : LiftedCell start finish} (childLifted : LiftedCell childStart childFinish)
    {cell : CellModel} {first last input : Rational}
    (cached : Restriction.Cached cell.polynomial (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last))
    (sameSheet : start.sheet = childStart.sheet)

namespace UniformObservation

variable (original : UniformObservation curve differential lifted cell (Cell.Restriction.parameter first last input))

/-- Transport one actual parent query to its cached physical child model at the corresponding local parameter.

The supplied child edge and its starting sheet are retained. Only the
observation's local parameter and polynomial indices change; its reading,
error, full sheet value, exact denotation and retained process state remain
the original cached values. Physical query incidence and both error payments
follow from the original query and exact restriction laws.
-/
def restrict : UniformObservation curve differential childLifted (Cell.Restriction.model cell cached) input := by
  let observation : LocalObservation (Cell.Restriction.model cell cached).polynomial
      (Cell.Restriction.model cell cached).localAllowance :=
    { parameter := input
      integrandReading := original.observation.integrandReading
      error := original.observation.error
      decomposition := by
        change original.observation.integrandReading -
          Evaluation.eval (Cell.Restriction.model cell cached).polynomial (Cast.Path.ofCoordinate input) = _
        rewrite [Cell.Restriction.eval_eq cell cached input]
        exact (congrArg (fun time : Rational => original.observation.integrandReading -
          Evaluation.eval cell.polynomial (Cast.Path.ofCoordinate time)) original.parameter_eq).symm.trans
          original.observation.decomposition
      error_le := original.observation.error_le }
  have point_eq : original.algebraic.point =
      (Cell.Restriction.model cell cached).observationPoint observation := by
    calc
      original.algebraic.point = cell.observationPoint original.observation := original.algebraic.point_eq
      _ = cell.point original.observation.parameter := cell.observationPoint_eq original.observation
      _ = cell.point (Cell.Restriction.parameter first last input) := congrArg cell.point original.parameter_eq
      _ = (Cell.Restriction.model cell cached).point input := (Cell.Restriction.point_eq cell cached input).symm
      _ = (Cell.Restriction.model cell cached).observationPoint observation :=
        ((Cell.Restriction.model cell cached).observationPoint_eq observation).symm
  exact
    { observation := observation
      parameter_eq := rfl
      algebraic :=
        { point := original.algebraic.point
          point_eq := point_eq
          sheetValue := original.algebraic.sheetValue
          chosenSheet_eq := original.algebraic.chosenSheet_eq.trans sameSheet
          interpretation := original.algebraic.interpretation
          readingState := original.algebraic.readingState
          readingPossible := original.algebraic.readingPossible }
      semantic_error_le := original.semantic_error_le }

/-- The child query keeps the SAME original parent integrand reading. -/
theorem restrict_reading :
    (restrict childLifted cached sameSheet original).observation.integrandReading =
      original.observation.integrandReading := by
  unfold restrict
  rfl

/-- The child query keeps the SAME original residual and its original allowance payment. -/
theorem restrict_error :
    (restrict childLifted cached sameSheet original).observation.error = original.observation.error := by
  unfold restrict
  rfl

/-- The actual physical observation point is unchanged by local-parameter restriction. -/
theorem restrict_point :
    (restrict childLifted cached sameSheet original).algebraic.point = original.algebraic.point := by
  unfold restrict
  rfl

/-- The child keeps the original full algebraic sheet cache, including its original point and certificate. -/
theorem restrict_sheetValue :
    HEq (restrict childLifted cached sameSheet original).algebraic.sheetValue original.algebraic.sheetValue := by
  unfold restrict
  rfl

/-- The same original signed sheet generator is read by the restricted uniform query. -/
theorem restrict_root_name :
    (restrict childLifted cached sameSheet original).algebraic.sheetValue.value.name =
      original.algebraic.sheetValue.value.name := by
  unfold restrict
  rfl

/-- The exact original coefficient interpretation cache is retained by the child observation. -/
theorem restrict_interpretation :
    HEq (restrict childLifted cached sameSheet original).algebraic.interpretation
      original.algebraic.interpretation := by
  unfold restrict
  rfl

/-- The restricted query preserves its original differential process state without reobservation. -/
theorem restrict_readingState :
    HEq (restrict childLifted cached sameSheet original).algebraic.readingState original.algebraic.readingState := by
  unfold restrict
  rfl

/-- The restricted query retains the original coefficient observation, including its selected state and radius. -/
theorem restrict_asReading :
    HEq (restrict childLifted cached sameSheet original).asReading original.asReading := by
  unfold restrict asReading
  rfl

/-- Restrict an existing parent observation using exact equality with the child affine parameter.

The equality transports the original record's parameter index before the
restriction operation. It neither executes a query nor replaces any of the
original observation caches.
-/
def restrictAt {time : Rational} (original : UniformObservation curve differential lifted cell time)
    (time_eq : time = Cell.Restriction.parameter first last input) :
    UniformObservation curve differential childLifted (Cell.Restriction.model cell cached) input := by
  cases time_eq
  exact restrict childLifted cached sameSheet original

/-- Restriction at an equal parameter keeps the same actual original integrand reading. -/
theorem restrictAt_reading {time : Rational} (original : UniformObservation curve differential lifted cell time)
    (time_eq : time = Cell.Restriction.parameter first last input) :
    (restrictAt childLifted cached sameSheet original time_eq).observation.integrandReading =
      original.observation.integrandReading := by
  cases time_eq
  exact restrict_reading childLifted cached sameSheet original

/-- Restriction at an equal parameter keeps the entire original coefficient observation and its retained radius. -/
theorem restrictAt_asReading {time : Rational} (original : UniformObservation curve differential lifted cell time)
    (time_eq : time = Cell.Restriction.parameter first last input) :
    HEq (restrictAt childLifted cached sameSheet original time_eq).asReading original.asReading := by
  cases time_eq
  exact restrict_asReading childLifted cached sameSheet original

namespace ArithmeticComparison

variable {original}
    {point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {rootObservation : RootObservation}
    {accuracy : Approximation.AccuracyRequest}
    {numeric : Reading differential point sheet apart state rootObservation accuracy}
    {identity : PowerIdentity sheet 2 (curve.polynomial.eval point)}

/-- Transport the existing arithmetic comparison to the cached child observation without selecting any new tail samples.

Both original observations, their exact channel relation, the cached numeric
denotation and all selected comparison samples are retained. Only the uniform
observation's physical cell and local parameter indices change.
-/
def restrict (retained : ArithmeticComparison original numeric identity) :
    ArithmeticComparison (UniformObservation.restrict childLifted cached sameSheet original) numeric identity := by
  unfold ArithmeticComparison UniformObservation.asReading UniformObservation.restrict
  exact retained

/-- The restricted comparison retains the cached numeric denotation and its original identity certificate. -/
theorem restrict_denotation (retained : ArithmeticComparison original numeric identity) :
    (restrict childLifted cached sameSheet retained).1 = retained.1 := by
  unfold restrict
  rfl

/-- The original comparison retains both observations and selected tail samples through restriction. -/
theorem restrict_comparison (retained : ArithmeticComparison original numeric identity) :
    HEq (restrict childLifted cached sameSheet retained).comparison retained.comparison := by
  unfold restrict comparison
  rfl

/-- Transport an existing arithmetic comparison through equal parameters and the cached child restriction.

The numerical reading, its request and square identity remain the original
indices. The equality reindexes the same parent observation; no comparison
builder or original query callback is executed.
-/
def restrictAt {time : Rational} {original : UniformObservation curve differential lifted cell time}
    (retained : ArithmeticComparison original numeric identity)
    (time_eq : time = Cell.Restriction.parameter first last input) :
    ArithmeticComparison
      (UniformObservation.restrictAt childLifted cached sameSheet original time_eq) numeric identity := by
  cases time_eq
  exact restrict childLifted cached sameSheet retained

/-- Equal-parameter restriction retains the complete original numeric denotation cache. -/
theorem restrictAt_denotation {time : Rational} {original : UniformObservation curve differential lifted cell time}
    (retained : ArithmeticComparison original numeric identity)
    (time_eq : time = Cell.Restriction.parameter first last input) :
    (restrictAt childLifted cached sameSheet retained time_eq).1 = retained.1 := by
  cases time_eq
  exact restrict_denotation childLifted cached sameSheet retained

/-- Equal-parameter restriction retains the whole original comparison and both selected sample payments. -/
theorem restrictAt_comparison {time : Rational} {original : UniformObservation curve differential lifted cell time}
    (retained : ArithmeticComparison original numeric identity)
    (time_eq : time = Cell.Restriction.parameter first last input) :
    HEq (restrictAt childLifted cached sameSheet retained time_eq).comparison retained.comparison := by
  cases time_eq
  exact restrict_comparison childLifted cached sameSheet retained

end ArithmeticComparison

end UniformObservation

namespace UniformCellCertificate

/-- Answer child-local queries by executing the original parent query once at the exact mapped parameter.

Both retained parameter endpoints lie in the original unit interval, in
either orientation. The original query record is passed unchanged to the
restriction operation; the existing cache supplies the child polynomial and
the original local allowance. Each callback executes its original parent
query once and retains all resulting observation caches.
-/
def restrict (original : UniformCellCertificate curve differential lifted cell)
    (first_inside : 0 ≤ first ∧ first ≤ 1) (last_inside : 0 ≤ last ∧ last ≤ 1) :
    UniformCellCertificate curve differential childLifted (Cell.Restriction.model cell cached) :=
  { query := fun input lower upper =>
      let inside := Cell.Restriction.parameter_inside first_inside last_inside ⟨lower, upper⟩
      let observed := original.query (Cell.Restriction.parameter first last input) inside.1 inside.2
      observed.restrict childLifted cached sameSheet }

end UniformCellCertificate

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets

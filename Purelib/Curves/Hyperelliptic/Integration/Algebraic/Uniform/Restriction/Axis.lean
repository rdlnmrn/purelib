module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Axis
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic

/-! # Same-observation restriction at an original axis-word occurrence

One supplied original observation is transported through its already
retained polynomial restriction. The continuation receives both complete
observations, the same stored cache and exact reading/root readbacks.
No root query, selector, row or model preparation is executed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)
open Purelib.Polynomial.Geometry.Grid

universe u v

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential curve.polynomial}
    {start finish childStart childFinish : LiftedPoint 2} {lifted : LiftedCell start finish}
    {cell : CellModel} {Alpha : Type u} {key : Alpha → Rational}
    {intervals : List (ClearGrid.Interval key)} {first last : Rational}
    (walk : AxisWalks.Walk intervals first last) {Edge : Type}
    (sources : List Edge) (read : Edge → Rational × Rational)
    (cached : Cell.Restriction.Axis.Caches walk sources read cell) (index : Fin sources.length)
    (childLifted : LiftedCell childStart childFinish) (sameSheet : start.sheet = childStart.sheet)
    (input : Rational)
    (original : UniformObservation curve differential lifted cell
      (Cell.Restriction.parameter (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).start
        (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).finish input))

/-- The exact continuation preserves both complete observation owners and their original readbacks. -/
@[expose] def AxisConsumer (Result : Type v) :=
  (kept : UniformObservation curve differential lifted cell
    (Cell.Restriction.parameter
      (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).start
      (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).finish input)) →
  kept = original →
  (restriction : Cached cell.polynomial
    (Cast.Path.ofCoordinate (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).start)
    (Cast.Path.ofCoordinate (Cell.Restriction.Axis.interval walk read (sources[index.val]'index.isLt)).finish)) →
  restriction = Cell.Restriction.Axis.restriction walk sources read cell cached index →
  (restricted : UniformObservation curve differential childLifted (Cell.Restriction.model cell restriction) input) →
  restricted = kept.restrict childLifted restriction sameSheet →
  restricted.observation.integrandReading = kept.observation.integrandReading →
  restricted.observation.error = kept.observation.error →
  restricted.algebraic.point = kept.algebraic.point →
  restricted.algebraic.sheetValue.value.name = kept.algebraic.sheetValue.value.name →
  HEq restricted.algebraic.sheetValue kept.algebraic.sheetValue →
  HEq restricted.algebraic.interpretation kept.algebraic.interpretation →
  HEq restricted.asReading kept.asReading → Result

/-- Retain the complete supplied observation and its actual stored axis restriction through one transport.

Both values remain available to the continuation. The original algebraic
sheet value, interpretation, root name, selected reading and residual are
preserved, with no original query operation called a second time.
-/
def withAxisRestriction {Result : Type v}
    (consume : AxisConsumer walk sources read cached index childLifted sameSheet input original Result) : Result :=
  let restriction := Cell.Restriction.Axis.restriction walk sources read cell cached index
  let restricted := original.restrict childLifted restriction sameSheet
  consume original rfl restriction rfl restricted rfl
    (restrict_reading childLifted restriction sameSheet original)
    (restrict_error childLifted restriction sameSheet original)
    (restrict_point childLifted restriction sameSheet original)
    (restrict_root_name childLifted restriction sameSheet original)
    (restrict_sheetValue childLifted restriction sameSheet original)
    (restrict_interpretation childLifted restriction sameSheet original)
    (restrict_asReading childLifted restriction sameSheet original)

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

end

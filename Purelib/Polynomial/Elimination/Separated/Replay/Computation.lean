module

public import Purelib.Polynomial.Elimination.Separated.Quadratic
public import Purelib.Polynomial.Elimination.Separated.Cubic
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Polynomial.Elimination.Separated.Replay.Computation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated
open Purelib.Data.Rat.Fraction (Rational)

set_option genInjectivity false in
/-- The retained outcome of checked quadratic and cubic unit-column production.

Success retains the actual checked original column and its proposal readback.
The cubic branch keeps the preceding quadratic attempt. General fallback
keeps both complete direct attempts, including any rejected vectors and actual
failed matrix products; it executes no general producer itself.
-/
inductive Outcome (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (generalCubic : Bool := false) where
  /-- The direct quadratic proposal supplied the original checked column. -/
  | quadratic (source : Quadratic.Shape p) (column : Replay.Column p positive parameter)
      (values_eq : column.values = source.propose parameter)
  /-- The direct cubic proposal supplied the column after the retained quadratic attempt. -/
  | cubic (quadratic : Quadratic.Attempt p positive parameter)
      (column : Replay.Column p positive parameter)
      (proposed : Cubic.propose? p parameter generalCubic = some column.values)
  /-- Both direct attempts are retained for the original general fallback. -/
  | fallback (quadratic : Quadratic.Attempt p positive parameter)
      (cubic : Cubic.Attempt p positive parameter generalCubic)

constructive_injectivity Outcome

/-- Try the two subject-owned direct rules against the same complete original equation.

An accepted quadratic prevents a cubic attempt. An accepted cubic prevents
general production. Every fallback retains the actual unsuccessful attempts
instead of turning a finite proposal failure into a global obstruction.
-/
@[expose] def compute (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (generalCubic : Bool := false) :
    Outcome p positive parameter generalCubic :=
  match Quadratic.attempt p positive parameter with
  | .accepted source column values_eq => .quadratic source column values_eq
  | quadratic =>
      match Cubic.attempt p positive parameter generalCubic with
      | .accepted column proposed => .cubic quadratic column proposed
      | cubic => .fallback quadratic cubic

/-- Read the actual checked column without rebuilding its vector or rerunning its checker. -/
@[expose] def Outcome.column? {p positive parameter generalCubic} :
    Outcome p positive parameter generalCubic → Option (Replay.Column p positive parameter)
  | .quadratic _ column _ => some column
  | .cubic _ column _ => some column
  | .fallback _ _ => none

/-- A false request preserves both complete direct attempts and the original branch order. -/
theorem compute_default (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) :
    compute p positive parameter false =
      match Quadratic.attempt p positive parameter with
      | .accepted source column values_eq => .quadratic source column values_eq
      | quadratic =>
          match Cubic.attempt p positive parameter with
          | .accepted column proposed => .cubic quadratic column proposed
          | cubic => .fallback quadratic cubic := by
  unfold compute
  generalize Quadratic.attempt p positive parameter = quadratic
  cases quadratic <;> first
    | rfl
    | (cases Cubic.attempt p positive parameter false <;> rfl)

end Purelib.Polynomial.Elimination.Separated.Replay.Computation

end

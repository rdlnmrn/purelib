module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original multiplicity occurrences at the exact origin -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Origin

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- The original ordered factor-list occurrence with its same exact origin root.

The bounded index retains its original positive multiplicity entry. Its
root certificate concerns that entry's same source polynomial, without
constructing an isolation family or choosing a completed root.
-/
structure Occurrence (entries : List PositiveEntry) where
  /-- The retained bounded position in the original positive multiplicity list. -/ index : Fin entries.length
  /-- The same original polynomial vanishes exactly at the origin. -/
  root : (entries.get index).part.polynomial.eval 0 = 0

constructive_injectivity Occurrence

/-- Read the exact original-factor root certificate of the same retained occurrence. -/
def Occurrence.certificate {entries : List PositiveEntry} (occurrence : Occurrence entries) :
    Roots.Certificate.ExactRoot (entries.get occurrence.index).part.polynomial :=
  ⟨0, occurrence.root⟩

set_option genInjectivity false in
/-- An exact original origin occurrence or a checked nonzero origin value for every retained factor.

Both branches refer to the same finite input list. The negative branch
retains every original bounded evaluation condition, rather than replacing
failure by an operational zero or impossibility assertion.
-/
inductive Attempt (entries : List PositiveEntry) where
  /-- Retain the exact same indexed source factor and its origin root. -/
  | found (occurrence : Occurrence entries)
  /-- Every original factor at its retained bounded index has nonzero origin value. -/
  | absent (nonzero : ∀ index : Fin entries.length, (entries.get index).part.polynomial.eval 0 ≠ 0)

constructive_injectivity Attempt

/-- Check original factor origin values in retained order with exact success or complete finite absence evidence. -/
def attempt : (entries : List PositiveEntry) → Attempt entries
  | [] => .absent (fun index => Fin.elim0 index)
  | entry :: entries =>
      if zero : entry.part.polynomial.eval 0 = 0 then
        .found ⟨0, zero⟩
      else
        match attempt entries with
        | .found occurrence => .found ⟨occurrence.index.succ, occurrence.root⟩
        | .absent nonzero => .absent (fun index => by
            cases index using Fin.cases with
            | zero => exact zero
            | succ tailIndex => exact nonzero tailIndex)

/-- Nonzero origin values at every original factor keep their retained weighted product nonzero. -/
private theorem value_nonzero : ∀ (entries : List PositiveEntry),
    (∀ index : Fin entries.length, (entries.get index).part.polynomial.eval 0 ≠ 0) →
      Basis.Positive.positiveValue entries 0 ≠ 0
  | [], _ => by decide
  | entry :: entries, nonzero =>
      Field.mul_ne_zero_direct
        (Power.pow_ne_zero_direct _ (nonzero 0) entry.multiplicity)
        (value_nonzero entries (fun index => nonzero index.succ))

/-- The original zero polynomial evaluation computes an exact origin occurrence in its same positive multiplicity list.

The finite scan supplies the actual bounded index. Complete absence would
contradict the original decomposition's nonzero unit and weighted product
identity, so no successful scan result is supplied as a hypothesis.
-/
def ofZero {polynomial : CoefficientPolynomial} (decomposition : Squarefree.Decomposition polynomial)
    (zero : polynomial.eval 0 = 0) : Occurrence decomposition.positiveMultiplicityEntries :=
  match attempt decomposition.positiveMultiplicityEntries with
  | .found occurrence => occurrence
  | .absent nonzero =>
      have product := Field.mul_ne_zero_direct decomposition.multiplicityUnit_ne_zero
        (value_nonzero _ nonzero)
      have identity := decomposition.eval_positiveMultiplicityEntries 0
      False.elim (product (identity.symm.trans zero))

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Origin

end

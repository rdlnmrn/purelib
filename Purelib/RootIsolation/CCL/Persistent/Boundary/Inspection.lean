module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Geometry.CCL.Parser.Formula.Advance
public import Purelib.Geometry.CCL.Parser.Formula.Description.Advance
import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.Next.Strict
import Purelib.RootIsolation.CCL.Persistent.Sample.Extension
import Purelib.RootIsolation.CCL.Persistent.State.Basic
public import Purelib.RootIsolation.Curve.Boundary.Inspection
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Box.Sign
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Projective.Hermitian.Formula.Description
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

public section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Boundary

set_option genInjectivity false in
/-- The strict next-bit inspection with universal equality boundaries already
discharged. -/
inductive NextInspection
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (formOverrides : List
      (Geometry.Projective.Hermitian.Formula.Box.FormOverride
        current.numerical.box)) where
  /-- The prepared original state admits no further local parser bit. -/ | terminal (result :
    Next.Strict.LocalTerminal current)
  /-- The original next parser bit has a retained strict or equality-owned stability certificate. -/ | stable (result :
    Next.Strict.StableNext current)
  /-- An unresolved next-bit atom retains its failed override lookup and complete original finite or curve boundary
    analysis. -/ | boundary (next : Next.Strict.BoundaryNext current)
      (notResolved : Geometry.Projective.Hermitian.Formula.Box.findFormOverride
        formOverrides next.atom.form = none)
      (remaining : Curve.Boundary.RemainingBoundary p
        (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate
          (Data.CCL.Encoding.Parser.State.parse current.word).matrix)
        current.numerical.box denominatorMargin marginPositive next.atom)

constructive_injectivity NextInspection

/-- Decide the local bit, inspect its complete incremental formula with exact
boundary provenance, and immediately apply universal equality ownership. -/
@[expose] def inspectNextWith
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (formOverrides : List
      (Geometry.Projective.Hermitian.Formula.Box.FormOverride
        current.numerical.box)) :
    NextInspection current denominatorMargin marginPositive formOverrides := by
  let sample := current.currentSample
  let next := sample.nextDecision
  match next.decision with
  | .terminal terminalNone =>
      exact .terminal
        { none := by
            intro bit possible
            apply terminalNone bit
            apply (Geometry.CCL.Parser.Formula.advanceFormula_iff
              (Data.CCL.Encoding.Parser.State.parse current.word) bit
              next.tail).2
            exact (Data.CCL.Encoding.Parser.Next.canStep_iff_canAdvanceAt
              (Data.CCL.Encoding.Parser.State.parse current.word) sample.point
              next.tail
              (Data.CCL.Encoding.Parser.State.parse_det_ne current.word)
              next.represents bit).1 possible }
  | .next bit tailHolds _unique =>
      let parser := Data.CCL.Encoding.Parser.State.parse current.word
      let reference := LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate parser.matrix
      let formula :=
        Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula parser bit
      have currentHolds : formula.Holds sample.point := by
        exact CCL.Persistent.Sample.Extension.CompatibleSample.inputIncrementalAdvanceFormula_holds_of_advance
          sample bit tailHolds
      let descriptions :=
        Geometry.CCL.Parser.Formula.Description.inputIncremental parser
          (Data.CCL.Encoding.Parser.State.parse_det_ne current.word) bit
      match Curve.Boundary.inspectOwnerWith p reference ambient current.numerical.box
          denominatorMargin marginPositive [] formOverrides formula
          (fun atom member => descriptions.boundaryFor atom member)
          current.numerical.refinesAmbient sample.point sample.inside with
      | .stable stable =>
          exact .stable
            { bit := bit
              stable := stable
              currentHolds := currentHolds }
      | .boundary atom member notResolved failure remaining =>
          exact .boundary
            { bit := bit
              atom := atom
              member := by simpa only [formula, -eq_self, -iff_self] using member
              failure := by simpa only [sample, formula, -eq_self, -iff_self] using failure
              currentHolds := by simpa only [sample, formula, -eq_self, -iff_self] using currentHolds }
            notResolved
            (by simpa only [reference, parser, -eq_self, -iff_self] using remaining)

/-- Initial persistent owner inspection with no previously resolved finite
form signs. -/
@[expose] def inspectNext
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) :
    NextInspection current denominatorMargin marginPositive [] :=
  inspectNextWith current denominatorMargin marginPositive []
end Purelib.RootIsolation.CCL.Persistent.Boundary

end

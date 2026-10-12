module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Rational.Request.Sixth
public import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Gap
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero

import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Curves.Legendre.BoundedTransport
import Init.Core
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual

open Purelib

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Rational.Request

open Purelib.Curves.Legendre.Acquisition

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Topology.Knot.Braid

public section

/-! # Exact word-denominator decisions with a finite candidate gap -/

namespace Purelib.Curves.Legendre.GapTransport

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Legendre.Acquisition.Automatic.Basic (State Ready)
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)
open Purelib.Data.Rat.Fraction (Rational)

set_option genInjectivity false in
/-- A retained ready result or proof of the specified exclusion condition. -/
inductive OutcomePayload.{u} (readyType : Type u) (exclusion : Prop) : Type
  u
  /-- The denominator decision produced the retained prepared word output. -/ | ready (result : readyType)
  /-- The denominator decision proved the retained exclusion condition. -/ | excluded (certificate : exclusion)

constructive_injectivity OutcomePayload

/-- A finite gap-based denominator decision indexed by its exact retained inspection.

The outcome either supplies a prepared output or proves that every candidate at the retained state is zero; the
inspection uses the original cached matrix and search state. -/
@[expose] def Report (tau : Coherent.CoherentNamed) (word : ThreeStrand.Word) (start : Automatic.Basic.State tau word)
    (gap : Fraction.Rational) (positive : 0 < gap) :=
  Sigma fun inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection
      (LegendreModularMonodromy.fractionalDenominator start.matrix tau)
      start.search (gap / 6) (Sixth.requestTarget_positive positive) =>
    OutcomePayload (Automatic.Basic.Ready tau word)
      (Zero.ZeroCandidates
        (LegendreModularMonodromy.fractionalDenominator start.matrix tau) inspection.retained)

/-- Only the structural gap, not the selected outcome, is an input. The ready output retains the ordinary transport and
equivalence theorems. -/
@[expose] def acquire (tau : Coherent.CoherentNamed) (word : ThreeStrand.Word) (start : Automatic.Basic.State tau word)
    (gap : Fraction.Rational) (positive : 0 < gap)
    (certificate : Approximation.Gaussian.Name.Coherent.Refinement.Gap
      (LegendreModularMonodromy.fractionalDenominator start.matrix tau) start.search gap) :
    Report tau word start gap positive :=
  let report := GapDecision.acquire start.search gap positive certificate
  ⟨report.1, match report.2 with
    | .prepared evidence => .ready (Automatic.Basic.ready tau word
        { start with search := report.1.retained }
        (FromSearch.preparationAt start.matrix tau
          report.1.retained evidence))
    | .excluded zero => .excluded zero⟩

end Purelib.Curves.Legendre.GapTransport

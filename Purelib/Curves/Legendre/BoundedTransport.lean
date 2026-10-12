module
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Rational.Request.Sixth
public import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.LegendreModularMonodromy
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
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual
import Purelib.Topology.Knot.Braid.ThreeStrand.Word

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Rational.Request

open Purelib.Curves.Legendre.Acquisition

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Topology.Knot

@[expose] public section

/-!
# Requested-precision Legendre denominator decisions

Unlike fuel exhaustion, the small branch carries a persistent mathematical
upper bound on the retained denominator candidates. The ready branch is the
same cached public result used by automatic and manual word transport, with
its existing output equation, transport witness, and schedule independence.
-/

namespace Purelib.Curves.Legendre.BoundedTransport

/-- Exact rational thresholds for finite denominator inspection. -/
abbrev Q := Fraction.Rational
/-- A productive Gaussian name with its retained coherence certificate. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- A finite three-strand braid word. -/
abbrev Word := Braid.Word 3
/-- The cached word matrix and its resumable denominator search state. -/
abbrev State := Automatic.Basic.State
/-- The cached prepared fractional output for the retained braid word. -/
abbrev Ready := Automatic.Basic.Ready

open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- Both branches retain the actual cached requested-target inspection. -/
def Report (tau : Curves.Legendre.BoundedTransport.CoherentNamed) (word : Curves.Legendre.BoundedTransport.Word) (start
  : Curves.Legendre.BoundedTransport.State tau word)
    (threshold : Curves.Legendre.BoundedTransport.Q) (positive : 0 < threshold) :=
  Sigma fun inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection
      (LegendreModularMonodromy.fractionalDenominator start.matrix tau)
      start.search (threshold / 6) (Sixth.requestTarget_positive positive) =>
    Sum (Curves.Legendre.BoundedTransport.Ready tau word)
      { _certificate : Approximation.Gaussian.Name.Coherent.Refinement.Small
          (LegendreModularMonodromy.fractionalDenominator start.matrix tau) inspection.retained
        threshold //
        Residual.SmallBall inspection.ball threshold }

/-- Reuse the already folded matrix and inspect its denominator at a prescribed accuracy. The threshold is not a fuel or
runtime limit. -/
def acquire (tau : Curves.Legendre.BoundedTransport.CoherentNamed) (word : Curves.Legendre.BoundedTransport.Word) (start
  : Curves.Legendre.BoundedTransport.State tau word)
    (threshold : Curves.Legendre.BoundedTransport.Q) (positive : 0 < threshold) :
      Curves.Legendre.BoundedTransport.Report tau word start threshold positive :=
  let report := SmallOrApart.acquire start.search threshold positive
  ⟨report.inspection, match selected : report.outcome with
    | .inl evidence => .inl (Automatic.Basic.ready tau word
        { start with search := report.inspection.retained }
        (FromSearch.preparationAt start.matrix tau
          report.inspection.retained evidence))
    | .inr small => .inr ⟨small, report.small_ball small selected⟩⟩

/-- Resume ordinary canonical retries from the new source, preserving the cached matrix and the not-yet-consumed
canonical request index. -/
def Report.retained {tau : Curves.Legendre.BoundedTransport.CoherentNamed} {word :
  Curves.Legendre.BoundedTransport.Word} {start : Curves.Legendre.BoundedTransport.State tau word}
    {threshold : Curves.Legendre.BoundedTransport.Q} {positive : 0 < threshold}
    (report : Curves.Legendre.BoundedTransport.Report tau word start threshold positive) :
      Curves.Legendre.BoundedTransport.State tau word :=
  { start with search := report.1.retained }

/-- Requested-accuracy inspection preserves the exact cached braid-word matrix. -/
@[simp] theorem Report.matrix_eq {tau : Curves.Legendre.BoundedTransport.CoherentNamed} {word :
  Curves.Legendre.BoundedTransport.Word} {start : Curves.Legendre.BoundedTransport.State tau word}
    {threshold : Curves.Legendre.BoundedTransport.Q} {positive : 0 < threshold}
    (report : Curves.Legendre.BoundedTransport.Report tau word start threshold positive) : report.retained.matrix =
      start.matrix := rfl

/-- Requested-accuracy inspection preserves the next canonical retry index. -/
theorem Report.nextIndex_eq {tau : Curves.Legendre.BoundedTransport.CoherentNamed} {word :
  Curves.Legendre.BoundedTransport.Word} {start : Curves.Legendre.BoundedTransport.State tau word}
    {threshold : Curves.Legendre.BoundedTransport.Q} {positive : 0 < threshold}
    (report : Curves.Legendre.BoundedTransport.Report tau word start threshold positive) :
    report.retained.search.nextIndex = start.search.nextIndex := report.1.index_eq

end Purelib.Curves.Legendre.BoundedTransport

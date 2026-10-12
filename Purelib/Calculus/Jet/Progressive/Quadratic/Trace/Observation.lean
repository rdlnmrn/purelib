module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Projection

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

open Purelib.Approximation in
open Purelib.Data in
/-- All five projected root enclosures share the geometric radius at their common index.

Each equality unfolds the retained projection schedule at that exact natural index. -/
theorem root_radius_eq {increment : Nat →
  Canonical}
    (trace : Trace increment) (index : Nat) :
    (trace.incrementApproximation.toProcess.ball index).radiusSq =
        Rational.Geometric.Basic.quarterRadius trace.errorScale index ∧
      (trace.baseApproximation.toProcess.ball index).radiusSq =
        Rational.Geometric.Basic.quarterRadius trace.errorScale index ∧
      (trace.outputApproximation.toProcess.ball index).radiusSq =
        Rational.Geometric.Basic.quarterRadius trace.errorScale index ∧
      (trace.slopeApproximation.toProcess.ball index).radiusSq =
        Rational.Geometric.Basic.quarterRadius trace.errorScale index ∧
      (trace.remainderApproximation.toProcess.ball index).radiusSq =
        Rational.Geometric.Basic.quarterRadius trace.errorScale index :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Purelib.Data
/-- The projected root centers are the indexed increment and retained certificate fields.

The conjunction records their ordered correspondence for the increment, base, output, slope and remainder projections.
-/
theorem root_centers {increment : Nat →
  Canonical}
    (trace : Trace increment) (index : Nat) :
    (trace.incrementApproximation.toProcess.ball index).center = increment index ∧
      (trace.baseApproximation.toProcess.ball index).center =
        (trace.certificate index).base ∧
      (trace.outputApproximation.toProcess.ball index).center =
        (trace.certificate index).output ∧
      (trace.slopeApproximation.toProcess.ball index).center =
        (trace.certificate index).slope ∧
      (trace.remainderApproximation.toProcess.ball index).center =
        (trace.certificate index).remainder :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The five root centers at a common index satisfy the exact first-order expansion.

The identity is the expansion field of the certificate retained at that same index. -/
theorem root_expansion {increment : Nat →
  Canonical}
    (trace : Trace increment) (index : Nat) :
    (trace.outputApproximation.toProcess.ball index).center -
        (trace.baseApproximation.toProcess.ball index).center -
        (trace.incrementApproximation.toProcess.ball index).center *
          (trace.slopeApproximation.toProcess.ball index).center =
      (trace.remainderApproximation.toProcess.ball index).center :=
  (trace.certificate index).expansion

/-- The root remainder quadrance obeys the indexed certificate's quadratic bound.

The factor is read from that certificate, and the increment center is the same indexed increment used in its type. -/
theorem root_remainder_le {increment : Nat →
  Canonical}
    (trace : Trace increment) (index : Nat) :
    Canonical.normSq (trace.remainderApproximation.toProcess.ball index).center ≤
      (trace.certificate index).factor *
        Canonical.normSq (trace.incrementApproximation.toProcess.ball index).center ^ 2 :=
  (trace.certificate index).remainder_le
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end

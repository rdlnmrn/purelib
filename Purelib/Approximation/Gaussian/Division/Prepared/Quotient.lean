module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Division

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
section
@[expose] public section

/-!
# Evidence-directed division with reusable state

The dispatcher first reuses an exact decision, then tries inferred finite
provenance, then an optional proved candidate gap, and finally one bounded
numerical request. A small result is inconclusive, not zero. Gap exclusion
is explicitly scoped to the retained branch. Exact provenance concerns
operational identities and is never used as a pointwise candidate gap.

All routes return the retained state. Requested refinements preserve the
retry index and transport optional gap evidence. Exact decisions, including
negative ones, are cached for subsequent numerators and requests.
-/

namespace Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Provenance)

/-- Construct ordinary coherent division using the retained equivalent denominator and its apartness certificate. -/
def quotient {channel : Coherent.CoherentNamed} (prepared : Prepared channel)
    (numerator : Coherent.CoherentNamed) : Coherent.CoherentNamed :=
  CoherentNamed.div numerator prepared.denominator prepared.apart

/-- Successful outputs respect changes to both input presentations, not just independently chosen preparations of the
same syntactic channel. -/
def quotient_respects_equivalent {first second firstNumerator secondNumerator : Coherent.CoherentNamed}
    (left : Prepared first) (right : Prepared second)
    (denominators : Gaussian.Equivalence.NamedEquivalent first.name second.name)
    (numerators : Gaussian.Equivalence.NamedEquivalent firstNumerator.name secondNumerator.name) :
    Gaussian.Equivalence.NamedEquivalent ((quotient left)
      firstNumerator).name ((quotient right)
      secondNumerator).name :=
  Equivalence.coherentDiv_respects firstNumerator secondNumerator
    left.denominator right.denominator left.apart right.apart numerators
    (NamedEquivalent.trans
      (NamedEquivalent.symm left.equivalent)
      (NamedEquivalent.trans denominators right.equivalent))

namespace Quotient

/-- This comparison also covers independently prepared successful outputs and equivalent numerator presentations. The
preparations are reused. -/
def quotients_respect {first second firstNumerator secondNumerator : Coherent.CoherentNamed}
    (left : Prepared first)
    (right : Prepared second)
    (denominators : Gaussian.Equivalence.NamedEquivalent first.name second.name)
    (numerators : Gaussian.Equivalence.NamedEquivalent firstNumerator.name secondNumerator.name) :
    Gaussian.Equivalence.NamedEquivalent
      ((quotient left) firstNumerator).name
        ((quotient right) secondNumerator).name :=
  (quotient_respects_equivalent left) right denominators
    numerators

end Quotient

set_option genInjectivity false in
/-- A cached ordinary quotient retaining its prepared denominator presentation.

The output equality ties the cached channel to division of the original numerator by that exact preparation. -/
structure Quotient (numerator channel : Coherent.CoherentNamed) where
  /-- The original denominator's retained equivalent apart presentation. -/ prepared : Prepared channel
  /-- The cached ordinary coherent quotient channel. -/ output : Coherent.CoherentNamed
  /-- The cached output equals division by the retained prepared denominator. -/ output_eq : output =
    (quotient prepared) numerator

constructive_injectivity Quotient

namespace Quotient

/-- Cache ordinary division together with the exact supplied denominator preparation and output equality. -/
def quotient {channel : Coherent.CoherentNamed} (numerator : Coherent.CoherentNamed) (prepared :
  Prepared channel) :
    Quotient numerator channel := ⟨prepared,
      (Purelib.Approximation.Gaussian.Division.Prepared.quotient prepared) numerator, rfl⟩

/-- Cached quotient outputs are operationally equivalent when both original numerators and denominators are equivalent.
-/
def respects {first second firstNumerator secondNumerator : Coherent.CoherentNamed}
    (left : Quotient firstNumerator first) (right :
      Quotient secondNumerator second)
    (denominators : Gaussian.Equivalence.NamedEquivalent first.name second.name)
    (numerators : Gaussian.Equivalence.NamedEquivalent firstNumerator.name secondNumerator.name) :
    Gaussian.Equivalence.NamedEquivalent left.output.name right.output.name := by
  rw [left.output_eq, right.output_eq]
  exact Approximation.Gaussian.Division.Prepared.Quotient.quotients_respect left.prepared right.prepared denominators
    numerators

end Quotient

end Purelib.Approximation.Gaussian.Division.Prepared

end

section
@[expose] public section

/-!
# Finite certificate acquisition: public theorem interface

Three distinct contracts are exposed here, without a universal partiality
framework:

* `boundedDivision` makes one prescribed request and returns an ordinary
  cached quotient or whole-ball smallness with persistent candidate bounds.
* `gapDivision` turns smallness into exact branch exclusion under a proved
  zero-or-gap law. `signedGap` computes a sufficient canonical inspection
  budget from an unsigned imaginary gap.
* `exact` decides between an equivalent prepared presentation and operational
  zero for the two supported finite provenance classes. Its semantic iff
  and presentation-invariance laws do not apply to opaque inputs lacking
  this provenance, nor to the overlapping numerical small/apart verdicts.

`separatedWord` prepares an entire word in either half-plane and exposes
single/fold agreement, braid invariance, reversal, and the dual period law
through its retained report. Negative imaginary evidence is not global
non-certifiability. Precision and inspection counts below are not CPU-time,
allocation, certificate-size, or general-polynomial separation bounds.
-/

section Purelib.CCL.Acquisition

end Purelib.CCL.Acquisition

end

end

section
@[expose] public section

/-!
# Semantic completeness and invariance of exact division decisions

Exact zero means an executable operational comparison with zero exists;
preparability means an equivalent whole-ball-apart presentation exists.
Neither predicate demands pointwise equality of approximate candidates.
The converse completeness laws require a computed exact decision, supplied
below by rational provenance and by the separate algebraic client. They are
not equality decisions for arbitrary opaque channels.
-/

section Purelib.CCL.Progressive.ExactProvenance

end Purelib.CCL.Progressive.ExactProvenance

end

section
@[expose] public section

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace Purelib.Approximation.Gaussian.Division.Prepared

/-- Independently prepared equivalent presentations give the same quotient. -/
def quotient_respects {channel : Coherent.CoherentNamed} (first second : Prepared channel)
    (numerator : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent ((quotient first)
      numerator).name ((quotient second) numerator).name :=
  Equivalence.coherentDiv_respects numerator numerator
    first.denominator second.denominator first.apart second.apart
    (NamedEquivalent.refl _)
    (NamedEquivalent.trans
      (NamedEquivalent.symm first.equivalent) second.equivalent)

/-- Compatibility includes the existing automatic and manual `Ready` API. -/
def quotient_respects_ready {channel numerator : Coherent.CoherentNamed}
    (prepared : Prepared channel) {state : Name.Coherent.Refinement.State channel} {output : Coherent.CoherentNamed}
    (ready : Partial.Ready numerator channel state output) :
    Gaussian.Equivalence.NamedEquivalent ((quotient prepared)
      numerator).name output.name := by
  rw [ready.output_eq]
  exact (quotient_respects prepared) (Prepared.ofEvidence state
    ready.evidence) numerator
end Purelib.Approximation.Gaussian.Division.Prepared

end

end

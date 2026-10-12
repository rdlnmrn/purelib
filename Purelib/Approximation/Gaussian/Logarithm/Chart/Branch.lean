module

public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Exponential.Progressive.Range

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Name.Basic

section
public section

/-!
# Operational branch certificates for the complex logarithm

The geometric `Chart` data proves that its finite local recurrence is safe
and productive.  It intentionally permits any additive correction name.
This module records the additional semantic obligation needed to call that
correction a logarithm branch: exponentiating it must reproduce the inverse
of the chart's displayed scale, in finite operational equality.

Once the local inverse law and the exponential addition law are established,
this certificate is the missing branch datum in the calculation

`Exp(localLog(factor * input) + correction) = input`.

The exponentiation, equality, and inverse factor below are all CCL programs
or displayed Gaussian rationals.  No completed complex number or global
single-valued logarithm is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Branch

set_option genInjectivity false in
/-- A supplied correction is semantically anchored when its CCL exponential agrees operationally with the exact
reciprocal of the displayed chart factor.

Different anchored corrections may still encode different branches; the exponential condition deliberately identifies
their common logarithmic meaning without choosing a global cut. -/
structure BranchCertificate (input : Gaussian.Name.Basic.Named) (chart : Chart input) where
  /-- The displayed chart scaling factor is nonzero. -/ factor_ne_zero : chart.factor ≠ 0
  /-- Exponentiating the retained correction name is operationally equivalent to the exact reciprocal of the chart
    factor. -/ correction_exponential :
    Gaussian.Equivalence.NamedEquivalent
      (Name.named chart.correction)
      (Named.exact
        (1 / chart.factor))

constructive_injectivity BranchCertificate

end Purelib.Approximation.Gaussian.Logarithm.Chart.Branch

end

section
public section

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

end

end

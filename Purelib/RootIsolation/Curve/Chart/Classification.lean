module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.Curve.Clearance.Global
import Purelib.RootIsolation.Curve.Clearance.Residual
import Purelib.RootIsolation.Curve.Event.Analysis

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Chart (BoundedAnalysis)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Finite elimination of globally clear CCL boundary charts

The curve dispatcher returns a finite list of bounded rational charts.  A
constant-gcd chart now carries an original-polynomial residual lower bound.
This module folds the winding-one refinement from that bound over every clear
chart while preserving the current raw prefix.

If every chart in the returned boundary analysis is globally clear, finite
chart coverage then proves that the Hermitian boundary has no displayed point
in the final box.  Nonconstant curve-event charts are deliberately retained
for the subsequent owner calculation.  A radius-zero norm boundary is
classified upstream as a finite singleton; on every remaining line or circle
chart, a finite non-pole/root-count argument eliminates the identically-zero
outcome.
-/

namespace Purelib.RootIsolation.Curve.Chart

namespace Classification

/-- Executable tag for the constant-gcd branch of one bounded chart. -/
@[expose] def isClear
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form} : BoundedAnalysis p box chart → Bool
  | .clear _certificate _residual => true
  | .identicallyZero _realZero _imaginaryZero => false
  | .events _data _degreePositive _factors _factorsEq => false

/-- Every member of the finite chart list is a constant-gcd clear analysis. -/
@[expose] def AllClear
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p box chart)) : Prop :=
  ∀ entry, entry ∈ analyses → Curve.Chart.Classification.isClear entry.2 = true

end Classification

set_option genInjectivity false in
/-- Executable finite classification of a chart list: either every entry is
constant-gcd clear, or the first identically-zero/event entry is retained. -/
inductive Classification
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p box chart)) where
  /-- Every original chart entry has a retained constant-gcd clear analysis. -/ | all (proof :
    Classification.AllClear analyses)
  /-- The first retained non-clear chart entry, with its original list membership and false clear tag. -/ | unresolved
      (entry : Sigma fun chart : BoundedChart form =>
        BoundedAnalysis p box chart)
      (member : entry ∈ analyses)
      (notClear : Classification.isClear entry.2 = false)

constructive_injectivity Classification

namespace Classification

/-- Scan the original bounded chart list for its first non-clear entry.

Return that actual entry with membership and its false clear tag, or certify that every retained entry has a
constant-gcd clearance analysis. -/
@[expose] def classify
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm} :
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p box chart)) → Classification analyses
  | [] => .all (by intro entry member; nomatch member)
  | ⟨chart, .identicallyZero realZero imaginaryZero⟩ :: _remaining =>
      .unresolved
        ⟨chart, .identicallyZero realZero imaginaryZero⟩
        List.mem_cons_self rfl
  | ⟨chart, .events data degreePositive factors factorsEq⟩ :: _remaining =>
      .unresolved ⟨chart, .events data degreePositive factors factorsEq⟩
        List.mem_cons_self rfl
  | ⟨chart, .clear certificate residual⟩ :: remaining => by
      match classify remaining with
      | .unresolved entry member notClear =>
          exact .unresolved entry
            (List.mem_cons_of_mem
              ⟨chart, .clear certificate residual⟩ member) notClear
      | .all proof =>
          exact .all (by
            intro entry member
            rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
            · subst entry
              rfl
            · exact proof entry tailMember)

end Classification

end Purelib.RootIsolation.Curve.Chart

end

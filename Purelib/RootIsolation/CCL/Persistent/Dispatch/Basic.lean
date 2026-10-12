module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.CCL.Persistent.Controller.Basic
public import Purelib.RootIsolation.CCL.Persistent.Next.Strict
import Purelib.RootIsolation.CCL.Persistent.State.Basic
public import Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare
public import Purelib.RootIsolation.Curve.Boundary.Analysis

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

public section

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Dispatch.Basic

set_option genInjectivity false in
/-- Positive denominator separation restricted to the fully prepared state.
This is the quantitative input needed to bound affine line parameters in the
subsequent boundary-owner calculation. -/
structure DenominatorCertificate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {current : State p ambient} (prepared :
      CCL.Persistent.Terminal.Prepare.SourcePersistentDispatchPreparedAlias current) where
  /-- The retained rational lower bound for the prepared parser denominator's squared norm. -/ margin :
    Fraction.Rational
  /-- The retained denominator margin is strictly positive. -/ margin_pos : 0 < margin
  /-- The original parser denominator meets this margin throughout the prepared numerical box. -/ lower : ∀ {value :
    Gaussian.Basic.Canonical},
    prepared.state.numerical.box.Contains value →
      margin ≤ Data.Gaussian.Norm.Basic.normSq
        (Geometry.Projective.Homography.Basic.denominator
          (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate
            (Data.CCL.Encoding.Parser.State.parse prepared.state.word).matrix)
          value)

constructive_injectivity DenominatorCertificate

set_option genInjectivity false in
/-- Total result of terminal preparation followed by structural strict-sign
and exact equality-owner inspection. -/
inductive Outcome
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The original persistent step has a retained terminal or next-bit decision. -/ | decided (result :
    CCL.Persistent.Controller.Basic.SourcePersistentDispatchStepResultAlias current)
  /-- A prepared same-word state retains its denominator certificate, unresolved next-bit atom and actual parameterized
    boundary analysis. -/ | boundary (prepared : CCL.Persistent.Terminal.Prepare.SourcePersistentDispatchPreparedAlias
    current)
      (denominator : DenominatorCertificate prepared)
      (next : CCL.Persistent.Next.Strict.SourcePersistentDispatchBoundaryNextAlias prepared.state)
      (boundary : Curve.Boundary.Analysis.CurveBoundary p
        (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate
          (Data.CCL.Encoding.Parser.State.parse prepared.state.word).matrix)
        prepared.state.numerical.box denominator.margin
        denominator.margin_pos next.atom)

constructive_injectivity Outcome

end Purelib.RootIsolation.CCL.Persistent.Dispatch.Basic

end

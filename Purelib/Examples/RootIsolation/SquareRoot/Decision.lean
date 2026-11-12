module
import Purelib.Approximation.Gaussian.Name.Apart.Exact
import Purelib.Approximation.Gaussian.Provenance.Rational.Decision.Laws
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation
public import Purelib.Examples.RootIsolation.SquareRoot.Provenance

import Purelib.Riemann.RootContinuation.SquareRootDecisionLaws
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootSidecar

public section

namespace Purelib.Examples.RootIsolation.SquareRoot.Decision

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Provenance

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic

open Purelib.Examples.Approximation.Gaussian.Provenance.Rational

open Purelib.Riemann.RootContinuation.SquareRootDecisionLaws

open Purelib.Examples.RootIsolation.SquareRoot

/-- The cancelling name is zero exactly when no prepared division witness exists. -/
theorem cancellation_complete :
    Zero.IsZero Cancellation.cancellation ↔
      ¬ Equivalence.IsPrepared Cancellation.cancellation :=
  Sidecar.zero_iff_unpreparable
    Provenance.cancellationSidecar

/-- The square-root and rational sidecars agree on the cancellation verdict. -/
theorem cancellation_cross_provenance :
    Provenance.cancellationSidecar.decide.isPrepared =
      Cancellation.cancellationSidecar.decide.isPrepared :=
  Sidecar.decide_respects_rational
    Provenance.cancellationSidecar
    Cancellation.cancellationSidecar
    (NamedEquivalent.refl _)

/-- The coherent name formed by adding exact zero to exact one. -/
@[expose] def alternateOne : CoherentNamed := CoherentNamed.add
  (Coherence.exact 1) (Coherence.exact 0)

/-- The rational sidecar retaining the original addition of one and zero. -/
@[expose] def alternateSidecar : RationalSidecar alternateOne :=
  (RationalSidecar.exact 1).add (RationalSidecar.exact 0)

/-- The original additive name is equivalent to the exact name of one. -/
@[expose] def alternate_equivalent : NamedEquivalent alternateOne.name
    (Coherence.exact 1).name :=
  Add.coherentAdd_zero_right _

/-- Equivalent rational sidecars return the same preparedness verdict. -/
theorem alternate_verdict :
    alternateSidecar.decide.isPrepared = (RationalSidecar.exact 1).decide.isPrepared :=
  alternateSidecar.decide_respects (RationalSidecar.exact 1) alternate_equivalent

/-- The exact division preparation for the nonzero Gaussian value one. -/
@[expose] def exactOnePrepared : Prepared (Coherence.exact 1) :=
  ⟨Coherence.exact 1, exactApart 1 (by decide),
    NamedEquivalent.refl _⟩

/-- Transport the exact preparation to the original additive name of one. -/
@[expose] def alternatePrepared : Prepared alternateOne := exactOnePrepared.transport
  (NamedEquivalent.symm alternate_equivalent)

/-- Transporting the denominator preparation preserves the quotient of every numerator. -/
@[expose] def alternate_quotient (numerator : CoherentNamed) : NamedEquivalent
    (alternatePrepared.quotient numerator).name (exactOnePrepared.quotient numerator).name
      :=
  alternatePrepared.quotient_respects_equivalent exactOnePrepared
    alternate_equivalent
    (NamedEquivalent.refl _)

/-- Each isolated square-root sheet is preparable exactly when it is nonzero. -/
theorem root_two_complete (sheet : Fin 2) :
    Equivalence.IsPrepared (Provenance.rootTwo sheet).1 ↔
      ¬ Zero.IsZero (Provenance.rootTwo sheet).1 :=
  Sidecar.prepared_iff_nonzero
    (Provenance.rootTwo sheet).2

end Purelib.Examples.RootIsolation.SquareRoot.Decision

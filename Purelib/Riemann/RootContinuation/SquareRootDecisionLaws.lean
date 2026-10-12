module
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

public import Purelib.Riemann.RootContinuation.SquareRootSidecar

@[expose] public section

/-! # Exact square-root decision completeness, independent of presentation -/

namespace Purelib.Riemann.RootContinuation.SquareRootDecisionLaws

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence.Zero (IsZero)
open Purelib.Approximation.Gaussian.Division.Prepared.Equivalence (IsPrepared)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Riemann.RootContinuation.SquareRootSidecar (Sidecar)

section
open Purelib.Approximation.Gaussian.Division.Prepared
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
/-- For a channel with retained square-root provenance, operational zero is equivalent to impossibility of preparation.
-/
theorem Sidecar.zero_iff_unpreparable {channel : Coherent.CoherentNamed} (sidecar : Sidecar channel) :
    Zero.IsZero channel ↔ ¬ Equivalence.IsPrepared channel := sidecar.decide.zero_iff_unpreparable

/-- For a channel with retained square-root provenance, preparability is equivalent to operational nonzero. -/
theorem Sidecar.prepared_iff_nonzero {channel : Coherent.CoherentNamed} (sidecar : Sidecar channel) :
    Equivalence.IsPrepared channel ↔ ¬ Zero.IsZero channel := sidecar.decide.prepared_iff_nonzero

end

open Purelib.Approximation in
open Purelib.Approximation.Gaussian.Name in
/-- Equivalent numerical channels with square-root sidecars have the same exact preparation verdict. -/
theorem Sidecar.decide_respects {first second : Coherent.CoherentNamed}
    (left : Sidecar first) (right : Sidecar second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    left.decide.isPrepared = right.decide.isPrepared := left.decide.respects right.decide equivalent

open Purelib.Approximation in
open Purelib.Approximation.Gaussian.Name in
open Purelib.Approximation.Gaussian.Provenance.Rational in
/-- Square-root and rational provenance give the same preparation verdict on equivalent channels.

The operational equivalence links the actual numerical names, so the exact decision is independent of which supported
provenance mechanism is retained. -/
theorem Sidecar.decide_respects_rational {first second : Coherent.CoherentNamed}
    (left : Sidecar first) (right : Basic.RationalSidecar second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    left.decide.isPrepared = right.decide.isPrepared := left.decide.respects right.decide equivalent

end Purelib.Riemann.RootContinuation.SquareRootDecisionLaws

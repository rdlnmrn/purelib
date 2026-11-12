module

public import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction

/-! # Residual requests on the same original owner tails

The executable square-versus-radicand comparison selects an all-later floor
before a root reading is taken. Both the original acquired tail and the
complete comparison are retained; no new square-root process is introduced.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootProvenance

namespace OwnerTail

variable {parameter : Canonical} {owner : Owner parameter}

/-- Select the original square comparison at the genuine trace residual request, before any new reading. -/
def traceComparison (tail : OwnerTail owner) (lower : Rational) (positive : 0 < lower) :
    Equivalence.Comparison (CertifiedSquareRoot.squareApproximation owner.track)
      (Sequence.Constant.constantApproximation parameter) tail.first 0 (traceAllowance lower) :=
  (CertifiedSquareRoot.squareApproximation_equivalent_parameter owner.track).compare
    tail.first 0 (traceAllowance lower) (traceAllowance_positive positive)

/-- A retained original tail and its complete executable trace-residual comparison, with both whole factories. -/
@[expose] def TraceRequest (owner : Owner parameter) (lower : Rational) (positive : 0 < lower) :=
  (tail : { value : OwnerTail owner // value = OwnerTail.acquire owner }) ×
    { compared : Equivalence.Comparison (CertifiedSquareRoot.squareApproximation owner.track)
        (Sequence.Constant.constantApproximation parameter) tail.val.first 0 (traceAllowance lower) //
      compared = tail.val.traceComparison lower positive }

/-- Acquire one original tail, then select its stricter residual floor once without sampling it. -/
def requestTrace (owner : Owner parameter) (lower : Rational) (positive : 0 < lower) :
    TraceRequest owner lower positive :=
  let tail := OwnerTail.acquire owner
  let compared := tail.traceComparison lower positive
  ⟨⟨tail, rfl⟩, ⟨compared, rfl⟩⟩

namespace TraceRequest

variable {lower : Rational} {positive : 0 < lower} (request : TraceRequest owner lower positive)

/-- Read the SAME acquired original owner tail. -/
@[expose] def tail : OwnerTail owner := request.1.val

/-- The retained whole tail has its original acquisition factory. -/
theorem tail_eq : request.tail = OwnerTail.acquire owner := request.1.property

/-- Read the SAME complete original square-versus-radicand comparison. -/
@[expose] def compared : Equivalence.Comparison (CertifiedSquareRoot.squareApproximation owner.track)
    (Sequence.Constant.constantApproximation parameter) request.tail.first 0 (traceAllowance lower) := request.2.val

/-- The retained complete comparison is the original executable selector on that SAME tail. -/
theorem compared_eq : request.compared = request.tail.traceComparison lower positive := request.2.property

/-- Every supplied later reading satisfies the stronger residual request on the same original radicand. -/
theorem residual (reading : OwnerTail.Reading request.tail)
    (later : request.compared.leftIndex ≤ reading.index) :
    Norm.Basic.normSq (reading.value * reading.value - parameter) < traceAllowance lower := by
  have paid := request.compared.close later (Nat.le_refl request.compared.rightIndex)
  rewrite [CertifiedSquareRoot.squareApproximation_sample] at paid
  change Norm.Basic.normSq ((ownerApproximation owner).sample reading.index *
    (ownerApproximation owner).sample reading.index - parameter) < traceAllowance lower at paid
  exact Eq.mp (congrArg (fun value : Canonical =>
    Norm.Basic.normSq (value * value - parameter) < traceAllowance lower) reading.value_eq.symm) paid

end TraceRequest

end OwnerTail

end Purelib.Riemann.Paths.OwnerTraceReadings

end

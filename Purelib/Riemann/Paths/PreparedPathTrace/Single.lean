module

public import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Polynomial.Geometry.ClearPath

/-! # Original complete head and budget of a retained single-segment trace

These readers inspect the existing prepared path and its same lineage.
They do not execute TracedSegment.build, prepare another subdivision or
claim equality of a reconstructed OwnerPath with an arbitrary trace thunk.
-/

public section

namespace Purelib.Riemann.Paths

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath CompleteSegment zeroEndpoint oneEndpoint)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {owner : Owner (polynomial.eval start)}

namespace PreparedClearPathModels.PreparedPath

/-- Read the complete original segment cache and its actual ambient proof from a literal one-segment preparation. -/
@[expose] def singleSegment (prepared : PreparedPath (.cons segment (.nil finish)) owner) :
    PSigma (fun within : segment.WithinAmbient => CompleteSegment segment within owner) :=
  match prepared with
  | .cons _ _ _ within first _ => ⟨within, first⟩

/-- Reading a literal one-segment preparation returns the SAME whole retained head cache. -/
theorem singleSegment_cons (within : segment.WithinAmbient) (first : CompleteSegment segment within owner)
    (tail : PreparedPath (.nil finish) first.finishOwner) :
    singleSegment (.cons segment (.nil finish) owner within first tail) = ⟨within, first⟩ := rfl

end PreparedClearPathModels.PreparedPath

open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)

namespace PreparedPathTrace.PreparedPath.TraceLineage

/-- Read the SAME original head budget and fit proof from the existing lineage, with its complete original indices. -/
@[expose] def singleBudget {prepared : PreparedPath (.cons segment (.nil finish)) owner}
    (lineage : TraceLineage prepared) :
    {budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint //
      budget.RequestsFit zeroEndpoint prepared.singleSegment.2.subdivision.requests} := by
  cases lineage with
  | cons budget fits _ _ => exact ⟨budget, fits⟩

/-- Reading the actual head lineage returns the original budget and fit certificate as a complete pair. -/
theorem singleBudget_cons {within : segment.WithinAmbient} {first : CompleteSegment segment within owner}
    {finishOwner : Owner (polynomial.eval finish)} {rest : PreparedPath (.nil finish) finishOwner}
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint first.subdivision.requests)
    (finishEq : finishOwner = first.finishOwner) (remaining : TraceLineage rest) :
    singleBudget (.cons budget fits finishEq remaining) = ⟨budget, fits⟩ := rfl

end PreparedPathTrace.PreparedPath.TraceLineage
end Purelib.Riemann.Paths

end

module
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Program.Gaussian.Cached.Schedule
public import Purelib.Integration.Program.Gaussian.Polynomial.Schedule

import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.CertifiedProgram
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract

section
@[expose] public section

/-!+# Generated numerical clients of finite integration observation

The polynomial API takes one finite coefficient/path source, two finite
partition policies, positive-stride syntax, and an observation request.
The exponential API fixes the interval `[0,1]` and the local finite Taylor
family; its inputs select partitions, degree schedules and later local
readings.  Neither constructor takes coherence, analytic antiderivative,
partition agreement, comparison, productivity or successful replay evidence.

`Comparison.outputs` gives operational equivalence, not equal raw prefixes.
Its observation projections give exact replay, enclosure, finite length,
extension and cursor semantics for each individual presentation.  The shared
`IntegrationObservation.payload_erasure_contract` applies to these same
generated programs, with no added assumption on an uninterpreted payload.
The existing exponential-minus-one identification remains independently
available through `ExponentialIntegrationEquivalence.output_equivalent_existing`.
-/

namespace Purelib.Integration.Program.Gaussian.Polynomial.CCL.Observation

open Purelib.CCL.Progressive in
open Purelib.Data.Nat in
open Purelib.Integration in
open Purelib.Integration.Polynomial.Gaussian.Partition in
open Purelib.Integration.Program in
/-- Construct the retained CCL observation comparison for two scheduled compilations of the original polynomial path.

The two original policies, schedules, request and output count remain explicit; source-sample equivalence supplies the
comparison of their retained programs. -/
def polynomial_contract (source :
  Source.PolynomialPath)
    (left right : IntegrationPrograms.PartitionPolicy source)
    (leftSchedule rightSchedule : Data.Nat.Schedule.PositiveStride)
    (request : CertifiedProgram.Request) (count : Nat) :
    Gaussian.CCL.Replay.Observation.Contract.Comparison
      (Gaussian.Cached.Schedule.reindexCached (IntegrationPrograms.polynomialProgram source left) leftSchedule)
      (Gaussian.Cached.Schedule.reindexCached (IntegrationPrograms.polynomialProgram source right) rightSchedule)
        request count :=
  Gaussian.CCL.Replay.Observation.Contract.comparison _ _ request count
    (Gaussian.Polynomial.Schedule.polynomial_scheduled_outputs_equivalent source left right leftSchedule rightSchedule)
end Purelib.Integration.Program.Gaussian.Polynomial.CCL.Observation

end

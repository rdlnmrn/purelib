module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.List.Map
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Computation.Query.Basic

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
import Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.PathObservation
public import Purelib.Integration.Algebraic.SquareFactor.SourceTransport
public import Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

public section

/-!
# Original-differential realization of recorded integration cells

An original-coordinate observation carries its generated domain evidence.
Selecting a logged query and a cell of its inherited layer produces the
operational coordinate equation, original-quotient equivalence and uniform
local model bound.  Membership in the actual logged model is derived from
the receipt contract, not supplied as an integrand-realization hypothesis.
The model-query replay boundary remains unchanged; this is not an internal
root-query transcript.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.ObservationTransport

open Purelib.Riemann.Integration

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor

open Purelib.Integration.Algebraic.SquareFactor.PathObservation (Policy ObservationRequest CachedModel)

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request} {segment :
  Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {sheet : Fin 2} {policy : Purelib.Integration.Algebraic.SquareFactor.PathObservation.Policy} {query :
    Purelib.Integration.Algebraic.SquareFactor.PathObservation.ObservationRequest} {count : Nat}

open Purelib.Computation.Query in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Read the exact recorded exchange at its original bounded transcript index. -/
@[expose] def traceExchange
    (observed : PolynomialObservation.Observation polynomial differential segment sheet .originalCoordinate policy query
      count)
    (index : Fin observed.recorded.trace.length) : Basic.Exchange Nat CachedModel :=
  observed.recorded.trace.get index

open Purelib.Integration.Algebraic.SquareFactor in
/-- Read the original integration layer at the exact policy-scheduled index of the retained transcript exchange. -/
@[expose] def traceLayer
    (observed : PolynomialObservation.Observation polynomial differential segment sheet .originalCoordinate policy query
      count)
    (index : Fin observed.recorded.trace.length) :
    IntegrationLayers.Layer observed.entry.source.safe
      (policy.schedule.index (ObservationTransport.traceExchange observed index).query) :=
  IntegrationProgram.layerAt observed.entry.source.safe sheet
    (policy.schedule.index (ObservationTransport.traceExchange observed index).query)

open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- An original compiled cell retained with membership in both its exact source layer and recorded reply model.

The original observation and transcript index remain part of the type, preserving the path, sheet and query owners. -/
structure TransportedCell
    (observed : PolynomialObservation.Observation polynomial differential segment sheet .originalCoordinate policy query
      count)
    (traceIndex : Fin observed.recorded.trace.length) where
  /-- The exact retained original compiled source-layer cell. -/ cell : OwnedCells.Cell observed.entry.source.safe
  /-- The retained cell occurs in the exact original source layer of this transcript exchange. -/ source_member : cell ∈
    (ObservationTransport.traceLayer observed traceIndex).cells
  /-- The retained cell model occurs in the exact recorded reply model. -/ model_member : cell.model.cell ∈
    (ObservationTransport.traceExchange observed traceIndex).reply.model.cells

constructive_injectivity TransportedCell

open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Retain the exact bounded source-layer cell and certify its occurrence in the original recorded model. -/
@[expose] def transportCell
    (observed : PolynomialObservation.Observation polynomial differential segment sheet .originalCoordinate policy query
      count)
    (traceIndex : Fin observed.recorded.trace.length)
    (cellIndex : Fin (ObservationTransport.traceLayer observed traceIndex).cells.length) :
      ObservationTransport.TransportedCell observed traceIndex :=
  let cell := (ObservationTransport.traceLayer observed traceIndex).cells.get cellIndex
  { cell := cell
    source_member := List.get_mem _ _
    model_member := by
      rw [observed.contract.trace_cells (ObservationTransport.traceExchange observed traceIndex) (List.get_mem _ _)]
      exact Map.mem_map_of_mem (List.get_mem (ObservationTransport.traceLayer observed traceIndex).cells cellIndex) }

namespace TransportedCell

variable {observed : Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation.Observation polynomial
  differential segment sheet .originalCoordinate policy query count}
  {traceIndex : Fin observed.recorded.trace.length}

section
open Purelib.Approximation.Gaussian
open Purelib.Integration.Algebraic.SquareFactor
/-- The retained transported cell's coordinate name squares to the exact original polynomial value. -/
@[expose] def coordinate_square (transported : ObservationTransport.TransportedCell observed traceIndex)
    (fraction : PathInput.Coordinate) (inside : PathInput.unitInterval.Contains fraction) :
    Equivalence.NamedEquivalent
      (Name.Coherent.CoherentNamed.mul (SourceTransport.coordinateName transported.cell.edge fraction inside)
        (SourceTransport.coordinateName transported.cell.edge fraction inside)).name
      (Name.Coherent.CoherentNamed.Coherence.exact
        (polynomial.eval (segment.point (transported.cell.edge.span.parameter fraction)))).name :=
  SourceTransport.coordinate_square transported.cell.edge fraction inside

/-- The retained transported cell's source is equivalent to its original-coordinate differential name at the same
fraction. -/
@[expose] def source_original (transported : ObservationTransport.TransportedCell observed traceIndex)
    (fraction : PathInput.Coordinate) (inside : PathInput.unitInterval.Contains fraction) :
    Equivalence.NamedEquivalent (transported.cell.edge.source fraction inside).name
      (SourceTransport.originalName transported.cell.edge observed.entry.domainEvidence fraction inside).name :=
  SourceTransport.source_original transported.cell.edge observed.entry.domainEvidence fraction inside

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
/-- Every possible reading of the exact retained transported-cell source meets its original polynomial model allowance.
-/
theorem uniform_bound (transported : ObservationTransport.TransportedCell observed traceIndex)
    (fraction : PathInput.Coordinate) (inside : PathInput.unitInterval.Contains fraction)
    (state : (transported.cell.edge.source fraction inside).name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (transported.cell.edge.source fraction inside).name.process.Possible state candidate) :
    Data.Gaussian.Norm.Basic.normSq
      (candidate - Gaussian.Evaluation.eval transported.cell.model.cell.polynomial ⟨fraction, 0⟩) ≤
        transported.cell.model.cell.localAllowance :=
  transported.cell.source_candidate_error_le fraction inside state possible

end TransportedCell

end Purelib.Integration.Algebraic.SquareFactor.ObservationTransport

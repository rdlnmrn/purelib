module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Refinement
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Accuracy
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Circuit
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original whole-quarter bank endpoints at their exact common request

The supplied Bank and interval Chain retain every original query, root
sample, Endpoint and selected arithmetic observation. Exact original span
and width laws identify the first and last chart times and the arithmetic
request. Equality transports move the complete old Entries to those indices;
their independent original root requests remain unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Layer Piece)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Integration
open Purelib.Riemann.RootContinuation

/-- The exact whole-quarter arithmetic request at one common original dyadic depth. -/
@[expose] def request (depth : Nat) : AccuracyRequest :=
  ⟨Geometric.Basic.quarterRadius 1 depth ^ 2,
    Fraction.Order.Arithmetic.pow_pos_direct
      (Geometric.Basic.quarterRadius_pos (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) depth) 2⟩

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}
variable {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
variable {samples : Differential.Refinement.Layer.RefinedSamples layer initialPositive}
variable {upper : Transport.Reading actual initial.span.upper
  (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)}

/-- The exact original unit-span readback gives whole-quarter chart width one. -/
theorem width_eq (whole : initial.span = Differential.Circuit.span) : initial.span.width = 1 := by
  rewrite [whole]
  change (1 : Fraction.Rational) - 0 = 1
  decide +kernel

/-- The supplied bank's original arithmetic request equals the common whole-quarter request at the same depth. -/
theorem request_eq (whole : initial.span = Differential.Circuit.span) :
    Bank.request layer initialPositive = request depth := by
  apply AccuracyRequest.eq_of_tolerance_eq
  calc
    _ = (layer.node ⟨0, layer.nonempty⟩).span.width ^ 4 :=
      Bank.request_tolerance layer initialPositive ⟨0, layer.nonempty⟩
    _ = ((layer.node ⟨0, layer.nonempty⟩).span.width ^ 2) ^ 2 := by ring1
    _ = Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 :=
      congrArg (fun value : Fraction.Rational => value ^ 2)
        (layer.widths (layer.node ⟨0, layer.nonempty⟩) (List.getElem_mem layer.nonempty))
    _ = _ := by
      rewrite [width_eq whole, show (1 : Fraction.Rational) ^ 2 = 1 by decide +kernel]
      rfl

variable (bank : Bank primitive samples upper)
variable (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
  (Differential.Refinement.Piece.chartIntervals layer.pieces))
variable (whole : initial.span = Differential.Circuit.span)

/-- The first actual original bank node has chart time zero by its retained interval Chain and original span. -/
theorem first_time
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Differential.Refinement.Piece.chartIntervals layer.pieces))
    (whole : initial.span = Differential.Circuit.span) :
    (layer.node ⟨0, layer.nonempty⟩).span.lower = 0 :=
  (layer.start_eq chain layer.nonempty).trans (congrArg (fun span => span.lower) whole)

/-- The supplied original terminal Reading has chart time one by the original full-span equality. -/
theorem last_time (whole : initial.span = Differential.Circuit.span) :
    initial.span.upper = 1 := congrArg (fun span => span.upper) whole

/-- Read the same complete first query at its exactly proved chart-time-zero index. -/
@[expose] def firstReading : Transport.Reading actual 0 ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩ :=
  (layer.node ⟨0, layer.nonempty⟩).source.castTime (first_time chain whole)

/-- Read the same original first-node cofactor sample after exact time-index transport. -/
@[expose] def firstSample :=
  (layer.node ⟨0, layer.nonempty⟩).source.castTimeSample
    (lastInside := ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩)
    (first_time chain whole) (samples.get ⟨0, layer.nonempty⟩).val.sample

/-- The first endpoint type retains the old query and root sample with the exactly equal common arithmetic request. -/
abbrev First (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Differential.Refinement.Piece.chartIntervals layer.pieces))
    (whole : initial.span = Differential.Circuit.span) :=
  Entry primitive (firstReading chain whole) initial.cell.regular
    (firstSample (samples := samples) chain whole) (request depth)

/-- Transport the whole old first-node Entry along its actual time and arithmetic-request equalities. -/
@[expose] def firstEntry : First (samples := samples) primitive chain whole :=
  ((bank.nodes.get ⟨0, layer.nonempty⟩).castTime
    (otherInside := ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩)
    (first_time chain whole)).castAccuracy (request_eq whole)

/-- Exact endpoint transports preserve the first original selected arithmetic value. -/
theorem firstEntry_value : (firstEntry bank chain whole).value = (bank.nodes.get ⟨0, layer.nonempty⟩).value :=
  (Entry.castAccuracy_value (request_eq whole) _).trans
    (Entry.castTime_value (otherInside := ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩)
      (first_time chain whole) (bank.nodes.get ⟨0, layer.nonempty⟩))

/-- Read the same complete terminal query at its exactly proved chart-time-one index. -/
@[expose] def lastReading : Transport.Reading actual 1 ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩ :=
  upper.castTime (last_time whole)

/-- Read the original terminal cofactor sample at the same exact chart-time-one index. -/
@[expose] def lastSample :=
  upper.castTimeSample (lastInside := ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩)
    (last_time whole) bank.terminal.sample

/-- The terminal endpoint type retains the unchanged old root request and the common equal arithmetic request. -/
abbrev Last :=
  Entry primitive (lastReading (upper := upper) whole) initial.cell.regular
    (lastSample bank whole) (request depth)

/-- Transport the whole old terminal Entry along the original upper-time and arithmetic-request equalities. -/
@[expose] def lastEntry : Last bank whole :=
  (bank.terminal.entry.castTime (otherInside := ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩)
    (last_time whole)).castAccuracy (request_eq whole)

/-- Exact endpoint transports preserve the original terminal selected arithmetic value. -/
theorem lastEntry_value : (lastEntry bank whole).value = bank.terminal.entry.value :=
  (Entry.castAccuracy_value (request_eq whole) _).trans
    (Entry.castTime_value (otherInside := ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩)
      (last_time whole) bank.terminal.entry)

/-- Two completed whole-cache transports retain the original first and terminal Entries and their exact factories. -/
abbrev Endpoints :=
  { first : First (samples := samples) primitive chain whole // first = firstEntry bank chain whole } ×
    { last : Last bank whole // last = lastEntry bank whole }

/-- Cache both exact whole-entry transports once without acquiring or observing another endpoint. -/
@[expose] def endpoints : Endpoints bank chain whole :=
  let first := firstEntry bank chain whole
  let last := lastEntry bank whole
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩⟩

namespace Endpoints

variable {bank chain whole}

/-- Read the whole transported first Entry with its original observation and completed factory identity. -/
@[expose] def first (retained : Endpoints bank chain whole) :
    First (samples := samples) primitive chain whole := retained.1.val

/-- Read the whole transported terminal Entry with its original observation and completed factory identity. -/
@[expose] def last (retained : Endpoints bank chain whole) : Last bank whole := retained.2.val

/-- The retained first whole-cache view is its exact original endpoint/time/request transport factory. -/
theorem first_eq (retained : Endpoints bank chain whole) :
    retained.first = firstEntry bank chain whole := retained.1.property

/-- The retained terminal whole-cache view is its exact original endpoint/time/request transport factory. -/
theorem last_eq (retained : Endpoints bank chain whole) :
    retained.last = lastEntry bank whole := retained.2.property

/-- The first whole-cache view keeps the actual original selected bank value. -/
theorem first_value (retained : Endpoints bank chain whole) :
    retained.first.value = (bank.nodes.get ⟨0, layer.nonempty⟩).value :=
  (congrArg (fun entry : First (samples := samples) primitive chain whole => entry.value) retained.first_eq).trans
    (firstEntry_value bank chain whole)

/-- The terminal whole-cache view keeps the actual original selected bank value. -/
theorem last_value (retained : Endpoints bank chain whole) :
    retained.last.value = bank.terminal.entry.value :=
  (congrArg (fun entry : Last bank whole => entry.value) retained.last_eq).trans (lastEntry_value bank whole)

/-- The two transported endpoint values are the same original bank's ordered boundary difference. -/
theorem boundary_eq (retained : Endpoints bank chain whole) :
    retained.last.value - retained.first.value =
      bank.terminal.entry.value - (bank.nodes.get ⟨0, layer.nonempty⟩).value := by
  rewrite [retained.first_value, retained.last_value]
  rfl

/-- The original bank's actual cell certificates bound these same whole-quarter endpoint values and scalar sample. -/
theorem boundary_error_le (retained : Endpoints bank chain whole) (cells : Cells specification bank chain) :
    Norm.Basic.normSq (retained.last.value - retained.first.value - layer.model.integralSample) ≤
      cellCeiling specification initial * Geometric.Basic.quarterRadius 1 depth := by
  rewrite [retained.boundary_eq]
  have paid := cells.boundary_error_le
  rewrite [width_eq whole, show (1 : Fraction.Rational) ^ 2 = 1 by decide +kernel] at paid
  exact paid.trans_eq (by ring1)

end Endpoints

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter

end

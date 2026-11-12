module

public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Transport

/-! # Exact parameter transport of the original six Legendre arithmetic readings

The scalar equality changes the polynomial/specification index only. The
whole original Reading, evaluator, observation, selected states, coefficient
channel, comparisons and displayed witness are retained by equality
elimination. No smaller request or new observation is assigned to old data.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Specification.Table

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Reindex the whole original Legendre Reading along EXACT equality of its parameter indices. -/
@[expose] def castReadingParameter
    {first last point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {observation : RootObservation} {accuracy : AccuracyRequest}
    (equal : first = last) (channel : Fin 6)
    (reading : Reading (forms first channel) point sheet apart state observation accuracy) :
    Reading (forms last channel) point sheet apart state observation accuracy := by
  cases equal
  exact reading

/-- Parameter reindexing retains the complete original Reading heterogeneously, including all evaluator caches. -/
theorem castReadingParameter_heq
    {first last point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {observation : RootObservation} {accuracy : AccuracyRequest}
    (equal : first = last) (channel : Fin 6)
    (reading : Reading (forms first channel) point sheet apart state observation accuracy) :
    HEq (castReadingParameter equal channel reading) reading := by
  cases equal
  rfl

/-- The displayed witness is the SAME actual original arithmetic reading after exact parameter transport. -/
theorem castReadingParameter_reading
    {first last point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {observation : RootObservation} {accuracy : AccuracyRequest}
    (equal : first = last) (channel : Fin 6)
    (reading : Reading (forms first channel) point sheet apart state observation accuracy) :
    (castReadingParameter equal channel reading).reading = reading.reading := by
  cases equal
  rfl

/-- The same complete original coefficient generator is retained under the exact specification-index transport. -/
theorem castReadingParameter_coefficient
    {first last point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {observation : RootObservation} {accuracy : AccuracyRequest}
    (equal : first = last) (channel : Fin 6)
    (reading : Reading (forms first channel) point sheet apart state observation accuracy) :
    (castReadingParameter equal channel reading).coefficient = reading.coefficient := by
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Specification.Table

end

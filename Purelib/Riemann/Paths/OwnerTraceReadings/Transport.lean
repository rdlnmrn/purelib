module

public import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Gaussian.Basic

/-! # Whole owner-tail and reading transport under an exact radicand equality

Only the displayed Gaussian parameter changes. The complete original Owner,
tail, process state, reading value, index, norm and residual caches are
retained. These operations perform no root construction or observation.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

namespace OwnerTail

variable {source target : Canonical} {owner : Owner source}

/-- Transport the SAME whole tail along a true parameter equality and the original whole-Owner transport. -/
@[expose] def castParameter (same : source = target) (tail : OwnerTail owner) :
    OwnerTail (castOwnerParameter same owner) := by
  cases same
  exact tail

/-- Exact parameter transport preserves the entire original tail as dependent data. -/
theorem castParameter_heq (same : source = target) (tail : OwnerTail owner) :
    HEq (tail.castParameter same) tail := by
  cases same
  rfl

/-- Exact parameter transport preserves the original tail's retained first reading index. -/
theorem castParameter_first (same : source = target) (tail : OwnerTail owner) :
    (tail.castParameter same).first = tail.first := by
  cases same
  rfl

namespace Reading

variable {tail : OwnerTail owner}

/-- Transport the SAME whole cached reading with its original tail and Owner parameter. -/
@[expose] def castParameter (same : source = target) (reading : Reading tail) :
    Reading (tail.castParameter same) := by
  cases same
  exact reading

/-- The complete retained reading is unchanged under its exact parameter reindexing. -/
theorem castParameter_heq (same : source = target) (reading : Reading tail) :
    HEq (reading.castParameter same) reading := by
  cases same
  rfl

/-- Parameter reindexing preserves the exact old root reading value. -/
theorem castParameter_value (same : source = target) (reading : Reading tail) :
    (reading.castParameter same).value = reading.value := by
  cases same
  rfl

/-- Parameter reindexing preserves the exact old root reading index. -/
theorem castParameter_index (same : source = target) (reading : Reading tail) :
    (reading.castParameter same).index = reading.index := by
  cases same
  rfl

/-- Read the SAME supplied transported reading in its original tail without reconstructing its cached data. -/
@[expose] def uncastParameter (same : source = target) (tail : OwnerTail owner)
    (reading : Reading (tail.castParameter same)) : Reading tail := by
  cases same
  exact reading

/-- Restoring the original reading index keeps the supplied reading's exact value. -/
theorem uncastParameter_value (same : source = target) (tail : OwnerTail owner)
    (reading : Reading (tail.castParameter same)) :
    (uncastParameter same tail reading).value = reading.value := by
  cases same
  rfl

/-- Restoring the original tail keeps the supplied reading's exact index. -/
theorem uncastParameter_index (same : source = target) (tail : OwnerTail owner)
    (reading : Reading (tail.castParameter same)) :
    (uncastParameter same tail reading).index = reading.index := by
  cases same
  rfl

end Reading

end OwnerTail

end Purelib.Riemann.Paths.OwnerTraceReadings

end

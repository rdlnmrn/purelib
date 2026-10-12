module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Retained finite exponential selection and observations

The original ordered geometry, positive-stride requests and polynomial depth
remain attached to their cached values and exact scalar readback certificates.
-/

public section
namespace Purelib.Integration.Partition.QuadraticWeight.Cache

open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- A retained unit partition with a cached quadratic amplification factor and exact specification equality.

The factor is computed from the same retained partition intervals. Its specification equality certifies the exact
interval-count and squared-width expression. -/
structure Geometry where
  /-- The exact original unit partition. -/ partition : Unit.Normalized
  /-- The cached rational amplification factor. -/ factor : Fraction.Rational
  /-- The cache equals interval count times squared-width sum for the retained partition. -/ factor_eq : factor =
    QuadraticWeight.amplification partition

constructive_injectivity Geometry

/-- Compute the original partition's amplification once and retain it with its defining equality.

The partition amplification is computed once from the supplied interval list and retained with its exact defining
equality. -/
@[expose] def Geometry.canonical (partition : Unit.Normalized) : QuadraticWeight.Cache.Geometry :=
  ⟨partition, QuadraticWeight.amplification partition, rfl⟩

/-- The certified cached partition amplification factor is nonnegative.

The factor specification transports the direct nonnegativity certificate of the same original partition amplification.
-/
theorem Geometry.factor_nonnegative (geometry : QuadraticWeight.Cache.Geometry) : 0 ≤ geometry.factor := by
  rw [geometry.factor_eq]
  exact QuadraticWeight.amplification_nonnegative geometry.partition

end Purelib.Integration.Partition.QuadraticWeight.Cache
end

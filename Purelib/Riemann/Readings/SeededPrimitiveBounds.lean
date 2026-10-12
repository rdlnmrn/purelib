module
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic

@[expose] public section

/-! Fixed derivative budgets on the actual retained seeded neighborhood. -/

namespace Purelib.Riemann.Readings.SeededPrimitiveBounds

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)

variable {polynomial : Polynomial} {count : Nat}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Certify polynomial clearance on the original seeded neighborhood using one quarter of its retained denominator
value.

The positive bound and pointwise lower estimate use the original observation site's radius and exact centered-box
equation. -/
def clearance (patch : SeededNeighborhood polynomial count) : RegionClearance polynomial patch.box where
  bound := patch.site.denominatorValue / 4
  positive := Fraction.Order.Field.div_pos_direct patch.site.denominatorValue_positive (by decide)
  lower := by
    intro point inside
    rw [patch.box_eq] at inside
    rw [Norm.Basic.normSq_eq_canonical]
    exact patch.site.denominator_lower patch.radius_positive.le patch.radius_le_site inside

/-- Cache uniform inverse-root refinement derivative bounds from the original seeded model and its retained polynomial
clearance. -/
def derivativeBounds (patch : SeededNeighborhood polynomial count) : DerivativeBounds (clearance patch) patch.model :=
  DerivativeBounds.build (clearance patch) patch.model

end Purelib.Riemann.Readings.SeededPrimitiveBounds

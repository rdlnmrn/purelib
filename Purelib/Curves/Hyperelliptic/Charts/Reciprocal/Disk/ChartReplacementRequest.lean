module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Riemann

/-!
# Cell budgets for replacing an existing joined parent

The replacement request is independent of the original source error budget.
It can therefore consume an existing parent or side request without rebuilding
its source, owners, or endpoint-request spine.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

-- Preserve the original ChartReplacementRequest.ChartReplacementRequest nominal path.
set_option genInjectivity false in
/-- An independently paid chart replacement for the original retained parent and endpoint owners.

The original edge count fixes the local comparison allowance without rebuilding source requests. -/
structure ChartReplacementRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular
  cover) (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained local tolerance for the original chart replacements. -/ localTarget :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The original local replacement tolerance is strictly positive. -/ localPositive : 0 < localTarget
  /-- The retained original edge-count-squared replacement error is strictly below the requested target. -/ paid :
    (cover.mesh.edges.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (2 * (localTarget + localTarget /
    4)) < target
  /-- The actual chart requests for the original retained owner bank and floor. -/ charts :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests localTarget floor prepared.owners

constructive_injectivity ChartReplacementRequest

namespace ChartReplacementRequest

/-- Prepare chart replacements for the original retained owner bank at a positive count-paid local tolerance. -/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover) (target
  : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    ChartReplacementRequest prepared target floor :=
  let localTarget := Rational.Budget.Aggregate.perTerm target cover.mesh.edges.length / 4
  have localPositive : 0 < localTarget := Fraction.Order.Field.div_pos_direct
    (Rational.Budget.Aggregate.perTerm_positive positive _) (by decide)
  ⟨localTarget, localPositive, Purelib.Approximation.Rational.Budget.Aggregate.count_square_mul_quarters_lt positive _,
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests.build localTarget localPositive floor
    prepared.owners⟩

end ChartReplacementRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

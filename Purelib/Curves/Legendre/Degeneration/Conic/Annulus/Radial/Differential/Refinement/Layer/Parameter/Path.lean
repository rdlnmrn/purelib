module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Neighbors
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path

/-!
# Nonlinear normalized paths on actual retained neighboring parameter samples

The original layerAt constructor supplies the two source-time endpoints and
the span-width payment. The retained anchor caches supply the complete source
Seed owners; their parameter Step target owners remain the original endpoint
comparison inputs. No root, source query or arithmetic observation is repeated.

The constructed PathData has two distinct fixed-box branches. Cross-window
branch agreement and full cubic/cofactor handoffs remain separate evidence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

open Purelib
open Purelib.Approximation
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Radial.Parameter

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {radicand : CoefficientPolynomial}

variable {site : Fin 2} {parameter increment : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Radial.Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}
variable {initial : Radial.Differential.Refinement.Piece data actual accuracy} {depth : Nat}
variable {regular : parameter ≠ criticalValue site}
variable {admitted : Radial.Parameter.IncrementBound site parameter increment} {nonzero : increment ≠ 0}

/-- The actual neighboring original node sources retain the exact constructed span seam. -/
theorem seam (first last : Fin (initial.layerAt depth).pieces.length) (next : last.val = first.val + 1) :
    ((initial.layerAt depth).node first).span.upper = ((initial.layerAt depth).node last).span.lower := by
  cases last with
  | mk index bound =>
      cases next
      exact initial.layerAt_seam depth first.val first.isLt bound

/-- The next original source time lies in the first original neighboring chart span. -/
theorem next_time_inside (first last : Fin (initial.layerAt depth).pieces.length) (next : last.val = first.val + 1) :
    ((initial.layerAt depth).node first).span.Contains ((initial.layerAt depth).node last).span.lower := by
  have endpoint := seam first last next
  rewrite [← endpoint]
  exact ⟨((initial.layerAt depth).node first).span.valid, Fraction.Order.Basic.le_refl _⟩

namespace Samples

/-- Construct the actual nonlinear changed-parameter path from the two original retained anchor caches.

The source span, endpoint containment and width payment are derived from
the actual layerAt midpoint chain at depth at least eight. Only the two original
Seed budgets and existing PathData are built; all selected root observations,
parameter Step targets, arithmetic rows and weights remain the input caches.
-/
def path (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) :
    Path.Cache (samples.anchors.get first).val (samples.anchors.get last).val increment admitted
      (span := ((initial.layerAt depth).node first).span)
      ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node first).span.valid⟩
      (next_time_inside first last next) (span_width_sq_le initial depth depthBound first) :=
  Path.build (samples.anchors.get first).val (samples.anchors.get last).val increment admitted
    (span := ((initial.layerAt depth).node first).span)
    ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node first).span.valid⟩
    (next_time_inside first last next) (span_width_sq_le initial depth depthBound first)

end Samples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

end

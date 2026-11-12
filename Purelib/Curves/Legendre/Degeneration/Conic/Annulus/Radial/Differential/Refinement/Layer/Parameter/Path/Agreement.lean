module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Path
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path.Agreement

/-!
# Original neighboring parameter caches on one normalized continuation path

The retained original layerAt midpoint chain pays the geometric center
separation between its two cached anchors. At every actual nonlinear path
parameter, their original fixed-box branches therefore have operational
agreement. The constructed span seam identifies the first branch's finish
with the independent original next parameter Step root cache.

The input nonlinear path cache is reused. No source query, Seed budget,
parameter Step, observed root, arithmetic row or finite weight is rebuilt.
Full cubic/cofactor attachment and geometric integral transport remain separate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Samples

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
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

/-- The exact retained nonlinear path-cache type on two original neighboring sample anchors.

This reducible view retains both original node indices, anchor values,
constructed span and geometric width payment. It introduces no owner or data
copy and is the original Samples.path constructor's complete result type.
-/
@[expose] def PathCache (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) :=
  Path.Cache (samples.anchors.get first).val (samples.anchors.get last).val increment admitted
    (span := ((initial.layerAt depth).node first).span)
    ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node first).span.valid⟩
    (next_time_inside first last next) (span_width_sq_le initial depth depthBound first)

/-- Both actual nonlinear branches agree at every retained parameter of an original neighboring sample span.

The exact layerAt midpoint seam and depth derive source-center separation.
The supplied original path cache retains its own two Seed budgets and root
owners; generic paid square comparison preserves both operational sample starts.
-/
def pathAgreement (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) (cache : PathCache samples depthBound first last next)
    (index : Fraction.Rational) (inside : FixedRootBoxPath.Inside index) : cache.path.Agreement index inside :=
  cache.agreement (ordinate_near initial depth depthBound first last next (samples.anchors.get first).val)
    index inside

/-- The first nonlinear branch finishes at the same original independent next parameter Step root cache.

The original constructed span seam identifies the exact finish radicand.
Internally paid cross-window agreement and the last branch's retained-Step
comparison compose without replacing either original endpoint owner or cache.
-/
def pathFinishEquivalent (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) (cache : PathCache samples depthBound first last next) :
    NamedEquivalent
      (ownerRootName (cache.path.nonzero 1 (by decide +kernel)) (cache.path.First 1 (by decide +kernel)))
      (samples.steps.get last).val.root.value.name :=
  cache.firstFinishEquivalent
    (ordinate_near initial depth depthBound first last next (samples.anchors.get first).val)
    (samples.steps.get last).val (seam first last next)

/-- The retained actual nonlinear preparation starts on the original first normalized target Step cache. -/
def preparedPathStartEquivalent (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) (cache : PathCache samples depthBound first last next)
    (prepared : FixedRootBoxPath.Preparation.Result cache.path) :
    NamedEquivalent (ownerRootName prepared.source.parameterNonzero prepared.source)
      (samples.steps.get first).val.root.value.name :=
  cache.prepared_startEquivalent prepared (samples.steps.get first).val rfl

/-- Internally paid original seams identify the genuine advanced finish with the original next normalized Step cache.

The actual preparation, both Seed budgets, source/target Steps, arithmetic
observations and weights remain retained inputs. Only the original layer
seam and internally derived neighboring-window payment are consumed.
-/
def preparedPathFinishEquivalent (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (first last : Fin (initial.layerAt depth).pieces.length)
    (next : last.val = first.val + 1) (cache : PathCache samples depthBound first last next)
    (prepared : FixedRootBoxPath.Preparation.Result cache.path) :
    NamedEquivalent (ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner)
      (samples.steps.get last).val.root.value.name :=
  cache.prepared_finishEquivalent prepared
    (ordinate_near initial depth depthBound first last next (samples.anchors.get first).val)
    (samples.steps.get last).val (seam first last next)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Samples

end

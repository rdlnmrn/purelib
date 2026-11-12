module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Path.Agreement
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Endpoint
import Purelib.Data.Rat.Interval.Bounds

/-!
# The final original normalized parameter span

The original constructed layer's final node ends at the initial Piece's
retained upper time. One original upper Reading, Anchor and admitted Step
complete the normalized endpoint chain. The final nonlinear path and its
actual finite preparation consume these same caches and the existing final
node's Anchor and Step, without changing any interior sample or weight.

The normalized advanced finish is compared with the retained upper Step.
Cofactor/full-cubic continuation and geometric integral evidence remain separate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
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

/-- The actual constructed layer's final piece ends at the identical original upper chart time. -/
theorem last_finish (initial : Radial.Differential.Refinement.Piece data actual accuracy) (depth : Nat) :
    ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.upper = initial.span.upper :=
  initial.layerAt_finish depth (initial.layerAt depth).lastNode.val
    (initial.layerAt depth).lastNode.isLt (initial.layerAt depth).lastNode_succ

/-- The retained original upper chart time belongs to the final constructed layer span. -/
theorem last_time_inside (initial : Radial.Differential.Refinement.Piece data actual accuracy) (depth : Nat) :
    ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.Contains initial.span.upper := by
  rewrite [← last_finish initial depth]
  exact ⟨((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.valid,
    Fraction.Order.Basic.le_refl _⟩

namespace Samples

/-- The final original normalized path-cache type retains its old last anchor and one separate upper endpoint cache. -/
@[expose] def FinishPathCache (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (endpoint : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :=
  Path.Cache (samples.anchors.get (initial.layerAt depth).lastNode).val endpoint.anchor increment admitted
    (span := ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span)
    ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.valid⟩
    (last_time_inside initial depth)
    (span_width_sq_le initial depth depthBound (initial.layerAt depth).lastNode)

/-- Cache the original upper endpoint and one final nonlinear path with its genuine actual preparation.

The existing Samples remains an index. The upper Reading/Anchor/Step chain,
path and preparation are separate retained values with exact factory equations;
neither the interior node caches nor their original finite weights are rebuilt.
-/
@[expose] def Finish (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) :=
  Σ endpoint : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted,
    Σ cache : { retained : FinishPathCache samples depthBound endpoint //
      retained = Path.build (samples.anchors.get (initial.layerAt depth).lastNode).val endpoint.anchor
        increment admitted (span := ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span)
        ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.valid⟩
        (last_time_inside initial depth)
        (span_width_sq_le initial depth depthBound (initial.layerAt depth).lastNode) },
      { prepared : FixedRootBoxPath.Preparation.Result cache.val.path // prepared = cache.val.prepare }

/-- The original last node's signed Seed window pays the retained upper endpoint center internally. -/
theorem finish_ordinate_near (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) :
    Norm.Basic.normSq
      ((Radial.Parameter.sourcePoint site parameter (Waist.direction quarter initial.span.upper)).ordinate -
        (Radial.Parameter.sourcePoint site parameter
          (Waist.direction quarter
            ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.lower)).ordinate) ≤
      (samples.anchors.get (initial.layerAt depth).lastNode).val.seed.separation.radius ^ 2 /
        Fraction.Cast.fromInt 256 := by
  apply (samples.anchors.get (initial.layerAt depth).lastNode).val.ordinate_near
  rewrite [← last_finish initial depth]
  exact span_width_sq_le initial depth depthBound (initial.layerAt depth).lastNode

namespace Finish

/-- Build the final nonlinear path and preparation once on a supplied identical retained upper endpoint. -/
def ofEndpoint (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (endpoint : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    Finish samples depthBound :=
  let cache := Path.build (samples.anchors.get (initial.layerAt depth).lastNode).val endpoint.anchor
    increment admitted (span := ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span)
    ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.valid⟩
    (last_time_inside initial depth) (span_width_sq_le initial depth depthBound (initial.layerAt depth).lastNode)
  let prepared := cache.prepare
  ⟨endpoint, ⟨cache, rfl⟩, ⟨prepared, rfl⟩⟩

/-- Retain the supplied original upper Reading and construct its one normalized endpoint and final preparation. -/
def ofReading (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (reading : Transport.Reading actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)) : Finish samples depthBound :=
  let endpoint := Endpoint.ofReading reading regular increment admitted
  ofEndpoint samples depthBound endpoint

/-- Query only the original upper endpoint, then retain its normalized endpoint, final path and actual preparation. -/
def build (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) : Finish samples depthBound :=
  let reading := Transport.Reading.build actual initial.span.upper
    (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)
  ofReading samples depthBound reading

variable {samples : Samples (initial.layerAt depth) regular increment admitted nonzero} {depthBound : 8 ≤ depth}

/-- Read the entire original upper Reading/Anchor/Step chain retained beside the same Samples. -/
@[expose] def endpoint (finish : Finish samples depthBound) :
    Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted := finish.1

/-- Read the identical final nonlinear path cache on the actual last node and retained original upper endpoint. -/
@[expose] def cache (finish : Finish samples depthBound) : FinishPathCache samples depthBound finish.endpoint :=
  finish.2.1.val

/-- Read the genuine original finite preparation retained on that exact final nonlinear path. -/
@[expose] def prepared (finish : Finish samples depthBound) : FixedRootBoxPath.Preparation.Result finish.cache.path :=
  finish.2.2.val

/-- The actual final path cache is its original factory on the two retained anchors and derived span payment. -/
theorem cache_eq (finish : Finish samples depthBound) : finish.cache =
    Path.build (samples.anchors.get (initial.layerAt depth).lastNode).val finish.endpoint.anchor
      increment admitted (span := ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span)
      ⟨Fraction.Order.Basic.le_refl _, ((initial.layerAt depth).node (initial.layerAt depth).lastNode).span.valid⟩
      (last_time_inside initial depth)
      (span_width_sq_le initial depth depthBound (initial.layerAt depth).lastNode) := finish.2.1.property

/-- The retained final preparation is the original actual-move factory on the identical cached nonlinear path. -/
theorem prepared_eq (finish : Finish samples depthBound) : finish.prepared = finish.cache.prepare :=
  finish.2.2.property

/-- Both original fixed-box branches agree everywhere on the same retained final span. -/
def agreement (finish : Finish samples depthBound) (index : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside index) : finish.cache.path.Agreement index inside :=
  finish.cache.agreement (finish_ordinate_near samples depthBound) index inside

/-- The genuine final-span preparation starts on the exact original last sampled normalized Step cache. -/
def startEquivalent (finish : Finish samples depthBound) :
    NamedEquivalent (ownerRootName finish.prepared.source.parameterNonzero finish.prepared.source)
      (samples.steps.get (initial.layerAt depth).lastNode).val.root.value.name :=
  finish.cache.prepared_startEquivalent finish.prepared
    (samples.steps.get (initial.layerAt depth).lastNode).val rfl

/-- The actual advanced final-span finish agrees with the identical retained upper normalized Step root cache. -/
def finishEquivalent (finish : Finish samples depthBound) :
    NamedEquivalent (ownerRootName finish.prepared.finishOwner.parameterNonzero finish.prepared.finishOwner)
      finish.endpoint.step.root.value.name :=
  finish.cache.prepared_finishEquivalent finish.prepared (finish_ordinate_near samples depthBound)
    finish.endpoint.step (last_finish initial depth)

/-- Reusing a retained original upper endpoint preserves its complete Reading/Anchor/Step cache. -/
theorem ofEndpoint_endpoint (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (original : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    (ofEndpoint samples depthBound original).endpoint = original := by
  unfold ofEndpoint endpoint
  rfl

/-- Supplying an original upper Reading preserves that entire cache in the final-span construction. -/
theorem ofReading_reading (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (reading : Transport.Reading actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)) :
    (ofReading samples depthBound reading).endpoint.reading = reading := by
  unfold ofReading ofEndpoint endpoint
  exact Endpoint.ofReading_reading reading regular increment admitted

end Finish

end Samples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter

end

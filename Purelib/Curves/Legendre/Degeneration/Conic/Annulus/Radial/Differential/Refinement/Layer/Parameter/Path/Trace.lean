module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Path.Finish
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Agreement
public import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Nat.Subtraction
import Purelib.Tactic.QuotientFreeOmega

/-!
# Retained normalized traces on an original sampled radial span

Each nonfinal original layer span retains one nonlinear path and one actual
finite preparation. A stored dependent spine preserves the original sample
indices and order. The last span reuses one separately retained upper Endpoint
through the original Finish.ofEndpoint constructor. All operational seams are
derived through the identical cached normalized Step at their common node.

The Samples, its source queries, Anchors, Steps, scalar observations and weights
remain unchanged. These are normalized-root traces; cofactor continuation,
full-product transport, covered geometric paths and integrals remain separate.
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
open Purelib.Data.Vector (DependentVector)
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

namespace Trace

/-- The original nonfinal spans retain the exact finite prefix of the actual layer's node indices. -/
@[expose] def Index (layer : Layer initial depth) := Fin layer.lastNode.val

/-- Read the original left node of a nonfinal span at the same retained natural index. -/
@[expose] def left {layer : Layer initial depth} (index : Index layer) : Fin layer.pieces.length :=
  ⟨index.val, Nat.lt_trans index.isLt layer.lastNode.isLt⟩

/-- Read the original next node of a nonfinal span at its exact successor index. -/
@[expose] def right {layer : Layer initial depth} (index : Index layer) : Fin layer.pieces.length :=
  ⟨index.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt index.isLt) layer.lastNode.isLt⟩

/-- Depth at least eight guarantees a nonempty original prefix before the final retained node. -/
theorem index_nonempty (layer : Layer initial depth) (depthBound : 8 ≤ depth) : 0 < layer.lastNode.val := by
  have count : depth + 1 ≤ layer.pieces.length := by
    rewrite [layer.count]
    exact Data.Nat.BinaryNormalization.succ_le_two_pow depth
  have finish := layer.lastNode_succ
  have depthPositive : 0 < depth := Nat.lt_of_lt_of_le (by decide +kernel : 0 < 8) depthBound
  omega0

/-- Select the first original nonfinal span using the internally derived finite prefix bound. -/
@[expose] def first (layer : Layer initial depth) (depthBound : 8 ≤ depth) : Index layer :=
  ⟨0, index_nonempty layer depthBound⟩

/-- Select the last original nonfinal span using the same retained prefix and derived bound. -/
@[expose] def last (layer : Layer initial depth) (depthBound : 8 ≤ depth) : Index layer :=
  ⟨layer.lastNode.val - 1, Nat.sub_lt (index_nonempty layer depthBound) (by decide +kernel)⟩

/-- The last nonfinal span's original right node is the same retained layer.lastNode. -/
theorem last_right (layer : Layer initial depth) (depthBound : 8 ≤ depth) :
    right (last layer depthBound) = layer.lastNode := by
  apply Fin.ext
  change layer.lastNode.val - 1 + 1 = layer.lastNode.val
  exact Data.Nat.Subtraction.sub_add_cancel (index_nonempty layer depthBound)

/-- Cache one original neighboring nonlinear path and its actual preparation with exact factory equations.

The index selects the same original two Samples Anchors and Steps. The
preparation consumes the retained path once; no source query, sampling request
or arithmetic observation is repeated.
-/
@[expose] def Entry (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (index : Index (initial.layerAt depth)) :=
  Σ cache : { retained : PathCache samples depthBound (left index) (right index) rfl //
      retained = samples.path depthBound (left index) (right index) rfl },
    { prepared : FixedRootBoxPath.Preparation.Result cache.val.path // prepared = cache.val.prepare }

namespace Entry

/-- Construct one neighboring path and actual preparation once from the two original cached sample anchors. -/
def build (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) (index : Index (initial.layerAt depth)) : Entry samples depthBound index :=
  let cache := samples.path depthBound (left index) (right index) rfl
  let prepared := cache.prepare
  ⟨⟨cache, rfl⟩, ⟨prepared, rfl⟩⟩

variable {samples : Samples (initial.layerAt depth) regular increment admitted nonzero} {depthBound : 8 ≤ depth}
variable {index : Index (initial.layerAt depth)}

/-- Read the identical neighboring nonlinear path retained by the entry. -/
@[expose] def cache (entry : Entry samples depthBound index) :
    PathCache samples depthBound (left index) (right index) rfl := entry.1.val

/-- Read the genuine finite preparation on the entry's same retained nonlinear path. -/
@[expose] def prepared (entry : Entry samples depthBound index) :
    FixedRootBoxPath.Preparation.Result entry.cache.path := entry.2.val

/-- The retained neighboring path is its exact original Samples.path factory. -/
theorem cache_eq (entry : Entry samples depthBound index) :
    entry.cache = samples.path depthBound (left index) (right index) rfl := entry.1.property

/-- The retained preparation is its original actual-move factory on the same cached path. -/
theorem prepared_eq (entry : Entry samples depthBound index) : entry.prepared = entry.cache.prepare :=
  entry.2.property

/-- Both original fixed-box branches agree everywhere on the same retained nonfinal span. -/
def agreement (entry : Entry samples depthBound index) (time : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside time) : entry.cache.path.Agreement time inside :=
  samples.pathAgreement depthBound (left index) (right index) rfl entry.cache time inside

/-- The actual nonfinal preparation starts on the identical original left Samples.Step root cache. -/
def startEquivalent (entry : Entry samples depthBound index) :
    NamedEquivalent (ownerRootName entry.prepared.source.parameterNonzero entry.prepared.source)
      (samples.steps.get (left index)).val.root.value.name :=
  samples.preparedPathStartEquivalent depthBound (left index) (right index) rfl entry.cache entry.prepared

/-- The genuine advanced nonfinal finish agrees with the original right Samples.Step root cache. -/
def finishEquivalent (entry : Entry samples depthBound index) :
    NamedEquivalent (ownerRootName entry.prepared.finishOwner.parameterNonzero entry.prepared.finishOwner)
      (samples.steps.get (right index)).val.root.value.name :=
  samples.preparedPathFinishEquivalent depthBound (left index) (right index) rfl entry.cache entry.prepared

end Entry

/-- A materialized original finite prefix retains each dependent path/preparation entry in its original node order. -/
@[expose] def Entries (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth) :=
  DependentVector (fun index : Index (initial.layerAt depth) => Entry samples depthBound index)

end Trace

/-- Retain the actual normalized preparation prefix and one final span on an already retained original upper Endpoint.

The literal Samples remains the index of every dependent entry. The final
Finish cache carries its exact ofEndpoint factory equation and preserves that
complete upper Reading/Anchor/Step chain. All handoffs are derived operations,
not fields requiring callers to supply operational equivalences.
-/
@[expose] def Trace (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :=
  Trace.Entries samples depthBound ×
    { finish : Finish samples depthBound // finish = Finish.ofEndpoint samples depthBound upper }

namespace Trace

/-- Build each original neighboring path/preparation once and reuse the supplied upper Endpoint for the final span. -/
def ofEndpoint (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    Trace samples depthBound upper :=
  let entries : Entries samples depthBound := DependentVector.ofFn (fun index => Entry.build samples depthBound index)
  let finish := Finish.ofEndpoint samples depthBound upper
  ⟨entries, ⟨finish, rfl⟩⟩

variable {samples : Samples (initial.layerAt depth) regular increment admitted nonzero} {depthBound : 8 ≤ depth}
variable {upper : Endpoint actual initial.span.upper
  (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted}

/-- Read the original materialized nonfinal preparation spine without reconstructing any entry. -/
@[expose] def entries (trace : Trace samples depthBound upper) : Entries samples depthBound := trace.1

/-- Read the retained actual final preparation cache on the same original upper Endpoint. -/
@[expose] def finish (trace : Trace samples depthBound upper) : Finish samples depthBound := trace.2.val

/-- Read one already materialized original nonfinal path/preparation entry at its retained finite index. -/
@[expose] def entry (trace : Trace samples depthBound upper) (index : Index (initial.layerAt depth)) :
    Entry samples depthBound index := trace.entries.get index

/-- The trace's final span is the exact original ofEndpoint factory on the supplied complete upper cache. -/
theorem finish_eq (trace : Trace samples depthBound upper) :
    trace.finish = Finish.ofEndpoint samples depthBound upper := trace.2.property

/-- The same supplied original upper Reading/Anchor/Step cache remains the trace's retained terminal Endpoint. -/
theorem endpoint_eq (trace : Trace samples depthBound upper) : trace.finish.endpoint = upper :=
  (congrArg Finish.endpoint trace.finish_eq).trans (Finish.ofEndpoint_endpoint samples depthBound upper)

/-- Building the trace materializes each original entry factory at its identical finite index. -/
theorem ofEndpoint_entry (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted)
    (index : Index (initial.layerAt depth)) :
    (ofEndpoint samples depthBound upper).entry index = Entry.build samples depthBound index := by
  unfold ofEndpoint entry entries
  exact DependentVector.ofFn_get (fun index => Entry.build samples depthBound index) index

/-- Adjacent actual preparations hand off through the identical original Samples.Step at their shared node.

The natural successor equality identifies the two original finite indices.
Both operational comparisons retain their own actual source and advanced finish
owners, and composition uses only the already cached common Step root process.
-/
def seam (trace : Trace samples depthBound upper) (first last : Index (initial.layerAt depth))
    (next : last.val = first.val + 1) :
    NamedEquivalent
      (ownerRootName (trace.entry first).prepared.finishOwner.parameterNonzero
        (trace.entry first).prepared.finishOwner)
      (ownerRootName (trace.entry last).prepared.source.parameterNonzero (trace.entry last).prepared.source) := by
  have shared : right first = left last := Fin.ext next.symm
  have sharedRoot := congrArg (fun node => (samples.steps.get node).val.root.value.name) shared
  exact (trace.entry first).finishEquivalent.trans
    (NamedEquivalent.transport sharedRoot.symm rfl (trace.entry last).startEquivalent.symm)

/-- The last original nonfinal advanced finish hands off to the retained final-span preparation source. -/
def finalSeam (trace : Trace samples depthBound upper) :
    NamedEquivalent
      (ownerRootName (trace.entry (last (initial.layerAt depth) depthBound)).prepared.finishOwner.parameterNonzero
        (trace.entry (last (initial.layerAt depth) depthBound)).prepared.finishOwner)
      (ownerRootName trace.finish.prepared.source.parameterNonzero trace.finish.prepared.source) := by
  have sharedRoot := congrArg (fun node => (samples.steps.get node).val.root.value.name)
    (last_right (initial.layerAt depth) depthBound)
  exact (trace.entry (last (initial.layerAt depth) depthBound)).finishEquivalent.trans
    (NamedEquivalent.transport sharedRoot.symm rfl trace.finish.startEquivalent.symm)

/-- The original constructed layer starts at the same retained initial lower chart endpoint. -/
theorem source_time (initial : Radial.Differential.Refinement.Piece data actual accuracy) (depth : Nat)
    (depthBound : 8 ≤ depth) :
    ((initial.layerAt depth).node (left (first (initial.layerAt depth) depthBound))).span.lower =
      initial.span.lower :=
  initial.layerAt_start depth (left (first (initial.layerAt depth) depthBound)).isLt

/-- A retained lower Endpoint agrees with the actual trace source through the original first sampled normalized Step.

The exact layerAt start identifies both original source coordinates. The two
independently retained Anchors and Steps are compared internally; the supplied
lower Reading is reused without another source query or root isolation.
-/
def startEquivalent (trace : Trace samples depthBound upper)
    (lower : Endpoint actual initial.span.lower
      (initial.within _ ⟨Fraction.Order.Basic.le_refl _, initial.span.valid⟩) regular increment admitted) :
    NamedEquivalent
      (ownerRootName (trace.entry (first (initial.layerAt depth) depthBound)).prepared.source.parameterNonzero
        (trace.entry (first (initial.layerAt depth) depthBound)).prepared.source)
      lower.step.root.value.name := by
  have direction_eq := congrArg (Waist.direction quarter) (source_time initial depth depthBound)
  have base_eq := congrArg (fun direction => (Radial.Parameter.sourcePoint site parameter direction).base) direction_eq
  have ordinate_eq := congrArg
    (fun direction => (Radial.Parameter.sourcePoint site parameter direction).ordinate) direction_eq
  exact (trace.entry (first (initial.layerAt depth) depthBound)).startEquivalent.trans
    (Radial.Parameter.Step.root_agrees_of_source_eq
      (samples.anchors.get (left (first (initial.layerAt depth) depthBound))).val lower.anchor
      (samples.steps.get (left (first (initial.layerAt depth) depthBound))).val lower.step base_eq ordinate_eq)

/-- The genuine final advanced normalized owner agrees with the identical supplied upper Endpoint.Step cache. -/
def finishEquivalent (trace : Trace samples depthBound upper) :
    NamedEquivalent (ownerRootName trace.finish.prepared.finishOwner.parameterNonzero trace.finish.prepared.finishOwner)
      upper.step.root.value.name :=
  NamedEquivalent.transport rfl
    (congrArg (fun endpoint : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted =>
      endpoint.step.root.value.name) trace.endpoint_eq) trace.finish.finishEquivalent

end Trace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Samples

end

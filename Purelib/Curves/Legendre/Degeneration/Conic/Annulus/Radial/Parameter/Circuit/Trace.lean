module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter.Path.Trace
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence

/-!
# Actual normalized continuation around an original radial integral circuit

Each original integral quarter retains its own sampled parameter bank and
materialized nonlinear preparation trace. The original circuit endpoint
caches supply all eight boundary Anchors and Steps without another query.
Actual advanced finishes and sources meet through the independent endpoint
comparisons, including the fourth-to-first returning sheet.

The circuit, differential, integral cells, physical weights and common
increment remain indices. These certificates concern normalized roots on the
unchanged original spatial circuit. Cofactor/full-cubic continuation and
geometric integral comparison require their separate retained evidence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Circuit

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Parameter (Samples)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter increment : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential} {accuracy : AccuracyRequest}
variable {admitted : IncrementBound site parameter increment} {nonzero : increment ≠ 0}
variable {depth : Nat} {depthBound : 8 ≤ depth}

namespace Trace

variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {regular : parameter ≠ criticalValue site}
variable {initial : Piece data actual accuracy}
variable {upper : Endpoint actual initial.span.upper
  (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted}

/-- Retain one original sampled parameter bank and its actual trace on a supplied upper Endpoint.

The complete Samples is retained as the dependent parent of every preparation.
The trace's factory equation preserves its supplied endpoint and materialized
prefix/final caches; no source bank or boundary owner is copied or replaced.
-/
@[expose] def Entry (initial : Piece data actual accuracy) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : IncrementBound site parameter increment) (nonzero : increment ≠ 0)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :=
  Σ samples : Samples (initial.layerAt depth) regular increment admitted nonzero,
    { trace : Samples.Trace samples depthBound upper // trace = Samples.Trace.ofEndpoint samples depthBound upper }

namespace Entry

/-- Reuse a complete original sampled bank and materialize its trace once on the identical supplied endpoint. -/
def ofSamples (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    Entry initial regular increment admitted nonzero depthBound upper :=
  let trace := Samples.Trace.ofEndpoint samples depthBound upper
  ⟨samples, ⟨trace, rfl⟩⟩

/-- Construct the original bank once on an integral quarter's actual layer, then retain its complete trace. -/
def build (initial : Piece data actual accuracy) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : IncrementBound site parameter increment) (nonzero : increment ≠ 0)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    Entry initial regular increment admitted nonzero depthBound upper :=
  let samples := Layer.Parameter.build (initial.layerAt depth) regular increment admitted nonzero
  ofSamples samples depthBound upper

/-- Read the identical original sampled parameter bank, including its retained weights and arithmetic rows. -/
@[expose] def samples (entry : Entry initial regular increment admitted nonzero depthBound upper) :
    Samples (initial.layerAt depth) regular increment admitted nonzero := entry.1

/-- Read the materialized actual normalized trace on that same retained bank and original upper Endpoint. -/
@[expose] def trace (entry : Entry initial regular increment admitted nonzero depthBound upper) :
    Samples.Trace entry.samples depthBound upper := entry.2.val

/-- The retained trace is its entire original factory on the same supplied sampled bank and endpoint. -/
theorem trace_eq (entry : Entry initial regular increment admitted nonzero depthBound upper) :
    entry.trace = Samples.Trace.ofEndpoint entry.samples depthBound upper := entry.2.property

/-- Reusing a completed sampled bank preserves that whole cache, without another sampling construction. -/
theorem ofSamples_samples (samples : Samples (initial.layerAt depth) regular increment admitted nonzero)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    (ofSamples samples depthBound upper).samples = samples := by
  unfold ofSamples Entry.samples
  rfl

/-- The quarter constructor keeps the complete original bank factory on its exact original integral layer. -/
theorem build_samples (initial : Piece data actual accuracy) (regular : parameter ≠ criticalValue site)
    (increment : Canonical) (admitted : IncrementBound site parameter increment) (nonzero : increment ≠ 0)
    (depthBound : 8 ≤ depth)
    (upper : Endpoint actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩) regular increment admitted) :
    (build initial regular increment admitted nonzero depthBound upper).samples =
      Layer.Parameter.build (initial.layerAt depth) regular increment admitted nonzero := by
  unfold build
  exact ofSamples_samples _ depthBound upper

/-- Read the original actual source root name of the materialized first nonlinear preparation. -/
@[expose] def sourceName (entry : Entry initial regular increment admitted nonzero depthBound upper) : Named :=
  let first := entry.trace.entry (Samples.Trace.first (initial.layerAt depth) depthBound)
  ownerRootName first.prepared.source.parameterNonzero first.prepared.source

/-- Read the genuine final advanced root name of the retained original final-span preparation. -/
@[expose] def finishName (entry : Entry initial regular increment admitted nonzero depthBound upper) : Named :=
  ownerRootName entry.trace.finish.prepared.finishOwner.parameterNonzero entry.trace.finish.prepared.finishOwner

/-- The actual source preparation agrees with a supplied original lower Endpoint through its retained first Step. -/
def startEquivalent (entry : Entry initial regular increment admitted nonzero depthBound upper)
    (lower : Endpoint actual initial.span.lower
      (initial.within _ ⟨Fraction.Order.Basic.le_refl _, initial.span.valid⟩) regular increment admitted) :
    NamedEquivalent entry.sourceName lower.step.root.value.name := entry.trace.startEquivalent lower

/-- The actual final advanced preparation agrees with the identical supplied original upper Endpoint.Step. -/
def finishEquivalent (entry : Entry initial regular increment admitted nonzero depthBound upper) :
    NamedEquivalent entry.finishName upper.step.root.value.name := entry.trace.finishEquivalent

end Entry

end Trace

variable {original : Transport.Circuit site parameter}
variable {integral : Differential.Circuit.Integral data original accuracy}
variable {endpoints : Endpoints original increment admitted}

/-- Four retained actual normalized quarter traces on the identical original geometric integral circuit.

Every entry keeps the same integral quarter's original cell/layer and the
matching already cached upper Endpoint. Their order is first, second, third,
fourth. Cross-quarter and returning-sheet certificates are derived operations
on these independently retained traces, rather than assumed record fields.
-/
@[expose] def Trace (integral : Differential.Circuit.Integral data original accuracy)
    (endpoints : Endpoints original increment admitted) (nonzero : increment ≠ 0) (depthBound : 8 ≤ depth) :=
  Trace.Entry (integral.cells.piece .first) original.first.regular increment admitted nonzero depthBound
      endpoints.first.target ×
    Trace.Entry (integral.cells.piece .second) original.second.regular increment admitted nonzero depthBound
      endpoints.second.target ×
    Trace.Entry (integral.cells.piece .third) original.third.regular increment admitted nonzero depthBound
      endpoints.third.target ×
    Trace.Entry (integral.cells.piece .fourth) original.fourth.regular increment admitted nonzero depthBound
      endpoints.fourth.target

namespace Trace

/-- Materialize four original banks and actual traces once, reusing the integral cells and all supplied endpoints. -/
def build (integral : Differential.Circuit.Integral data original accuracy)
    (endpoints : Endpoints original increment admitted) (nonzero : increment ≠ 0) (depthBound : 8 ≤ depth) :
    Trace integral endpoints nonzero depthBound :=
  let first := Entry.build (integral.cells.piece .first) original.first.regular increment admitted nonzero depthBound
    endpoints.first.target
  let second := Entry.build (integral.cells.piece .second) original.second.regular increment admitted nonzero depthBound
    endpoints.second.target
  let third := Entry.build (integral.cells.piece .third) original.third.regular increment admitted nonzero depthBound
    endpoints.third.target
  let fourth := Entry.build (integral.cells.piece .fourth) original.fourth.regular increment admitted nonzero depthBound
    endpoints.fourth.target
  ⟨first, second, third, fourth⟩

/-- Read the first retained original integral-quarter bank and normalized preparation trace. -/
@[expose] def first (trace : Trace integral endpoints nonzero depthBound) :
    Entry (integral.cells.piece .first) original.first.regular increment admitted nonzero depthBound
      endpoints.first.target := trace.1

/-- Read the second retained original integral-quarter bank and actual normalized trace. -/
@[expose] def second (trace : Trace integral endpoints nonzero depthBound) :
    Entry (integral.cells.piece .second) original.second.regular increment admitted nonzero depthBound
      endpoints.second.target := trace.2.1

/-- Read the third original bank and trace from the same ordered circuit cache. -/
@[expose] def third (trace : Trace integral endpoints nonzero depthBound) :
    Entry (integral.cells.piece .third) original.third.regular increment admitted nonzero depthBound
      endpoints.third.target := trace.2.2.1

/-- Read the fourth retained original bank and trace completing the same circuit's quarter order. -/
@[expose] def fourth (trace : Trace integral endpoints nonzero depthBound) :
    Entry (integral.cells.piece .fourth) original.fourth.regular increment admitted nonzero depthBound
      endpoints.fourth.target := trace.2.2.2

/-- The first actual advanced finish hands off to the second actual source through both original endpoint Steps. -/
def first_second (trace : Trace integral endpoints nonzero depthBound) :
    NamedEquivalent trace.first.finishName trace.second.sourceName :=
  trace.first.finishEquivalent.trans
    (endpoints.first_second.trans (trace.second.startEquivalent endpoints.second.source).symm)

/-- The second genuine advanced finish agrees with the third preparation's actual original source root. -/
def second_third (trace : Trace integral endpoints nonzero depthBound) :
    NamedEquivalent trace.second.finishName trace.third.sourceName :=
  trace.second.finishEquivalent.trans
    (endpoints.second_third.trans (trace.third.startEquivalent endpoints.third.source).symm)

/-- The third original actual trace hands off to the fourth through the independently retained endpoint owners. -/
def third_fourth (trace : Trace integral endpoints nonzero depthBound) :
    NamedEquivalent trace.third.finishName trace.fourth.sourceName :=
  trace.third.finishEquivalent.trans
    (endpoints.third_fourth.trans (trace.fourth.startEquivalent endpoints.fourth.source).symm)

/-- The fourth actual normalized finish returns to the first actual preparation's retained source sheet.

The original endpoint direction closure and both actual trace comparisons
derive the returning-sheet relation. It is independent of any endpoint matrix
calculation. Full-cubic sheets and geometric integral agreement remain separate.
-/
def fourth_first (trace : Trace integral endpoints nonzero depthBound) :
    NamedEquivalent trace.fourth.finishName trace.first.sourceName :=
  trace.fourth.finishEquivalent.trans
    (endpoints.fourth_first.trans (trace.first.startEquivalent endpoints.first.source).symm)

end Trace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Circuit

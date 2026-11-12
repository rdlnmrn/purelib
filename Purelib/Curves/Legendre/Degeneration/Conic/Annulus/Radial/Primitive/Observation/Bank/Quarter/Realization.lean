module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Partition

/-! # One finite whole-quarter bank realization on retained original source cells

The original initial Piece and depth remain indices. Each finite producer
is run once and stored with its complete original factory identity: Layer,
later cofactor observations, terminal query and Bank, actual primitive cell
certificates, and exact old-entry endpoint views. No earlier Bank or integral
model execution is asserted equal to this new retained realization.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Layer Piece)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Integration
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}

/-- The original full-span equality internally gives the strictly positive width used by the same bank producers. -/
theorem width_positive (whole : initial.span = Differential.Circuit.span) : 0 < initial.span.width := by
  rewrite [width_eq whole]
  exact of_decide_eq_true rfl

/-- The original layer cache keeps the complete finite layerAt factory and its exact identity. -/
abbrev LayerCache (initial : Piece data actual initialAccuracy) (depth : Nat) :=
  { layer : Layer initial depth // layer = initial.layerAt depth }

/-- The original layerAt Chain transports to the identical retained whole layer cache. -/
theorem layerChain (retained : LayerCache initial depth) :
    Partition.Interval.Chain initial.span.lower initial.span.upper
      (Differential.Refinement.Piece.chartIntervals retained.val.pieces) := by
  rewrite [retained.property]
  exact initial.layerAt_chain depth

/-- A finite bank realization retains every original producer cache at its literal source and depth. -/
@[expose] def Realization (initial : Piece data actual initialAccuracy)
    (whole : initial.span = Differential.Circuit.span) (depth : Nat) :=
  Σ layer : LayerCache initial depth,
    Σ samples : { retained : Differential.Refinement.Layer.RefinedSamples layer.val (width_positive whole) //
        retained = layer.val.refineSamples (width_positive whole) },
      Σ requested : { retained :
          (Σ upper : Transport.Reading actual initial.span.upper
              (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩),
            Bank primitive samples.val upper) //
          retained = Bank.build primitive samples.val },
        { retained : Cells specification requested.val.2 (layerChain layer) //
          retained = Bank.cells specification requested.val.2 (layerChain layer) } ×
          { endpoints : Endpoints requested.val.2 (layerChain layer) whole //
            endpoints = Quarter.endpoints requested.val.2 (layerChain layer) whole }

namespace Realization

/-- Compute and retain one original finite realization without repeating any completed producer. -/
def build (initial : Piece data actual initialAccuracy) (whole : initial.span = Differential.Circuit.span)
    (depth : Nat) : Realization (specification := specification) initial whole depth :=
  let layer : LayerCache initial depth := ⟨initial.layerAt depth, rfl⟩
  let samples := layer.val.refineSamples (width_positive whole)
  let requested := Bank.build primitive samples
  let cells := Bank.cells specification requested.2 (layerChain layer)
  let endpoints := Quarter.endpoints requested.2 (layerChain layer) whole
  ⟨layer, ⟨⟨samples, rfl⟩, ⟨⟨requested, rfl⟩, ⟨⟨cells, rfl⟩, ⟨endpoints, rfl⟩⟩⟩⟩⟩

variable {whole : initial.span = Differential.Circuit.span}

/-- Read the exact retained complete layer and its layerAt factory identity. -/
@[expose] def layer (retained : Realization (specification := specification) initial whole depth) :
    LayerCache initial depth := retained.1

/-- Read the same later cofactor observation family without invoking its producer again. -/
@[expose] def samples (retained : Realization (specification := specification) initial whole depth) :
    Differential.Refinement.Layer.RefinedSamples retained.layer.val (width_positive whole) := retained.2.1.val

/-- Read the same actual original terminal query and complete shared primitive Bank. -/
@[expose] def requested (retained : Realization (specification := specification) initial whole depth) :
    Σ upper : Transport.Reading actual initial.span.upper
        (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩),
      Bank primitive retained.samples upper := retained.2.2.1.val

/-- Read the actual original arithmetic primitive cell certificates on that identical retained Bank. -/
@[expose] def cells (retained : Realization (specification := specification) initial whole depth) :
    Cells specification retained.requested.2 (layerChain retained.layer) := retained.2.2.2.1.val

/-- Read the same cached complete old-entry endpoint views at the common exactly equal arithmetic request. -/
@[expose] def endpoints (retained : Realization (specification := specification) initial whole depth) :
    Endpoints retained.requested.2 (layerChain retained.layer) whole := retained.2.2.2.2.val

/-- The retained cofactor observation vector is its exact original producer on the same layer. -/
theorem samples_eq (retained : Realization (specification := specification) initial whole depth) :
    retained.samples = retained.layer.val.refineSamples (width_positive whole) := retained.2.1.property

/-- The retained terminal query and whole Bank are the exact single original Bank.build result. -/
theorem requested_eq (retained : Realization (specification := specification) initial whole depth) :
    retained.requested = Bank.build primitive retained.samples := retained.2.2.1.property

/-- The retained actual cell vector is its exact original producer on the same Bank and interval Chain. -/
theorem cells_eq (retained : Realization (specification := specification) initial whole depth) :
    retained.cells = Bank.cells specification retained.requested.2 (layerChain retained.layer) :=
  retained.2.2.2.1.property

/-- The retained old-entry endpoint views are their exact completed whole-cache transport factory. -/
theorem endpoints_eq (retained : Realization (specification := specification) initial whole depth) :
    retained.endpoints = Quarter.endpoints retained.requested.2 (layerChain retained.layer) whole :=
  retained.2.2.2.2.property

/-- The retained scalar model sample has the original canonical layerAt readback at this exact finite depth. -/
theorem sample_eq (retained : Realization (specification := specification) initial whole depth) :
    retained.layer.val.model.integralSample = (initial.layerAt depth).model.integralSample :=
  congrArg (fun layer : Layer initial depth => layer.model.integralSample) retained.layer.property

end Realization

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter

end

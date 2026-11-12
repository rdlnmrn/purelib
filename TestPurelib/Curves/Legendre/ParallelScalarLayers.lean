module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Vector.Dependent
import Purelib.Data.List.Map
import Purelib.Data.List.DependentProduct

/-! # Whole scalar-layer reweighting on actual retained midpoint observations

One actual dyadic layer supplies all six original differential layers. The
complete former factories, exact ordered meshes and full accuracy requests
are checked independently of later coefficient or integral comparisons.
-/

namespace TestPurelib.Curves.Legendre.ParallelScalarLayers

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Approximation
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Radial.Differential.Refinement
open Purelib.Algebra.Quadratic (Pair)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Radial.Transport.Quarter site parameter 2 quarter positive}
variable {radicand : Pair.Polynomial.Coefficients} {differential : OddPowerDifferential radicand}
variable {data : WaistBounds site parameter differential} {accuracy : AccuracyRequest}

/-- One completed original layer produces all six former factories with its exact shared sampled mesh.

The actual layer is built once outside the channel callback. Each callback
only reweights its retained coefficients and forwards all complete Reading
and cofactor observation caches.
-/
def channelLayers (initial : Piece data actual accuracy)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel))) (depth : Nat) :
    let base := initial.layerAt depth
    {entries : DependentVector (fun channel : Fin 6 => Layer (initial.reweight (forms.get channel)) depth) //
      ∀ channel, entries.get channel = (initial.reweight (forms.get channel)).layerAt depth ∧
        (entries.get channel).accuracy = base.accuracy ∧
        (entries.get channel).pieces.map (fun piece => piece.span) = base.pieces.map (fun piece => piece.span)} := by
  let base := initial.layerAt depth
  let entries := DependentVector.ofFn (fun channel : Fin 6 => base.reweight (forms.get channel))
  refine ⟨entries, ?_⟩
  intro channel
  have entry := DependentVector.ofFn_get (fun channel : Fin 6 => base.reweight (forms.get channel)) channel
  rewrite [entry]
  exact ⟨initial.layerAt_reweight (forms.get channel) depth,
    base.reweight_accuracy (forms.get channel), base.reweight_spans (forms.get channel)⟩

/-- Actual supplied per-occurrence coefficient caches produce all six complete original numerical layers.

Each returned layer consumes the corresponding retained whole Models and
original Piece parents. The finite construction allocates only its piece
and container spines; it does not execute another coefficient Model or
Reading factory inside a channel lookup.
-/
def cachedChannelLayers {initial : Piece data actual accuracy} {depth : Nat} (base : Layer initial depth)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (cells : DependentVector (fun channel : Fin 6 => Layer.ReweightedCells base (forms.get channel))) :
    {entries : DependentVector (fun channel : Fin 6 => Layer (initial.reweight (forms.get channel)) depth) //
      ∀ channel, entries.get channel = base.reweight (forms.get channel)} := by
  let entries := DependentVector.ofFn (fun channel : Fin 6 =>
    base.reweight (forms.get channel) (some (base.reweightedPieces (forms.get channel) (cells.get channel))))
  refine ⟨entries, ?_⟩
  intro channel
  have entry := DependentVector.ofFn_get (fun channel : Fin 6 =>
    base.reweight (forms.get channel) (some (base.reweightedPieces (forms.get channel) (cells.get channel)))) channel
  rewrite [entry]
  exact base.reweight_supplied (forms.get channel) _

/-- The actual supplied scalar-cache layer has the identical original numerical integral sample.

The complete Layer equality is consumed after construction. No equality
between separately sampled approximate roots is used in this readback.
-/
theorem cachedChannelLayer_integral {initial : Piece data actual accuracy} {depth : Nat}
    (base : Layer initial depth)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (cells : DependentVector (fun channel : Fin 6 => Layer.ReweightedCells base (forms.get channel)))
    (channel : Fin 6) :
    ((cachedChannelLayers base forms cells).val.get channel).model.integralSample =
      (base.reweight (forms.get channel)).model.integralSample :=
  congrArg (fun layer => layer.model.integralSample) ((cachedChannelLayers base forms cells).property channel)

/-- A bounded output occurrence retains exactly the original whole supplied Piece and coefficient Model.

The projection law certifies the actual constructor data rather than only
its scalar value or reweight readback. All source, domain and observation
caches remain attached to that same complete original Piece parent.
-/
example {initial : Piece data actual accuracy} {depth : Nat} (base : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (models : Layer.ReweightedCells base nextData) (ordinal : Fin base.pieces.length) :
    (base.reweightedPieces nextData models).val[ordinal.val]'
        ((base.reweightedPieces_count nextData models).symm ▸ ordinal.isLt) =
      Piece.ofCell (DependentProduct.get base.pieces models ordinal).1.val.within
        (DependentProduct.get base.pieces models ordinal).2.val :=
  base.reweightedPieces_get nextData models ordinal

/-- The complete original steps factory survives reweighting, including both actual sampled half-span cells. -/
example (parents : List (Piece data actual accuracy))
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (Steps.build parents).reweight nextData = Steps.build (parents.map (fun piece => piece.reweight nextData)) :=
  Steps.reweight_build nextData parents

end TestPurelib.Curves.Legendre.ParallelScalarLayers

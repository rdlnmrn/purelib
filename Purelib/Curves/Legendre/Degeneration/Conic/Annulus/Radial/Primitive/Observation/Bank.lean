module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Sampling
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Partition
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Shared actual primitive endpoint observations on a retained original layer

The supplied Layer and RefinedSamples are actual cached inputs. Interior
entries reuse their exact original source queries and later cofactor
observations, including the old/new stage relation. One separate upper
Reading supplies a terminal observation on its own certificate. Each
endpoint's original primitive preparation, evaluator caches and selected
arithmetic comparison are materialized once.

Adjacent cells read one identical stored endpoint value. Original interval
Chain evidence transports the whole next endpoint cache to the preceding
span's upper time, preserving the actual observations and comparison.
Successive differences of these stored arithmetic witnesses telescope by
finite algebra alone. This asserts no continuation of a full sheet, returning
sheet, primitive integral endpoint law or canonical integral comparison.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Layer Piece)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Integration
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}
variable {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
variable {samples : Refinement.Layer.RefinedSamples layer initialPositive}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {upper : Transport.Reading actual initial.span.upper
  (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)}

namespace Bank

/-- The original retained squared-width quarter radius computes one common arithmetic endpoint accuracy request. -/
def request (_layer : Layer initial depth) (initialPositive : 0 < initial.span.width) : AccuracyRequest :=
  let squaredWidth := Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth
  ⟨squaredWidth ^ 2,
    Fraction.Order.Arithmetic.pow_pos_direct
      (Geometric.Basic.quarterRadius_pos (Fraction.Order.Arithmetic.pow_pos_direct initialPositive 2) depth) 2⟩

/-- The common request has exactly each actual node's fourth-power width, without changing that node's root request. -/
theorem request_tolerance (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (index : Fin layer.pieces.length) :
    (request layer initialPositive).tolerance = (layer.node index).span.width ^ 4 := by
  have member : layer.node index ∈ layer.pieces := List.getElem_mem index.isLt
  calc
    _ = Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := rfl
    _ = ((layer.node index).span.width ^ 2) ^ 2 :=
      congrArg (fun value : Fraction.Rational => value ^ 2) (layer.widths (layer.node index) member).symm
    _ = _ := by ring1

/-- Each interior bank entry retains its original node query, later cofactor sample and common arithmetic request. -/
abbrev Nodes (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (samples : Refinement.Layer.RefinedSamples layer initialPositive) :=
  Data.Vector.DependentVector (fun index : Fin layer.pieces.length =>
    Entry primitive (layer.node index).source initial.cell.regular (samples.get index).val.sample
      (request layer initialPositive))

end Bank

/-- One shared endpoint bank keeps the unchanged actual layer's interior observations and one distinct terminal cache.

The cached Layer and original RefinedSamples remain indices; neither is
reconstructed by a layerAt call. The terminal root request begins at its own
original certificate's stage zero, rather than an index from another point.
The original node-specific residual requests remain distinct from the common
arithmetic request, with their equal tolerances proved separately.
-/
@[expose] def Bank (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (samples : Refinement.Layer.RefinedSamples layer initialPositive)
    (upper : Transport.Reading actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)) :=
  Bank.Nodes primitive samples ×
    Entry.Sampled primitive upper initial.cell.regular (Bank.request layer initialPositive)
      (Bank.request layer initialPositive) 0

namespace Bank

/-- Materialize each original interior endpoint once while reusing a supplied complete terminal observation cache. -/
def ofTerminal (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (samples : Refinement.Layer.RefinedSamples layer initialPositive)
    (upper : Transport.Reading actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩))
    (terminal : Entry.Sampled primitive upper initial.cell.regular
      (request layer initialPositive) (request layer initialPositive) 0) : Bank primitive samples upper :=
  let accuracy := request layer initialPositive
  let nodes := Data.Vector.DependentVector.ofFn (fun index : Fin layer.pieces.length =>
    Entry.build primitive (layer.node index).source initial.cell.regular (samples.get index).val.sample accuracy)
  ⟨nodes, terminal⟩

/-- Retain a supplied original upper Reading and request its terminal root/primitive observations exactly once. -/
def ofReading (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (samples : Refinement.Layer.RefinedSamples layer initialPositive)
    (upper : Transport.Reading actual initial.span.upper
      (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)) : Bank primitive samples upper :=
  let accuracy := request layer initialPositive
  let terminal := Entry.Sampled.build primitive upper initial.cell.regular accuracy accuracy 0
  ofTerminal primitive samples upper terminal

/-- Query only the original upper endpoint once and retain that complete query beside the shared primitive bank. -/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (samples : Refinement.Layer.RefinedSamples layer initialPositive) :
    Σ upper : Transport.Reading actual initial.span.upper
        (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩),
      Bank primitive samples upper :=
  let upper := Transport.Reading.build actual initial.span.upper
    (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)
  let bank := ofReading primitive samples upper
  ⟨upper, bank⟩

/-- Read all original interior endpoint caches without repeating a query, preparation or observation. -/
@[expose] def nodes (bank : Bank primitive samples upper) : Nodes primitive samples := bank.1

/-- Read the distinct original upper endpoint cache, its own cofactor selection and actual primitive observation. -/
@[expose] def terminal (bank : Bank primitive samples upper) :
    Entry.Sampled primitive upper initial.cell.regular (request layer initialPositive)
      (request layer initialPositive) 0 := bank.2

/-- The original stored node sample still pays that same node's old selected cofactor comparison index. -/
theorem node_index_ge (_bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    (layer.node index).cell.sample.comparison.leftIndex ≤ (samples.get index).val.sample.comparison.leftIndex :=
  (samples.get index).property

/-- Read one stored arithmetic endpoint witness at its original interior index or the distinct final endpoint. -/
def vertex (bank : Bank primitive samples upper) (index : Fin (layer.pieces.length + 1)) : Canonical :=
  if within : index.val < layer.pieces.length then (bank.nodes.get ⟨index.val, within⟩).value
  else bank.terminal.entry.value

/-- An interior vertex reads that identical retained original Entry's selected arithmetic witness. -/
theorem vertex_source (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    bank.vertex index.castSucc = (bank.nodes.get index).value := by
  unfold vertex
  change (if within : index.val < layer.pieces.length then
    (bank.nodes.get ⟨index.val, within⟩).value else bank.terminal.entry.value) = _
  rewrite [dif_pos index.isLt]
  rfl

/-- The last vertex reads the terminal Entry's identical selected original arithmetic witness. -/
theorem vertex_finish (bank : Bank primitive samples upper) :
    bank.vertex (Fin.last layer.pieces.length) = bank.terminal.entry.value := by
  unfold vertex
  change (if within : layer.pieces.length < layer.pieces.length then
    (bank.nodes.get ⟨layer.pieces.length, within⟩).value else bank.terminal.entry.value) = _
  rewrite [dif_neg (Nat.lt_irrefl layer.pieces.length)]
  rfl

/-- The first vertex reads the first actual original node's selected arithmetic endpoint observation. -/
theorem vertex_start (bank : Bank primitive samples upper) :
    bank.vertex 0 = (bank.nodes.get ⟨0, layer.nonempty⟩).value :=
  bank.vertex_source ⟨0, layer.nonempty⟩

/-- Each original cell's endpoint increment uses the same retained vertices as both of its incident neighbors. -/
@[expose] def increment (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) : Canonical :=
  bank.vertex index.succ - bank.vertex index.castSucc

/-- Sum the actual retained endpoint increments in their original finite cell order. -/
@[expose] def incrementSum (bank : Bank primitive samples upper) : Canonical :=
  FiniteSum.Fin.sumFin (fun index => bank.increment index)

/-- The same shared actual arithmetic endpoint observations telescope exactly across the finite bank.

Both occurrences of every interior value are the identical stored Entry's
selected witness. No integral defines an endpoint value, and no continued
sheet or geometric returning comparison is needed for this algebraic sum.
-/
theorem incrementSum_eq (bank : Bank primitive samples upper) :
    bank.incrementSum = bank.terminal.entry.value - (bank.nodes.get ⟨0, layer.nonempty⟩).value := by
  calc
    _ = bank.vertex (Fin.last layer.pieces.length) - bank.vertex 0 :=
      FiniteSum.Fin.sumFin_successive_differences (fun index => bank.vertex index)
    _ = _ := by rewrite [bank.vertex_finish, bank.vertex_start]; rfl

/-- Adjacent cells share exactly the next original node's cached arithmetic endpoint witness. -/
theorem successor_value (bank : Bank primitive samples upper) (index : Fin layer.pieces.length)
    (nextBound : index.val + 1 < layer.pieces.length) :
    bank.vertex index.succ = (bank.nodes.get ⟨index.val + 1, nextBound⟩).value :=
  bank.vertex_source ⟨index.val + 1, nextBound⟩

/-- The original interval Chain transports the complete next Entry to this exact original cell's upper time. -/
def successorEntry (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Refinement.Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length)
    (nextBound : index.val + 1 < layer.pieces.length) :=
  (bank.nodes.get ⟨index.val + 1, nextBound⟩).castTime
    (otherInside := (layer.node index).within (layer.node index).span.upper
      ⟨(layer.node index).span.valid, Fraction.Order.Basic.le_refl _⟩)
    (layer.seam chain index.val index.isLt nextBound).symm

/-- The preceding cell's upper Entry is the same selected witness used at the following cell's source. -/
theorem successorEntry_value (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Refinement.Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length)
    (nextBound : index.val + 1 < layer.pieces.length) :
    (bank.successorEntry chain index nextBound).value = bank.vertex index.succ := by
  have retained := Entry.castTime_value
    (otherInside := (layer.node index).within (layer.node index).span.upper
      ⟨(layer.node index).span.valid, Fraction.Order.Basic.le_refl _⟩)
    (layer.seam chain index.val index.isLt nextBound).symm (bank.nodes.get ⟨index.val + 1, nextBound⟩)
  exact retained.trans (bank.successor_value index nextBound).symm

/-- The preceding upper Entry retains the same complete original/factored arithmetic comparison as the next source. -/
theorem successorEntry_comparison (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Refinement.Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length)
    (nextBound : index.val + 1 < layer.pieces.length) :
    HEq (bank.successorEntry chain index nextBound).selected.comparison
      (bank.nodes.get ⟨index.val + 1, nextBound⟩).selected.comparison :=
  Entry.castTime_comparison
    (otherInside := (layer.node index).within (layer.node index).span.upper
      ⟨(layer.node index).span.valid, Fraction.Order.Basic.le_refl _⟩)
    (layer.seam chain index.val index.isLt nextBound).symm (bank.nodes.get ⟨index.val + 1, nextBound⟩)

/-- The original interval Chain identifies the bank's first actual query time with the original initial span start. -/
theorem start_time (_bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Refinement.Piece.chartIntervals layer.pieces)) :
    (layer.node ⟨0, layer.nonempty⟩).span.lower = initial.span.lower :=
  layer.start_eq chain layer.nonempty

/-- The original interval Chain transports the same terminal Entry to the final original span's upper time. -/
def finishEntry (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Refinement.Piece.chartIntervals layer.pieces)) :=
  bank.terminal.entry.castTime
    (otherInside := (layer.node layer.lastNode).within (layer.node layer.lastNode).span.upper
      ⟨(layer.node layer.lastNode).span.valid, Fraction.Order.Basic.le_refl _⟩)
    (layer.finish_eq chain layer.lastNode.val layer.lastNode.isLt layer.lastNode_succ).symm

/-- The final span's upper Entry retains exactly the terminal selected primitive witness. -/
theorem finishEntry_value (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Refinement.Piece.chartIntervals layer.pieces)) :
    (bank.finishEntry chain).value = bank.terminal.entry.value :=
  Entry.castTime_value
    (otherInside := (layer.node layer.lastNode).within (layer.node layer.lastNode).span.upper
      ⟨(layer.node layer.lastNode).span.valid, Fraction.Order.Basic.le_refl _⟩)
    (layer.finish_eq chain layer.lastNode.val layer.lastNode.isLt layer.lastNode_succ).symm bank.terminal.entry

end Bank

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

end

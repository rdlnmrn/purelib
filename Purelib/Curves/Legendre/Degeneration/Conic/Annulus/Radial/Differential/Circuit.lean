module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
public import Purelib.Integration.Program.Gaussian.Concatenation.Uniform
import Purelib.Data.List.Append
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual odd-power scalar integrals on the retained original curved regular parallel circuit

Every quarter consumes the exact original source lift of the same geometric
circuit. The residual-controlled initial cells and their complete root owners
are cached once. Equal finite refinement counts derive the concatenation
allowances internally, retaining all four actual numerical model sequences.

These scalar integrals include all original odd denominators. Agreement
with independently sampled arithmetic pullbacks, parameter variation and
actual prescribed primitive boundaries remain separate certificates.
The resulting integral has its original curved circuit as an index. A
canonical A/B identification still requires the geometric cut attachment and
the finite trace/refinement and integral comparisons.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Circuit

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : WaistBounds site parameter differential} {accuracy : AccuracyRequest}

/-- The original closed unit chart interval of each complete rational quarter. -/
@[expose] def span : Interval.Bounds := ⟨0, 1, by decide +kernel⟩

/-- The original residual-controlled full-quarter cell on an exact retained geometric leg source. -/
abbrev QuarterCell (data : WaistBounds site parameter differential)
    {quarter : UnitCircuitQuarter} (leg : Transport.Leg site parameter quarter)
    (accuracy : AccuracyRequest) :=
  Differential.Cells.Model (span := span) data leg.source accuracy

set_option genInjectivity false in
/-- Four cached actual differential cells on the same original geometric circuit's source lifts.

The differential and geometric circuit remain indices. Each field retains the
original signed owner, selected process state and observed coefficient on its
exact circuit leg, including the positive normalized-ordinate floors at all real-axis seams.
-/
structure Cells (data : WaistBounds site parameter differential)
    (circuit : Transport.Circuit site parameter) (accuracy : AccuracyRequest) where
  /-- The actual first quarter cell on this circuit's identical retained source lift. -/
  first : QuarterCell data circuit.first accuracy
  /-- The actual second quarter cell on this circuit's identical retained source lift. -/
  second : QuarterCell data circuit.second accuracy
  /-- The actual third quarter cell on this circuit's identical retained source lift. -/
  third : QuarterCell data circuit.third accuracy
  /-- The actual fourth quarter cell on this circuit's identical retained source lift. -/
  fourth : QuarterCell data circuit.fourth accuracy

constructive_injectivity Cells

namespace Cells

variable {circuit : Transport.Circuit site parameter}

/-- Sample each original cached geometric source once and derive its paid signed scalar chart cell. -/
@[expose] def build (data : WaistBounds site parameter differential)
    (circuit : Transport.Circuit site parameter) (accuracy : AccuracyRequest) : Cells data circuit accuracy :=
  { first := Differential.Cells.Model.build (span := span) data circuit.first.source circuit.first.regular accuracy
    second := Differential.Cells.Model.build (span := span) data circuit.second.source circuit.second.regular accuracy
    third := Differential.Cells.Model.build (span := span) data circuit.third.source circuit.third.regular accuracy
    fourth := Differential.Cells.Model.build (span := span) data circuit.fourth.source circuit.fourth.regular accuracy }

/-- Read each identical cached source cell as a whole original scalar quarter piece. -/
@[expose] def piece (cells : Cells data circuit accuracy) :
    (quarter : UnitCircuitQuarter) → Refinement.Piece data (circuit.leg quarter).actual accuracy
  | .first => Refinement.Piece.ofCell (span := span) (fun _ contained => contained) cells.first
  | .second => Refinement.Piece.ofCell (span := span) (fun _ contained => contained) cells.second
  | .third => Refinement.Piece.ofCell (span := span) (fun _ contained => contained) cells.third
  | .fourth => Refinement.Piece.ofCell (span := span) (fun _ contained => contained) cells.fourth

/-- The original scalar quarter piece retains the same complete circuit source Reading at its original indices. -/
theorem piece_source (cells : Cells data circuit accuracy) (quarter : UnitCircuitQuarter) :
    HEq (cells.piece quarter).source (circuit.leg quarter).source := by
  cases quarter <;> rfl

/-- Reweight the original four completed scalar cells without resampling any of their actual cofactor certificates. -/
@[expose] def reweight (cells : Cells data circuit accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) : Cells nextData circuit accuracy :=
  { first := cells.first.reweight nextData
    second := cells.second.reweight nextData
    third := cells.third.reweight nextData
    fourth := cells.fourth.reweight nextData }

/-- Construct the ordered four-quarter integral program from the original cached cells and internally bounded joins. -/
@[expose] def program (cells : Cells data circuit accuracy) : Basic.RefinementProgram :=
  let first := (cells.piece .first).program
  let second := (cells.piece .second).program
  let third := (cells.piece .third).program
  let fourth := (cells.piece .fourth).program
  let left := first.concatOfEqualCounts second (fun index =>
    ((cells.piece .first).layerAt index).model_count.trans
      ((cells.piece .second).layerAt index).model_count.symm)
  let right := third.concatOfEqualCounts fourth (fun index =>
    ((cells.piece .third).layerAt index).model_count.trans
      ((cells.piece .fourth).layerAt index).model_count.symm)
  left.concatOfEqualCounts right (by
    intro index
    change ((first.model index).cells ++ (second.model index).cells).length =
      ((third.model index).cells ++ (fourth.model index).cells).length
    have firstCount : (first.model index).cells.length = 2 ^ index :=
      ((cells.piece .first).layerAt index).model_count
    have secondCount : (second.model index).cells.length = 2 ^ index :=
      ((cells.piece .second).layerAt index).model_count
    have thirdCount : (third.model index).cells.length = 2 ^ index :=
      ((cells.piece .third).layerAt index).model_count
    have fourthCount : (fourth.model index).cells.length = 2 ^ index :=
      ((cells.piece .fourth).layerAt index).model_count
    rewrite [List.length_append, List.length_append, firstCount, secondCount, thirdCount, fourthCount]
    rfl)

/-- The combined program keeps the exact original quarter models in their geometric circuit order. -/
theorem program_model (cells : Cells data circuit accuracy) (index : Nat) :
    cells.program.model index =
      (((cells.piece .first).layerAt index).model.concat ((cells.piece .second).layerAt index).model).concat
        (((cells.piece .third).layerAt index).model.concat ((cells.piece .fourth).layerAt index).model) := rfl

/-- Each combined model has exactly four original dyadic quarter cell lists. -/
theorem program_count (cells : Cells data circuit accuracy) (index : Nat) :
    (cells.program.model index).cells.length = 4 * 2 ^ index := by
  rewrite [cells.program_model]
  change ((((cells.piece .first).layerAt index).model.cells ++
    ((cells.piece .second).layerAt index).model.cells) ++
    (((cells.piece .third).layerAt index).model.cells ++ ((cells.piece .fourth).layerAt index).model.cells)).length = _
  simp only [List.length_append,
    ((cells.piece .first).layerAt index).model_count,
    ((cells.piece .second).layerAt index).model_count,
    ((cells.piece .third).layerAt index).model_count,
    ((cells.piece .fourth).layerAt index).model_count]
  omega0

/-- The actual combined sample adds the four original oriented quarter integral samples. -/
theorem program_sample (cells : Cells data circuit accuracy) (index : Nat) :
    (cells.program.model index).integralSample =
      (((cells.piece .first).layerAt index).model.integralSample +
        ((cells.piece .second).layerAt index).model.integralSample) +
      (((cells.piece .third).layerAt index).model.integralSample +
        ((cells.piece .fourth).layerAt index).model.integralSample) := by
  rewrite [cells.program_model, Basic.PathModel.integralSample_concat,
    Basic.PathModel.integralSample_concat, Basic.PathModel.integralSample_concat]
  rfl

end Cells

set_option genInjectivity false in
/-- The actual original curved-circuit integral, retaining the original sampled cells and its constructed program cache.

The same geometric circuit and original differential remain indices. The
cache equality identifies the complete original refinement program, including
its exact models and internally proved finite comparison schedules.
-/
structure Integral (data : WaistBounds site parameter differential)
    (circuit : Transport.Circuit site parameter) (accuracy : AccuracyRequest) where
  /-- The original four completed source cells, retained once. -/
  cells : Cells data circuit accuracy
  /-- The actual cached refinement program built on those same completed cells. -/
  program : Basic.RefinementProgram
  /-- The cache retains the whole original four-quarter construction. -/
  program_eq : program = cells.program

constructive_injectivity Integral

namespace Integral

variable {circuit : Transport.Circuit site parameter}

/-- Construct and cache the actual original circuit integral without acquiring any replacement source owner. -/
@[expose] def build (data : WaistBounds site parameter differential)
    (circuit : Transport.Circuit site parameter) (accuracy : AccuracyRequest) : Integral data circuit accuracy :=
  let cells := Cells.build data circuit accuracy
  let program := cells.program
  { cells, program, program_eq := rfl }

/-- Present the identical original program through the generic certified integral-cache interface. -/
@[expose] def cached (integral : Integral data circuit accuracy) : Cached.Basic.CachedProgram :=
  integral.program.certifiedView.program

/-- Each cached sample is the exact original four-quarter circuit model's integral sample. -/
theorem cached_sample (integral : Integral data circuit accuracy) (index : Nat) :
    (integral.cached.stage index).sample = (integral.program.model index).integralSample := rfl

/-- Every cached original circuit model retains the complete original four-quarter cell count. -/
theorem model_count (integral : Integral data circuit accuracy) (index : Nat) :
    (integral.program.model index).cells.length = 4 * 2 ^ index := by
  rewrite [integral.program_eq]
  exact integral.cells.program_count index

/-- The constructed original circuit program internally meets every supplied positive finite allowance request. -/
theorem requested_allowance (integral : Integral data circuit accuracy) (current : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    (integral.cached.stage (integral.cached.approximation.refineIndex current target positive)).allowance < target :=
  integral.cached.requested_allowance current target positive

end Integral

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Circuit

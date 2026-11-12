module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks.Circuit
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Program
public import Purelib.Integration.Program.Gaussian.Concatenation.Uniform
import Purelib.Data.List.Append
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual value integrals on the retained original curved waist circuit

Every quarter consumes the exact original source lift of the same geometric
circuit. The residual-controlled initial cells and their complete root owners
are cached once. Equal finite refinement counts derive the concatenation
allowances internally, retaining all four actual numerical model sequences.

The resulting integral has its original curved circuit as an index. A
canonical A/B identification still requires the geometric cut attachment and
the finite trace/refinement and integral comparisons.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {accuracy : Fraction.Rational}

/-- The original closed unit chart interval of each complete rational quarter. -/
@[expose] def span : Interval.Bounds := ⟨0, 1, by decide +kernel⟩

/-- The original residual-controlled full-quarter cell on an exact retained geometric leg source. -/
abbrev QuarterCell (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    {quarter : UnitCircuitQuarter} (leg : Banks.Leg site parameter quarter regular bound)
    (accuracy : Fraction.Rational) :=
  Refinement.Cell (span := span) data simple leg.source accuracy

set_option genInjectivity false in
/-- Four cached actual differential cells on the same original geometric circuit's source lifts.

The differential and geometric circuit remain indices. Each field retains the
original signed owner, selected process state and observed coefficient on its
exact circuit leg, including the two branch-safe value endpoints.
-/
structure Cells (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (circuit : Banks.Circuit site parameter regular bound) (accuracy : Fraction.Rational) where
  /-- The actual first quarter cell on this circuit's identical retained source lift. -/
  first : QuarterCell data simple circuit.first accuracy
  /-- The actual second quarter cell on this circuit's identical retained source lift. -/
  second : QuarterCell data simple circuit.second accuracy
  /-- The actual third quarter cell on this circuit's identical retained source lift. -/
  third : QuarterCell data simple circuit.third accuracy
  /-- The actual fourth quarter cell on this circuit's identical retained source lift. -/
  fourth : QuarterCell data simple circuit.fourth accuracy

constructive_injectivity Cells

namespace Cells

variable {circuit : Banks.Circuit site parameter regular bound}

/-- Prepare each actual source cell once, deriving its signed window from the same original geometric leg. -/
@[expose] def build (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (circuit : Banks.Circuit site parameter regular bound) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Cells data simple circuit accuracy :=
  { first := Refinement.Cell.build (span := span) data simple circuit.first.source
      circuit.first.source_signed accuracy positive
    second := Refinement.Cell.build (span := span) data simple circuit.second.source
      circuit.second.source_signed accuracy positive
    third := Refinement.Cell.build (span := span) data simple circuit.third.source
      circuit.third.source_signed accuracy positive
    fourth := Refinement.Cell.build (span := span) data simple circuit.fourth.source
      circuit.fourth.source_signed accuracy positive }

/-- Read each identical cached source cell as a complete original quarter piece. -/
@[expose] def piece (cells : Cells data simple circuit accuracy) :
    (quarter : UnitCircuitQuarter) → Refinement.Piece data simple quarter regular bound accuracy
  | .first => Refinement.Piece.ofCell cells.first
  | .second => Refinement.Piece.ofCell cells.second
  | .third => Refinement.Piece.ofCell cells.third
  | .fourth => Refinement.Piece.ofCell cells.fourth

/-- Construct the ordered four-quarter integral program from the original cached cells and internally bounded joins. -/
@[expose] def program (cells : Cells data simple circuit accuracy) : Basic.RefinementProgram :=
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
theorem program_model (cells : Cells data simple circuit accuracy) (index : Nat) :
    cells.program.model index =
      (((cells.piece .first).layerAt index).model.concat ((cells.piece .second).layerAt index).model).concat
        (((cells.piece .third).layerAt index).model.concat ((cells.piece .fourth).layerAt index).model) := rfl

/-- Each combined model has exactly four original dyadic quarter cell lists. -/
theorem program_count (cells : Cells data simple circuit accuracy) (index : Nat) :
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
theorem program_sample (cells : Cells data simple circuit accuracy) (index : Nat) :
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
structure Integral (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (circuit : Banks.Circuit site parameter regular bound) (accuracy : Fraction.Rational) where
  /-- The original four completed source cells, retained once. -/
  cells : Cells data simple circuit accuracy
  /-- The actual cached refinement program built on those same completed cells. -/
  program : Basic.RefinementProgram
  /-- The cache retains the whole original four-quarter construction. -/
  program_eq : program = cells.program

constructive_injectivity Integral

namespace Integral

variable {circuit : Banks.Circuit site parameter regular bound}

/-- Construct and cache the actual original circuit integral without acquiring any replacement source owner. -/
@[expose] def build (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (circuit : Banks.Circuit site parameter regular bound) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Integral data simple circuit accuracy :=
  let cells := Cells.build data simple circuit accuracy positive
  let program := cells.program
  { cells, program, program_eq := rfl }

/-- Present the identical original program through the generic certified integral-cache interface. -/
@[expose] def cached (integral : Integral data simple circuit accuracy) : Cached.Basic.CachedProgram :=
  integral.program.certifiedView.program

/-- Each cached sample is the exact original four-quarter circuit model's integral sample. -/
theorem cached_sample (integral : Integral data simple circuit accuracy) (index : Nat) :
    (integral.cached.stage index).sample = (integral.program.model index).integralSample := rfl

/-- Every cached original circuit model retains the complete original four-quarter cell count. -/
theorem model_count (integral : Integral data simple circuit accuracy) (index : Nat) :
    (integral.program.model index).cells.length = 4 * 2 ^ index := by
  rewrite [integral.program_eq]
  exact integral.cells.program_count index

/-- The constructed original circuit program internally meets every supplied positive finite allowance request. -/
theorem requested_allowance (integral : Integral data simple circuit accuracy) (current : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    (integral.cached.stage (integral.cached.approximation.refineIndex current target positive)).allowance < target :=
  integral.cached.requested_allowance current target positive

end Integral

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Circuit

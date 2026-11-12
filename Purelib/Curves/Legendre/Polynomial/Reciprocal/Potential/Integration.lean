module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Cells
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Continued
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Observation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # Original physical cells for the weighted reciprocal split

The weighted and lifted remainder pullbacks consume the same stored inverse
cube and ordered segment coordinate as the potential density. Their exact
finite integral split precedes any analytic comparison. Original uniform
requests pay the actual cubic observations before a sufficient cell is built.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {sourceDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal sourceDifferential}
    {preparation : PotentialComparison.Preparation comparison}

/-- The actual cubic differential retains its full numerator and unit scale on the same reciprocal curve. -/
def differential (numerator : Coefficients) :
    OddPowerDifferential (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) :=
  OddPowerDifferential.ofCoefficients (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) numerator 1 1

/-- The unit-scale source numerator has the same scalar evaluation without changing its normalized representation. -/
theorem effective_eval (numerator : Coefficients) (point : Gaussian) :
    (numerator.scale 1).eval point = numerator.eval point := by
  rewrite [eval_scale, Basic.one_mul]
  rfl

section Cells

variable {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- The two original pullback models retain the same actual tables, coordinate, displacement and allowance. -/
@[expose] def Pullbacks (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) : Type _ :=
  { value : Spatial.Pullback coordinate tables.1.val allowance //
    value = Spatial.Pullback.build coordinate tables.1.val allowance nonnegative } ×
  { value : Spatial.Pullback coordinate tables.2.val allowance //
    value = Spatial.Pullback.build coordinate tables.2.val allowance nonnegative }

/-- Compile the two already retained spatial tables without refining an inverse or rebuilding its cube. -/
def pullbacks (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) : Pullbacks retained tables :=
  let weighted := Spatial.Pullback.build coordinate tables.1.val allowance nonnegative
  let regular := Spatial.Pullback.build coordinate tables.2.val allowance nonnegative
  ⟨⟨weighted, rfl⟩, ⟨regular, rfl⟩⟩

/-- The whole physical-cell factory retains exactly the two original pullback constructors. -/
private theorem packaged_pullbacks_factory (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) :
    pullbacks retained tables =
      (let weighted := Spatial.Pullback.build coordinate tables.1.val allowance nonnegative
       let regular := Spatial.Pullback.build coordinate tables.2.val allowance nonnegative
       ⟨⟨weighted, rfl⟩, ⟨regular, rfl⟩⟩ : Pullbacks retained tables) := by rfl

/-- The whole physical-cell factory retains exactly the two original pullback constructors. -/
theorem pullbacks_factory (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) :
    pullbacks retained tables =
      (let weighted := Spatial.Pullback.build coordinate tables.1.val allowance nonnegative
       let regular := Spatial.Pullback.build coordinate tables.2.val allowance nonnegative
       ⟨⟨weighted, rfl⟩, ⟨regular, rfl⟩⟩ : Pullbacks retained tables) := packaged_pullbacks_factory retained tables

/-- The exact weighted split integrates on the three unchanged physical cells with their original orientation. -/
theorem integral_split (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) (cells : Pullbacks retained tables) :
    cells.1.val.model.integralSample =
      2 * retained.pullback.model.integralSample + cells.2.val.model.integralSample := by
  let linear := CellModel.exact start finish
    (Arithmetic.add (Arithmetic.scale 2 retained.pullback.model.polynomial) cells.2.val.model.polynomial)
  have linearIntegral : linear.integralSample =
      2 * retained.pullback.model.integralSample + cells.2.val.model.integralSample := by
    change (finish - start) * Integral.definiteIntegral
      (Arithmetic.add (Arithmetic.scale 2 retained.pullback.model.polynomial) cells.2.val.model.polynomial) 0 1 = _
    rewrite [Integral.definiteIntegral_add, Integral.definiteIntegral_scale]
    change _ = 2 * ((retained.pullback.model.finish - retained.pullback.model.start) *
      Integral.definiteIntegral retained.pullback.model.polynomial 0 1) +
        (cells.2.val.model.finish - cells.2.val.model.start) *
          Integral.definiteIntegral cells.2.val.model.polynomial 0 1
    rewrite [retained.pullback.start_eq, retained.pullback.finish_eq, cells.2.val.start_eq, cells.2.val.finish_eq]
    ring1
  have bounded := Primitive.integral_difference_le cells.1.val.model linear cells.1.val.start_eq
    cells.1.val.finish_eq 0 (by
      intro input _
      change Norm.Basic.normSq
        (Evaluation.eval cells.1.val.model.polynomial (⟨input, 0⟩ : Gaussian) -
          Evaluation.eval (Arithmetic.add (Arithmetic.scale 2 retained.pullback.model.polynomial)
            cells.2.val.model.polynomial) (⟨input, 0⟩ : Gaussian)) ≤ 0
      rewrite [Evaluation.eval_add, Evaluation.eval_scale, cells.1.val.eval_point,
        retained.pullback.eval_point, cells.2.val.eval_point]
      have split := Tables.split retained tables (coordinate.point input)
      rewrite [split]
      have zero : 2 * retained.density.eval (coordinate.point input) + tables.2.val.eval (coordinate.point input) -
          (2 * retained.density.eval (coordinate.point input) + tables.2.val.eval (coordinate.point input)) = 0 := by
        ring1
      rewrite [zero, Norm.Basic.normSq_zero]
      exact Fraction.Order.Basic.le_refl _)
  have zeroBound : Norm.Basic.normSq (cells.1.val.model.integralSample - linear.integralSample) ≤ 0 :=
    bounded.trans_eq (by ring1)
  have zero := Norm.Basic.normSq_eq_zero.mp
    (Fraction.Order.Basic.le_antisymm _ _ zeroBound (Norm.Basic.normSq_nonneg _))
  have equal := congrArg (fun value : Gaussian => value + linear.integralSample) zero
  have exactIntegral : cells.1.val.model.integralSample = linear.integralSample := by
    calc
      _ = (cells.1.val.model.integralSample - linear.integralSample) + linear.integralSample := by ring1
      _ = 0 + linear.integralSample := equal
      _ = _ := Basic.zero_add _
  exact exactIntegral.trans linearIntegral

end Cells

/-- Both actual uniform odd-reading requests retain their source bounds and exact future common floor. -/
@[expose] def Floors (preparation : PotentialComparison.Preparation comparison)
    (allowance : Coordinate) (_positive : 0 < allowance) (floor : Nat) : Type _ :=
  (weighted : UniformRequest preparation.2.2 1 ((-cap.polynomial).scale 1) floor (allowance / 4)) ×
  (regular : UniformRequest preparation.2.2 1
    (((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).scale 1) floor (allowance / 4)) ×
  { stage : Nat // stage = max weighted.selection.stage regular.selection.stage }

namespace Floors

/-- Select both actual cubic numerator floors before any new inverse, power or spatial model is constructed. -/
def build (preparation : PotentialComparison.Preparation comparison)
    (allowance : Coordinate) (positive : 0 < allowance) (floor : Nat) : Floors preparation allowance positive floor :=
  let quarterPositive : 0 < allowance / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let weighted := preparation.2.2.request 1 ((-cap.polynomial).scale 1) floor (allowance / 4) quarterPositive
  let regular := preparation.2.2.request 1
    (((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).scale 1) floor (allowance / 4) quarterPositive
  let stage := max weighted.selection.stage regular.selection.stage
  ⟨weighted, regular, ⟨stage, rfl⟩⟩

/-- The complete planner retains both original requests and their literal selected maximum. -/
private theorem packaged_build_factory (preparation : PotentialComparison.Preparation comparison)
    (allowance : Coordinate) (positive : 0 < allowance) (floor : Nat) :
    build preparation allowance positive floor =
      (let quarterPositive : 0 < allowance / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       let weighted := preparation.2.2.request 1 ((-cap.polynomial).scale 1) floor (allowance / 4) quarterPositive
       let regular := preparation.2.2.request 1
         (((wRemainder (parameter := parameter)) *
           HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).scale 1) floor (allowance / 4) quarterPositive
       let stage := max weighted.selection.stage regular.selection.stage
       ⟨weighted, regular, ⟨stage, rfl⟩⟩ : Floors preparation allowance positive floor) := by rfl

/-- The complete planner retains both original requests and their literal selected maximum. -/
theorem build_factory (preparation : PotentialComparison.Preparation comparison)
    (allowance : Coordinate) (positive : 0 < allowance) (floor : Nat) :
    build preparation allowance positive floor =
      (let quarterPositive : 0 < allowance / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       let weighted := preparation.2.2.request 1 ((-cap.polynomial).scale 1) floor (allowance / 4) quarterPositive
       let regular := preparation.2.2.request 1
         (((wRemainder (parameter := parameter)) *
           HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).scale 1) floor (allowance / 4) quarterPositive
       let stage := max weighted.selection.stage regular.selection.stage
       ⟨weighted, regular, ⟨stage, rfl⟩⟩ : Floors preparation allowance positive floor) :=
  packaged_build_factory preparation allowance positive floor

variable {allowance : Coordinate} {positive : 0 < allowance} {floor : Nat}

/-- The retained future stage pays the actual weighted numerator request. -/
theorem weighted_le (paid : Floors preparation allowance positive floor) :
    paid.1.selection.stage ≤ paid.2.2.val := by
  rewrite [paid.2.2.property]
  exact Data.Nat.Order.le_max_left _ _

/-- The retained future stage pays the actual regular numerator request. -/
theorem regular_le (paid : Floors preparation allowance positive floor) :
    paid.2.1.selection.stage ≤ paid.2.2.val := by
  rewrite [paid.2.2.property]
  exact Data.Nat.Order.le_max_right _ _

/-- The true original floor is retained by both independently selected requests. -/
theorem floor_le (paid : Floors preparation allowance positive floor) : floor ≤ paid.2.2.val :=
  paid.1.selection.lower.trans paid.weighted_le

end Floors

section Build

variable {start finish : Gaussian} (coordinate : Spatial.Coordinate start finish)
    {allowance : Coordinate} {positive : 0 < allowance} {floor : Nat}
    (paid : Floors preparation allowance positive floor)

/-- One genuinely sufficient original cell and its two same-cube tables and physical pullback caches. -/
@[expose] def Materialized : Type _ :=
  (retained : Cell preparation.2.1 coordinate paid.2.2.val allowance positive.le) ×
  (tables : Tables retained) × Pullbacks retained tables

/-- Construct one new inverse and cube only after the two actual source requests have selected their common floor. -/
def build : Materialized coordinate paid :=
  let retained := Cell.build preparation.2.1 coordinate paid.2.2.val allowance positive.le
  let tables := Tables.build retained
  let cells := pullbacks retained tables
  ⟨retained, tables, cells⟩

/-- The materialized result retains the one original cell factory and its two exact dependent consumers. -/
private theorem packaged_build_factory :
    build coordinate paid =
      (let retained := Cell.build preparation.2.1 coordinate paid.2.2.val allowance positive.le
       let tables := Tables.build retained
       let cells := pullbacks retained tables
       ⟨retained, tables, cells⟩ : Materialized coordinate paid) := by rfl

/-- The materialized result retains the one original cell factory and its two exact dependent consumers. -/
theorem build_factory :
    build coordinate paid =
      (let retained := Cell.build preparation.2.1 coordinate paid.2.2.val allowance positive.le
       let tables := Tables.build retained
       let cells := pullbacks retained tables
       ⟨retained, tables, cells⟩ : Materialized coordinate paid) := packaged_build_factory coordinate paid

end Build

section Continued

variable {first last : LiftedPoint 2} {coordinate : Spatial.Coordinate first.coordinate last.coordinate}
    {allowance : Coordinate} {positive : 0 < allowance} {floor stage : Nat}
    (retained : Cell preparation.2.1 coordinate stage allowance positive.le)

/-- Construct one original uniform cubic observation using the same supplied Point, inverse and stored cube. -/
def observe (numerator table : Coefficients) (pulled : Spatial.Pullback coordinate table allowance)
    (compiled : ∀ point, table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (request : UniformRequest preparation.2.2 1 (numerator.scale 1) floor (allowance / 4))
    (lifted : LiftedCell first last) (input : Coordinate)
    (sample : Point terminal.neighborhood.patch (coordinate.point input))
    (inside : terminal.neighborhood.patch.box.Contains (coordinate.point input))
    (later : request.selection.stage ≤ stage) :
    Jets.UniformObservation (reciprocalCurve (Fibre.frameCurve frame)) (differential numerator) lifted
      pulled.model input := by
  let localBounds := sample.primitiveBounds
  let source := numerator.scale 1
  let factor := source.eval (coordinate.point input)
  let original := retainPrimitiveDenotation sample localBounds 1 source ⟨factor, rfl⟩
  let precision := ReadingPrecision.build (Norm.Basic.normSq original.value.im) allowance
    (Norm.Basic.normSq_nonneg _) positive
  let root := selectPrimitiveRoot sample stage precision.target precision.target_positive
  let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
  have sourceCompiled : table.eval (coordinate.point input) = source.eval (coordinate.point input) *
      (primitivePolynomial retained.powers 1).eval (coordinate.point input) := by
    rewrite [effective_eval]
    exact compiled (coordinate.point input)
  let value := retainPrimitiveValue reading 1 source original table sourceCompiled ⟨factor, rfl⟩
  exact Jets.UniformObservation.ofContinuedPrimitive (reciprocalCurve (Fibre.frameCurve frame))
    (differential numerator) 1 rfl lifted pulled input sample inside request retained.inverse_eq precision root
      reading rfl original value later (Fraction.Order.Basic.le_refl _)

/-- The new uniform observation retains the original supplied Point's full selected root name. -/
private theorem packaged_observe_root_name (numerator table : Coefficients)
    (pulled : Spatial.Pullback coordinate table allowance)
    (compiled : ∀ point, table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (request : UniformRequest preparation.2.2 1 (numerator.scale 1) floor (allowance / 4))
    (lifted : LiftedCell first last) (input : Coordinate)
    (sample : Point terminal.neighborhood.patch (coordinate.point input))
    (inside : terminal.neighborhood.patch.box.Contains (coordinate.point input))
    (later : request.selection.stage ≤ stage) :
    (observe (positive := positive) retained numerator table pulled compiled request lifted input sample inside
      later).algebraic.sheetValue.value.name = sample.certificate.value.name := by
  unfold observe
  apply Jets.UniformObservation.ofContinuedPrimitive_root_name

/-- The new uniform observation retains the original supplied Point's full selected root name. -/
theorem observe_root_name (numerator table : Coefficients) (pulled : Spatial.Pullback coordinate table allowance)
    (compiled : ∀ point, table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (request : UniformRequest preparation.2.2 1 (numerator.scale 1) floor (allowance / 4))
    (lifted : LiftedCell first last) (input : Coordinate)
    (sample : Point terminal.neighborhood.patch (coordinate.point input))
    (inside : terminal.neighborhood.patch.box.Contains (coordinate.point input))
    (later : request.selection.stage ≤ stage) :
    (observe (positive := positive) retained numerator table pulled compiled request lifted input sample inside
      later).algebraic.sheetValue.value.name = sample.certificate.value.name :=
  packaged_observe_root_name (positive := positive) retained numerator table pulled compiled request lifted
    input sample inside later

/-- Supply the physical uniform-cell contract with genuine continued Points at the actual queried parameters. -/
def certificate (numerator table : Coefficients) (pulled : Spatial.Pullback coordinate table allowance)
    (compiled : ∀ point, table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (request : UniformRequest preparation.2.2 1 (numerator.scale 1) floor (allowance / 4))
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) (later : request.selection.stage ≤ stage) :
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame)) (differential numerator)
      lifted pulled.model where
  query := fun input lower upper =>
    observe (positive := positive) retained numerator table pulled compiled request lifted
    input (samples input lower upper) (coordinate.point_inside firstInside lastInside lower upper) later

/-- Both stored physical models have original uniform certificates on the same supplied continuation family. -/
def certificates (tables : Tables retained) (cells : Pullbacks retained tables)
    (paid : Floors preparation allowance positive floor) (later : paid.2.2.val ≤ stage)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame)) (differential (-cap.polynomial))
      lifted cells.1.val.model ×
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame))
      (differential ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) lifted cells.2.val.model :=
  let weighted := certificate (positive := positive) retained (-cap.polynomial) tables.1.val cells.1.val
    (Tables.weighted_compiled retained tables) paid.1 lifted firstInside lastInside samples
    (paid.weighted_le.trans later)
  let regular := certificate (positive := positive) retained
    ((wRemainder (parameter := parameter)) * HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))
    tables.2.val cells.2.val (Tables.remainder_compiled retained tables) paid.2.1 lifted firstInside lastInside samples
    (paid.regular_le.trans later)
  ⟨weighted, regular⟩

/-- Both original uniform query closures retain their supplied continued Point's exact root name. -/
private theorem packaged_certificates_root_names
    (tables : Tables retained) (cells : Pullbacks retained tables)
    (paid : Floors preparation allowance positive floor) (later : paid.2.2.val ≤ stage)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((certificates (positive := positive) retained tables cells paid later lifted
      firstInside lastInside samples).1.query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name ∧
    ((certificates (positive := positive) retained tables cells paid later lifted
      firstInside lastInside samples).2.query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name := by
  constructor
  · exact observe_root_name (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
      (count := count) (center := center) (centerOwner := centerOwner) (terminal := terminal)
      (sourceDifferential := sourceDifferential) (comparison := comparison) (preparation := preparation)
      (first := first) (last := last) (coordinate := coordinate) (stage := stage)
      (allowance := allowance) (positive := positive) (floor := floor)
      retained (-cap.polynomial) tables.1.val cells.1.val (Tables.weighted_compiled retained tables)
      paid.1 lifted input (samples input lower upper)
      (coordinate.point_inside firstInside lastInside lower upper) (paid.weighted_le.trans later)
  · exact observe_root_name (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
      (count := count) (center := center) (centerOwner := centerOwner) (terminal := terminal)
      (sourceDifferential := sourceDifferential) (comparison := comparison) (preparation := preparation)
      (first := first) (last := last) (coordinate := coordinate) (stage := stage)
      (allowance := allowance) (positive := positive) (floor := floor)
      retained ((wRemainder (parameter := parameter)) * HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))
      tables.2.val cells.2.val (Tables.remainder_compiled retained tables) paid.2.1 lifted input
      (samples input lower upper) (coordinate.point_inside firstInside lastInside lower upper)
      (paid.regular_le.trans later)

/-- Both original uniform query closures retain their supplied continued Point's exact root name.

The two certificate queries keep their independent observation work and
use the same provided Point callback. The equality concerns the actual
retained generator owner, not coordinate equality or a local sheet label.
-/
theorem certificates_root_names
    (tables : Tables retained) (cells : Pullbacks retained tables)
    (paid : Floors preparation allowance positive floor) (later : paid.2.2.val ≤ stage)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((certificates (positive := positive) retained tables cells paid later lifted
      firstInside lastInside samples).1.query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name ∧
    ((certificates (positive := positive) retained tables cells paid later lifted
      firstInside lastInside samples).2.query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name :=
  packaged_certificates_root_names (positive := positive) retained tables cells paid later lifted
    firstInside lastInside samples input lower upper

/-- Certify both cells of the already materialized sufficient cache without repeating any model factory. -/
def certify (paid : Floors preparation allowance positive floor) (work : Materialized coordinate paid)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame)) (differential (-cap.polynomial))
      lifted work.2.2.1.val.model ×
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame))
      (differential ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) lifted work.2.2.2.val.model :=
  certificates (positive := positive) work.1 work.2.1 work.2.2 paid (Nat.le_refl _)
    lifted firstInside lastInside samples

/-- The constructed physical cells retain the exact finite integral split on their same stored potential density. -/
theorem materialized_integral_split (paid : Floors preparation allowance positive floor)
    (work : Materialized coordinate paid) :
    work.2.2.1.val.model.integralSample =
      2 * work.1.pullback.model.integralSample + work.2.2.2.val.model.integralSample :=
  integral_split work.1 work.2.1 work.2.2

/-- An actual spatial uniform query retains the original coordinate point, independently of its reading state. -/
private theorem query_point {numerator table : Coefficients}
    (pulled : Spatial.Pullback coordinate table allowance) (lifted : LiftedCell first last) (input : Coordinate)
    (query : Jets.UniformObservation (reciprocalCurve (Fibre.frameCurve frame))
      (differential numerator) lifted pulled.model input) :
    query.algebraic.point = coordinate.point input :=
  query.algebraic.point_eq.trans ((pulled.observationPoint_eq query.observation).trans
    (congrArg coordinate.point query.parameter_eq))

/-- Drop only the unit-scale representation from an actual query's same-pair coefficient interpretation. -/
private def unscale {point : Gaussian} {generator : CoherentNamed} (numerator : Coefficients)
    (original : Expression.Denotation (differential (frame := frame) numerator).coefficient point generator) :
    Expression.Denotation
      (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1 numerator)
      point generator :=
  original.reinterpretAt
    (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1 numerator)
    (by
      apply Algebra.Quadratic.Pair.ext
      · rfl
      · change numerator.eval point / _ = (numerator.scale 1).eval point / _
        rewrite [effective_eval]
        rfl)
    original.defined

/-- The unit-scale view keeps the whole actual original query channel. -/
private theorem unscale_channel {point : Gaussian} {generator : CoherentNamed} (numerator : Coefficients)
    (original : Expression.Denotation (differential (frame := frame) numerator).coefficient point generator) :
    (unscale numerator original).channel = original.channel := by rfl

/-- Transport only a proven point index of the same complete coefficient denotation. -/
private def movePoint {radicand : Coefficients} {expression : Expression radicand}
    {point replacement : Gaussian} {generator : CoherentNamed}
    (original : Expression.Denotation expression point generator) (equal : point = replacement) :
    Expression.Denotation expression replacement generator := by
  cases equal
  exact original

/-- A point-index transport retains the original channel without recomputing its coefficients. -/
private theorem movePoint_channel {radicand : Coefficients} {expression : Expression radicand}
    {point replacement : Gaussian} {generator : CoherentNamed}
    (original : Expression.Denotation expression point generator) (equal : point = replacement) :
    (movePoint original equal).channel = original.channel := by
  cases equal
  rfl

/-- Reuse the actual query pair at its original continued Point through its owned root-name readback. -/
private def sourceView (numerator table : Coefficients) (pulled : Spatial.Pullback coordinate table allowance)
    (lifted : LiftedCell first last) (input : Coordinate)
    (query : Jets.UniformObservation (reciprocalCurve (Fibre.frameCurve frame))
      (differential numerator) lifted pulled.model input)
    (sample : Point terminal.neighborhood.patch (coordinate.point input))
    (sameRoot : query.algebraic.sheetValue.value.name = sample.certificate.value.name) :
    (original : PrimitiveDenotation sample 1 numerator) ×
      NamedEquivalent original.channel.name query.algebraic.interpretation.channel.name := by
  let plain := unscale numerator query.algebraic.interpretation
  let atPoint := movePoint plain (query_point pulled lifted input query)
  have roots : NamedEquivalent sample.certificate.value.name query.algebraic.sheetValue.value.name :=
    NamedEquivalent.transport rfl sameRoot.symm (NamedEquivalent.refl _)
  let moved := atPoint.transport sample.certificate.value roots
  have compared := atPoint.transport_equivalent sample.certificate.value roots
  have same : atPoint.channel = query.algebraic.interpretation.channel :=
    (movePoint_channel plain (query_point pulled lifted input query)).trans
      (unscale_channel numerator query.algebraic.interpretation)
  exact ⟨moved, NamedEquivalent.transport rfl (congrArg CoherentNamed.name same) compared⟩

variable {input : Coordinate}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval
      (coordinate.point input))}
    {overlap : Cap.RootCoordinates.Overlap cap (coordinate.point input) pointOwner}

/-- Build one actual weighted query and derive its operational comparison from that same query's retained Point.

The source view consumes the original interpretation pair. Only its unit
scale, exact point index and owned generator readback are transported; it
performs no Point acquisition, inverse refinement or root resampling.
-/
def weightedObservation (tables : Tables retained) (cells : Pullbacks retained tables)
    (paid : Floors preparation allowance positive floor) (later : paid.2.2.val ≤ stage)
    (lifted : LiftedCell first last) (data : EndpointComparison.Data comparison overlap) :
    (query : Jets.UniformObservation (reciprocalCurve (Fibre.frameCurve frame)) (differential (-cap.polynomial))
      lifted cells.1.val.model input) ×
    NamedEquivalent query.algebraic.interpretation.channel.name (weightedChannel overlap).name := by
  let query := observe (positive := positive) retained (-cap.polynomial) tables.1.val cells.1.val
    (Tables.weighted_compiled retained tables) paid.1 lifted input data.owner.point data.inside
    (paid.weighted_le.trans later)
  have rootName := observe_root_name (positive := positive) retained (-cap.polynomial) tables.1.val cells.1.val
    (Tables.weighted_compiled retained tables) paid.1 lifted input data.owner.point data.inside
    (paid.weighted_le.trans later)
  let source := sourceView (-cap.polynomial) tables.1.val cells.1.val lifted input query data.owner.point rootName
  exact ⟨query, source.2.symm.trans (weightedEquivalent data source.1)⟩

/-- Build one actual regular-remainder query and derive its signed original channel relation internally. -/
def remainderObservation (tables : Tables retained) (cells : Pullbacks retained tables)
    (paid : Floors preparation allowance positive floor) (later : paid.2.2.val ≤ stage)
    (lifted : LiftedCell first last) (data : EndpointComparison.Data comparison overlap) :
    (query : Jets.UniformObservation (reciprocalCurve (Fibre.frameCurve frame))
      (differential ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) lifted cells.2.val.model input) ×
    NamedEquivalent query.algebraic.interpretation.channel.name (remainderChannel overlap).name := by
  let numerator := (wRemainder (parameter := parameter)) *
    HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)
  let query := observe (positive := positive) retained numerator tables.2.val cells.2.val
    (Tables.remainder_compiled retained tables) paid.2.1 lifted input data.owner.point data.inside
    (paid.regular_le.trans later)
  have rootName := observe_root_name (positive := positive) retained numerator tables.2.val cells.2.val
    (Tables.remainder_compiled retained tables) paid.2.1 lifted input data.owner.point data.inside
    (paid.regular_le.trans later)
  let source := sourceView numerator tables.2.val cells.2.val lifted input query data.owner.point rootName
  exact ⟨query, source.2.symm.trans (remainderEquivalent data source.1)⟩

end Continued

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration

end

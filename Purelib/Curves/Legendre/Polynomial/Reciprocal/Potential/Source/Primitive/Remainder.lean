module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial.Requests
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive.Requests
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # Uniform regular-remainder decay on the original physical cell

The original regular-model residual cache and the reciprocal root ceiling
give one fixed integral scale before either finite stage is chosen. The
comparison reads the actual two pullbacks and their same retained cube.
Both original boxes still require their own endpoint containments.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample (ResidualBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow quarterRadius_nonneg)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Ascending.Gaussian

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {sourceDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal sourceDifferential}
    {preparation : PotentialComparison.Preparation comparison}
    {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {index stage : Nat} {regularBox : Box}
    {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- The original regular residual cache, fixed reciprocal cube ceiling and exact physical integral scale.

No finite sample or cell stage occurs in this cache. The retained cube
ceiling uses the original reciprocal root owner; the scale also retains
the supplied physical coordinate's actual displacement.
-/
@[expose] def RemainderBounds (comparison : TerminalComparison.Data terminal sourceDifferential)
    (coordinate : Spatial.Coordinate start finish) :=
  (regular : PolynomialSample.ResidualBounds cap (regularNumerator (parameter := parameter))) ×
  (cube : {value : Coordinate // value = comparison.rootBounds.inverseUpper ^ 3}) ×
  {scale : Coordinate // scale = 2 * regular.scale * cube.val * Norm.Basic.normSq coordinate.displacement}

namespace RemainderBounds

/-- Compute the regular cache and fixed cube ceiling once before either sample stage is chosen. -/
def build (comparison : TerminalComparison.Data terminal sourceDifferential)
    (coordinate : Spatial.Coordinate start finish) : RemainderBounds comparison coordinate :=
  let regular := PolynomialSample.ResidualBounds.build cap (regularNumerator (parameter := parameter))
  let cube := comparison.rootBounds.inverseUpper ^ 3
  let scale := 2 * regular.scale * cube * Norm.Basic.normSq coordinate.displacement
  ⟨regular, ⟨cube, rfl⟩, ⟨scale, rfl⟩⟩

/-- The complete bound cache retains its original factories and exact fixed scalar combination. -/
private theorem packaged_build_factory (comparison : TerminalComparison.Data terminal sourceDifferential)
    (coordinate : Spatial.Coordinate start finish) :
    build comparison coordinate =
      (let regular := PolynomialSample.ResidualBounds.build cap (regularNumerator (parameter := parameter))
       let cube := comparison.rootBounds.inverseUpper ^ 3
       let scale := 2 * regular.scale * cube * Norm.Basic.normSq coordinate.displacement
       ⟨regular, ⟨cube, rfl⟩, ⟨scale, rfl⟩⟩ : RemainderBounds comparison coordinate) := by rfl

/-- The complete bound cache retains its original factories and exact fixed scalar combination. -/
theorem build_factory (comparison : TerminalComparison.Data terminal sourceDifferential)
    (coordinate : Spatial.Coordinate start finish) :
    build comparison coordinate =
      (let regular := PolynomialSample.ResidualBounds.build cap (regularNumerator (parameter := parameter))
       let cube := comparison.rootBounds.inverseUpper ^ 3
       let scale := 2 * regular.scale * cube * Norm.Basic.normSq coordinate.displacement
       ⟨regular, ⟨cube, rfl⟩, ⟨scale, rfl⟩⟩ : RemainderBounds comparison coordinate) :=
  packaged_build_factory comparison coordinate

variable (bounds : RemainderBounds comparison coordinate)

/-- Read the same complete regular numerator, inverse and differential-residual cache. -/
def regular : PolynomialSample.ResidualBounds cap (regularNumerator (parameter := parameter)) := bounds.1

/-- Read the retained reciprocal cube ceiling without recomputing the scalar power. -/
def cube : Coordinate := bounds.2.1.val

/-- Read the fixed physical integral scale before selecting a regular-model stage. -/
def scale : Coordinate := bounds.2.2.val

/-- The cached cube ceiling uses the original reciprocal root owner at every finite cell stage. -/
private theorem packaged_cube_eq : bounds.cube = comparison.rootBounds.inverseUpper ^ 3 := bounds.2.1.property

/-- The cached cube ceiling uses the original reciprocal root owner at every finite cell stage. -/
theorem cube_eq : bounds.cube = comparison.rootBounds.inverseUpper ^ 3 := packaged_cube_eq bounds

/-- The cached integral scale uses the same original regular cache, cube ceiling and physical displacement. -/
private theorem packaged_scale_eq : bounds.scale =
    2 * bounds.regular.scale * bounds.cube * Norm.Basic.normSq coordinate.displacement := bounds.2.2.property

/-- The cached integral scale uses the same original regular cache, cube ceiling and physical displacement. -/
theorem scale_eq : bounds.scale =
    2 * bounds.regular.scale * bounds.cube * Norm.Basic.normSq coordinate.displacement := packaged_scale_eq bounds

/-- The fixed reciprocal cube ceiling is nonnegative before either model stage is chosen. -/
theorem cube_nonnegative : 0 ≤ bounds.cube := by
  rewrite [bounds.cube_eq]
  exact Arithmetic.pow_nonneg_direct comparison.rootBounds.inverseUpper_positive.le 3

/-- The fixed physical integral scale is nonnegative before selecting a sample. -/
theorem scale_nonnegative : 0 ≤ bounds.scale := by
  rewrite [bounds.scale_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) bounds.regular.scale_nonnegative) bounds.cube_nonnegative)
    (Norm.Basic.normSq_nonneg _)

variable (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    {retained : Cell preparation.2.1 coordinate stage allowance nonnegative}
    (data : PhysicalPrimitive regular retained)

/-- The actual physical coefficient difference has its original regular-stage residual allowance. -/
theorem coefficient_le {point : Gaussian} (inside : collar.box.Contains point) :
    Norm.Basic.normSq ((regularDifference regular data).eval point) ≤ quarterRadius bounds.regular.scale index :=
  (congrArg Norm.Basic.normSq
    ((regularDifference_eval regular data point).trans (regular.physicalCoefficient_residual point).symm)).trans_le
      (regular.physicalCoefficient_residual_le bounds.regular inside)

/-- The actual two pullbacks have the fixed-scale regular-stage allowance at every original unit parameter.

Both endpoint containments are retained for each original box. The bound
uses the same finite cube at its unchanged reciprocal stage and the same
regular sample at its actual regular stage.
-/
theorem point_difference_le
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (startRegular : collar.box.Contains start) (finishRegular : collar.box.Contains finish)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval data.cell.pullback.model.polynomial ⟨input, 0⟩ -
        Evaluation.eval cells.2.val.model.polynomial ⟨input, 0⟩) ≤
      quarterRadius (bounds.regular.scale * bounds.cube) index := by
  let point := coordinate.point input
  have reciprocalInside := coordinate.point_inside startInside finishInside lower upper
  have regularInside := coordinate.point_inside startRegular finishRegular lower upper
  have coefficient := bounds.coefficient_le regular data regularInside
  have cube := (retained.cube_norm_le reciprocalInside).trans_eq bounds.cube_eq.symm
  have product := Arithmetic.mul_le_mul_direct coefficient cube (Norm.Basic.normSq_nonneg _)
    (quarterRadius_nonneg bounds.regular.scale_nonnegative index)
  have scalar := congrArg Norm.Basic.normSq (regular_point_difference regular data tables cells input)
  have value := (Norm.Basic.normSq_mul ((regularDifference regular data).eval point)
    (retained.powers.cube.eval point)).trans_le product
  exact (scalar.trans_le value).trans_eq (by
    rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1)

/-- The actual regular-remainder integral discrepancy has the fixed scale at its original regular stage.

The two finite integral tables remain independent and use the same
oriented physical coordinate. No canonical period, endpoint root join or
closed-integral conclusion is supplied as a premise.
-/
theorem integral_difference_le
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (startRegular : collar.box.Contains start) (finishRegular : collar.box.Contains finish)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) :
    Norm.Basic.normSq (data.cell.pullback.model.integralSample - cells.2.val.model.integralSample) ≤
      quarterRadius bounds.scale index := by
  have estimate := Primitive.integral_difference_le data.cell.pullback.model cells.2.val.model
    (data.cell.pullback.start_eq.trans cells.2.val.start_eq.symm)
    (data.cell.pullback.finish_eq.trans cells.2.val.finish_eq.symm)
    (quarterRadius (bounds.regular.scale * bounds.cube) index) (by
      intro input inside
      exact bounds.point_difference_le regular data startInside finishInside startRegular finishRegular
        tables cells input inside.1 inside.2)
  exact estimate.trans_eq (by
    rewrite [data.cell.pullback.displacement_eq, bounds.scale_eq,
      quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1)

/-- The same finite selection pays the actual regular sample at every retained later regular stage.

The original discrepancy bound reads the supplied sample and reciprocal
cell unchanged. Monotonicity of the retained quarter-radius Selection
pays the target at the sample's actual stage; no sample is retagged or
rebuilt and no final integral inequality is an input.
-/
theorem integral_difference_lt {floor : Nat} {target : Coordinate}
    (selection : Selection bounds.scale floor target) (later : selection.stage ≤ index)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (startRegular : collar.box.Contains start) (finishRegular : collar.box.Contains finish)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) :
    Norm.Basic.normSq (data.cell.pullback.model.integralSample - cells.2.val.model.integralSample) < target :=
  (bounds.integral_difference_le regular data startInside finishInside startRegular finishRegular tables cells).trans_lt
    (selection.later_accurate later)

/-- The fixed physical displacement and reciprocal cube give a nonnegative residual multiplier. -/
theorem selectionMultiplier_nonnegative : 0 ≤ 2 * bounds.cube * Norm.Basic.normSq coordinate.displacement :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) bounds.cube_nonnegative) (Norm.Basic.normSq_nonneg _)

/-- Present the SAME cached total scale to the generic sampler under its exact multiplier equation. -/
def selectionScale :
    {value : Coordinate // value =
      (2 * bounds.cube * Norm.Basic.normSq coordinate.displacement) * bounds.regular.scale} :=
  ⟨bounds.scale, bounds.scale_eq.trans (by ring1)⟩

/-- The scalar view consumes the original cached integral scale without recomputing its factors. -/
private theorem packaged_selectionScale_value : bounds.selectionScale.val = bounds.scale := rfl

/-- The scalar view consumes the original cached integral scale without recomputing its factors. -/
theorem selectionScale_value : bounds.selectionScale.val = bounds.scale := packaged_selectionScale_value bounds

/-- One paid regular-stage selection and the complete original sample constructed at that same stage.

The generic sampler receives the cached physical integral scale itself.
The reciprocal cell stage and any endpoint Points remain independent
inputs to the later physical comparison.
-/
@[expose] def SelectedSample (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :=
  ResidualBounds.SelectedSample bounds.regular (2 * bounds.cube * Norm.Basic.normSq coordinate.displacement)
    bounds.selectionMultiplier_nonnegative bounds.selectionScale floor target positive box

/-- Select the paid original regular stage, then construct its sample once using the retained total scale. -/
def select (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :
    SelectedSample bounds floor target positive box :=
  bounds.regular.select (2 * bounds.cube * Norm.Basic.normSq coordinate.displacement)
    bounds.selectionMultiplier_nonnegative bounds.selectionScale floor target positive box

/-- The physical sampler is the same complete generic selection/sample factory on the original cached scale. -/
private theorem packaged_select_factory (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :
    bounds.select floor target positive box =
      bounds.regular.select (2 * bounds.cube * Norm.Basic.normSq coordinate.displacement)
        bounds.selectionMultiplier_nonnegative bounds.selectionScale floor target positive box := by rfl

/-- The physical sampler is the same complete generic selection/sample factory on the original cached scale. -/
theorem select_factory (floor : Nat) (target : Coordinate) (positive : 0 < target) (box : Box) :
    bounds.select floor target positive box =
      bounds.regular.select (2 * bounds.cube * Norm.Basic.normSq coordinate.displacement)
        bounds.selectionMultiplier_nonnegative bounds.selectionScale floor target positive box :=
  packaged_select_factory bounds floor target positive box

namespace SelectedSample

variable {bounds : RemainderBounds comparison coordinate} {floor : Nat}
    {target : Coordinate} {positive : 0 < target}
variable (selected : SelectedSample bounds floor target positive regularBox)

/-- Read the SAME original finite selection, including its actual stage, fuel and paid allowance. -/
def selection : Selection bounds.selectionScale.val floor target := ResidualBounds.SelectedSample.selection selected

/-- Read the whole original polynomial sample at the SAME retained selection's stage. -/
def sample : PolynomialSample cap (regularNumerator (parameter := parameter)) selected.selection.stage regularBox :=
  ResidualBounds.SelectedSample.sample selected

/-- The actual physical integral discrepancy strictly pays the selected target with this SAME original sample.

The original reciprocal and regular endpoint containments are still
required. This conclusion compares the actual finite integrals; it does
not identify primitive constants, endpoint roots or canonical cycles.
-/
private theorem packaged_integral_difference_lt
    {retained : Cell preparation.2.1 coordinate stage allowance nonnegative}
    (data : PhysicalPrimitive selected.sample retained)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (startRegular : collar.box.Contains start) (finishRegular : collar.box.Contains finish)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) :
    Norm.Basic.normSq (data.cell.pullback.model.integralSample - cells.2.val.model.integralSample) < target := by
  have estimate := bounds.integral_difference_le selected.sample data startInside finishInside
    startRegular finishRegular tables cells
  have paid : quarterRadius bounds.selectionScale.val selected.selection.stage < target :=
    ResidualBounds.SelectedSample.accurate selected
  have cached := congrArg (fun value : Coordinate => quarterRadius value selected.selection.stage)
    bounds.selectionScale_value
  exact estimate.trans_lt (cached.symm.trans_lt paid)

/-- The actual physical integral discrepancy strictly pays the selected target with this SAME original sample. -/
theorem integral_difference_lt
    {retained : Cell preparation.2.1 coordinate stage allowance nonnegative}
    (data : PhysicalPrimitive selected.sample retained)
    (startInside : terminal.neighborhood.patch.base.box.Contains start)
    (finishInside : terminal.neighborhood.patch.base.box.Contains finish)
    (startRegular : collar.box.Contains start) (finishRegular : collar.box.Contains finish)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) :
    Norm.Basic.normSq (data.cell.pullback.model.integralSample - cells.2.val.model.integralSample) < target :=
  packaged_integral_difference_lt selected data startInside finishInside startRegular finishRegular tables cells

end SelectedSample

/-- The same checked primitive endpoint difference and actual regular integral jointly pay the full local target.

The regular sample and the original successful physical check each pay
one quarter of the target on the same retained reciprocal cell and
oriented coordinate. Both actual sample stages remain unchanged. This local
estimate does not identify primitive constants or close a root path.
-/
theorem primitive_integral_difference_lt
    {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {sourceDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal sourceDifferential}
    {preparation : PotentialComparison.Preparation comparison}
    {first last : LiftedPoint 2} {coordinate : Spatial.Coordinate first.coordinate last.coordinate}
    {regularBox : Box} {pFloor qFloor index stage : Nat} {target allowance : Coordinate}
    {allowancePositive : 0 < allowance}
    (residuals : RemainderBounds comparison coordinate)
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index regularBox)
    (selection : Selection residuals.scale pFloor (target / 4))
    (regularPaid : selection.stage ≤ index)
    {retained : Cell preparation.2.1 coordinate stage allowance allowancePositive.le}
    (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := allowancePositive) data qFloor (target / 4))
    {lifted : LiftedCell first last}
    {firstInside : terminal.neighborhood.patch.box.Contains first.coordinate}
    {lastInside : terminal.neighborhood.patch.box.Contains last.coordinate}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)}
    (checked : Checked (positive := allowancePositive) data paid lifted firstInside lastInside points)
    (firstRegular : collar.box.Contains first.coordinate) (lastRegular : collar.box.Contains last.coordinate)
    (tables : Tables retained) (cells : Integration.Pullbacks retained tables) :
    Norm.Basic.normSq (data.cell.value.eval last.coordinate -
      data.cell.value.eval first.coordinate - cells.2.val.model.integralSample) < target := by
  have primitive := checked.val.property.2.2
  have regular := integral_difference_lt
    (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (count := count) (center := center) (centerOwner := centerOwner) (terminal := terminal)
    (sourceDifferential := sourceDifferential) (comparison := comparison) (preparation := preparation)
    (start := first.coordinate) (finish := last.coordinate) (coordinate := coordinate)
    (index := index) (stage := stage) (regularBox := regularBox)
    (allowance := allowance) (nonnegative := allowancePositive.le)
    (floor := pFloor) (target := target / 4) (retained := retained)
    residuals sample data selection regularPaid
    (terminal.neighborhood.patch.box_refines.contains firstInside)
    (terminal.neighborhood.patch.box_refines.contains lastInside) firstRegular lastRegular tables cells
  exact Norm.Bounds.normSq_sub_lt_of_quarter_bounds
    (first := data.cell.value.eval last.coordinate - data.cell.value.eval first.coordinate)
    (middle := data.cell.pullback.model.integralSample)
    (last := cells.2.val.model.integralSample) (target := target) primitive regular

end RemainderBounds

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive

end

module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Comparison
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Independent polynomial and original source cells on the same covered occurrence

Both complete original model owners remain. The query-to-Point factory laws
identify the actual root names at equal affine inputs; the original uniform
integral comparison then pays both independent local allowances.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformCellCertificate)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {inside : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}

/-- The actual polynomial cell and original value-zero source cell pay their own independent local allowances.

The first certificate is built from the supplied retained polynomial model.
The second consumes the original source query. Their root relation follows
from the two exact inputs to the same original Point.acquire operation.
-/
theorem polynomial_valueZero_difference_le {polynomialFloor polynomialStage : Nat}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)} {tail : CoveredParents count remaining}
    (work : PolynomialWork (.cons patch inside tail) polynomialFloor (Specification.valueSpecification parameter 0))
    (polynomial : work.Models polynomialStage)
    (source : PreparedParent (parameter := parameter) (frame := frame) patch count floor inside targets) :
    Norm.Basic.normSq (polynomial.1.2.val.pullback.model.integralSample -
      source.preparation.cell.models.valueZero.model.integralSample) ≤
        16 * (quarterRadius 1 polynomialStage + targets.localBound) * parent.edge.pointMovement := by
  let retained := polynomial.1.2.val
  let coordinate := work.1.1.val
  let newCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 0) (liftedCell parent) retained.pullback.model :=
    retained.certificate (coordinate := coordinate) (Specification.valueSpecification_denominatorPairs parameter 0)
      (liftedCell parent) (start_inside patch count) (finish_inside patch count inside)
      (PolynomialWork.Models.points patch inside coordinate)
  let query := source.preparation.query.castCell source.preparation.cell_eq
  let oldCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 0) (liftedCell parent)
      source.preparation.models.valueZero.model :=
    ⟨fun input lower upper => (query.observe frame input lower upper).valueZero⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (newCertificate.query input lower upper).algebraic.sheetValue.value.name
        (oldCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    have first := retained.certificate_root_name (coordinate := coordinate)
      (Specification.valueSpecification_denominatorPairs parameter 0)
      (liftedCell parent) (start_inside patch count) (finish_inside patch count inside)
      (PolynomialWork.Models.points patch inside coordinate) input lower upper
    have last := query.observe_valueZero_root_name frame input lower upper
    have acquired := congrArg (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count)
        (coordinate.point input) => sample.certificate.value.name)
      (PolynomialWork.Models.points_factory patch inside coordinate input lower upper)
    have equal := ContinuedNeighborhood.Point.acquire_name_eq (patch := patch.neighborhood count)
      (coordinate.point_inside (start_inside patch count) (finish_inside patch count inside) lower upper)
      (source.preparation.models.coordinate.point_inside
        (start_inside patch count) (finish_inside patch count inside) lower upper)
      ((coordinate.point_eq input).trans (source.preparation.models.coordinate.point_eq input).symm)
    change NamedEquivalent (newCertificate.query input lower upper).algebraic.sheetValue.value.name
      (query.observe frame input lower upper).valueZero.algebraic.sheetValue.value.name
    have fromNew := first.trans acquired
    have toOld := equal.trans last.symm
    have names := fromNew.trans toOld
    exact Eq.mp (congrArg (fun name => NamedEquivalent
      (newCertificate.query input lower upper).algebraic.sheetValue.value.name name) names)
      (NamedEquivalent.refl _)
  have bounded := newCertificate.integral_difference_le oldCertificate
    (retained.pullback.start_eq.trans source.preparation.models.valueZero.start_eq.symm)
    (retained.pullback.finish_eq.trans source.preparation.models.valueZero.finish_eq.symm) roots (by
      rewrite [retained.pullback.allowance_eq, source.preparation.models.valueZero.allowance_eq]
      exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
        (quarterRadius_pos (by decide +kernel) _) targets.localBound_positive.le)
  have allowance : retained.pullback.model.localAllowance +
      source.preparation.models.valueZero.model.localAllowance =
        quarterRadius 1 polynomialStage + targets.localBound :=
    (congrArg (fun value => value + source.preparation.models.valueZero.model.localAllowance)
      retained.pullback.allowance_eq).trans
        (congrArg (fun value => quarterRadius 1 polynomialStage + value)
          source.preparation.models.valueZero.allowance_eq)
  have modelDisplacement : retained.pullback.model.displacement = coordinate.displacement :=
    retained.pullback.displacement_eq
  have displacement := (congrArg Norm.Basic.normSq modelDisplacement).trans
    (PolynomialWork.Models.movement patch inside work)
  have paid := (congrArg (fun value : Rational =>
      16 * value * Norm.Basic.normSq retained.pullback.model.displacement) allowance).trans
    (congrArg (fun value => 16 * (quarterRadius 1 polynomialStage + targets.localBound) * value) displacement)
  have samples := congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) =>
    cell.models.valueZero.model.integralSample) source.preparation.cell_eq
  have sameNorm := congrArg (fun value : Canonical =>
    Norm.Basic.normSq (retained.pullback.model.integralSample - value)) samples
  have sampleBound := bounded.trans_eq paid
  exact sameNorm.trans_le sampleBound

/-- The coordinate-weighted polynomial and independent original value-one source cell pay both allowances. -/
theorem polynomial_valueOne_difference_le {polynomialFloor polynomialStage : Nat}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)} {tail : CoveredParents count remaining}
    (work : PolynomialWork (.cons patch inside tail) polynomialFloor (Specification.valueSpecification parameter 1))
    (polynomial : work.Models polynomialStage)
    (source : PreparedParent (parameter := parameter) (frame := frame) patch count floor inside targets) :
    Norm.Basic.normSq (polynomial.1.2.val.pullback.model.integralSample -
      source.preparation.cell.models.valueOne.model.integralSample) ≤
        16 * (quarterRadius 1 polynomialStage + targets.localBound) * parent.edge.pointMovement := by
  let retained := polynomial.1.2.val
  let coordinate := work.1.1.val
  let newCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 1) (liftedCell parent) retained.pullback.model :=
    retained.certificate (coordinate := coordinate) (Specification.valueSpecification_denominatorPairs parameter 1)
      (liftedCell parent) (start_inside patch count) (finish_inside patch count inside)
      (PolynomialWork.Models.points patch inside coordinate)
  let query := source.preparation.query.castCell source.preparation.cell_eq
  let oldCertificate : UniformCellCertificate (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter 1) (liftedCell parent)
      source.preparation.models.valueOne.model :=
    ⟨fun input lower upper => (query.observe frame input lower upper).valueOne⟩
  have roots : ∀ (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1),
      NamedEquivalent (newCertificate.query input lower upper).algebraic.sheetValue.value.name
        (oldCertificate.query input lower upper).algebraic.sheetValue.value.name := by
    intro input lower upper
    have first := retained.certificate_root_name (coordinate := coordinate)
      (Specification.valueSpecification_denominatorPairs parameter 1)
      (liftedCell parent) (start_inside patch count) (finish_inside patch count inside)
      (PolynomialWork.Models.points patch inside coordinate) input lower upper
    have last := query.observe_valueOne_root_name frame input lower upper
    have acquired := congrArg (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count)
        (coordinate.point input) => sample.certificate.value.name)
      (PolynomialWork.Models.points_factory patch inside coordinate input lower upper)
    have equal := ContinuedNeighborhood.Point.acquire_name_eq (patch := patch.neighborhood count)
      (coordinate.point_inside (start_inside patch count) (finish_inside patch count inside) lower upper)
      (source.preparation.models.coordinate.point_inside
        (start_inside patch count) (finish_inside patch count inside) lower upper)
      ((coordinate.point_eq input).trans (source.preparation.models.coordinate.point_eq input).symm)
    change NamedEquivalent (newCertificate.query input lower upper).algebraic.sheetValue.value.name
      (query.observe frame input lower upper).valueOne.algebraic.sheetValue.value.name
    have fromNew := first.trans acquired
    have toOld := equal.trans last.symm
    have names := fromNew.trans toOld
    exact Eq.mp (congrArg (fun name => NamedEquivalent
      (newCertificate.query input lower upper).algebraic.sheetValue.value.name name) names)
      (NamedEquivalent.refl _)
  have bounded := newCertificate.integral_difference_le oldCertificate
    (retained.pullback.start_eq.trans source.preparation.models.valueOne.start_eq.symm)
    (retained.pullback.finish_eq.trans source.preparation.models.valueOne.finish_eq.symm) roots (by
      rewrite [retained.pullback.allowance_eq, source.preparation.models.valueOne.allowance_eq]
      exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
        (quarterRadius_pos (by decide +kernel) _) targets.localBound_positive.le)
  have allowance : retained.pullback.model.localAllowance +
      source.preparation.models.valueOne.model.localAllowance =
        quarterRadius 1 polynomialStage + targets.localBound :=
    (congrArg (fun value => value + source.preparation.models.valueOne.model.localAllowance)
      retained.pullback.allowance_eq).trans
        (congrArg (fun value => quarterRadius 1 polynomialStage + value)
          source.preparation.models.valueOne.allowance_eq)
  have modelDisplacement : retained.pullback.model.displacement = coordinate.displacement :=
    retained.pullback.displacement_eq
  have displacement := (congrArg Norm.Basic.normSq modelDisplacement).trans
    (PolynomialWork.Models.movement patch inside work)
  have paid := (congrArg (fun value : Rational =>
      16 * value * Norm.Basic.normSq retained.pullback.model.displacement) allowance).trans
    (congrArg (fun value => 16 * (quarterRadius 1 polynomialStage + targets.localBound) * value) displacement)
  have samples := congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) =>
    cell.models.valueOne.model.integralSample) source.preparation.cell_eq
  have sameNorm := congrArg (fun value : Canonical =>
    Norm.Basic.normSq (retained.pullback.model.integralSample - value)) samples
  have sampleBound := bounded.trans_eq paid
  exact sameNorm.trans_le sampleBound

/-- Both actual value numerators compare their retained polynomial cell with its independent original source channel. -/
theorem polynomial_value_difference_le {polynomialFloor polynomialStage : Nat}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)} {tail : CoveredParents count remaining}
    (coordinate : Fin 2) :
    (work : PolynomialWork (.cons patch inside tail) polynomialFloor
      (Specification.valueSpecification parameter coordinate)) →
    (polynomial : work.Models polynomialStage) →
    (source : PreparedParent (parameter := parameter) (frame := frame) patch count floor inside targets) →
    Norm.Basic.normSq (polynomial.1.2.val.pullback.model.integralSample -
      (source.preparation.cell.models.cell (Specification.Table.valueIndex coordinate)).integralSample) ≤
        16 * (quarterRadius 1 polynomialStage + targets.localBound) * parent.edge.pointMovement := by
  refine Fin.cases ?_ ?_ coordinate
  · intro work polynomial source
    exact polynomial_valueZero_difference_le (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent) (patch := patch) (count := count) (floor := floor) (inside := inside) (targets := targets)
      (polynomialFloor := polynomialFloor) (polynomialStage := polynomialStage) (remaining := remaining) (tail := tail)
      work polynomial source
  · intro next
    refine Fin.cases ?_ ?_ next
    · intro work polynomial source
      exact polynomial_valueOne_difference_le (parameter := parameter) (frame := frame) (basis := basis)
        (parent := parent) (patch := patch) (count := count) (floor := floor) (inside := inside) (targets := targets)
        (polynomialFloor := polynomialFloor) (polynomialStage := polynomialStage)
        (remaining := remaining) (tail := tail)
        work polynomial source
    · intro impossible
      exact Fin.elim0 impossible

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end

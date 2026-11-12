module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Weighted
public import Purelib.Integration.CertifiedProgram
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Cells
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells.Models
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Materialized
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells.Certificates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Certified cap programmes on the original closed parent path

A finite stage consumes one actual weighted construction and its two
original model lists. Its original uniform certificates are attached to
the GIVEN retained parent-chain path. The cached programme interface keeps
the complete joint stage result in each prepared request; it does not
claim that independently evaluating stage functions memoizes their work.
-/

public section

universe u v

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration
open Purelib.Integration.CertifiedProgram (ModelOperations CachedModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}

namespace ClosedModels

/-- One finite pair of actual uniformly certified model lists with its internally paid stage bounds.

The subtype adds only the derived finite estimates. All model, Point,
root, sheet and coefficient data remain in the two original certificate
banks on the same displayed parent-chain path.
-/
@[expose] def Stage (closed : Boundary.Data cap owner sourceDifferential)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (index : Nat) : Type 2 :=
  { retained : LiftedCells.CertifiedModels (parameter := parameter) (frame := frame)
      (collar := collar) (cap := cap) keptPath //
    Norm.Basic.normSq (PathModel.mk retained.1.1).integralSample < quarterRadius 1 index ∧
    Norm.Basic.normSq (PathModel.mk retained.1.2).integralSample < quarterRadius 1 index ∧
    (PathModel.mk retained.1.1).aggregateAllowance ≤
      movementMass closed.covered.cache.parents * quarterRadius 1 index ∧
    (PathModel.mk retained.1.2).aggregateAllowance ≤
      movementMass closed.covered.cache.parents * quarterRadius 1 index }

/-- Construct one paid pair of original model banks on a GIVEN original parent-chain path.

The actual Plan, shared P sample, sufficient q cells and endpoint payments
are constructed once by withWeightedReadings. The certificate assembly
consumes those exact Heads and the supplied path; it never calls the path
factory. Both norm and allowance estimates follow from their original
readbacks, with no requested accuracy supplied as an assumption.
-/
def buildStage (closed : Boundary.Data cap owner sourceDifferential) (values : Potentials closed.covered.bank)
    (chain : CenteredPathChain closed.covered.cache.parents
      (start := (⟨collar.box.anchor, 0⟩ : LiftedPoint 2)) (finish := ⟨collar.box.anchor, 0⟩))
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (pathEq : keptPath = chain.path) (floor pFloor : Nat) (box : Box) (index : Nat) :
    Stage (parameter := parameter) (frame := frame) closed keptPath index :=
  let target := quarterRadius 1 index
  have targetPositive : 0 < target := quarterRadius_pos (by decide +kernel) index
  withWeightedReadings (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) closed values target targetPositive floor pFloor box
    (fun errorPositive planned paths pathsFactory positive cached _endpoints common originalPaid _physicalPaid
        _endpointPaid actual _readings _sampled _compared _joints _returned _closing
        regularSmall _differenceSmall weightedSmall =>
      have pathFactory : keptPath = LiftedCells.path (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := 1)
          (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
          (errorPositive := errorPositive) (floor := floor)
          closed.covered.bank planned paths pathsFactory closed.covered.cache.chain :=
        pathEq.trans (LiftedCells.path_eq closed.covered.bank planned paths pathsFactory chain).symm
      let retained := Materialized.certifyOnPath (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
        closed.covered.cache.chain keptPath pathFactory
      have retainedFactory := Eq.refl retained
      have lists := Materialized.integral_lists_eq (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
        closed.covered.cache.chain keptPath pathFactory retained retainedFactory
      have allowances := Materialized.allowances_eq (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
        closed.covered.cache.chain keptPath pathFactory retained retainedFactory
      have weightedEq := (PathModel.mk retained.1.1).integralSample_eq_gaussianSum.trans
        (congrArg (fun rows : List Gaussian × List Gaussian => Norm.Sum.Basic.gaussianSum rows.1) lists)
      have regularEq := (PathModel.mk retained.1.2).integralSample_eq_gaussianSum.trans
        (congrArg (fun rows : List Gaussian × List Gaussian => Norm.Sum.Basic.gaussianSum rows.2) lists)
      have quarterPositive := Field.div_pos_direct targetPositive (by decide +kernel : (0 : Coordinate) < 4)
      have potentialPositive := Field.div_pos_direct quarterPositive (by decide +kernel : (0 : Coordinate) < 4)
      have quarter := Field.divide_le_self targetPositive.le (by decide +kernel : (1 : Coordinate) ≤ 4)
      have potential := Field.divide_le_self quarterPositive.le (by decide +kernel : (1 : Coordinate) ≤ 4)
      have localBound :=
        (PotentialCells.localError_le closed.covered.parentCount ((target / 4) / 4) potentialPositive.le).trans
        (potential.trans quarter)
      have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct localBound
        (movementMass_nonnegative closed.covered.cache.parents)
      ⟨retained,
        (congrArg Norm.Basic.normSq weightedEq).trans_lt weightedSmall,
        ((congrArg Norm.Basic.normSq regularEq).trans_lt regularSmall).trans_le quarter,
        (congrArg (fun pair : Coordinate × Coordinate => pair.1) allowances).trans_le paid,
        (congrArg (fun pair : Coordinate × Coordinate => pair.2) allowances).trans_le paid⟩)

/-- One cached programme model retains the actual stage index and BOTH original certified channels. -/
@[expose] def Model (closed : Boundary.Data cap owner sourceDifferential)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩) : Type 2 :=
  (index : Nat) × Stage (parameter := parameter) (frame := frame) closed keptPath index

/-- Read the weighted model's original sample and aggregate allowance from the same joint stage cache. -/
@[expose] def weightedOperations (closed : Boundary.Data cap owner sourceDifferential)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩) :
    ModelOperations (Model (parameter := parameter) (frame := frame) closed keptPath) :=
  ⟨fun retained => (PathModel.mk retained.2.val.1.1).integralSample,
    fun retained => (PathModel.mk retained.2.val.1.1).aggregateAllowance⟩

/-- Read the remainder model's original sample and aggregate allowance from the same joint stage cache. -/
@[expose] def remainderOperations (closed : Boundary.Data cap owner sourceDifferential)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩) :
    ModelOperations (Model (parameter := parameter) (frame := frame) closed keptPath) :=
  ⟨fun retained => (PathModel.mk retained.2.val.1.2).integralSample,
    fun retained => (PathModel.mk retained.2.val.1.2).aggregateAllowance⟩

/-- The original finite decay estimates provide a cached programme without changing any stage model. -/
private def cachedProgram {Carrier : Type v} (operations : ModelOperations Carrier)
    (stages : Nat → CachedModel operations) (mass : Coordinate) (massNonnegative : 0 ≤ mass)
    (allowances : ∀ index, (stages index).allowance ≤ mass * quarterRadius 1 index)
    (small : ∀ index, Norm.Basic.normSq (stages index).sample < quarterRadius 1 index) :
    CertifiedProgram.Program operations where
  stage := stages
  errorScale := mass + 4
  errorScale_nonneg :=
    (Field.zero_add 0).symm.trans_le
      (Arithmetic.add_le_add_direct massNonnegative (by decide +kernel : (0 : Coordinate) ≤ 4))
  modelAllowance_le := by
    intro index
    have scalar : mass * quarterRadius 1 index = quarterRadius mass index := by
      rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
      ring1
    have dominates : mass ≤ mass + 4 := by
      have translated := Arithmetic.add_le_add_right_direct (by decide +kernel : (0 : Coordinate) ≤ 4) mass
      exact (Field.zero_add mass).symm.trans_le (translated.trans_eq (Field.add_comm _ _))
    exact ((allowances index).trans_eq scalar).trans (quarterRadius_scale_mono dominates index)
  later_close := by
    intro earlier later order
    have laterSmall := (small later).le.trans (quarterRadius_antitone (by decide +kernel) order)
    have bound := (Norm.Bounds.normSq_sub_le_two (stages later).sample (stages earlier).sample).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct laterSmall (small earlier).le) (by decide +kernel : (0 : Coordinate) ≤ 2))
    have scalar : 2 * (quarterRadius 1 earlier + quarterRadius 1 earlier) = quarterRadius 4 earlier := by
      rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
      ring1
    have dominates : (4 : Coordinate) ≤ mass + 4 :=
      (Field.zero_add 4).symm.trans_le (Arithmetic.add_le_add_right_direct massNonnegative 4)
    exact (bound.trans_eq scalar).trans (quarterRadius_scale_mono dominates earlier)
  centerBound := 1
  centerBound_nonneg := by decide +kernel
  sample_bounded := fun index => (small index).le.trans (quarterRadius_le_scale (by decide +kernel) index)

/-- The weighted cached programme builds one actual joint stage cache per stage evaluation.

Program.prepare binds its chosen stage once, retaining the complete two
model lists and both certificate banks in its actual CachedModel. Repeated
independent calls to a stage or to prepare are separate finite work.
-/
def weightedProgram (closed : Boundary.Data cap owner sourceDifferential) (values : Potentials closed.covered.bank)
    (chain : CenteredPathChain closed.covered.cache.parents
      (start := (⟨collar.box.anchor, 0⟩ : LiftedPoint 2)) (finish := ⟨collar.box.anchor, 0⟩))
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (pathEq : keptPath = chain.path) (floor pFloor : Nat) (box : Box) :
    CertifiedProgram.Program (weightedOperations (parameter := parameter) (frame := frame) closed keptPath) :=
  let stages := fun index => CachedModel.canonical
    (operations := weightedOperations (parameter := parameter) (frame := frame) closed keptPath)
    (⟨index, buildStage (parameter := parameter) (frame := frame)
      closed values chain keptPath pathEq floor pFloor box index⟩ :
      Model (parameter := parameter) (frame := frame) closed keptPath)
  cachedProgram (weightedOperations (parameter := parameter) (frame := frame) closed keptPath)
    stages (movementMass closed.covered.cache.parents)
    (movementMass_nonnegative closed.covered.cache.parents)
    (fun index => (buildStage (parameter := parameter) (frame := frame)
      closed values chain keptPath pathEq floor pFloor box index).property.2.2.1)
    (fun index => (buildStage (parameter := parameter) (frame := frame)
      closed values chain keptPath pathEq floor pFloor box index).property.1)

/-- The remainder cached programme reads its actual channel from one joint stage construction per evaluation. -/
def remainderProgram (closed : Boundary.Data cap owner sourceDifferential) (values : Potentials closed.covered.bank)
    (chain : CenteredPathChain closed.covered.cache.parents
      (start := (⟨collar.box.anchor, 0⟩ : LiftedPoint 2)) (finish := ⟨collar.box.anchor, 0⟩))
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (pathEq : keptPath = chain.path) (floor pFloor : Nat) (box : Box) :
    CertifiedProgram.Program (remainderOperations (parameter := parameter) (frame := frame) closed keptPath) :=
  let stages := fun index => CachedModel.canonical
    (operations := remainderOperations (parameter := parameter) (frame := frame) closed keptPath)
    (⟨index, buildStage (parameter := parameter) (frame := frame)
      closed values chain keptPath pathEq floor pFloor box index⟩ :
      Model (parameter := parameter) (frame := frame) closed keptPath)
  cachedProgram (remainderOperations (parameter := parameter) (frame := frame) closed keptPath)
    stages (movementMass closed.covered.cache.parents)
    (movementMass_nonnegative closed.covered.cache.parents)
    (fun index => (buildStage (parameter := parameter) (frame := frame)
      closed values chain keptPath pathEq floor pFloor box index).property.2.2.2)
    (fun index => (buildStage (parameter := parameter) (frame := frame)
      closed values chain keptPath pathEq floor pFloor box index).property.2.1)

/-- Read actual path models from a generic cached programme while transporting only its scalar readbacks. -/
private def integral {Carrier : Type v} (operations : ModelOperations Carrier)
    (readModel : Carrier → PathModel)
    (sample : ∀ model, operations.sample model = (readModel model).integralSample)
    (allowance : ∀ model, operations.allowance model = (readModel model).aggregateAllowance)
    (program : CertifiedProgram.Program operations) : RefinementProgram where
  model := fun index => readModel (program.stage index).model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := fun index =>
    ((program.stage index).allowance_eq.trans (allowance (program.stage index).model)).symm.trans_le
      (program.modelAllowance_le index)
  later_close := by
    intro earlier later order
    have first := (program.stage later).sample_eq.trans (sample (program.stage later).model)
    have last := (program.stage earlier).sample_eq.trans (sample (program.stage earlier).model)
    have difference := congrArg₂ (fun first last : Gaussian => first - last) first.symm last.symm
    exact (Norm.Basic.normSq_eq_canonical _).symm.trans_le
      ((congrArg Norm.Basic.normSq difference).trans_le (program.later_close order))
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := fun index =>
    (Norm.Basic.normSq_eq_canonical _).symm.trans_le
      ((congrArg Norm.Basic.normSq
        ((program.stage index).sample_eq.trans (sample (program.stage index).model)).symm).trans_le
          (program.sample_bounded index))

/-- The original retained closed lifted path is the displayed path at every programme stage. -/
@[expose] def cycle
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩) :
    LiftedCycleRefinement 2 :=
  ⟨fun _ => ⟨⟨collar.box.anchor, 0⟩, keptPath⟩⟩

/-- Project the actual weighted cached programme to the original algebraically certified period interface.

The model and uniform certificate functions read the same original joint
stage carrier. Separate evaluations of these functions remain separate
finite work; a prepared cached request is the API for retaining one actual
stage's complete models and certificates together.
-/
def weightedPeriod (closed : Boundary.Data cap owner sourceDifferential)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (program : CertifiedProgram.Program
      (weightedOperations (parameter := parameter) (frame := frame) closed keptPath)) :
    Period.Jets.CertifiedPeriodProgram (reciprocalCurve (Fibre.frameCurve frame))
      (Integration.differential (-cap.polynomial))
      (cycle (parameter := parameter) (frame := frame) (collar := collar) keptPath) where
  integral := integral (weightedOperations (parameter := parameter) (frame := frame) closed keptPath)
    (fun retained => PathModel.mk retained.2.val.1.1) (fun _ => rfl) (fun _ => rfl) program
  certificates := fun index => (program.stage index).model.2.val.2.1

/-- Project the actual remainder cached programme without changing its original cells or algebraic differential. -/
def remainderPeriod (closed : Boundary.Data cap owner sourceDifferential)
    (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩)
    (program : CertifiedProgram.Program
      (remainderOperations (parameter := parameter) (frame := frame) closed keptPath)) :
    Period.Jets.CertifiedPeriodProgram (reciprocalCurve (Fibre.frameCurve frame))
      (Integration.differential ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)))
      (cycle (parameter := parameter) (frame := frame) (collar := collar) keptPath) where
  integral := integral (remainderOperations (parameter := parameter) (frame := frame) closed keptPath)
    (fun retained => PathModel.mk retained.2.val.1.2) (fun _ => rfl) (fun _ => rfl) program
  certificates := fun index => (program.stage index).model.2.val.2.2

/-- Construct both actual certified cap programmes on one retained original parent-chain path.

Only the original parent records construct the computational chain. The
Nonempty witness is used by that original constructor solely for erased
endpoint identities. The path is retained outside both stage functions;
each stage constructs its genuine requests and sampled integrands afresh.
This does not identify the original cap cycle with a canonical A/B cycle.
-/
def withPrograms (closed : Boundary.Data cap owner sourceDifferential) (values : Potentials closed.covered.bank)
    (floor pFloor : Nat) (box : Box) {Result : Type u}
    (consume :
      (chain : CenteredPathChain closed.covered.cache.parents
        (start := (⟨collar.box.anchor, 0⟩ : LiftedPoint 2)) (finish := ⟨collar.box.anchor, 0⟩)) →
      chain = CenteredPathChain.ofParents closed.covered.cache.parents closed.covered.cache.chain →
      (keptPath : LiftedPath 2 (⟨collar.box.anchor, 0⟩ : LiftedPoint 2) ⟨collar.box.anchor, 0⟩) →
      keptPath = chain.path →
      (weighted : CertifiedProgram.Program
        (weightedOperations (parameter := parameter) (frame := frame) closed keptPath)) →
      (remainder : CertifiedProgram.Program
        (remainderOperations (parameter := parameter) (frame := frame) closed keptPath)) →
      (weightedCertified : Period.Jets.CertifiedPeriodProgram (reciprocalCurve (Fibre.frameCurve frame))
        (Integration.differential (-cap.polynomial))
        (cycle (parameter := parameter) (frame := frame) (collar := collar) keptPath)) →
      weightedCertified = weightedPeriod (parameter := parameter) (frame := frame) closed keptPath weighted →
      (remainderCertified : Period.Jets.CertifiedPeriodProgram (reciprocalCurve (Fibre.frameCurve frame))
        (Integration.differential ((wRemainder (parameter := parameter)) *
          HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)))
        (cycle (parameter := parameter) (frame := frame) (collar := collar) keptPath)) →
      remainderCertified = remainderPeriod (parameter := parameter) (frame := frame) closed keptPath remainder →
      Result) : Result :=
  let chain := CenteredPathChain.ofParents closed.covered.cache.parents closed.covered.cache.chain
  let keptPath := chain.path
  let weighted := weightedProgram (parameter := parameter) (frame := frame)
    closed values chain keptPath rfl floor pFloor box
  let remainder := remainderProgram (parameter := parameter) (frame := frame)
    closed values chain keptPath rfl floor pFloor box
  let weightedCertified := weightedPeriod (parameter := parameter) (frame := frame) closed keptPath weighted
  let remainderCertified := remainderPeriod (parameter := parameter) (frame := frame) closed keptPath remainder
  consume chain rfl keptPath rfl weighted remainder weightedCertified rfl remainderCertified rfl

end ClosedModels

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end

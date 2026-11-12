module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Centered
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
import Purelib.Riemann.Integration.PreparedCoveredParentLists
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Program.Comparison

/-! # Both ordinary Legendre value numerators on one retained canonical cycle

The actual covered root-closed spine is retained. Polynomial dx/y and x dx/y
programmes are constructed on that same spine with their own original paid
requests and complete polynomial caches. The old holomorphic dx/y programme
remains an independent input, and its agreement is derived through the
original source programme and finite controlled primitive comparison.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_recast)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedCoveredParentLists
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}

/-- The once-retained recast parent/chain pair and the SAME original cover transported by its list-factory equation. -/
@[expose] def PolynomialSpine (walk : PeriodWalk grid base owner source) : Type _ :=
  (kept : { value : CenteredPathChain.Recast (PeriodMatrix.standardDifferential (0 : Fin 1))
      walk.initial.state.parents walk.initial.state.start walk.initial.state.start //
    value = walk.initialChain.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) }) ×
  { covered : UniformPreparedMesh.CoveredParents 1 kept.val.1.val //
    covered = Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) kept.val.1.property.symm)
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) }

namespace PolynomialSpine

variable {walk : PeriodWalk grid base owner source}

/-- Read the actual retained recast parents rather than another map of the original list. -/
@[expose] def parents (spine : PolynomialSpine walk) := spine.1.val.1.val

/-- The retained parent cache is the complete original existing recast factory. -/
theorem parents_eq (spine : PolynomialSpine walk) : spine.parents =
    walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))) :=
  spine.1.val.1.property

/-- Read the actual centered chain sharing those exact retained recast parent values. -/
@[expose] def chain (spine : PolynomialSpine walk) : CenteredPathChain spine.parents
    (start := walk.initial.state.start) (finish := walk.initial.state.start) := spine.1.val.2

/-- Read the same actual retained cover after its exact derived parent-index transport. -/
@[expose] def covered (spine : PolynomialSpine walk) : UniformPreparedMesh.CoveredParents 1 spine.parents :=
  spine.2.val

/-- The exact two cover-index transports cancel on the whole original covered cache. -/
private theorem cover_roundtrip {first last : List (CenteredEdge
      (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : first = last) (covered : UniformPreparedMesh.CoveredParents 1 last) :
    Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) same)
      (Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) same.symm) covered) = covered := by
  cases same
  rfl

/-- The whole supplied cover is exactly the original cover factory after its derived original-list index view. -/
theorem covered_factory (spine : PolynomialSpine walk) :
    Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) spine.parents_eq) spine.covered =
      CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered :=
  (congrArg (fun value => Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) spine.parents_eq) value)
    spine.2.property).trans (cover_roundtrip spine.parents_eq _)

/-- The actual retained centered chain follows the original whole closed lifted path. -/
private theorem packaged_chain_path (spine : PolynomialSpine walk) :
    spine.chain.path = (walk.initial.state.closedLift walk.initial.closed).path := by
  change spine.1.val.2.path = _
  rewrite [spine.1.property]
  exact (walk.initialChain.path_recast (PeriodMatrix.standardDifferential (0 : Fin 1))).trans
    walk.initialChain_path

/-- The actual retained centered chain follows the original whole closed lifted path. -/
theorem chain_path (spine : PolynomialSpine walk) :
    spine.chain.path = (walk.initial.state.closedLift walk.initial.closed).path := packaged_chain_path spine

end PolynomialSpine

/-- Materialize the shared recast spine and cover ONCE before either value or stage factory is constructed. -/
def polynomialSpine (walk : PeriodWalk grid base owner source) : PolynomialSpine walk :=
  let initial := walk.initialChain
  let kept := initial.recast (PeriodMatrix.standardDifferential (0 : Fin 1))
  let originalCover := CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered
  let covered := Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) kept.1.property.symm) originalCover
  ⟨⟨kept, rfl⟩, ⟨covered, rfl⟩⟩

/-- The whole spine factory retains the same original centered extraction, shared recast and exact cover transport. -/
private theorem packaged_polynomialSpine_factory (walk : PeriodWalk grid base owner source) :
    polynomialSpine walk =
      let initial := walk.initialChain
      let kept := initial.recast (PeriodMatrix.standardDifferential (0 : Fin 1))
      let originalCover := CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered
      let covered := Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) kept.1.property.symm) originalCover
      ⟨⟨kept, rfl⟩, ⟨covered, rfl⟩⟩ := by rfl

/-- The whole spine factory retains the same original centered extraction, shared recast and exact cover transport. -/
theorem polynomialSpine_factory (walk : PeriodWalk grid base owner source) :
    polynomialSpine walk =
      let initial := walk.initialChain
      let kept := initial.recast (PeriodMatrix.standardDifferential (0 : Fin 1))
      let originalCover := CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered
      let covered := Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) kept.1.property.symm) originalCover
      ⟨⟨kept, rfl⟩, ⟨covered, rfl⟩⟩ := packaged_polynomialSpine_factory walk

/-- One actual numerator's work and certified programme, indexed by the SAME retained shared spine. -/
@[expose] def PolynomialValue (walk : PeriodWalk grid base owner source) (spine : PolynomialSpine walk)
    (floor : Nat) (coordinate : Fin 2) : Type _ :=
  (work : PolynomialWork spine.covered floor (Jets.Specification.valueSpecification parameter coordinate)) ×
  { program : CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Jets.Specification.valueSpecification parameter coordinate)
      ⟨fun _ => ⟨walk.initial.state.start, spine.chain.path⟩⟩ //
    program = PolynomialWork.fromWork spine.chain work
      (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate) }

/-- Construct dx/y or x dx/y on the actual already retained spine without another recast or cover factory. -/
def polynomialValue (walk : PeriodWalk grid base owner source) (spine : PolynomialSpine walk)
    (floor : Nat) (coordinate : Fin 2) : PolynomialValue walk spine floor coordinate :=
  let work := PolynomialWork.build spine.covered floor (Jets.Specification.valueSpecification parameter coordinate)
  let program := PolynomialWork.fromWork spine.chain work
    (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate)
  ⟨work, ⟨program, rfl⟩⟩

/-- The entire numerator programme consumes the same retained spine before one original work/programme factory. -/
private theorem packaged_polynomialValue_factory (walk : PeriodWalk grid base owner source)
    (spine : PolynomialSpine walk) (floor : Nat) (coordinate : Fin 2) : polynomialValue walk spine floor coordinate =
  let work := PolynomialWork.build spine.covered floor (Jets.Specification.valueSpecification parameter coordinate)
  let program := PolynomialWork.fromWork spine.chain work
    (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate)
  ⟨work, ⟨program, rfl⟩⟩ := by rfl

/-- The entire numerator programme consumes the same retained spine before one original work/programme factory. -/
theorem polynomialValue_factory (walk : PeriodWalk grid base owner source)
    (spine : PolynomialSpine walk) (floor : Nat) (coordinate : Fin 2) : polynomialValue walk spine floor coordinate =
  let work := PolynomialWork.build spine.covered floor (Jets.Specification.valueSpecification parameter coordinate)
  let program := PolynomialWork.fromWork spine.chain work
    (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate)
  ⟨work, ⟨program, rfl⟩⟩ := packaged_polynomialValue_factory walk spine floor coordinate

/-- Every stage reads its actual ordered polynomial cells from the same retained work, parent list and cover. -/
theorem polynomialValue_model (walk : PeriodWalk grid base owner source) {spine : PolynomialSpine walk}
    {floor : Nat} {coordinate : Fin 2} (retained : PolynomialValue walk spine floor coordinate) (stage : Nat) :
    retained.2.val.integral.model stage = PolynomialWork.model retained.1 retained.1.models stage := by
  rewrite [retained.2.property, PolynomialWork.fromWork_integral, PolynomialWork.program_model]
  rfl

/-- Both original value numerators retain E=32G from the original canonical movement mass. -/
theorem polynomialValue_errorScale (walk : PeriodWalk grid base owner source) {spine : PolynomialSpine walk}
    {floor : Nat} {coordinate : Fin 2} (retained : PolynomialValue walk spine floor coordinate) :
    retained.2.val.integral.errorScale =
      32 * movementMass walk.initial.state.parents := by
  rewrite [retained.2.property, PolynomialWork.fromWork_integral, PolynomialWork.program_errorScale]
  exact congrArg (32 * ·) ((congrArg movementMass
    spine.parents_eq).trans (movementMass_recast
      (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.initial.state.parents))

/-- Each actual value numerator agrees with the original independently prepared source programme on its SAME spine.

Both the unit numerator and coordinate numerator use their original Fin-two
specifications. The source family executes only its original preparation on
the retained cover; finite programme comparison pays all later requests.
-/
def polynomialValue_sourceEquivalent (walk : PeriodWalk grid base owner source) {spine : PolynomialSpine walk}
    {floor : Nat} {coordinate : Fin 2} (retained : PolynomialValue walk spine floor coordinate) :
    NamedEquivalent retained.2.val.integral.output.name
      (PreparedParents.certified spine.covered spine.chain
        (fun stage => Jets.Source.Cell.prepareCovered (parameter := parameter) (frame := frame) spine.covered floor
          (CellEndpoints.Targets.build spine.chain.path stage))
        (Jets.Specification.Table.valueIndex coordinate)).integral.output.name := by
  have factory := (congrArg (fun value => value.integral) retained.2.property).trans
    (PolynomialWork.fromWork_integral spine.chain retained.1
      (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate))
  exact PreparedParents.polynomial_outputEquivalent (parameter := parameter) (frame := frame)
    spine.covered spine.chain coordinate retained.1 retained.1.models
    (fun stage => Jets.Source.Cell.prepareCovered (parameter := parameter) (frame := frame) spine.covered floor
      (CellEndpoints.Targets.build spine.chain.path stage)) retained.2.val.integral factory

/-- Compare an actual polynomial programme after the exact original-list cover index transport.

Only dependent indices move. The actual cover, prepared source bank and
polynomial programme remain supplied caches, and every source preparation
starts from that retained cover instead of another covering factory.
-/
private def polynomialZero_originalEquivalent (walk : PeriodWalk grid base owner source)
    (parents : List (CenteredEdge (Fibre.frameCurve frame)
      (PeriodMatrix.standardDifferential (0 : Fin 1))))
    (same : parents = walk.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
    (covered : UniformPreparedMesh.CoveredParents 1 parents)
    (covered_eq : Eq.mp (congrArg (UniformPreparedMesh.CoveredParents 1) same) covered =
      CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
    (chain : CenteredPathChain parents (start := walk.initial.state.start) (finish := walk.initial.state.start))
    (floor : Nat) (work : PolynomialWork covered floor (Jets.Specification.valueSpecification parameter 0))
    (actual : RefinementProgram)
    (factory : actual = PolynomialWork.program work work.models
      (Jets.Specification.valueSpecification_denominatorPairs parameter 0)) :
    NamedEquivalent actual.output.name (walk.program 0).integral.output.name := by
  cases same
  let prepared := fun stage =>
    Jets.Source.Cell.prepareCovered (parameter := parameter) (frame := frame) covered floor
      (CellEndpoints.Targets.build chain.path stage)
  let originalPrepared := fun stage => (prepared stage).castCovered covered_eq
  have first := PreparedParents.polynomial_outputEquivalent (parameter := parameter) (frame := frame)
    covered chain 0 work work.models prepared actual factory
  have transported := Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_eq
    (PreparedParents.certified covered chain prepared 0).integral
    (PreparedParents.certified
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      chain originalPrepared 0).integral (by
        intro stage
        have left := PreparedParents.certified_cells covered chain prepared 0 stage
        have right := PreparedParents.certified_cells
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          chain originalPrepared 0 stage
        have middle := congrArg (fun source : Jets.Source.Path parameter chain.path =>
          (PathModel.mk (source.cells 0)).integralSample) ((prepared stage).sources_castCovered covered_eq chain)
        exact (congrArg (fun cells => (PathModel.mk cells).integralSample)
          left).trans (middle.symm.trans
            (congrArg (fun cells => (PathModel.mk cells).integralSample)
              right).symm))
  have last := walk.valueZero_outputEquivalent (parameter := parameter) (frame := frame) chain originalPrepared
  exact first.trans (transported.trans last)

/-- Derive polynomial dx/y agreement with the actual independently retained old holomorphic programme.

The extra equality is precisely that old programme's factory certificate,
not a desired period or name relation. Both output owners stay original.
-/
def polynomialValueZero_outputEquivalent (walk : PeriodWalk grid base owner source)
    {spine : PolynomialSpine walk} {floor : Nat} (retained : PolynomialValue walk spine floor 0)
    (old : { value : Basis.CertifiedPeriodProgram (Fibre.frameCurve frame)
      (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.cycle // value = walk.program 0 }) :
    NamedEquivalent retained.2.val.integral.output.name old.val.integral.output.name := by
  have factory := (congrArg (fun value => value.integral) retained.2.property).trans
    (PolynomialWork.fromWork_integral spine.chain retained.1
      (Jets.Specification.valueSpecification_denominatorPairs parameter 0))
  have original := polynomialZero_originalEquivalent walk spine.parents spine.parents_eq spine.covered
    spine.covered_factory spine.chain floor retained.1 retained.2.val.integral factory
  exact Eq.mp (congrArg (fun value => NamedEquivalent retained.2.val.integral.output.name value)
    (congrArg (fun value => value.integral.output.name) old.property).symm) original

/-- The shared actual recast spine, both independently paid value numerators and old holomorphic dx/y input. -/
@[expose] def PolynomialValues (walk : PeriodWalk grid base owner source) (floor : Nat) : Type _ :=
  (spine : PolynomialSpine walk) × PolynomialValue walk spine floor 0 × PolynomialValue walk spine floor 1 ×
  { old : Basis.CertifiedPeriodProgram (Fibre.frameCurve frame)
    (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.cycle // old = walk.program 0 }

/-- Construct both value numerators after the one shared spine, retaining the old dx/y programme separately. -/
def polynomialValues (walk : PeriodWalk grid base owner source) (floor : Nat) : PolynomialValues walk floor :=
  let spine := walk.polynomialSpine
  let first := walk.polynomialValue spine floor 0
  let second := walk.polynomialValue spine floor 1
  let old := walk.program 0
  ⟨spine, first, second, ⟨old, rfl⟩⟩

/-- The complete two-value factory retains the one shared spine, both actual numerator programmes and old dx/y owner. -/
private theorem packaged_polynomialValues_factory (walk : PeriodWalk grid base owner source) (floor : Nat) :
    walk.polynomialValues floor =
      let spine := walk.polynomialSpine
      let first := walk.polynomialValue spine floor 0
      let second := walk.polynomialValue spine floor 1
      let old := walk.program 0
      ⟨spine, first, second, ⟨old, rfl⟩⟩ := by rfl

/-- The complete two-value factory retains the one shared spine, both actual numerator programmes and old dx/y owner. -/
theorem polynomialValues_factory (walk : PeriodWalk grid base owner source) (floor : Nat) :
    walk.polynomialValues floor =
      let spine := walk.polynomialSpine
      let first := walk.polynomialValue spine floor 0
      let second := walk.polynomialValue spine floor 1
      let old := walk.program 0
      ⟨spine, first, second, ⟨old, rfl⟩⟩ := packaged_polynomialValues_factory walk floor

namespace PolynomialValues

/-- Read the original retained value programme at its genuine numerator coordinate, without another construction.

The finite dependent eliminator selects only the given numerator-1 or
numerator-x cache on the SAME retained spine. The geometric differential
index and actual model/work floors are unchanged.
-/
@[expose] def value {walk : PeriodWalk grid base owner source} {floor : Nat}
    (retained : PolynomialValues walk floor) (coordinate : Fin 2) :
    PolynomialValue walk retained.1 floor coordinate :=
  Fin.cases retained.2.1
    (fun following : Fin 1 => Fin.cases retained.2.2.1 (fun empty : Fin 0 => Fin.elim0 empty) following)
    coordinate

/-- Coordinate zero reads the SAME original unit-numerator cache. -/
theorem value_zero {walk : PeriodWalk grid base owner source} {floor : Nat}
    (retained : PolynomialValues walk floor) : retained.value 0 = retained.2.1 := rfl

/-- Coordinate one reads the SAME original full x-numerator cache. -/
theorem value_one {walk : PeriodWalk grid base owner source} {floor : Nat}
    (retained : PolynomialValues walk floor) : retained.value 1 = retained.2.2.1 := rfl

end PolynomialValues

/-- The actual retained pair's first polynomial output agrees with its independently stored old dx/y programme. -/
def polynomialValues_valueZero_equivalent (walk : PeriodWalk grid base owner source) {floor : Nat}
    (retained : PolynomialValues walk floor) :
    NamedEquivalent retained.2.1.2.val.integral.output.name retained.2.2.2.val.integral.output.name :=
  walk.polynomialValueZero_outputEquivalent retained.2.1 retained.2.2.2

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end

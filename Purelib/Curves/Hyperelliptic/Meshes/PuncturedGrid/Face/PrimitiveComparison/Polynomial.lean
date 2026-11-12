module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Selection
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Queries
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Tactic.Ring

/-! # Retained source observations compared with actual polynomial row models

The row's original contained trace and exact retained centered-data factory
derive its queried Point's face Entry. Both actual Point owners then use
one new common comparison acquisition and its retained same-bank selector.
The full ordinary numerator and both old model allowances remain unchanged.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_pos)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached ParentReached)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (Acquisition)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian.Evaluation (eval)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName_eq_of_heq)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {faceModels : FaceModels frames face}
    {basis : Differential genus} {rowSheet : Fin 2} {start finish : Canonical}
    {ambient : Geometry.Rational.Box} {path : ClearPath curve.polynomial ambient start finish}
    {initial : Owner (curve.polynomial.eval start)} (traced : TracedPath path initial)
    (contained : InBox face.cell.box path) (entered : Entry faceModels start initial)
    (data : CenteredPathChain.PreparedPathCenteredData curve basis rowSheet start finish)
    (dataFactory : data = CenteredPathChain.ofPreparedPath curve basis rowSheet traced.prepared)
    {count floor stage : Nat} {differential : OddPowerDifferential curve.polynomial}
    {covered : CoveredParents count data.parents} {work : PolynomialWork covered floor differential}
    (retained : work.Models stage) (ordinary : differential.denominatorPairs = 0)
    (index : Fin data.parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : PolynomialWork.Models.RootedQuery retained ordinary index input inside)

include traced contained dataFactory in
/-- The actual row lineage reaches this exact retained numerical model parent and its bounded direct queries. -/
private theorem parent_reached : ParentReached face.cell.box (faceModels.frame.owners entered.sheet)
    (data.parents[index.val]'index.isLt) := by
  have all := (PreparedFaceTracePrefixes.lineage_reached
    face.clearance basis rowSheet traced.lineage contained entered.reached).1
  have parentsEq := congrArg (fun value :
    CenteredPathChain.PreparedPathCenteredData curve basis rowSheet start finish => value.parents) dataFactory
  have member : (data.parents[index.val]'index.isLt) ∈
      (CenteredPathChain.ofPreparedPath curve basis rowSheet traced.prepared).parents :=
    Eq.mp (congrArg (fun values : List (CenteredEdge curve basis) =>
      (data.parents[index.val]'index.isLt) ∈ values) parentsEq) (List.getElem_mem index.isLt)
  exact all _ member

/-- The SAME given direct Query and original patch bridge reach the actual retained numerical Point. -/
private theorem sample_reached (reached : ParentReached face.cell.box (faceModels.frame.owners entered.sheet)
    (data.parents[index.val]'index.isLt)) :
    Reached face.cell.box (faceModels.frame.owners entered.sheet) queried.sample.owner := by
  let parent := data.parents[index.val]'index.isLt
  have raw := Eq.mpr (congrArg (fun owner : Owner (curve.polynomial.eval
      (parent.edge.segment.pointAt
        (Riemann.Branches.PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request input))) =>
      Reached face.cell.box (faceModels.frame.owners entered.sheet) owner) queried.direct.direct_eq)
    (reached.query_reached input inside)
  have physical := raw.castFinish
    (Riemann.Branches.PreparedSheetContinuation.pointAt_parameterAt parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.request input)
    (castOwnerParameter_heq (parent.edge.directQueryParameter_eq input) queried.direct.direct).symm
  let pointEq := PolynomialWork.Models.coordinate_point (work := work) index input
  let target := castOwnerParameter (congrArg curve.polynomial.eval pointEq) queried.sample.owner
  have targetName : ownerName target = ownerName queried.sample.owner :=
    ownerName_eq_of_heq (congrArg curve.polynomial.eval pointEq).symm
      (castOwnerParameter_heq (congrArg curve.polynomial.eval pointEq) queried.sample.owner)
  let roots := NamedEquivalent.transport rfl targetName.symm
    (NamedEquivalent.transport rfl queried.root_name queried.roots)
  exact (physical.append (Entries.Reached.ofEquivalent roots)).castFinish pointEq.symm
    (castOwnerParameter_heq (congrArg curve.polynomial.eval pointEq) queried.sample.owner)

include traced contained dataFactory in
/-- Construct the actual row-query Point Entry from the original trace, lineage and same given rooted query.

The nominal model occurrence and whole centered-data factory retain the
original prepared parent. No preparation, query, numerical Point, selector
or observation is executed to construct this Entry view.
-/
def polynomialEntry : Entry faceModels ((work.entry index).1.val.point input) queried.sample.owner :=
  ⟨entered.sheet, sample_reached (entered := entered) (data := data) (retained := retained)
    (ordinary := ordinary) (index := index) (input := input) (inside := inside) queried
    (parent_reached traced contained entered data dataFactory index)⟩

/-- The actual row-query Entry retains the original entered face sheet. -/
theorem polynomialEntry_sheet : (polynomialEntry traced contained entered data dataFactory
    retained ordinary index input inside queried).sheet = entered.sheet := by
  unfold polynomialEntry
  rfl

section Source

variable {sourceStart sourceFinish : LiftedPoint 2} {sourceLift : LiftedCell sourceStart sourceFinish}
    {sourceCell : CellModel} (source : UniformObservation curve differential sourceLift sourceCell input)
    {sourceCount : Nat} {sourcePatch : ContinuedNeighborhood curve.polynomial sourceCount}
    (sourcePoint : ContinuedNeighborhood.Point sourcePatch source.algebraic.point)
    (sourceEntry : Entry faceModels source.algebraic.point sourcePoint.owner)
    (sourceRoots : NamedEquivalent (ownerName sourcePoint.owner) source.algebraic.sheetValue.value.name)

/-- Both original source endpoints derive the same actual queried numerical row point. -/
private theorem source_point
    (first : sourceCell.start = (polynomialStart (data.parents[index.val]'index.isLt)).coordinate)
    (last : sourceCell.finish = (polynomialFinish (data.parents[index.val]'index.isLt)).coordinate) :
    source.algebraic.point = (work.entry index).1.val.point input := by
  have old := source.algebraic.point_eq.trans
    ((sourceCell.observationPoint_eq source.observation).trans (congrArg sourceCell.point source.parameter_eq))
  have same : sourceCell.point input = (work.entry index).1.val.point input := by
    unfold CellModel.point CellModel.displacement Spatial.Coordinate.point
    rewrite [first, last, (work.entry index).1.val.displacement_eq]
    exact congrArg (fun movement : Canonical =>
      (polynomialStart (data.parents[index.val]'index.isLt)).coordinate + movement)
      (Data.Gaussian.Scale.scalar_mul_eq_scale input
        ((polynomialFinish (data.parents[index.val]'index.isLt)).coordinate -
          (polynomialStart (data.parents[index.val]'index.isLt)).coordinate))
  exact old.trans same

/-- Exact point transport preserves reachability of the SAME original Point Owner. -/
private theorem castPoint_reached {first last : Canonical}
    {patch : ContinuedNeighborhood curve.polynomial count} (equal : first = last)
    (sample : ContinuedNeighborhood.Point patch last)
    (reached : Reached face.cell.box (faceModels.frame.owners entered.sheet) sample.owner) :
    Reached face.cell.box (faceModels.frame.owners entered.sheet)
      (ContinuedNeighborhood.Point.castPoint equal sample).owner := by
  cases equal
  exact reached

/-- The cached reading and residual recover the SAME original polynomial value without evaluating its table again. -/
private theorem cached_value {first last : LiftedPoint 2} {lift : LiftedCell first last}
    {cell : CellModel} {time : Rational} (observed : UniformObservation curve differential lift cell time) :
    observed.observation.integrandReading - observed.observation.error = eval cell.polynomial ⟨time, 0⟩ := by
  have original := (congrArg (fun value : Rational => observed.observation.integrandReading -
    eval cell.polynomial ⟨value, 0⟩) observed.parameter_eq).symm.trans observed.observation.decomposition
  rewrite [← original]
  ring1

/-- The genuine source/row Owners, retained comparison selections and derived original polynomial discrepancy.

The source observation and row query remain input owners. All new finite
comparison caches, their exact factories and actual operational relation
are forwarded. A point equality only reindexes the same whole row Point;
its real Entry and selector evidence supply the signed root comparison.
-/
@[expose] def PolynomialConsumer (Result : Type u) :=
  (samePoint : source.algebraic.point = (work.entry index).1.val.point input) →
  (rowEntry : Entry faceModels ((work.entry index).1.val.point input) queried.sample.owner) →
  rowEntry.sheet = entered.sheet →
  (mapped : ContinuedNeighborhood.Point ((covered.entry index).val.neighborhood count) source.algebraic.point) →
  (mappedFactory : mapped = ContinuedNeighborhood.Point.castPoint samePoint queried.sample) →
  (mappedEntry : Entry faceModels source.algebraic.point mapped.owner) →
  mappedEntry.sheet = entered.sheet →
  (admitted : face.cell.box.Contains source.algebraic.point) →
  (acquired : Acquisition faceModels admitted sourcePoint.owner) →
  acquired = Acquisition.build faceModels admitted sourcePoint.owner →
  (selected : Acquisition faceModels admitted mapped.owner) →
  (selectedFactory : selected = acquired.selectOwner mapped.owner) →
  (same : mappedEntry.sheet = acquired.entry.sheet) →
  (compared : NamedEquivalent (ownerName mapped.owner) (ownerName sourcePoint.owner)) →
  compared = acquired.equivalentOfEntry mapped.owner selected selectedFactory mappedEntry same →
  (roots : NamedEquivalent source.algebraic.sheetValue.value.name queried.observed.algebraic.sheetValue.value.name) →
  (residual : Canonical) →
  residual = (source.observation.integrandReading - source.observation.error) -
    (queried.observed.observation.integrandReading - queried.observed.observation.error) →
  residual = eval sourceCell.polynomial ⟨input, 0⟩ -
    eval (retained.entry index).2.val.pullback.model.polynomial ⟨input, 0⟩ →
  (ceiling : Rational) →
  ceiling = 8 * (sourceCell.localAllowance + (retained.entry index).2.val.pullback.model.localAllowance) →
  normSq residual ≤ ceiling → Result

/-- Compare the actual restricted source observation with the original retained ordinary polynomial row model.

The existing row-data factory and its contained trace derive the queried
Entry. Both source endpoint laws derive geometric incidence internally.
One new common acquisition and one same-bank selection execute before the
root comparison; both original numerical observations are retained. Their
existing uniform candidate bounds derive the eightfold discrepancy using
both literal allowances. No desired root relation or closeness is an input.
-/
def withPolynomialComparison
    (first : sourceCell.start = (polynomialStart (data.parents[index.val]'index.isLt)).coordinate)
    (last : sourceCell.finish = (polynomialFinish (data.parents[index.val]'index.isLt)).coordinate)
    (lineage : entered.sheet = sourceEntry.sheet) {Result : Type u}
    (consume : PolynomialConsumer (entered := entered) (data := data) (retained := retained) (ordinary := ordinary)
      (index := index) (input := input) (inside := inside) queried source sourcePoint Result) : Result := by
  have samePoint := source_point (data := data) (work := work) (index := index) (input := input) source
    first last
  let rowEntry := polynomialEntry traced contained entered data dataFactory retained ordinary index input inside queried
  let mapped := ContinuedNeighborhood.Point.castPoint samePoint queried.sample
  let mappedEntry : Entry faceModels source.algebraic.point mapped.owner :=
    ⟨entered.sheet, castPoint_reached (entered := entered) samePoint queried.sample rowEntry.reached⟩
  have reached := parent_reached traced contained entered data dataFactory index
  have firstInside := Eq.mp (congrArg face.cell.box.Contains
    (data.parents[index.val]'index.isLt).edge.point_zero) reached.first_inside
  have lastInside := Eq.mp (congrArg face.cell.box.Contains
    (data.parents[index.val]'index.isLt).edge.point_one) reached.last_inside
  have insideRow := (work.entry index).1.val.point_inside firstInside lastInside inside.1 inside.2
  have admitted := Eq.mpr (congrArg face.cell.box.Contains samePoint) insideRow
  let acquired := Acquisition.build faceModels admitted sourcePoint.owner
  let selected := acquired.selectOwner mapped.owner
  have same : mappedEntry.sheet = acquired.entry.sheet :=
    lineage.trans (sourceEntry.sheet_unique acquired.entry admitted)
  let compared := acquired.equivalentOfEntry mapped.owner selected rfl mappedEntry same
  have mappedName : ownerName mapped.owner = ownerName queried.sample.owner :=
    ContinuedNeighborhood.Point.castPoint_name samePoint queried.sample
  let roots := sourceRoots.symm.trans
    (NamedEquivalent.transport rfl (mappedName.trans queried.root_name.symm) compared.symm)
  have positive : 0 < sourceCell.localAllowance + (retained.entry index).2.val.pullback.model.localAllowance :=
    Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct sourceCell.localAllowance_nonneg
      (Eq.mpr (congrArg (fun allowance : Rational => 0 < allowance)
        (retained.entry index).2.val.pullback.allowance_eq) (quarterRadius_pos (by decide +kernel) stage))
  have bounded := source.polynomial_difference_le queried.observed
    (samePoint.trans queried.point_eq.symm) roots positive
  let residual := (source.observation.integrandReading - source.observation.error) -
    (queried.observed.observation.integrandReading - queried.observed.observation.error)
  have residualEq : residual = eval sourceCell.polynomial ⟨input, 0⟩ -
      eval (retained.entry index).2.val.pullback.model.polynomial ⟨input, 0⟩ :=
    congrArg₂ (fun first last : Canonical => first - last) (cached_value source) (cached_value queried.observed)
  let ceiling := 8 * (sourceCell.localAllowance + (retained.entry index).2.val.pullback.model.localAllowance)
  have paid : normSq residual ≤ ceiling := (congrArg normSq residualEq).trans_le bounded
  exact consume samePoint rowEntry (polynomialEntry_sheet traced contained entered data dataFactory
    retained ordinary index input inside queried) mapped rfl mappedEntry rfl admitted acquired rfl selected rfl same
    compared rfl roots residual rfl residualEq ceiling rfl paid

end Source

include traced contained dataFactory in
/-- The retained same-face query evidence bounds the two actual polynomial cell integrals.

Each source answer retains its actual observation, numerical Point, face
Entry and same-source root attachment. The row answers are the original
rooted queries on their selected model. The per-query constructor derives
their cross-owner comparison internally; the finite polynomial primitive
bound then compares the unchanged integral samples with both allowances
and the original oriented displacement. No integral or cross-owner root
comparison is an input.
-/
theorem polynomial_integral_difference_le
    {sourceStart sourceFinish : LiftedPoint 2} {sourceLift : LiftedCell sourceStart sourceFinish}
    {sourceCell : CellModel} {sourceCount : Nat}
    (sourcePatch : ContinuedNeighborhood curve.polynomial sourceCount)
    (sourceQueries : ∀ (input : Rational) (_inside : 0 ≤ input ∧ input ≤ 1),
      Σ observed : UniformObservation curve differential sourceLift sourceCell input,
      Σ sample : ContinuedNeighborhood.Point sourcePatch observed.algebraic.point,
      Σ _sourceEntry : { entry : Entry faceModels observed.algebraic.point sample.owner //
        entered.sheet = entry.sheet },
      NamedEquivalent (ownerName sample.owner) observed.algebraic.sheetValue.value.name)
    (rowQueries : ∀ (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1),
      PolynomialWork.Models.RootedQuery retained ordinary index input inside)
    (first : sourceCell.start = (polynomialStart (data.parents[index.val]'index.isLt)).coordinate)
    (last : sourceCell.finish = (polynomialFinish (data.parents[index.val]'index.isLt)).coordinate) :
    normSq (sourceCell.integralSample - (retained.entry index).2.val.pullback.model.integralSample) ≤
      16 * (sourceCell.localAllowance + (retained.entry index).2.val.pullback.model.localAllowance) *
        normSq sourceCell.displacement := by
  have firstEq := first.trans (retained.entry index).2.val.pullback.start_eq.symm
  have lastEq := last.trans (retained.entry index).2.val.pullback.finish_eq.symm
  have bounded := Primitive.integral_difference_le sourceCell (retained.entry index).2.val.pullback.model
    firstEq lastEq (8 * (sourceCell.localAllowance + (retained.entry index).2.val.pullback.model.localAllowance)) (by
      intro input inside
      let source := sourceQueries input inside
      let queried := rowQueries input inside
      have compared : PLift (normSq (eval sourceCell.polynomial ⟨input, 0⟩ -
          eval (retained.entry index).2.val.pullback.model.polynomial ⟨input, 0⟩) ≤
          8 * (sourceCell.localAllowance + (retained.entry index).2.val.pullback.model.localAllowance)) :=
        withPolynomialComparison traced contained entered data dataFactory retained ordinary index input inside
        queried source.1 source.2.1 source.2.2.1.val source.2.2.2 first last source.2.2.1.property
        (fun _samePoint _rowEntry _rowSheet _mapped _mappedFactory _mappedEntry _mappedSheet _admitted
          _acquired _acquiredFactory _selected _selectedFactory _same _compared _comparedFactory _roots
          _residual _residualFactory residualEq _ceiling ceilingEq paid =>
          ⟨(congrArg normSq residualEq).symm.trans_le (paid.trans_eq ceilingEq)⟩)
      exact compared.down)
  exact bounded.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end

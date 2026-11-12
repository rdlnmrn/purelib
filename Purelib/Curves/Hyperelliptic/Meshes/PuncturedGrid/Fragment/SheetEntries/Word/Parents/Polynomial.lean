module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Polynomial
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
public import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Tactic.Ring

/-! # Full-numerator source models on the same retained closed fragment word

The source work/models and the whole physical/numerical Closed cache are
given actual values. One original comparison per original leaf retains
its independent source and mesh stages. The literal outgoing-gap telescope
then gives a count-weighted comparison with the actual model integral.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.PolynomialComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets
open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append gaussianNormSqSum gaussianNormSqSum_append)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (add_le_add_direct mul_le_mul_of_nonneg_left_direct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count polynomialFloor polynomialStage : Nat}
variable {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {target tolerance : Rational}
variable {points : List Canonical} {index : Nat} {differential : OddPowerDifferential curve.polynomial}
variable {budgets : FaceMeshBudgets source points tolerance
  (numerator := differential.numerator.scale differential.scale) domains}
variable {numerics : FacePrimitiveBank source index
  (numerator := differential.numerator.scale differential.scale) domains}
variable (shared : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale) budgets numerics)

/-- The existing indexed leaf-comparison products on the SAME retained parent bank and ordinary source models.

Ordinary pairs and the actual empty product retain the original parent
order. The source work, model bank and physical leaves are supplied caches;
this family introduces no replacement source/model or geometric owner.
-/
@[expose] def Blocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests), SplitSheets.Blocks shared entries →
    (work : PolynomialWork requests.covered polynomialFloor differential) → work.Models polynomialStage → Type 3
  | _, _, _, _, .nil, _bank, _work, _models => PUnit.{4}
  | _, _, _, _, .cons _first remaining, bank, work, models =>
      Word.PolynomialComparison.Leaves models.1.2.val bank.1.word ×
        Blocks remaining bank.2 work.2 models.2

section Preparation

variable (ordinary : differential.denominatorPairs = 0)

include ordinary in
/-- Compare each original bounded leaf once against its GIVEN original whole polynomial model.

The retained bank provides all numerical endpoint views. Source request,
work, model, primitive bank, Finish and physical join producers are never
run to recover these inputs. Only the actual new analytic comparisons are
materialized in the existing finite products.
-/
def buildBlocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage),
    Blocks shared entries bank work models
  | _, _, _, _, .nil, _bank, _work, _models => PUnit.unit
  | _, _, _, _, .cons _first remaining, bank, work, models =>
      let head := Word.PolynomialComparison.compareLeaves models.1.2.val bank.1.word ordinary
      let following := buildBlocks remaining bank.2 work.2 models.2
      (head, following)

end Preparation

/-- Fold only actual already computed fragment charges in literal parent/fragment order. -/
@[expose] def chargeSum : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage),
    Blocks shared entries bank work models → Rational
  | _, _, _, _, .nil, _bank, _work, _models, _compared => 0
  | _, _, _, _, .cons _first remaining, bank, work, models, compared =>
      Word.PolynomialComparison.chargeSum models.1.2.val bank.1.word compared.1 +
        chargeSum remaining bank.2 work.2 models.2 compared.2

/-- The actual ordered per-fragment errors against the SAME retained source model bank.

These source polynomial expressions appear only in the proof of the
comparison. The executable preparation folds the cached numerical values
and charges without evaluating source primitive polynomials.
-/
@[expose] def errors : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (_bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential), work.Models polynomialStage → List Canonical
  | _, _, _, _, .nil, _bank, _work, _models => []
  | _, _, _, _, .cons _first remaining, bank, work, models =>
      Word.PolynomialComparison.errors models.1.2.val bank.1.word ++
        errors remaining bank.2 work.2 models.2

/-- Every literal original fragment contributes exactly one error occurrence, including stationary/repeated roles. -/
theorem errors_length : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage),
    (errors shared entries bank work models).length = fragmentCount entries
  | _, _, _, _, .nil, _bank, _work, _models => rfl
  | _, _, _, _, .cons _first remaining, bank, work, models =>
      (Data.List.Append.length_append _ _).trans (congrArg₂ Nat.add
        (Word.PolynomialComparison.errors_length models.1.2.val bank.1.word)
        (errors_length remaining bank.2 work.2 models.2))

/-- The whole proof error is the SAME numerical increment sum minus the SAME source-model primitive increment sum. -/
theorem errors_sum : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage),
    gaussianSum (errors shared entries bank work models) = gaussianSum (SplitSheets.increments shared entries bank) -
      gaussianSum (PolynomialWork.Models.increments requests.covered work models)
  | _, _, _, _, .nil, _bank, _work, _models => by change (0 : Canonical) = 0 - 0; ring1
  | _, _, _, _, .cons (parent := parent) (requests := tailRequests) first remaining, bank, work, models => by
      let numericHead := gaussianSum bank.1.word.increments
      let numericTail := gaussianSum (SplitSheets.increments shared remaining bank.2)
      let sourceHead := models.1.2.val.primitive.primitive.value.eval (parent.edge.point 1) -
        models.1.2.val.primitive.primitive.value.eval (parent.edge.point 0)
      let sourceTail := gaussianSum (PolynomialWork.Models.increments tailRequests.covered work.2 models.2)
      have head := Word.PolynomialComparison.errors_sum models.1.2.val bank.1.word
      have tail := errors_sum remaining bank.2 work.2 models.2
      change gaussianSum _ = numericHead - sourceHead at head
      change gaussianSum _ = numericTail - sourceTail at tail
      have numeric : gaussianSum (SplitSheets.increments shared (.cons first remaining) bank) =
          numericHead + numericTail := gaussianSum_append _ _
      change gaussianSum (Word.PolynomialComparison.errors models.1.2.val bank.1.word ++
        errors shared remaining bank.2 work.2 models.2) =
          gaussianSum (SplitSheets.increments shared (.cons first remaining) bank) - (sourceHead + sourceTail)
      have joined := congrArg₂ (fun first last : Canonical => first + last) head tail
      have scalar : (numericHead - sourceHead) + (numericTail - sourceTail) =
          (numericHead + numericTail) - (sourceHead + sourceTail) := by ring1
      exact (gaussianSum_append _ _).trans (joined.trans (scalar.trans
        (congrArg (fun value : Canonical => value - (sourceHead + sourceTail)) numeric.symm)))

/-- Summing actual squared errors uses exactly the sum of the original per-fragment charges. -/
theorem errors_bounded : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage)
    (compared : Blocks shared entries bank work models),
    gaussianNormSqSum (errors shared entries bank work models) ≤ chargeSum shared entries bank work models compared
  | _, _, _, _, .nil, _bank, _work, _models, _compared => Data.Rat.Fraction.Order.Basic.le_refl 0
  | _, _, _, _, .cons _first remaining, bank, work, models, compared => by
      have head := Word.PolynomialComparison.errors_bounded models.1.2.val bank.1.word compared.1
      have tail := errors_bounded remaining bank.2 work.2 models.2 compared.2
      rewrite [errors, gaussianNormSqSum_append]
      exact add_le_add_direct head tail

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable (requests : RequestedParents count target parents) (entries : SplitSheets domains fragments requests)
variable {point : LiftedPoint 2} {root : Named}
variable (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
variable (closed : Closed shared entries geometry roots included)
variable (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage)

/-- The actual outgoing gaps and actual source-model integral obey the literal K times the same charge sum.

The source primitive telescope and complete original Closed telescope are
both derived from their retained owners. No gap is set to zero and no
physical integral or independently canonical cycle is identified here.
-/
theorem integral_difference_le
    (compared : Blocks shared entries (Closed.blocks shared entries geometry roots closed) work models) :
    normSq (gaussianSum (Closed.gaps shared entries geometry roots closed) -
      (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample) ≤
        (fragmentCount entries : Rational) *
          chargeSum shared entries (Closed.blocks shared entries geometry roots closed) work models compared := by
  let bank := Closed.blocks shared entries geometry roots closed
  have finite := Norm.Sum.Basic.normSq_gaussianSum_le (errors shared entries bank work models)
  have scalar : normSq (gaussianSum (errors shared entries bank work models)) ≤
      ((errors shared entries bank work models).length : Rational) *
        gaussianNormSqSum (errors shared entries bank work models) := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact finite
  have counted := scalar.trans (mul_le_mul_of_nonneg_left_direct
    (errors_bounded shared entries bank work models compared)
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
  have lengthEq := errors_length shared entries bank work models
  have boundEq := congrArg (fun value : Nat => (value : Rational) *
    chargeSum shared entries bank work models compared) lengthEq
  have numerics := (congrArg gaussianSum (Closed.increments_blocks shared entries geometry roots closed)).trans
    (Closed.telescope shared entries geometry roots closed)
  have primitives := PolynomialWork.Models.increments_integral requests.covered work models
  have valueEq := (errors_sum shared entries bank work models).trans
    (congrArg₂ (fun first last : Canonical => first - last) numerics primitives)
  exact Eq.mp (congrArg (fun value : Canonical => normSq value ≤
    (fragmentCount entries : Rational) * chargeSum shared entries bank work models compared) valueEq)
    (counted.trans_eq boundEq)

/-- One actual whole word/model input and its once materialized fragment comparison bank and finite charge.

The original request, geometry/root/Entry word, full work/model products,
stages and independent primitive constants remain data. A failed bound
check cannot turn an unchanged old floor into a paid observation schedule.
-/
abbrev Cache (ordinary : differential.denominatorPairs = 0) :=
  {value : (OddPowerDifferential curve.polynomial × Nat × Nat × Nat) ×
      RequestedParents count target parents × Closed shared entries geometry roots included ×
      PolynomialWork requests.covered polynomialFloor differential × work.Models polynomialStage //
    value = ((differential, polynomialFloor, polynomialStage, index), requests, closed, work, models)} ×
  (Σ compared : {value : Blocks shared entries (Closed.blocks shared entries geometry roots closed) work models //
      value = buildBlocks shared ordinary entries (Closed.blocks shared entries geometry roots closed) work models},
  Σ value : {value : Canonical // value = gaussianSum (Closed.gaps shared entries geometry roots closed)},
  Σ bound : {value : Rational // value = (fragmentCount entries : Rational) *
      chargeSum shared entries (Closed.blocks shared entries geometry roots closed) work models compared.val},
  {_value : Unit // normSq (value.val -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample) ≤ bound.val})

/-- Execute the fragment comparisons once and fold only retained numerical values and actual scalar charges. -/
def build (ordinary : differential.denominatorPairs = 0) :
    Cache shared requests entries geometry roots closed work models ordinary :=
  let bank := Closed.blocks shared entries geometry roots closed
  let originals : {value : (OddPowerDifferential curve.polynomial × Nat × Nat × Nat) ×
      RequestedParents count target parents × Closed shared entries geometry roots included ×
      PolynomialWork requests.covered polynomialFloor differential × work.Models polynomialStage //
      value = ((differential, polynomialFloor, polynomialStage, index), requests, closed, work, models)} :=
    ⟨((differential, polynomialFloor, polynomialStage, index), requests, closed, work, models), rfl⟩
  let compared : {value : Blocks shared entries bank work models //
      value = buildBlocks shared ordinary entries bank work models} :=
    ⟨buildBlocks shared ordinary entries bank work models, rfl⟩
  let value : {value : Canonical // value = gaussianSum (Closed.gaps shared entries geometry roots closed)} :=
    ⟨gaussianSum (SplitSheets.increments shared entries bank),
      (congrArg gaussianSum (Closed.increments_blocks shared entries geometry roots closed)).trans
        (Closed.telescope shared entries geometry roots closed)⟩
  let bound : {value : Rational // value = (fragmentCount entries : Rational) *
      chargeSum shared entries bank work models compared.val} :=
    ⟨(fragmentCount entries : Rational) * chargeSum shared entries bank work models compared.val, rfl⟩
  ⟨originals, compared, value, bound, ⟨(), Eq.mpr (congrArg (fun scalar : Canonical => normSq (scalar -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample) ≤ bound.val)
      value.property)
      (integral_difference_le shared requests entries geometry roots closed work models compared.val)⟩⟩

namespace Cache

variable {shared requests entries geometry roots closed work models} {ordinary : differential.denominatorPairs = 0}
variable (kept : Cache shared requests entries geometry roots closed work models ordinary)

/-- Read the actual ordinary specification and separate model floor/stage and numerical index as retained data. -/
@[expose] def inputs : OddPowerDifferential curve.polynomial × Nat × Nat × Nat := kept.1.val.1

/-- Read the original complete request/patch/query spine as actual retained data. -/
@[expose] def sourceRequests : RequestedParents count target parents := kept.1.val.2.1

/-- Read the SAME original rooted word, including its independent old/new physical and numerical cache owners. -/
@[expose] def word : Closed shared entries geometry roots included := kept.1.val.2.2.1

/-- Read the SAME whole coordinate/bounds/pre-stage request product without executing its factory. -/
@[expose] def sourceWork : PolynomialWork requests.covered polynomialFloor differential := kept.1.val.2.2.2.1

/-- Read the SAME selected request/model product at its independent supplied source-model stage. -/
@[expose] def sourceModels : work.Models polynomialStage := kept.1.val.2.2.2.2

/-- Read the original supplied whole source work/model products and every selected request factory. -/
theorem originals_eq : kept.1.val =
    ((differential, polynomialFloor, polynomialStage, index), requests, closed, work, models) := kept.1.property

/-- Read the original once materialized full-numerator fragment comparisons. -/
@[expose] def comparisons : Blocks shared entries (Closed.blocks shared entries geometry roots closed) work models :=
  kept.2.1.val

/-- Read the cached same-word numerical increment sum. -/
@[expose] def value : Canonical := kept.2.2.1.val

/-- Read the exact K-weighted total of original actual fragment charges. -/
@[expose] def bound : Rational := kept.2.2.2.1.val

/-- The entire comparison product retains its one actual factory on the original work/model/word caches. -/
theorem comparisons_eq : kept.comparisons =
    buildBlocks shared ordinary entries (Closed.blocks shared entries geometry roots closed) work models :=
  kept.2.1.property

/-- The cached numerical value is the literal ordered signed outgoing-gap sum with its actual closing contribution. -/
theorem value_eq : kept.value = gaussianSum (Closed.gaps shared entries geometry roots closed) := kept.2.2.1.property

/-- The exact finite charge keeps the actual K occurrences and all independent actual per-piece bounds. -/
theorem bound_eq : kept.bound = (fragmentCount entries : Rational) *
    chargeSum shared entries (Closed.blocks shared entries geometry roots closed) work models kept.comparisons :=
  kept.2.2.2.1.property

/-- The same actual gap word and ordinary source-model integral satisfy their internally derived finite bound. -/
theorem accurate : normSq (kept.value -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample) ≤ kept.bound :=
  kept.2.2.2.2.property

/-- A strict target check on the SAME retained caches, with honest fixed-bound insufficiency otherwise. -/
abbrev Payment (requested : Rational) :=
  {value : Cache shared requests entries geometry roots closed work models ordinary × Rational //
    value = (kept, requested)} ×
  ({_value : Unit // kept.bound < requested ∧ normSq (kept.value -
    (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample) < requested} ⊕
    {_value : Unit // ¬kept.bound < requested})

/-- Test the computed bound without changing either actual numerical/source stage or claiming impossibility. -/
def pay (requested : Rational) : kept.Payment requested :=
  if admitted : kept.bound < requested then
    ⟨⟨(kept, requested), rfl⟩, Sum.inl ⟨(), admitted, kept.accurate.trans_lt admitted⟩⟩
  else ⟨⟨(kept, requested), rfl⟩, Sum.inr ⟨(), admitted⟩⟩

end Cache

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.PolynomialComparison

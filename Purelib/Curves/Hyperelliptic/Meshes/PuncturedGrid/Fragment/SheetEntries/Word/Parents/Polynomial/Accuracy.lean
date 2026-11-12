module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Polynomial.Accuracy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Polynomial
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Tactic.Ring

/-! # Arbitrary requested accuracy on one original closed numerator word

The actual original fragment count selects one local target. Original
fragment allocations and their common source/face floors precede all new
source models and P primitive values. The same given physical word then
supplies every retained leaf and join to the original numerical revaluation
and the actual whole-model comparison.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.PolynomialComparison

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append gaussianNormSqSum gaussianNormSqSum_append)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Rational.Budget
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
variable (budgets : FaceMeshBudgets source points tolerance
  (numerator := differential.numerator.scale differential.scale) domains)
variable {numerics : FacePrimitiveBank source index
  (numerator := differential.numerator.scale differential.scale) domains}
variable (shared : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale) budgets numerics)

/-- Original per-fragment accuracy requests in the SAME parent/fragment products, before observations. -/
@[expose] def Requests : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents},
    SplitSheets domains fragments requests → Rational → Type
  | _, _, _, _, .nil, _requested => PUnit
  | _, _, _, _, .cons first remaining, requested =>
      Word.PolynomialComparison.Requests first budgets requested × Requests remaining requested

/-- Materialize every original fragment allocation once before either model or P-bank observations. -/
def prepareRequests (requested : Rational) (positive : 0 < requested) :
    ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests), Requests budgets entries requested
  | _, _, _, _, .nil => PUnit.unit
  | _, _, _, _, .cons first remaining =>
      let head := Word.PolynomialComparison.prepareRequests first budgets requested positive
      let following := prepareRequests requested positive remaining
      (head, following)

/-- The common source floor is the maximum of the SAME retained requests, in parent order. -/
@[expose] def sourceFloor : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {requested : Rational}, Requests budgets entries requested → Nat
  | _, _, _, _, .nil, _, _allocated => 0
  | _, _, _, _, .cons _first remaining, _, allocated =>
      max (Word.PolynomialComparison.sourceFloor allocated.1) (sourceFloor remaining allocated.2)

/-- The common numerical floor is the maximum of the SAME genuine P requests, in parent order. -/
@[expose] def faceFloor : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) {requested : Rational}, Requests budgets entries requested → Nat
  | _, _, _, _, .nil, _, _allocated => 0
  | _, _, _, _, .cons _first remaining, _, allocated =>
      max (Word.PolynomialComparison.faceFloor allocated.1) (faceFloor remaining allocated.2)

namespace Requests

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits}
    {parentRequests : RequestedParents count target parents}
    {entries : SplitSheets domains fragments parentRequests} {requested : Rational}
    {next : FaceMeshBudgets source points tolerance
      (numerator := differential.numerator.scale differential.scale) domains}

/-- Transport the SAME retained request product along equality of its complete original numerical-budget owner.

All point, domain, numerator, tolerance and source indices remain those of
the original budget family. Equality elimination forwards the actual
ordered request product; no allocation or observation is repeated.
-/
@[expose] def castBudgets (equal : budgets = next) (kept : Requests budgets entries requested) :
    Requests next entries requested := by
  cases equal
  exact kept

/-- Whole-budget index transport retains the complete original request product heterogeneously. -/
theorem castBudgets_heq (equal : budgets = next) (kept : Requests budgets entries requested) :
    HEq (castBudgets budgets equal kept) kept := by
  cases equal
  exact HEq.rfl

/-- Whole-budget transport preserves the source coefficient floor selected from those SAME requests. -/
theorem sourceFloor_castBudgets (equal : budgets = next) (kept : Requests budgets entries requested) :
    sourceFloor next entries (castBudgets budgets equal kept) = sourceFloor budgets entries kept := by
  cases equal
  rfl

/-- Whole-budget transport preserves the actual numerical floor of the original independent request product. -/
theorem faceFloor_castBudgets (equal : budgets = next) (kept : Requests budgets entries requested) :
    faceFloor next entries (castBudgets budgets equal kept) = faceFloor budgets entries kept := by
  cases equal
  rfl

end Requests

/-- The scalar original occurrence count distributes over the two unchanged parent products. -/
private theorem count_add_mul (first last : Nat) (requested : Rational) :
    ((first + last : Nat) : Rational) * requested = (first : Rational) * requested +
      (last : Rational) * requested :=
  (congrArg (fun value : Rational => value * requested)
    (Data.Rat.Fraction.Cast.natCast_add_direct first last)).trans (by ring1)

/-- All actual comparison charges obey the single global occurrence count, with no extra parent factor.

Each original leaf uses its retained pre-observation request and both actual
floors. The SAME whole-model bank and SAME physical/numerical block product
supply every comparison; no source or comparison is recomputed for payment.
-/
theorem chargeSum_le {requested : Rational} :
    ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : SplitSheets.Blocks shared entries)
    (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage)
    (compared : Blocks shared entries bank work models) (allocated : Requests budgets entries requested),
    sourceFloor budgets entries allocated ≤ polynomialFloor → faceFloor budgets entries allocated ≤ index →
    chargeSum shared entries bank work models compared ≤ (fragmentCount entries : Rational) * requested
  | _, _, _, _, .nil, _bank, _work, _models, _compared, _allocated, _sourceLater, _faceLater => by
      change (0 : Rational) ≤ 0 * requested
      rewrite [show (0 : Rational) * requested = 0 by ring1]
      exact Data.Rat.Fraction.Order.Basic.le_refl 0
  | _, _, _, _, .cons (partition := partition) first remaining,
      bank, work, models, compared, allocated, sourceLater, faceLater => by
      have headSource := (Data.Nat.Order.le_max_left _ _).trans sourceLater
      have tailSource := (Data.Nat.Order.le_max_right _ _).trans sourceLater
      have headFace := (Data.Nat.Order.le_max_left _ _).trans faceLater
      have tailFace := (Data.Nat.Order.le_max_right _ _).trans faceLater
      have head := Word.PolynomialComparison.chargeSum_le allocated.1 models.1.2.val bank.1.word
        compared.1 headSource headFace
      have following := chargeSum_le remaining bank.2 work.2 models.2 compared.2 allocated.2 tailSource tailFace
      change Word.PolynomialComparison.chargeSum models.1.2.val bank.1.word compared.1 +
        chargeSum shared remaining bank.2 work.2 models.2 compared.2 ≤
          ((partition.intervals.length + fragmentCount remaining : Nat) : Rational) * requested
      exact (add_le_add_direct head following).trans_eq
        (count_add_mul partition.intervals.length (fragmentCount remaining) requested).symm

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable (requests : RequestedParents count target parents) (entries : SplitSheets domains fragments requests)
variable {point : LiftedPoint 2} {root : Named}
variable (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
variable (closed : Closed shared entries geometry roots included)
variable (work : PolynomialWork requests.covered polynomialFloor differential) (models : work.Models polynomialStage)
variable {ordinary : differential.denominatorPairs = 0}
variable (compared : Cache shared requests entries geometry roots closed work models ordinary)

/-- The actual retained K-weighted comparison charge meets an arbitrary target from its original allocations.

The local target is Aggregate.perTerm requested K on the SAME literal K.
A single global Cauchy count and the original sum of all actual fragment
charges are paid. The proof reads the given comparison cache and never
repeats a numerical producer or assumes the wanted final closeness.
-/
theorem Cache.bound_lt {requested : Rational} (positive : 0 < requested)
    (allocated : Requests budgets entries (Aggregate.perTerm requested (fragmentCount entries)))
    (sourceLater : sourceFloor budgets entries allocated ≤ polynomialFloor)
    (faceLater : faceFloor budgets entries allocated ≤ index) : compared.bound < requested := by
  have summed := chargeSum_le budgets shared entries (Closed.blocks shared entries geometry roots closed)
    work models compared.comparisons allocated sourceLater faceLater
  have paid := Aggregate.count_mul_perTerm_lt positive (fragmentCount entries)
  have counted := mul_le_mul_of_nonneg_left_direct summed
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (fragmentCount entries)))
  exact compared.bound_eq.trans_lt (counted.trans_lt paid)

/-- The SAME original outgoing gaps and SAME ordinary source-model integral meet the requested error. -/
theorem Cache.accurate_lt {requested : Rational} (positive : 0 < requested)
    (allocated : Requests budgets entries (Aggregate.perTerm requested (fragmentCount entries)))
    (sourceLater : sourceFloor budgets entries allocated ≤ polynomialFloor)
    (faceLater : faceFloor budgets entries allocated ≤ index) :
    normSq (compared.value -
      (PathModel.mk (PolynomialWork.Models.cells requests.covered work models)).integralSample) < requested :=
  compared.accurate.trans_lt (Cache.bound_lt budgets shared requests entries geometry roots closed work models
    compared positive allocated sourceLater faceLater)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.PolynomialComparison

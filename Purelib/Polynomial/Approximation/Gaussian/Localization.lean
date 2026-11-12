module

public import Purelib.RootIsolation.Residual.Multiplicity
public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Computed finite localization of polynomial approximation samples

An original geometric sample program and its polynomial residual budget
prepare the same coefficient decomposition and factor caches once. Each
positive radius request computes a sufficient finite refinement stage and
localizes that actual original sample using those retained caches.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Localization

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.RootIsolation.Residual
open Purelib.Riemann.RootContinuation

set_option genInjectivity false in
/-- A retained original sample program with its computed coefficient-localization data and residual scale.

The decomposition concerns the original polynomial's exact normalization,
whose evaluations are unchanged. The same stored source supplies every
localized sample. Its residual bound is quantitative at every finite index.
-/
structure Preparation (polynomial : CoefficientPolynomial) (original : GeometricApproximation) where
  /-- The actual retained original geometric sample program. -/
  source : GeometricApproximation
  /-- The stored program is the original input. -/
  source_eq : source = original
  /-- The exact normalization's original squarefree occurrence decomposition. -/
  decomposition : Squarefree.Decomposition polynomial.normalize
  /-- The actual localization cache on that same retained decomposition. -/
  factors : Multiplicity.Preparation decomposition
  /-- The actual coherent root programs at those same stored original factor/isolation parents. -/
  roots : CoherentRoot.Multiplicity.Family factors.factors
  /-- The retained geometric scale of the original polynomial's sample residuals. -/
  residualScale : Rational
  /-- The retained residual scale is nonnegative. -/
  residualScale_nonnegative : 0 ≤ residualScale
  /-- Every original sample satisfies the original polynomial's retained geometric residual budget. -/
  residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index

constructive_injectivity Preparation

namespace Preparation

/-- Attach original coherent root programs to one retained decomposition and factor preparation.

The actual source, residual scale and complete original factor family are
retained. Root realization consumes those same factors directly, without
executing a decomposition or factor-isolation producer. -/
@[expose] def ofFactors (polynomial : CoefficientPolynomial)
    (decomposition : Squarefree.Decomposition polynomial.normalize)
    (source : GeometricApproximation) (residualScale : Rational) (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index)
    (factors : Multiplicity.Preparation decomposition) : Preparation polynomial source :=
  let roots := CoherentRoot.Multiplicity.Family.ofPreparation factors.factors
  ⟨source, rfl, decomposition, factors, roots, residualScale, scaleNonnegative, residual⟩

/-- Prepare the same retained coefficient decomposition and original sample program without decomposing again. -/
@[expose] def ofDecomposition (polynomial : CoefficientPolynomial)
    (decomposition : Squarefree.Decomposition polynomial.normalize)
    (source : GeometricApproximation) (residualScale : Rational) (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index) :
    Preparation polynomial source :=
  ofFactors polynomial decomposition source residualScale scaleNonnegative residual
    (Multiplicity.Preparation.ofDecomposition decomposition)

/-- Read the exact retained decomposition used by the complete localization constructor. -/
theorem ofDecomposition_decomposition (polynomial : CoefficientPolynomial)
    (decomposition : Squarefree.Decomposition polynomial.normalize)
    (source : GeometricApproximation) (residualScale : Rational) (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index) :
    (ofDecomposition polynomial decomposition source residualScale scaleNonnegative residual).decomposition =
      decomposition := rfl

/-- Compute the original normalized coefficient decomposition for a positive-degree source polynomial.

Normalization and its original nonzero and degree witnesses feed the same
finite squarefree decomposition procedure used by residual preparation.
Naming this operation permits independent factor-cache loading before the
complete localization preparation is assembled. -/
def decompose (polynomial : CoefficientPolynomial) (degreePositive : 0 < polynomial.natDegree) :
    Squarefree.Decomposition polynomial.normalize :=
  let nonzero := Degree.Global.isZero_false_of_natDegree_pos degreePositive
  Squarefree.Decomposition.Compute.decomposeNormalized polynomial.normalize
    (Dense.Basic.DensePolynomial.normalize_normalize polynomial)
    (by rewrite [Dense.Basic.DensePolynomial.isZero_normalize]; exact nonzero)
    (by rewrite [Dense.Basic.DensePolynomial.natDegree_normalize]; exact degreePositive)

/-- Prepare the original coefficient decomposition, factor data and root caches once from a positive-degree program. -/
def ofResidual (polynomial : CoefficientPolynomial) (degreePositive : 0 < polynomial.natDegree)
    (source : GeometricApproximation) (residualScale : Rational) (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index) :
    Preparation polynomial source :=
  let decomposition := decompose polynomial degreePositive
  ofDecomposition polynomial decomposition source residualScale scaleNonnegative residual

/-- Retained original factors preserve the complete original residual localization preparation.

Both the coefficient decomposition and factor preparation retain their
original defining equalities. The coherent root programs, actual source,
residual scale and all dependent factor and root indices are preserved. -/
theorem ofFactors_eq_ofResidual (polynomial : CoefficientPolynomial) (degreePositive : 0 < polynomial.natDegree)
    (decomposition : Squarefree.Decomposition polynomial.normalize)
    (decompositionEq : decomposition = decompose polynomial degreePositive)
    (source : GeometricApproximation) (residualScale : Rational) (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index)
    (factors : Multiplicity.Preparation decomposition)
    (factorsEq : factors = Multiplicity.Preparation.ofDecomposition decomposition) :
    ofFactors polynomial decomposition source residualScale scaleNonnegative residual factors =
      ofResidual polynomial degreePositive source residualScale scaleNonnegative residual := by
  cases decompositionEq
  cases factorsEq
  rfl

/-- An authenticated original residual preparation keeps each original same-index factor constructor. -/
theorem factor_eq_ofResidual (polynomial : CoefficientPolynomial) (degreePositive : 0 < polynomial.natDegree)
    (source : GeometricApproximation) (residualScale : Rational) (scaleNonnegative : 0 ≤ residualScale)
    (residual : ∀ index, normSq (polynomial.eval (source.sample index)) ≤ Basic.quarterRadius residualScale index)
    (preparation : Preparation polynomial source)
    (same : preparation = ofResidual polynomial degreePositive source residualScale scaleNonnegative residual)
    (index : Fin preparation.factors.entries.length) :
    preparation.factors.factors.get index =
      Multiplicity.Factor.ofEntry (preparation.factors.entries.get index) := by
  cases same
  exact Multiplicity.Preparation.get_eq _ rfl index

variable {polynomial : CoefficientPolynomial} {original : GeometricApproximation}

set_option genInjectivity false in
/-- One actual finite refinement request and its same-sample original multiplicity localization.

The result retains the computed target, returned index and exact original
sample. Lower and upper index bounds concern the actual finite scan and its
computed fuel. Localization consumes the same retained factor caches.
-/
structure Observation (preparation : Preparation polynomial original) (current : Nat) (epsilon : Rational) where
  /-- The same computed source-residual target for the positive radius request. -/
  target : Rational
  /-- The target comes from the preparation's actual original factor caches. -/
  target_eq : target = preparation.factors.threshold epsilon
  /-- The actual index returned by the finite residual-budget scan. -/
  index : Nat
  /-- The stored index is the actual scan result on the same scale, start and target. -/
  index_eq : index = Search.firstQuarterBelow preparation.residualScale current target
  /-- Refinement preserves the supplied original starting index. -/
  index_ge : current ≤ index
  /-- The actual finite scan does not exceed its computed binary-width fuel. -/
  index_le : index ≤ current +
    (Nat.log2 (Data.Rat.Rounding.Floor.ceilNat (preparation.residualScale / target)) + 1)
  /-- The actual returned stage meets the retained original residual-budget stopping condition. -/
  budgetSmall : Basic.quarterRadius preparation.residualScale index < target
  /-- The original displayed sample is stored once at that same finite index. -/
  sample : Canonical
  /-- The retained point is the reading of the same stored original program at that index. -/
  sample_eq : sample = preparation.source.sample index
  /-- The actual normalized original polynomial reading meets the same computed target. -/
  residualSmall : normSq (polynomial.normalize.eval sample) < target
  /-- The selected original factor and nearby root data use that same sample and positive radius. -/
  localization : Multiplicity.Preparation.Localization preparation.factors sample epsilon

constructive_injectivity Observation

/-- Compute a sufficient bounded refinement and localize its actual original sample at a positive radius.

The target is positive by the original finite multiplicity preparation. The
quarter-radius scan computes its own sufficient fuel; residual transport
through exact normalization supplies localization without a successful-search
or branch-selection hypothesis.
-/
def observe (preparation : Preparation polynomial original) (current : Nat) {epsilon : Rational}
    (epsilonPositive : 0 < epsilon) : Observation preparation current epsilon :=
  let target := preparation.factors.threshold epsilon
  let targetPositive := preparation.factors.threshold_positive epsilonPositive
  let index := Search.firstQuarterBelow preparation.residualScale current target
  let sample := preparation.source.sample index
  have budgetSmall : Basic.quarterRadius preparation.residualScale index < target :=
    Search.firstQuarterBelow_accurate preparation.residualScale preparation.residualScale_nonnegative
      current target targetPositive
  have residualSmall : normSq (polynomial.normalize.eval sample) < target := by
    rewrite [Dense.Basic.DensePolynomial.eval_normalize]
    exact (preparation.residual index).trans_lt budgetSmall
  let localization := preparation.factors.localize sample epsilonPositive residualSmall
  ⟨target, rfl, index, rfl,
    Search.firstQuarterBelow_ge preparation.residualScale current target,
    Search.firstQuarterBelow_le preparation.residualScale current target,
    budgetSmall, sample, rfl, residualSmall, localization⟩

/-- Read the stored coherent root cache of the same original factor selected by this actual observation. -/
@[expose] def Observation.realization {preparation : Preparation polynomial original}
    {current : Nat} {epsilon : Rational} (observation : Observation preparation current epsilon) :
    CoherentRoot.Multiplicity.Realization (preparation.factors.factors.get observation.localization.selected.index) :=
  preparation.roots.get observation.localization.selected.index

/-- Read an original selected factor's retained root approximation at its unchanged bounded root index. -/
@[expose] def Observation.rootApproximation {preparation : Preparation polynomial original}
    {current : Nat} {epsilon : Rational} (observation : Observation preparation current epsilon)
    (index : Fin (CoherentRoot.Multiplicity.count
      (preparation.factors.factors.get observation.localization.selected.index))) :
    ApproximationData := observation.realization.approximation index

/-- Every later original sample meets the same retained residual target without another scan or preparation. -/
theorem Observation.later_residualSmall {preparation : Preparation polynomial original}
    {current : Nat} {epsilon : Rational} (observation : Observation preparation current epsilon)
    {later : Nat} (order : observation.index ≤ later) :
    normSq (polynomial.normalize.eval (preparation.source.sample later)) < observation.target := by
  rewrite [Dense.Basic.DensePolynomial.eval_normalize]
  exact (preparation.residual later).trans_lt
    ((Basic.quarterRadius_antitone preparation.residualScale_nonnegative order).trans_lt observation.budgetSmall)

/-- Localize a later original sample using the successful observation's same target and original factor caches. -/
def Observation.localizeLater {preparation : Preparation polynomial original}
    {current : Nat} {epsilon : Rational} (observation : Observation preparation current epsilon)
    (epsilonPositive : 0 < epsilon) (later : Nat) (order : observation.index ≤ later) :
    Multiplicity.Preparation.Localization preparation.factors (preparation.source.sample later) epsilon :=
  preparation.factors.localize (preparation.source.sample later) epsilonPositive (by
    have small := observation.later_residualSmall order
    rewrite [observation.target_eq] at small
    exact small)

/-- Later localization uses the same original factor cache and exact source reading.

The equality exposes its pointwise operands without unfolding the observation
or evaluating its earlier stored sample. The complete localization result is
retained at the supplied later index. -/
theorem Observation.localizeLater_eq {preparation : Preparation polynomial original}
    {current : Nat} {epsilon : Rational} (observation : Observation preparation current epsilon)
    (epsilonPositive : 0 < epsilon) (later : Nat) (order : observation.index ≤ later) :
    observation.localizeLater epsilonPositive later order =
      preparation.factors.localize (preparation.source.sample later) epsilonPositive (by
        have small := observation.later_residualSmall order
        rewrite [observation.target_eq] at small
        exact small) := (rfl)

end Preparation

end Purelib.Polynomial.Approximation.Gaussian.Localization

end

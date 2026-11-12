module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Bounds
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Arithmetic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Allowance
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Full cubic root certificates retaining the original fixed-point channels

The source certificate consumes the exact supplied preparation of the
original cubic lift. The target preparation consumes the actual changed
cubic product with the identical original cofactor certificate and retained
normalized target root. Both full cubic certificates retain operational
links to those original input channels. The target preparation also exposes
the actual original paired operand states beneath its apartification.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}
variable {source : Lift (sourcePoint site parameter original) unit}
variable {anchor : Anchor source} {increment : Canonical}

namespace Roots

/-- The complete original full-cubic source certificate type at the unchanged spatial point. -/
@[expose] def SourceRoot (_source : Lift (sourcePoint site parameter original) unit) : Type 1 :=
  CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (sourcePoint site parameter original).base)

/-- The complete original full-cubic target certificate type at the changed parameter and unchanged spatial point. -/
@[expose] def TargetRoot (_step : Step anchor increment) : Type 1 :=
  CertifiedSquareRoot.Certificate
    ((Paths.polynomial (parameter + increment)).eval (sourcePoint site parameter original).base)

/-- The exact division-preparation type on the retained changed full-cubic value process. -/
@[expose] def TargetPreparation (step : Step anchor increment) : Type 1 := Division.Prepared step.value

/-- The complete construction equation retaining the target product's actual original factors and apartness inputs. -/
@[expose, irreducible] def TargetPreparationRetained (step : Step anchor increment)
    (prepared : TargetPreparation step) : Prop :=
  prepared = Division.Prepared.ofProduct step.value source.unitRoot.value step.root.value
    step.value_eq source.unitRoot.apart step.root.apart

/-- The full source certificate construction equation retains the exact supplied original preparation cache. -/
@[expose, irreducible] def SourceRootRetained (sourcePrepared : Division.Prepared source.value)
    (root : SourceRoot source) : Prop :=
  root = CertifiedSquareRoot.Certificate.ofPrepared source.value source.square sourcePrepared

/-- The full target certificate construction equation retains the exact original changed-product preparation cache. -/
@[expose, irreducible] def TargetRootRetained (step : Step anchor increment) (prepared : TargetPreparation step)
    (root : TargetRoot step) : Prop :=
  root = CertifiedSquareRoot.Certificate.ofPrepared step.value step.square prepared

end Roots

/-- Full cubic certificate data retaining the exact externally supplied original source-preparation cache.

The original target preparation and both complete root certificates are
stored directly with their exact construction equations. Their indexed
subtypes preserve the supplied source cache and identical target cache;
the original input processes and factor certificates remain the parents.
-/
@[expose] def Roots (step : Step anchor increment) (sourcePrepared : Division.Prepared source.value) : Type 1 :=
  Σ prepared : { value : Roots.TargetPreparation step // Roots.TargetPreparationRetained step value },
    { root : Roots.SourceRoot source // Roots.SourceRootRetained sourcePrepared root } ×
      { root : Roots.TargetRoot step // Roots.TargetRootRetained step prepared.val root }

namespace Roots

variable {step : Step anchor increment} {sourcePrepared : Division.Prepared source.value}

/-- Read the actual retained target-product preparation without recomputing it. -/
@[expose] def targetPrepared (roots : Roots step sourcePrepared) : TargetPreparation step := roots.1.val

/-- Read the actual retained full source-certificate cache. -/
@[expose] def sourceRoot (roots : Roots step sourcePrepared) : SourceRoot source := roots.2.1.val

/-- Read the actual retained full target-certificate cache. -/
@[expose] def targetRoot (roots : Roots step sourcePrepared) : TargetRoot step := roots.2.2.val

/-- Attach both full cubic roots using the supplied source preparation and one actual target-product preparation. -/
def build (step : Step anchor increment) (sourcePrepared : Division.Prepared source.value) :
    Roots step sourcePrepared :=
  let targetPrepared := Division.Prepared.ofProduct step.value source.unitRoot.value step.root.value
    step.value_eq source.unitRoot.apart step.root.apart
  let sourceRoot := CertifiedSquareRoot.Certificate.ofPrepared source.value source.square sourcePrepared
  let targetRoot := CertifiedSquareRoot.Certificate.ofPrepared step.value step.square targetPrepared
  ⟨⟨targetPrepared, by unfold TargetPreparationRetained; rfl⟩,
    ⟨⟨sourceRoot, by unfold SourceRootRetained; rfl⟩,
      ⟨targetRoot, by unfold TargetRootRetained; rfl⟩⟩⟩

/-- Read the complete construction equation of the retained original target-product preparation. -/
theorem targetPrepared_eq (roots : Roots step sourcePrepared) :
    roots.targetPrepared = Division.Prepared.ofProduct step.value source.unitRoot.value step.root.value
      step.value_eq source.unitRoot.apart step.root.apart := by
  have retained := roots.1.property
  unfold TargetPreparationRetained at retained
  exact retained

/-- Read the complete full source-certificate equation on the identical supplied preparation cache. -/
theorem sourceRoot_eq (roots : Roots step sourcePrepared) :
    roots.sourceRoot = CertifiedSquareRoot.Certificate.ofPrepared source.value source.square sourcePrepared := by
  have retained := roots.2.1.property
  unfold SourceRootRetained at retained
  exact retained

/-- Read the complete full target-certificate equation on the identical changed-product preparation cache. -/
theorem targetRoot_eq (roots : Roots step sourcePrepared) :
    roots.targetRoot = CertifiedSquareRoot.Certificate.ofPrepared step.value step.square roots.targetPrepared := by
  have retained := roots.2.2.property
  unfold TargetRootRetained at retained
  exact retained

/-- The full source root retains the exact supplied prepared denominator value. -/
theorem source_value (roots : Roots step sourcePrepared) : roots.sourceRoot.value = sourcePrepared.denominator := by
  rewrite [roots.sourceRoot_eq]
  exact CertifiedSquareRoot.Certificate.ofPrepared_value source.value source.square sourcePrepared

/-- The full target root retains the identical cached changed-product prepared denominator value. -/
theorem target_value (roots : Roots step sourcePrepared) :
    roots.targetRoot.value = roots.targetPrepared.denominator := by
  rewrite [roots.targetRoot_eq]
  exact CertifiedSquareRoot.Certificate.ofPrepared_value step.value step.square roots.targetPrepared

/-- The original full source cubic channel agrees operationally with the retained full source root certificate. -/
def source_agrees (roots : Roots step sourcePrepared) : NamedEquivalent source.value.name roots.sourceRoot.value.name :=
  NamedEquivalent.transport rfl
    (congrArg (fun certificate : CertifiedSquareRoot.Certificate
      ((Paths.polynomial parameter).eval (sourcePoint site parameter original).base) => certificate.value.name)
        roots.sourceRoot_eq).symm
    (CertifiedSquareRoot.Certificate.ofPrepared_agrees source.value source.square sourcePrepared)

/-- The actual changed cubic input agrees operationally with its retained full target root certificate. -/
def target_agrees (roots : Roots step sourcePrepared) : NamedEquivalent step.value.name roots.targetRoot.value.name :=
  NamedEquivalent.transport rfl
    (congrArg (fun certificate : CertifiedSquareRoot.Certificate
      ((Paths.polynomial (parameter + increment)).eval (sourcePoint site parameter original).base) =>
        certificate.value.name) roots.targetRoot_eq).symm
    (CertifiedSquareRoot.Certificate.ofPrepared_agrees step.value step.square roots.targetPrepared)

/-- The full source root is compared with the actual original cofactor and exact normalized source factor. -/
def source_factor_agrees (roots : Roots step sourcePrepared) :
    NamedEquivalent roots.sourceRoot.value.name
      (source.unitRoot.value.mul (Coherence.exact (sourcePoint site parameter original).ordinate)).name :=
  NamedEquivalent.transport rfl (congrArg (fun value : CoherentNamed => value.name) source.value_eq)
    roots.source_agrees.symm

/-- The full target root is compared with the identical original cofactor and actual normalized target root. -/
def target_factor_agrees (roots : Roots step sourcePrepared) :
    NamedEquivalent roots.targetRoot.value.name (source.unitRoot.value.mul step.root.value).name :=
  NamedEquivalent.transport rfl (congrArg (fun value : CoherentNamed => value.name) step.value_eq)
    roots.target_agrees.symm

/-- Read the original source product's actual paired cofactor and exact-ordinate state. -/
def sourceProductState (state : source.value.name.process.State) :
    (source.unitRoot.value.mul (Coherence.exact (sourcePoint site parameter original).ordinate)).name.process.State :=
  source.productState state

/-- Every original source candidate is a cofactor candidate times the same retained exact normalized ordinate. -/
theorem source_candidate_factors {state : source.value.name.process.State} {candidate : Canonical}
    (possible : source.value.name.process.Possible state candidate) :
    ∃ cofactor : Canonical,
      source.unitRoot.value.name.process.Possible (sourceProductState state).1 cofactor ∧
        candidate = cofactor * (sourcePoint site parameter original).ordinate := by
  exact source.candidate_factors possible

/-- The original source product allowance pays the actual source cofactor state's semantic allowance. -/
theorem source_cofactor_allowance_le (state : source.value.name.process.State) :
    4 * Norm.Basic.normSq (sourcePoint site parameter original).ordinate *
      source.unitRoot.value.coherent.allowance (sourceProductState state).1 ≤
        source.value.coherent.allowance state := by
  have lower := Name.Coherent.Arithmetic.Product.leftAllowance_le source.unitRoot.value
    (Coherence.exact (sourcePoint site parameter original).ordinate) (sourceProductState state)
  exact lower.trans_eq (CoherentNamed.castState_allowance source.value_eq state)

/-- The target root value is precisely the retained original changed-product process with its apartification. -/
private theorem target_product_value (roots : Roots step sourcePrepared) :
    roots.targetRoot.value = step.value.apartify
      (Division.Prepared.retainedProductApart step.value source.unitRoot.value step.root.value
        step.value_eq source.unitRoot.apart step.root.apart) :=
  roots.target_value.trans ((congrArg (fun prepared : Division.Prepared step.value => prepared.denominator)
    roots.targetPrepared_eq).trans (Division.Prepared.ofProduct_denominator step.value
      source.unitRoot.value step.root.value step.value_eq source.unitRoot.apart step.root.apart))

/-- Read the actual original paired factor state below the full target certificate's apartification.

The cached full root and target preparation identify the original wrapper.
Its stored source state is reindexed only by the actual changed-product
construction equation; both resulting factor states are the original ones.
-/
def targetProductState (roots : Roots step sourcePrepared) (state : roots.targetRoot.value.name.process.State) :
    (source.unitRoot.value.mul step.root.value).name.process.State :=
  let prepared := Process.Sampling.castState
    (congrArg (fun value : CoherentNamed => value.name.process) roots.target_product_value) state
  Process.Sampling.castState (congrArg (fun value : CoherentNamed => value.name.process) step.value_eq) prepared.source

/-- The target state transport preserves the identical original paired product's semantic allowance. -/
theorem targetProductState_allowance (roots : Roots step sourcePrepared)
    (state : roots.targetRoot.value.name.process.State) :
    (source.unitRoot.value.mul step.root.value).coherent.allowance (roots.targetProductState state) =
      roots.targetRoot.value.coherent.allowance state := by
  let prepared := CoherentNamed.castState roots.target_product_value state
  have first := CoherentNamed.castState_allowance roots.target_product_value state
  have middle := CoherentNamed.apartify_allowance step.value
    (Division.Prepared.retainedProductApart step.value source.unitRoot.value step.root.value
      step.value_eq source.unitRoot.apart step.root.apart) prepared
  have last := CoherentNamed.castState_allowance step.value_eq prepared.source
  exact last.trans (middle.symm.trans first)

/-- The full target product allowance pays the original target cofactor state's semantic allowance. -/
theorem target_cofactor_allowance_le (roots : Roots step sourcePrepared)
    (state : roots.targetRoot.value.name.process.State) :
    4 * step.root.value.name.process.centerBound *
      source.unitRoot.value.coherent.allowance (roots.targetProductState state).1 ≤
        roots.targetRoot.value.coherent.allowance state :=
  (Name.Coherent.Arithmetic.Product.leftAllowance_le source.unitRoot.value step.root.value
    (roots.targetProductState state)).trans_eq (roots.targetProductState_allowance state)

/-- Every actual full target candidate decomposes using the original retained factor states. -/
theorem target_candidate_factors (roots : Roots step sourcePrepared)
    {state : roots.targetRoot.value.name.process.State} {candidate : Canonical}
    (possible : roots.targetRoot.value.name.process.Possible state candidate) :
    ∃ cofactor ordinate : Canonical,
      source.unitRoot.value.name.process.Possible (roots.targetProductState state).1 cofactor ∧
      step.root.value.name.process.Possible (roots.targetProductState state).2 ordinate ∧
        candidate = cofactor * ordinate :=
  Process.Sampling.possible_castState
    (congrArg (fun value : CoherentNamed => value.name.process) step.value_eq)
    (Process.Sampling.castState
      (congrArg (fun value : CoherentNamed => value.name.process) roots.target_product_value) state).source
    (Process.Sampling.possible_castState
      (congrArg (fun value : CoherentNamed => value.name.process) roots.target_product_value) state possible)

/-- Actual full target candidates inherit both the original cofactor floor and the normalized geometric floor. -/
theorem target_candidate_normSq_lower (roots : Roots step sourcePrepared)
    {state : roots.targetRoot.value.name.process.State} {candidate : Canonical}
    (possible : roots.targetRoot.value.name.process.Possible state candidate) :
    source.unitRoot.apart.certificate.lowerSq *
      ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) ≤ Norm.Basic.normSq candidate := by
  rcases roots.target_candidate_factors possible with ⟨cofactor, ordinate, cofactorPossible, ordinatePossible, equal⟩
  rewrite [equal, Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct
    (source.unitRoot.apart.certificate.lower _
      (source.unitRoot.value.name.process.possible_inside cofactorPossible))
    (step.candidate_normSq_lower ordinatePossible)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
    (Norm.Basic.normSq_nonneg _)

end Roots

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

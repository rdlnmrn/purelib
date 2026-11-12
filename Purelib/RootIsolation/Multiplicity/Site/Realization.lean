module

public import Purelib.RootIsolation.Multiplicity.Site.Basic
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coherent realizations of original polynomial multiplicity sites

The original site identifies its focused factor, positive multiplicity and
cofactor within the original source decomposition. A realization retains that
same parent and its initial root track, actual approximation cache, computed
cofactor and scalar bound. Its source equation concerns the original polynomial.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Site

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

set_option genInjectivity false in
/-- The initial coherent root realization and cached cofactor of one original positive-multiplicity site.

The root is indexed by the site's actual focused-factor track. The cached
cofactor and bound retain their defining equations at that same parent, and
the stored operational equation evaluates the original source polynomial.
-/
structure Realization {source opposite : CoefficientPolynomial}
    (input : Basic.TrackSiteInput source opposite) where
  /-- The actual initial root certificate and its retained approximation cache. -/
  root : CoherentRoot.CertifiedName input.track
  /-- The retained polynomial after removing one occurrence of the focused factor. -/
  cofactor : CoefficientPolynomial
  /-- The cached cofactor is computed from this exact original decomposition and occurrence. -/
  cofactor_eq : cofactor = input.context.singleCofactor input.decomposition
  /-- The computed squared-norm bound for this cofactor on the original factor's ambient box. -/
  cofactorBound : Rational
  /-- The bound is the original coefficient-derived box evaluation bound. -/
  cofactorBound_eq : cofactorBound = Bounds.Box.denseEvalNormBound cofactor input.ambient
  /-- Horner evaluation of the original source at this actual root channel is operationally zero. -/
  equation : NamedEquivalent (Horner.polynomialEval source root.value).name (Coherence.exact 0).name

constructive_injectivity Realization

namespace Realization

/-- Construct the original site realization from its supplied original-track root certificate.

The same literal root is retained. The original factorization supplies its
source equation, and the coefficient fold computes the cached cofactor bound
without reconstructing the root or its approximation.
-/
@[expose] def ofRoot {source opposite : CoefficientPolynomial}
    (input : Basic.TrackSiteInput source opposite) (root : CoherentRoot.CertifiedName input.track) :
    Realization input := by
  let cofactor := input.context.singleCofactor input.decomposition
  let bound := Bounds.Box.denseEvalNormBound cofactor input.ambient
  have boundNonnegative : 0 ≤ bound :=
    (Bounds.Box.denseHornerNormBounds_nonneg cofactor input.ambient).1
  have bounded : ∀ index, normSq (cofactor.eval (root.approximation.sample index)) ≤ bound :=
    fun index => Bounds.Box.normSq_eval_le_denseEvalNormBound cofactor (root.sample_inside index)
  have identity : ∀ point, source.eval point = input.context.focus.part.polynomial.eval point * cofactor.eval point :=
    fun point => Dense.Gaussian.Factorization.Identity.eval_factorization
      (input.context.focusFactorization input.decomposition rfl) point
  exact
    { root := root
      cofactor := cofactor
      cofactor_eq := rfl
      cofactorBound := bound
      cofactorBound_eq := rfl
      equation := root.factor_zero source cofactor identity bound boundNonnegative bounded }

/-- Construct the original site realization with an optional checked original-state bank.

The original root constructor consumes this literal retained bank. The same
root-based realization constructor supplies the unchanged original cofactor,
bound and source equation without repeating root isolation or refinement.
-/
@[expose] def ofInput {source opposite : CoefficientPolynomial}
    (input : Basic.TrackSiteInput source opposite)
    (cached : Option (List (CoherentRoot.StateCache.Entry input.track)) := none) : Realization input :=
  ofRoot input (CoherentRoot.certifiedName input.track input.context.focus.degreePositive cached)

/-- The absent state bank preserves the entire original root, cofactor, bound and source-equation record. -/
theorem ofInput_none {source opposite : CoefficientPolynomial}
    (input : Basic.TrackSiteInput source opposite) :
    ofInput input none = (by
      let root := CoherentRoot.certifiedName input.track input.context.focus.degreePositive
      let cofactor := input.context.singleCofactor input.decomposition
      let bound := Bounds.Box.denseEvalNormBound cofactor input.ambient
      have boundNonnegative : 0 ≤ bound :=
        (Bounds.Box.denseHornerNormBounds_nonneg cofactor input.ambient).1
      have bounded : ∀ index, normSq (cofactor.eval (root.approximation.sample index)) ≤ bound :=
        fun index => Bounds.Box.normSq_eval_le_denseEvalNormBound cofactor (root.sample_inside index)
      have identity : ∀ point,
          source.eval point = input.context.focus.part.polynomial.eval point * cofactor.eval point :=
        fun point => Dense.Gaussian.Factorization.Identity.eval_factorization
          (input.context.focusFactorization input.decomposition rfl) point
      exact
        { root := root
          cofactor := cofactor
          cofactor_eq := rfl
          cofactorBound := bound
          cofactorBound_eq := rfl
          equation := root.factor_zero source cofactor identity bound boundNonnegative bounded }) := rfl

/-- A checked retained state bank preserves the complete original site realization and source equation.

The root constructor consumes that same literal bank and retains whole root
identity. Its original cofactor, bound, channel and residual-based source
equation therefore remain fields of the same complete original realization.
-/
theorem ofInput_cached_eq_default {source opposite : CoefficientPolynomial}
    (input : Basic.TrackSiteInput source opposite)
    (cached : Option (List (CoherentRoot.StateCache.Entry input.track))) :
    ofInput input cached = ofInput input none := by
  exact congrArg (ofRoot input)
    (CoherentRoot.certifiedName_cached_eq_default input.track input.context.focus.degreePositive cached)

/-- The original focused squarefree factor admitted at its actual positive degree.

This view preserves the original site's complete decomposition and focused
multiplicity; only the factor data needed for root identification is projected.
-/
abbrev factorInput {source opposite : CoefficientPolynomial}
    {input : Basic.TrackSiteInput source opposite} (_realization : Realization input) :
    FTA.Positive.Input.PositiveInput input.context.focus.part.polynomial :=
  ⟨input.context.focus.part.squarefree, input.context.focus.degreePositive⟩

/-- Compare two original multiplicity-site channels through their retained focused squarefree factors.

Both complete original sites remain indices of the inputs, including their
source polynomials, multiplicities and source equations. Identification uses
the actual retained root caches and computes its common source and sufficient
refinement internally; no multiplicity or source channel is replaced. The
checked initial request is enabled by default and shares the same original
comparison procedure used by algebraic Sidecars. An explicit false request
retains the original full common-source path.
-/
@[expose] def compare {firstSource firstOpposite secondSource secondOpposite : CoefficientPolynomial}
    {firstInput : Basic.TrackSiteInput firstSource firstOpposite}
    {secondInput : Basic.TrackSiteInput secondSource secondOpposite}
    (first : Realization firstInput) (second : Realization secondInput) (firstStart secondStart : Nat)
    (inspectInitial : Bool := true) (inspectLocal : Bool := inspectInitial) :
    CoherentRoot.CommonSource.PreparedComparison first.factorInput second.factorInput
      first.root second.root firstStart secondStart :=
  CoherentRoot.CommonSource.prepareComparison first.factorInput second.factorInput
    first.root second.root firstStart secondStart inspectInitial inspectLocal

/-- Disabling the checked initial request retains the entire original common-source comparison procedure. -/
theorem compare_default {firstSource firstOpposite secondSource secondOpposite : CoefficientPolynomial}
    {firstInput : Basic.TrackSiteInput firstSource firstOpposite}
    {secondInput : Basic.TrackSiteInput secondSource secondOpposite}
    (first : Realization firstInput) (second : Realization secondInput) (firstStart secondStart : Nat) :
    first.compare second firstStart secondStart false =
      CoherentRoot.CommonSource.prepareComparison first.factorInput second.factorInput
        first.root second.root firstStart secondStart false := rfl

/-- The original site comparison retains the same actual checked-initial request at its result owner. -/
theorem compare_request {firstSource firstOpposite secondSource secondOpposite : CoefficientPolynomial}
    {firstInput : Basic.TrackSiteInput firstSource firstOpposite}
    {secondInput : Basic.TrackSiteInput secondSource secondOpposite}
    (first : Realization firstInput) (second : Realization secondInput) (firstStart secondStart : Nat)
    (inspectInitial : Bool) :
    (first.compare second firstStart secondStart inspectInitial).inspectInitial = inspectInitial := rfl

end Realization

end Purelib.RootIsolation.Multiplicity.Site

end

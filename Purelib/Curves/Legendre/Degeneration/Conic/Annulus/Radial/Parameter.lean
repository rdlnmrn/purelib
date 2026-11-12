module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
public import Purelib.Riemann.Topology.SquareRootContinuationChain.Exact
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Polynomial.Quadratic.Split
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Fixed-spatial-point parameter channels from an original regular parallel point

The source radial point supplies its exact normalized ordinate and its
complete original cubic lift. Parameter increments keep that source spatial
point fixed. The cofactor polynomial is unchanged; only the normalized square
changes by minus the fixed source branch factor times the increment.

The original parallel ordinate floor and computed branch-factor ceiling pay
a uniform positive increment budget against the actual known-root seed owner.
The source conic point, its labelled parameter and its original unit owner and
certificate remain the parents of the construction.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

/-- The complete original scale-two source conic point on the retained unit direction. -/
@[expose] def sourcePoint (site : Fin 2) (parameter : Canonical) (original : UnitVertex) : Point site parameter :=
  Radial.point site parameter 2 original (by decide +kernel)

/-- The fixed original spatial factor multiplying parameter displacement in the normalized quadratic. -/
@[expose] def branchFactor (site : Fin 2) (parameter : Canonical) (original : UnitVertex) : Canonical :=
  (sourcePoint site parameter original).base - criticalValue site

/-- The actual target normalized radicand on the identical source spatial point. -/
@[expose] def radicand (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (increment : Canonical) : Canonical :=
  (sourcePoint site parameter original).ordinate ^ 2 - branchFactor site parameter original * increment

/-- The source branch factor retains the exact original half-gap and computed parallel ellipse direction. -/
private theorem branchFactor_eq (site : Fin 2) (parameter : Canonical) (original : UnitVertex) :
    branchFactor site parameter original = halfGap site parameter * (1 + baseDirection 2 original.value) := by
  have endpoint := Polynomial.Quadratic.Split.center_sub_halfGap (criticalValue site) parameter
    (by decide +kernel : (2 : Canonical) ≠ 0)
  change center site parameter - halfGap site parameter = criticalValue site at endpoint
  unfold branchFactor sourcePoint
  rewrite [point_base, ← endpoint]
  ring1

/-- Every original parallel source has the same internally computed branch-factor norm ceiling. -/
theorem branchFactor_normSq_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex) :
    Norm.Basic.normSq (branchFactor site parameter original) ≤
      (41 / 8) * Norm.Basic.normSq (halfGap site parameter) := by
  have directionBound := baseDirection_normSq_le 2 original.value
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rewrite [original.unit, Fraction.Field.mul_one_direct] at directionBound
  have sumBound : Norm.Basic.normSq (1 + baseDirection 2 original.value) ≤ (41 / 8 : Fraction.Rational) := by
    calc
      _ ≤ 2 * (Norm.Basic.normSq (1 : Canonical) + Norm.Basic.normSq (baseDirection 2 original.value)) :=
        Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (1 + 25 / 16) := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct (by decide +kernel) directionBound) (by decide +kernel)
      _ = _ := by decide +kernel
  rewrite [branchFactor_eq, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (Norm.Basic.normSq_nonneg _)).trans_eq
    (Fraction.Field.mul_comm _ _)

/-- The fixed-source target radicand is the original centered quadratic at the changed parameter. -/
theorem radicand_eq (site : Fin 2) (parameter : Canonical) (original : UnitVertex) (increment : Canonical) :
    radicand site parameter original increment =
      coordinate site (parameter + increment) (sourcePoint site parameter original).base ^ 2 -
        smoothing site (parameter + increment) := by
  have sourceSplit := Polynomial.Quadratic.Split.product_eq (criticalValue site) parameter
    (sourcePoint site parameter original).base (by decide +kernel : (2 : Canonical) ≠ 0)
  have targetSplit := Polynomial.Quadratic.Split.product_eq (criticalValue site) (parameter + increment)
    (sourcePoint site parameter original).base (by decide +kernel : (2 : Canonical) ≠ 0)
  change _ = coordinate site parameter (sourcePoint site parameter original).base ^ 2 - smoothing site parameter
    at sourceSplit
  change _ = coordinate site (parameter + increment) (sourcePoint site parameter original).base ^ 2 -
    smoothing site (parameter + increment) at targetSplit
  have sourceSquare := (sourcePoint site parameter original).quadratic
  rewrite [← (sourcePoint site parameter original).coordinate_base] at sourceSquare
  unfold radicand branchFactor
  rewrite [sourceSquare, ← sourceSplit, ← targetSplit]
  ring1

/-- The exact original uniform increment admission proposition on the fixed source parallel point. -/
@[expose] def IncrementBound (site : Fin 2) (parameter increment : Canonical) : Prop :=
  Norm.Basic.normSq increment ≤ (1 / 256) * Norm.Basic.normSq (halfGap site parameter)

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}

set_option genInjectivity false in
/-- An original parallel cubic lift with its actual known-normalized-root seed and intrinsic source admission. -/
structure Anchor (source : Lift (sourcePoint site parameter original) unit) where
  /-- The retained original parameter is regular at the labelled collision. -/ regular : parameter ≠ criticalValue site
  /-- The complete original radial-family parameter admission. -/
  bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)
  /-- The actual original known-root seed of the exact source normalized ordinate. -/
  seed : Exact.Seed (sourcePoint site parameter original).ordinate

constructive_injectivity Anchor

namespace Anchor

variable {source : Lift (sourcePoint site parameter original) unit}

/-- Construct the normalized known-root seed while retaining the same original source lift and cofactor cache. -/
def build (source : Lift (sourcePoint site parameter original) unit)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) : Anchor source :=
  { regular := regular
    bound := bound
    seed := Exact.Seed.build (sourcePoint site parameter original).ordinate
      (parallel_ordinate_ne_zero site parameter original regular) }

/-- The original labelled half-gap has positive squared norm at the retained regular source. -/
theorem gapNorm_positive (anchor : Anchor source) : 0 < Norm.Basic.normSq (halfGap site parameter) :=
  Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero
    (by decide +kernel : (2 : Canonical) ≠ 0) anchor.regular.symm)

/-- The actual source normalized owner has its uniform original half-gap fourth-power clearance floor. -/
theorem clearance_lower (anchor : Anchor source) :
    (729 / 16384) * Norm.Basic.normSq (halfGap site parameter) ^ 2 ≤
      anchor.seed.owner.track.initial.clearance.bound := by
  have ordinateBound := parallel_ordinate_lower site parameter original
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)) ordinateBound 2
  calc
    _ = ((9 / 64) * (9 / 16) ^ 2) * Norm.Basic.normSq (halfGap site parameter) ^ 2 :=
      congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter) ^ 2)
        (show ((9 / 64) * (9 / 16) ^ 2 : Fraction.Rational) = 729 / 16384 from by
          change (((9 : Nat) : Fraction.Rational) / ((64 : Nat) : Fraction.Rational)) *
              (((9 : Nat) : Fraction.Rational) / ((16 : Nat) : Fraction.Rational)) ^ 2 =
            ((729 : Nat) : Fraction.Rational) / ((16384 : Nat) : Fraction.Rational)
          rewrite [Fraction.Cast.natCast_eq_fromInt 9, Fraction.Cast.natCast_eq_fromInt 64,
            Fraction.Cast.natCast_eq_fromInt 16, Fraction.Cast.natCast_eq_fromInt 729,
            Fraction.Cast.natCast_eq_fromInt 16384]
          decide +kernel).symm
    _ = (9 / 64) * ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) ^ 2 := by ring1
    _ ≤ (9 / 64) * Norm.Basic.normSq (sourcePoint site parameter original).ordinate ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct squared (by decide +kernel)
    _ ≤ _ := anchor.seed.clearance_lower

/-- The original fixed-source radicand movement is paid by the same uniform increment and branch-factor budgets. -/
theorem movement_le (_anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :
    Norm.Basic.normSq ((sourcePoint site parameter original).ordinate ^ 2 -
        radicand site parameter original increment) ≤
      (41 / 2048) * Norm.Basic.normSq (halfGap site parameter) ^ 2 := by
  have difference : (sourcePoint site parameter original).ordinate ^ 2 -
      radicand site parameter original increment = branchFactor site parameter original * increment := by
    unfold radicand
    ring1
  rewrite [difference, Norm.Basic.normSq_mul]
  calc
    _ ≤ ((41 / 8) * Norm.Basic.normSq (halfGap site parameter)) *
        ((1 / 256) * Norm.Basic.normSq (halfGap site parameter)) :=
      Arithmetic.mul_le_mul_direct (branchFactor_normSq_le site parameter original) admitted
        (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct
          (by decide +kernel) (Norm.Basic.normSq_nonneg _))
    _ = ((41 / 8) * (1 / 256)) * Norm.Basic.normSq (halfGap site parameter) ^ 2 := by ring1
    _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter) ^ 2)
      (by
        change (((41 : Nat) : Fraction.Rational) / ((8 : Nat) : Fraction.Rational)) *
            (((1 : Nat) : Fraction.Rational) / ((256 : Nat) : Fraction.Rational)) =
          ((41 : Nat) : Fraction.Rational) / ((2048 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 41, Fraction.Cast.natCast_eq_fromInt 8,
          Fraction.Cast.natCast_eq_fromInt 1, Fraction.Cast.natCast_eq_fromInt 256,
          Fraction.Cast.natCast_eq_fromInt 2048]
        decide +kernel)

/-- Every admitted original parameter increment pays an actual accepted normalized-root move internally. -/
theorem movement_small (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :
    Norm.Basic.normSq ((sourcePoint site parameter original).ordinate ^ 2 -
        radicand site parameter original increment) < anchor.seed.owner.track.initial.clearance.bound :=
  (anchor.movement_le increment admitted).trans_lt
    ((Arithmetic.mul_lt_mul_of_pos_right_direct
      (by
        change ((41 : Nat) : Fraction.Rational) / ((2048 : Nat) : Fraction.Rational) <
          ((729 : Nat) : Fraction.Rational) / ((16384 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 41, Fraction.Cast.natCast_eq_fromInt 2048,
          Fraction.Cast.natCast_eq_fromInt 729, Fraction.Cast.natCast_eq_fromInt 16384]
        decide +kernel)
      (Arithmetic.pow_pos_direct anchor.gapNorm_positive 2)).trans_le anchor.clearance_lower)

/-- An admitted original parameter increment keeps the actual fixed-source normalized radicand nonzero. -/
theorem radicand_ne_zero (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : radicand site parameter original increment ≠ 0 := by
  have ordinateBound := parallel_ordinate_lower site parameter original
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)) ordinateBound 2
  have sourceLower : (81 / 256) * Norm.Basic.normSq (halfGap site parameter) ^ 2 ≤
      Norm.Basic.normSq ((sourcePoint site parameter original).ordinate ^ 2) := by
    rewrite [Data.Gaussian.Power.normSq_pow]
    exact (show (81 / 256) * Norm.Basic.normSq (halfGap site parameter) ^ 2 =
      ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) ^ 2 from by
        calc
          _ = (9 / 16 : Fraction.Rational) ^ 2 * Norm.Basic.normSq (halfGap site parameter) ^ 2 :=
            congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter) ^ 2)
              (by decide +kernel : (9 / 16 : Fraction.Rational) ^ 2 = 81 / 256).symm
          _ = _ := by ring1).trans_le squared
  have smallSource := (anchor.movement_le increment admitted).trans_lt
    ((Arithmetic.mul_lt_mul_of_pos_right_direct
      (by
        change ((41 : Nat) : Fraction.Rational) / ((2048 : Nat) : Fraction.Rational) <
          ((81 : Nat) : Fraction.Rational) / ((256 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 41, Fraction.Cast.natCast_eq_fromInt 2048,
          Fraction.Cast.natCast_eq_fromInt 81, Fraction.Cast.natCast_eq_fromInt 256]
        decide +kernel)
      (Arithmetic.pow_pos_direct anchor.gapNorm_positive 2)).trans_le sourceLower)
  intro zero
  rewrite [zero, Basic.sub_zero] at smallSource
  exact smallSource.2 smallSource.1

/-- The retained known-normalized-root source channel multiplied by the same original cofactor cache. -/
@[expose] def sourceValue (anchor : Anchor source) : CoherentNamed :=
  source.unitRoot.value.mul anchor.seed.certificate.value

/-- The known-root source cube agrees with the complete original parallel cubic lift channel. -/
def source_agrees (anchor : Anchor source) : NamedEquivalent anchor.sourceValue.name source.value.name := by
  have compared := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    source.unitRoot.value source.unitRoot.value anchor.seed.certificate.value
    (Coherence.exact (sourcePoint site parameter original).ordinate)
    (NamedEquivalent.refl _) anchor.seed.agrees_exact
  exact NamedEquivalent.transport rfl
    (congrArg (fun value : CoherentNamed => value.name) source.value_eq.symm) compared

end Anchor

/-- The actual product of the same cached original cofactor and normalized root has its original cubic square. -/
private def cubicSquare (source : Lift (sourcePoint site parameter original) unit) (increment : Canonical)
    (normalized : CertifiedSquareRoot.Certificate (radicand site parameter original increment)) :
    NamedEquivalent
      ((source.unitRoot.value.mul normalized.value).mul (source.unitRoot.value.mul normalized.value)).name
      (Named.exact ((Paths.polynomial (parameter + increment)).eval (sourcePoint site parameter original).base)) := by
  let bindings : Fin 2 → CoherentNamed :=
    Data.Fin.cases source.unitRoot.value (fun _ => normalized.value)
  let first := Normalized.atom bindings 0
  let second := Normalized.atom bindings 1
  let product := (first.mul second).mul (first.mul second)
  let factored := (first.mul first).mul (second.mul second)
  have forms : product.form.terms = factored.form.terms := by
    dsimp only [product, factored, first, second]
    simp only [Normalized.mul_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  have factorization := product.compare factored forms
  have roots := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    (source.unitRoot.value.mul source.unitRoot.value)
    (Coherence.exact ((unitPolynomial site).eval (sourcePoint site parameter original).base))
    (normalized.value.mul normalized.value) (Coherence.exact (radicand site parameter original increment))
    source.unitRoot.square normalized.square
  have scalar : (unitPolynomial site).eval (sourcePoint site parameter original).base *
      radicand site parameter original increment =
      (Paths.polynomial (parameter + increment)).eval (sourcePoint site parameter original).base := by
    rewrite [radicand_eq, polynomial_centered]
    exact Basic.mul_comm _ _
  exact factorization.trans (roots.trans (NamedEquivalent.transport rfl (congrArg Named.exact scalar)
    (Name.Coherent.Exact.Arithmetic.exact_mul _ _)))

set_option genInjectivity false in
/-- One actual normalized-root move on the fixed source point with the unchanged original cofactor and cubic channels.

The full source lift and anchor remain indices. The target root owner is the
accepted advance of that anchor's exact source owner. The target cubic value
and forward coordinates consume the identical original cofactor certificate;
their original curve and conic square laws are derived internally.
-/
structure Step {source : Lift (sourcePoint site parameter original) unit} (anchor : Anchor source)
    (increment : Canonical) where
  /-- The exact original uniform increment admission payment. -/ admitted : IncrementBound site parameter increment
  /-- The actual normalized target owner on the same original fixed source point. -/
  target : Owner (radicand site parameter original increment)
  /-- The target owner is the accepted move of the identical retained normalized source owner. -/
  target_eq : target = anchor.seed.owner.advance (anchor.radicand_ne_zero increment admitted)
    (anchor.movement_small increment admitted)
  /-- The actual advanced normalized target certificate cached once. -/
  root : CertifiedSquareRoot.Certificate (radicand site parameter original increment)
  /-- The root certificate is the complete certificate of that same retained actual target owner. -/
  root_eq : root = target.certificate target.parameterNonzero
  /-- The target cubic channel constructed on the original unchanged cofactor certificate. -/ value : CoherentNamed
  /-- The actual target value retains the identical source cofactor channel and cached normalized target root. -/
  value_eq : value = source.unitRoot.value.mul root.value
  /-- The target channel has the original curve square at the changed parameter and identical fixed source point. -/
  square : NamedEquivalent (value.mul value).name
    (Named.exact ((Paths.polynomial (parameter + increment)).eval (sourcePoint site parameter original).base))
  /-- The original forward-coordinate construction at that same fixed point and changed parameter. -/
  channels : CoordinateChannels site (parameter + increment) (sourcePoint site parameter original).base
    value source.unitOwner
  /-- Its cofactor cache is the identical complete original source certificate. -/
  channels_unitRoot : channels.unitRoot = source.unitRoot

constructive_injectivity Step

namespace Step

variable {source : Lift (sourcePoint site parameter original) unit} {anchor : Anchor source} {increment : Canonical}

/-- Construct the actual accepted parameter move and original target cubic channels, paying all movement internally. -/
def build (anchor : Anchor source) (increment : Canonical) (admitted : IncrementBound site parameter increment) :
    Step anchor increment := by
  let target := anchor.seed.owner.advance (anchor.radicand_ne_zero increment admitted)
    (anchor.movement_small increment admitted)
  let root := target.certificate target.parameterNonzero
  let value := source.unitRoot.value.mul root.value
  let square := cubicSquare source increment root
  let channels := CoordinateChannels.ofRoot site (parameter + increment) (sourcePoint site parameter original).base
    value square source.unitOwner source.unitRoot source.unitRoot_eq
  exact
    { admitted := admitted
      target := target
      target_eq := rfl
      root := root
      root_eq := rfl
      value := value
      value_eq := rfl
      square := square
      channels := channels
      channels_unitRoot := CoordinateChannels.ofRoot_unitRoot _ _ _ value square
        source.unitOwner source.unitRoot source.unitRoot_eq }

/-- The actual normalized target owner retains a box refining the exact original known-root source window. -/
theorem target_refines (step : Step anchor increment) :
    step.target.track.initial.box.Refines anchor.seed.owner.track.initial.box := by
  rewrite [step.target_eq]
  exact anchor.seed.owner.advance_initial_box_refines (anchor.radicand_ne_zero increment step.admitted)
    (anchor.movement_small increment step.admitted)

/-- Every cached normalized target reading remains in the identical original signed source window. -/
theorem target_candidate_inside (step : Step anchor increment) {candidate : Canonical}
    {state : step.root.value.name.process.State} (possible : step.root.value.name.process.Possible state candidate) :
    (Purelib.Geometry.Rational.Box.Square.Centered.Affine.centeredSquare
      (sourcePoint site parameter original).ordinate anchor.seed.separation.radius
      anchor.seed.separation.positive.le).Contains candidate := by
  have inside := CertifiedSquareRoot.Sampling.candidate_in_initial_box step.target step.root_eq possible
  have sourceInside := step.target_refines.contains inside
  rewrite [anchor.seed.box_eq] at sourceInside
  exact sourceInside

/-- Source and target normalized readings in the retained original window have the same internally paid sum floor. -/
theorem sum_normSq_lower (step : Step anchor increment) {first last : Canonical}
    {sourceState : anchor.seed.certificate.value.name.process.State} {targetState : step.root.value.name.process.State}
    (sourcePossible : anchor.seed.certificate.value.name.process.Possible sourceState first)
    (targetPossible : step.root.value.name.process.Possible targetState last) :
    4 * anchor.seed.separation.radius ^ 2 ≤ Norm.Basic.normSq (first + last) :=
  anchor.seed.separation.sum_normSq_lower (anchor.seed.candidate_inside sourcePossible)
    (step.target_candidate_inside targetPossible)

/-- The original target forward ordinate agrees with the retained normalized-root channel used to construct it. -/
def normalized_agrees (step : Step anchor increment) :
    NamedEquivalent step.channels.ordinate.name step.root.value.name := by
  have cacheName := congrArg (fun certificate =>
    (step.channels.ordinate.mul certificate.value).name) step.channels_unitRoot
  have recovers := NamedEquivalent.transport cacheName rfl step.channels.recovers
  have exchanged := Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm
    source.unitRoot.value step.channels.ordinate
  have valueName := congrArg (fun value : CoherentNamed => value.name) step.value_eq
  exact Division.Cancellation.coherentMul_cancel_left source.unitRoot.value step.channels.ordinate step.root.value
    source.unitRoot.apart (exchanged.trans (NamedEquivalent.transport rfl valueName recovers))

end Step

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

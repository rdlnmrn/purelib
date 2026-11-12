module

import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Geometry.Rational.Box.Square.Centered.Separation
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Exact
import Purelib.RootIsolation.Owner.Local.Split
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Gaussian.Power
import Purelib.Data.List.DropWhile.Basic
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original square-root owners seeded by a known nonzero root

A computed signed square gives an actual split-pair owner for `Z²-root²`.
Its original initial state, quadratic acceleration, exact clearance and
certificate are retained. The certificate's existing square comparison and
the same signed window prove operational agreement with the exact input root.
No root isolation or replacement sampler is used.
-/

public section

namespace Purelib.Riemann.Topology.SquareRootContinuationChain.Owner.Exact

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Square.Centered (Separation)
open Purelib.RootIsolation
open Purelib.RootIsolation.Owner
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- The original displayed quadratic table is the product of its two retained exact-root affine factors. -/
private theorem polynomial_eq (root : Canonical) (nonzero : root ≠ 0) :
    Power.Gaussian.rootPolynomial (root ^ 2) SquareRootDegree.degreeTwo =
      Dense.Gaussian.Linear.Translated.translatedCoordinate root *
        Dense.Gaussian.Linear.Translated.translatedCoordinate (-root) := by
  let factor : DensePolynomial Canonical := ⟨[1, root]⟩
  have factorNormalized : factor.normalize = factor :=
    DensePolynomial.normalize_linear_of_leading_ne_zero (by decide +kernel : (1 : Canonical) ≠ 0)
  have negativeNonzero : -root ≠ 0 := by
    intro zero
    exact nonzero (by
      have reversed := congrArg (fun value : Canonical => -value) zero
      rewrite [show -(-root) = root by ring1, show -(0 : Canonical) = 0 by decide +kernel] at reversed
      exact reversed)
  have scaled : DensePolynomial.scale (-root) factor = ⟨[-root, -(root ^ 2)]⟩ := by
    apply DensePolynomial.ext
    rewrite [DensePolynomial.scale_coeffs_of_ne_zero negativeNonzero, factorNormalized]
    change [-root * 1, -root * root] = [-root, -(root ^ 2)]
    exact congrArg₂ List.cons (Basic.mul_one _) (congrArg₂ List.cons (by ring1) rfl)
  have shifted : DensePolynomial.shift 1 factor = ⟨[1, root, 0]⟩ := by
    have factorNonzero : factor.isZero = false := by
      unfold DensePolynomial.isZero
      rewrite [factorNormalized]
      rfl
    unfold DensePolynomial.shift
    rewrite [if_neg (by intro zero; have impossible : false = true := factorNonzero.symm.trans zero; cases impossible),
      factorNormalized]
    rfl
  have product : Dense.Gaussian.Linear.Translated.translatedCoordinate root *
      Dense.Gaussian.Linear.Translated.translatedCoordinate (-root) =
      DensePolynomial.shift 1 factor + DensePolynomial.scale (-root) factor := by
    change DensePolynomial.mulPolynomial ⟨[1, -root]⟩ ⟨[1, -(-root)]⟩ = _
    rewrite [show -(-root) = root by ring1]
    unfold DensePolynomial.mulPolynomial
    rewrite [List.foldl_cons, List.foldl_cons, List.foldl_nil, DensePolynomial.shift_zero,
      DensePolynomial.scale_one_left, DensePolynomial.zero_add_normalize, factorNormalized, factorNormalized]
    rfl
  rewrite [product, shifted, scaled]
  apply DensePolynomial.ext
  change [1, 0, -(root ^ 2)] =
    ([1 + 0, root + -root, 0 + -(root ^ 2)] : List Canonical).dropWhile (fun value => decide (value = 0))
  rewrite [show (1 : Canonical) + 0 = 1 by ring1, show root + -root = 0 by ring1,
    show (0 : Canonical) + -(root ^ 2) = -(root ^ 2) by ring1,
    Data.List.DropWhile.cons_of_false (fun value : Canonical => decide (value = 0))
      1 [0, -(root ^ 2)] (decide_eq_false (by decide +kernel : (1 : Canonical) ≠ 0))]
  rfl

/-- Reindex the original split-pair owner to its exact original quadratic table. -/
@[irreducible] private def splitOwner (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) :
    Local.Basic.LocalOwner (Owner.rootPolynomial (root ^ 2)) :=
  Local.Transport.castOwner (polynomial_eq root nonzero).symm
    (Local.Basic.LocalOwner.ofSplitPair root (-root) separation.positive separation.opposite)

/-- The reindexed original split owner retains the identical signed-square box. -/
private theorem splitOwner_box (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) :
    (splitOwner root nonzero separation).box =
      Box.Square.Centered.Affine.centeredSquare root separation.radius separation.positive.le := by
  unfold splitOwner
  exact (Local.Transport.castOwner_box _ _).trans
    (Local.Basic.LocalOwner.ofSplitPair_box root (-root) separation.positive separation.opposite)

/-- The reindexed original split owner retains the original product clearance. -/
private theorem splitOwner_clearance (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) :
    (splitOwner root nonzero separation).clearance.bound = 9 * separation.radius ^ 4 := by
  unfold splitOwner
  rewrite [Local.Transport.castOwner_clearance_bound, Local.Basic.LocalOwner.ofSplitPair_clearance_bound,
    separation.opposite_margin]
  ring1

/-- Accelerate the original local initial state without rebuilding its box or clearance. -/
@[irreducible] private def acceleratedOwner (root : Canonical) (nonzero : root ≠ 0)
    (localOwner : Local.Basic.LocalOwner (Owner.rootPolynomial (root ^ 2))) : Owner (root ^ 2) :=
  Owner.ofState (Data.Gaussian.Power.pow_ne_zero_direct root nonzero 2) localOwner.initialState

/-- The accelerated owner retains the exact original local box. -/
private theorem acceleratedOwner_box (root : Canonical) (nonzero : root ≠ 0)
    (localOwner : Local.Basic.LocalOwner (Owner.rootPolynomial (root ^ 2))) :
    (acceleratedOwner root nonzero localOwner).track.initial.box = localOwner.box := by
  unfold acceleratedOwner
  rewrite [Owner.ofState_initial]
  exact localOwner.initialState_box

/-- The accelerated owner retains the exact original local boundary-clearance bound. -/
private theorem acceleratedOwner_clearance (root : Canonical) (nonzero : root ≠ 0)
    (localOwner : Local.Basic.LocalOwner (Owner.rootPolynomial (root ^ 2))) :
    (acceleratedOwner root nonzero localOwner).track.initial.clearance.bound = localOwner.clearance.bound := by
  unfold acceleratedOwner
  rewrite [Owner.ofState_initial]
  exact localOwner.initialState_clearance_bound

/-- Retain the accelerated original split owner under its complete original quadratic index. -/
@[irreducible] private def seedOwner (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) :
    Owner (root ^ 2) :=
  acceleratedOwner root nonzero (splitOwner root nonzero separation)

/-- The complete seeded owner retains the same original signed-square box. -/
private theorem seedOwner_box (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) :
    (seedOwner root nonzero separation).track.initial.box =
      Box.Square.Centered.Affine.centeredSquare root separation.radius separation.positive.le := by
  unfold seedOwner
  exact (acceleratedOwner_box root nonzero (splitOwner root nonzero separation)).trans
    (splitOwner_box root nonzero separation)

/-- The complete seeded owner retains the same original split-pair clearance bound. -/
private theorem seedOwner_clearance (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) :
    (seedOwner root nonzero separation).track.initial.clearance.bound = 9 * separation.radius ^ 4 := by
  unfold seedOwner
  exact (acceleratedOwner_clearance root nonzero (splitOwner root nonzero separation)).trans
    (splitOwner_clearance root nonzero separation)

set_option genInjectivity false in
/-- One original known-root seed retaining its computed signed square, actual root owner and cached certificate. -/
structure Seed (root : Canonical) where
  /-- The original signed-square geometry computed from the retained exact root. -/ separation : Separation root
  /-- The actual original square-root owner of the exact root's square. -/ owner : Owner (root ^ 2)
  /-- Its complete original initial box is the same computed signed square. -/
  box_eq : owner.track.initial.box =
    Box.Square.Centered.Affine.centeredSquare root separation.radius separation.positive.le
  /-- The original split-pair clearance is exactly nine times that retained radius to the fourth power. -/
  clearance_eq : owner.track.initial.clearance.bound = 9 * separation.radius ^ 4
  /-- The complete original owner certificate cached once. -/ certificate : CertifiedSquareRoot.Certificate (root ^ 2)
  /-- The cached certificate belongs to this identical full original owner. -/
  certificate_eq : certificate = owner.certificate owner.parameterNonzero

constructive_injectivity Seed

namespace Seed

/-- Retain one original owner and its full certificate behind the exact signed-square readback laws. -/
private def ofOwner (root : Canonical) (separation : Separation root) (owner : Owner (root ^ 2))
    (certificate : CertifiedSquareRoot.Certificate (root ^ 2))
    (box : owner.track.initial.box =
      Box.Square.Centered.Affine.centeredSquare root separation.radius separation.positive.le)
    (clearance : owner.track.initial.clearance.bound = 9 * separation.radius ^ 4)
    (certificateEq : certificate = Owner.certificate owner owner.parameterNonzero) : Seed root :=
  { separation := separation
    owner := owner
    box_eq := box
    clearance_eq := clearance
    certificate := certificate
    certificate_eq := certificateEq }

/-- Assemble the retained split-pair seed using the same original signed-square input. -/
private def ofSeparation (root : Canonical) (nonzero : root ≠ 0) (separation : Separation root) : Seed root := by
  let owner : Owner (root ^ 2) := seedOwner root nonzero separation
  let certificate : CertifiedSquareRoot.Certificate (root ^ 2) := Owner.certificate owner owner.parameterNonzero
  exact ofOwner root separation owner certificate (seedOwner_box root nonzero separation)
    (seedOwner_clearance root nonzero separation) rfl

/-- Construct an actual original quadratic owner directly from the exact nonzero input root and its opposite. -/
def build (root : Canonical) (nonzero : root ≠ 0) : Seed root :=
  ofSeparation root nonzero (Separation.build root nonzero)

/-- Every original cached-certificate reading remains in the identical computed seed square. -/
theorem candidate_inside {root candidate : Canonical} (seed : Seed root)
    {state : seed.certificate.value.name.process.State}
    (possible : seed.certificate.value.name.process.Possible state candidate) :
    (Box.Square.Centered.Affine.centeredSquare root seed.separation.radius seed.separation.positive.le).Contains
      candidate := by
  have inside := CertifiedSquareRoot.Sampling.candidate_in_initial_box seed.owner seed.certificate_eq possible
  rewrite [seed.box_eq] at inside
  exact inside

/-- The original exact-root seed has its uniform centre-norm fourth-power boundary-clearance floor. -/
theorem clearance_lower {root : Canonical} (seed : Seed root) :
    (9 / 64) * Norm.Basic.normSq root ^ 2 ≤ seed.owner.track.initial.clearance.bound := by
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg root) seed.separation.norm_le 2
  rewrite [seed.clearance_eq]
  calc
    _ ≤ (9 / 64) * (8 * seed.separation.radius ^ 2) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared (by decide +kernel)
    _ = ((9 / 64) * 64) * seed.separation.radius ^ 4 := by ring1
    _ = _ := by rewrite [show ((9 / 64) * 64 : Fraction.Rational) = 9 by decide +kernel]; rfl

/-- The actual cached owner channel agrees operationally with the exact retained nonzero input root.

The original square comparison chooses the left index after the requested
start. Its residual request is paid by the same signed sum floor. Initial-box
persistence bounds all later original root readings; the exact right sampler
keeps its requested start unchanged.
-/
def agrees_exact {root : Canonical} (seed : Seed root) :
    NamedEquivalent seed.certificate.value.name (Named.exact root) :=
  CertifiedSquareRoot.Sampling.Exact.agrees seed.certificate seed.separation root rfl
    (Box.Square.Centered.centeredSquare_contains_center root seed.separation.radius seed.separation.positive.le)
    (fun possible => seed.candidate_inside possible)

end Seed

end Purelib.Riemann.Topology.SquareRootContinuationChain.Owner.Exact

import mathlib.Tactic.QuotientFreeOmega
import RFAP.Polynomial.Linear
import RFAP.Isolation.Maximality

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace RFAP.BoxFTA

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev SquarefreeCertificate :=
  RFAP.Squarefree.SquarefreeCertificate
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

/-- The exact Gaussian-rational root returned for a degree-one polynomial. -/
structure ExactRoot (p : GaussianPolynomial) where
  point : RFAP.ConstructiveGaussian.Gaussian
  root : p.eval point = 0

/-- Finite mathematical input for exact box isolation.  Degree at least two
is the range needed by the current Newton-band extraction theorem; the linear
case is intentionally kept separate rather than hidden behind a classical
root formula. -/
structure Input (p : GaussianPolynomial) where
  squarefree : SquarefreeCertificate p
  degreeAtLeastTwo : 2 ≤ p.natDegree

/-- Paper-level input for every positive degree.  The squarefree certificate
is consumed only by the higher-degree box algorithm; retaining it here keeps
the degree-one and degree-greater-than-one public signatures uniform. -/
structure PositiveInput (p : GaussianPolynomial) where
  squarefree : SquarefreeCertificate p
  degreePositive : 0 < p.natDegree

namespace Input

theorem degreePositive {p : GaussianPolynomial} (input : Input p) :
    0 < p.natDegree :=
  (by decide : (0 : Nat) < 2).trans_le input.degreeAtLeastTwo

theorem nonzero {p : GaussianPolynomial} (input : Input p) :
    p.isZero = false :=
  RFAP.GlobalWinding.isZero_false_of_natDegree_pos
    input.degreePositive

/-- The exact finite degree bound of the two internally computed axis
eliminants. -/
def eliminationDegree {p : GaussianPolynomial} (_input : Input p) : Nat :=
  RFAP.AxisSafeCuts.separatedEliminationDegree p

/-- Closed finite axis-elimination certificate computed from `p`'s displayed
coefficient list. -/
def elimination {p : GaussianPolynomial} (input : Input p) :
    RFAP.AxisSafeCuts.AxisEliminationCertificate p
      input.eliminationDegree :=
  RFAP.AxisSafeCuts.separatedAxisEliminationCertificate p
    input.nonzero input.degreePositive

/-- Exact degree-many isolation in the coefficient-computed large square. -/
def isolation {p : GaussianPolynomial} (input : Input p) :
    RFAP.ExactIsolation.Output p
      (RFAP.GlobalWinding.largeSquareBox p) p.natDegree :=
  RFAP.ExactIsolation.isolateLargeSquare input.degreeAtLeastTwo
    input.squarefree input.elimination

/-- Degree-sharp bound for every finite pairwise-separated family of
winding-one tracks in the same large square. -/
theorem familyCardLe
    {p : GaussianPolynomial} (input : Input p) {familyCount : Nat}
    (family : Fin familyCount → WindingOneTrack p
      (RFAP.GlobalWinding.largeSquareBox p))
    (pairwise : ∀ left right, left ≠ right →
      (family left).initial.box.Separated
        (family right).initial.box) :
    familyCount ≤ p.natDegree :=
  RFAP.Maximality.finite_family_card_le_natDegree
    input.degreeAtLeastTwo input.squarefree input.elimination family pairwise

end Input

/-- Complete box-only conclusion: an exact degree-sized finite isolation and
the matching degree-sharp maximality theorem. -/
structure Result (p : GaussianPolynomial) where
  isolation : RFAP.ExactIsolation.Output p
    (RFAP.GlobalWinding.largeSquareBox p) p.natDegree
  ownership :
    ∀ (track : WindingOneTrack p
        (RFAP.GlobalWinding.largeSquareBox p)),
      track.initial.box.Refines isolation.support →
        RFAP.Maximality.OwnerSelection isolation track
  maximality :
    ∀ {familyCount : Nat}
      (family : Fin familyCount → WindingOneTrack p
        (RFAP.GlobalWinding.largeSquareBox p)),
      (∀ left right, left ≠ right →
        (family left).initial.box.Separated
          (family right).initial.box) →
      familyCount ≤ p.natDegree

/-- Standalone choice-free box-only finite RFAP. -/
def prove {p : GaussianPolynomial} (input : Input p) : Result p where
  isolation := input.isolation
  ownership := fun track supported =>
    RFAP.Maximality.selectOutputOwner
      input.degreeAtLeastTwo input.squarefree input.elimination
      input.isolation track supported
  maximality := input.familyCardLe

/-- Degree-greater-than-one specialization with an explicit finite
squarefree certificate.  A later irreducibility wrapper may compute this
certificate, but the trusted numerical theorem needs no sparse or
infinite-root interface. -/
def proveDegreeGtOne
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : Result p :=
  prove { squarefree := squarefree, degreeAtLeastTwo := degree }

/-- Complete positive-degree box result.  Linear polynomials terminate at
their exact Gaussian-rational root; higher-degree polynomials carry the full
degree-many shrinking-box isolation. -/
inductive PositiveResult (p : GaussianPolynomial) where
  | linear (root : ExactRoot p) (degree : p.natDegree = 1)
  | higher (boxes : Result p) (degree : 2 ≤ p.natDegree)

/-- Integrate the exact linear formula with the constructive box theorem. -/
def provePositive {p : GaussianPolynomial}
    (input : PositiveInput p) : PositiveResult p := by
  cases degreeEq : p.natDegree with
  | zero =>
      have := input.degreePositive
      rw [degreeEq] at this
      exact (Nat.lt_asymm this this).elim
  | succ degree =>
      cases degree with
      | zero =>
          have linear : p.natDegree = 1 := degreeEq
          let data := RFAP.Linear.rootData linear
          exact .linear ⟨data.point, data.root⟩ linear
      | succ degree =>
          have degreeAtLeastTwo : 2 ≤ p.natDegree := by
            rw [degreeEq]
            omega
          exact .higher (prove ⟨input.squarefree, degreeAtLeastTwo⟩)
            degreeAtLeastTwo

/-- Degree-greater-than-one specialization of the unified positive-degree
result. -/
def provePositiveDegreeGtOne
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : PositiveResult p :=
  .higher (proveDegreeGtOne squarefree degree) degree

end RFAP.BoxFTA

module

public import Purelib.Curves.Legendre.Degeneration.UnitRoot.PreparedTransport
import Purelib.Curves.Legendre.Degeneration.UnitRoot
public import Purelib.Approximation.Gaussian.Division.Cancellation
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual nodal coordinate channels of retained Legendre sheet owners

The original cubic sheet owner and the original cofactor owner supply their
own certified numerical roots. Dividing these retained channels constructs
the centered nodal ordinate. The two actual coordinate programs satisfy the
conic equation by operational comparison, and multiplication by the same
cofactor root recovers the original sheet channel.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration

open Purelib.Approximation.Gaussian.Name

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

/-- The actual sum/difference coordinate product compares with its displayed smoothing parameter.

Both original coherent channels are retained polynomial bindings. The existing
normalization compares their actual multiplication trees; the supplied square
comparison then evaluates the original exact scalar difference.
-/
private def conicProduct (abscissa smoothing : Canonical) (ordinate : CoherentNamed)
    (square : NamedEquivalent (ordinate.mul ordinate).name (Named.exact (abscissa ^ 2 - smoothing))) :
    NamedEquivalent
      (((Coherence.exact abscissa).add ordinate).mul
        ((Coherence.exact abscissa).add ordinate.neg)).name (Named.exact smoothing) := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases (Coherence.exact abscissa) (fun _ => ordinate)
  let first := Normalized.atom bindings 0
  let second := Normalized.atom bindings 1
  let left := (first.add second).mul (first.sub second)
  let right := (first.mul first).sub (second.mul second)
  have forms : left.form.terms = right.form.terms := by
    dsimp only [left, right, first, second]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.sub_form, Normalized.atom_form,
      -eq_self, -iff_self]
    decide +kernel
  have factorized := left.compare right forms
  have firstSquare : NamedEquivalent
      ((Coherence.exact abscissa).mul (Coherence.exact abscissa)).name (Named.exact (abscissa ^ 2)) := by
    rewrite [pow_two]
    exact Name.Coherent.Exact.Arithmetic.exact_mul _ _
  have difference := Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    ((Coherence.exact abscissa).mul (Coherence.exact abscissa)) (Coherence.exact (abscissa ^ 2))
    (ordinate.mul ordinate).neg (Coherence.exact (abscissa ^ 2 - smoothing)).neg firstSquare
    (Coherent.Additive.coherentNeg_respects _ _ square)
  have exactNegative := Arithmetic.Neg.exactNeg (abscissa ^ 2 - smoothing)
  have replaceNegative := Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (Coherence.exact (abscissa ^ 2)) (Coherence.exact (abscissa ^ 2))
    (Coherence.exact (abscissa ^ 2 - smoothing)).neg (Coherence.exact (-(abscissa ^ 2 - smoothing)))
    (NamedEquivalent.refl _) exactNegative
  have scalar : abscissa ^ 2 + -(abscissa ^ 2 - smoothing) = smoothing := by ring1
  exact factorized.trans (difference.trans (replaceNegative.trans
    (NamedEquivalent.transport rfl (congrArg Named.exact scalar)
      (Name.Coherent.Exact.Arithmetic.exact_add _ _))))

/-- The actual half-sum and half-difference of the conic channels recover their original two inputs.

The existing polynomial normalizer retains both original coherent bindings.
The fixed rational half coefficients give two checked equalities of finite
forms, which compare the actual reconstruction programs with those inputs.
-/
private def recoverPair (first second : CoherentNamed) :
    NamedEquivalent ((Coherence.exact (1 / 2 : Canonical)).mul
      ((first.add second).add (first.add second.neg))).name first.name ×
    NamedEquivalent ((Coherence.exact (1 / 2 : Canonical)).mul
      ((first.add second).add (first.add second.neg).neg)).name second.name := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases first (fun _ => second)
  let a := Normalized.atom bindings 0
  let b := Normalized.atom bindings 1
  let half := Normalized.constant bindings (1 / 2)
  let plus := a.add b
  let minus := a.sub b
  let sum := half.mul (plus.add minus)
  let difference := half.mul (plus.sub minus)
  have sumForms : sum.form.terms = a.form.terms := by
    dsimp only [sum, plus, minus, half, a, b]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.sub_form,
      Normalized.constant_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  have differenceForms : difference.form.terms = b.form.terms := by
    dsimp only [difference, plus, minus, half, a, b]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.sub_form,
      Normalized.constant_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  exact ⟨sum.compare a sumForms, difference.compare b differenceForms⟩

set_option genInjectivity false in
/-- Actual nodal coordinate programs for an original coherent curve ordinate and retained cofactor owner.

The original ordinate may be zero. Its curve-square comparison and the same
cofactor certificate derive every coordinate law. The complete original unit
owner, numerical root cache and defining arithmetic programs remain retained.
-/
structure CoordinateChannels (site : Fin 2) (parameter point : Canonical)
    (source : CoherentNamed) (unit : Owner ((unitPolynomial site).eval point)) where
  /-- The complete original cofactor owner retained by the coordinate programs. -/
  unitOwner : Owner ((unitPolynomial site).eval point)
  /-- The retained cofactor owner is exactly the original input parent. -/
  unitOwner_eq : unitOwner = unit
  /-- The original cofactor owner's cached numerical certificate. -/
  unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point)
  /-- The root cache belongs to the same complete retained cofactor owner. -/
  unitRoot_eq : unitRoot = unitOwner.certificate unitOwner.parameterNonzero
  /-- The original coherent ordinate satisfies the original cubic curve equation operationally. -/
  sourceSquare : NamedEquivalent (source.mul source).name (Named.exact ((Paths.polynomial parameter).eval point))
  /-- The actual normalized nodal ordinate program. -/
  ordinate : CoherentNamed
  /-- Normalization divides the original ordinate by the same cached cofactor root. -/
  ordinate_eq : ordinate = source.div unitRoot.value unitRoot.apart
  /-- The actual centered abscissa plus normalized ordinate program. -/
  plus : CoherentNamed
  /-- The first conic coordinate retains its defining arithmetic operation. -/
  plus_eq : plus = (Coherence.exact (coordinate site parameter point)).add ordinate
  /-- The actual centered abscissa minus normalized ordinate program. -/
  minus : CoherentNamed
  /-- The second conic coordinate retains its defining arithmetic operation. -/
  minus_eq : minus = (Coherence.exact (coordinate site parameter point)).add ordinate.neg
  /-- The normalized ordinate has the exact original quadratic nodal square operationally. -/
  square : NamedEquivalent (ordinate.mul ordinate).name
    (Named.exact (coordinate site parameter point ^ 2 - smoothing site parameter))
  /-- Multiplication by the same cached cofactor root recovers the original ordinate channel. -/
  recovers : NamedEquivalent (ordinate.mul unitRoot.value).name source.name
  /-- The two actual coordinate programs have the original computed smoothing product. -/
  product : NamedEquivalent (plus.mul minus).name (Named.exact (smoothing site parameter))

constructive_injectivity CoordinateChannels

namespace CoordinateChannels

/-- Construct actual nodal channels from the original curve equation and exact cached cofactor certificate.

The original ordinate need not be apart from zero. One cached cofactor root
supplies division, both square cancellations and recovery; the original cubic
factorization and retained polynomial comparison derive the conic product.
-/
def ofRoot (site : Fin 2) (parameter point : Canonical) (source : CoherentNamed)
    (sourceSquare : NamedEquivalent (source.mul source).name (Named.exact ((Paths.polynomial parameter).eval point)))
    (unit : Owner ((unitPolynomial site).eval point))
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point))
    (unitRoot_eq : unitRoot = unit.certificate unit.parameterNonzero) :
    CoordinateChannels site parameter point source unit := by
  let ordinate := source.div unitRoot.value unitRoot.apart
  let plus := (Coherence.exact (coordinate site parameter point)).add ordinate
  let minus := (Coherence.exact (coordinate site parameter point)).add ordinate.neg
  have originalProduct : (Paths.polynomial parameter).eval point =
      (unitPolynomial site).eval point * (coordinate site parameter point ^ 2 - smoothing site parameter) := by
    rewrite [polynomial_centered]
    exact Data.Gaussian.Basic.mul_comm _ _
  have square := Division.Cancellation.coherentDiv_square_of_squares source unitRoot.value unitRoot.apart
    ((Paths.polynomial parameter).eval point) ((unitPolynomial site).eval point)
    (coordinate site parameter point ^ 2 - smoothing site parameter) sourceSquare unitRoot.square originalProduct
  exact
    { unitOwner := unit
      unitOwner_eq := rfl
      unitRoot := unitRoot
      unitRoot_eq := unitRoot_eq
      sourceSquare := sourceSquare
      ordinate := ordinate
      ordinate_eq := rfl
      plus := plus
      plus_eq := rfl
      minus := minus
      minus_eq := rfl
      square := square
      recovers := Division.Cancellation.coherentDiv_mul_cancel source unitRoot.value unitRoot.apart
      product := conicProduct _ _ ordinate square }

/-- Construct actual nodal channels while caching the original cofactor certificate once.

The original coherent ordinate may be zero. Its original curve equation and
the same complete unit owner supply the exact retained certificate consumed by
the common forward-coordinate constructor.
-/
def ofSquare (site : Fin 2) (parameter point : Canonical) (source : CoherentNamed)
    (sourceSquare : NamedEquivalent (source.mul source).name (Named.exact ((Paths.polynomial parameter).eval point)))
    (unit : Owner ((unitPolynomial site).eval point)) : CoordinateChannels site parameter point source unit :=
  ofRoot site parameter point source sourceSquare unit (unit.certificate unit.parameterNonzero) rfl

/-- The forward constructor retains the entire supplied cofactor certificate as its actual root cache. -/
theorem ofRoot_unitRoot (site : Fin 2) (parameter point : Canonical) (source : CoherentNamed)
    (sourceSquare : NamedEquivalent (source.mul source).name (Named.exact ((Paths.polynomial parameter).eval point)))
    (unit : Owner ((unitPolynomial site).eval point))
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point))
    (unitRoot_eq : unitRoot = unit.certificate unit.parameterNonzero) :
    (ofRoot site parameter point source sourceSquare unit unitRoot unitRoot_eq).unitRoot = unitRoot := by
  unfold ofRoot
  rfl

/-- Construct actual branch-point coordinate programs from the original cubic root equation.

The exact zero ordinate belongs to the original displayed curve point.
Spatial admission constructs the original signed cofactor owner internally;
no nonzero cubic sheet owner or supplied conic identity is needed.
-/
def atBranch (site : Fin 2) (parameter point : Canonical) (inside : (spatialBox site).Contains point)
    (branch : (Paths.polynomial parameter).eval point = 0) :
    CoordinateChannels site parameter point (Coherence.exact 0) (UnitRoot.owner site point inside) := by
  have zeroSquare : NamedEquivalent ((Coherence.exact (0 : Canonical)).mul (Coherence.exact 0)).name
      (Named.exact (0 : Canonical)) := by
    have square := Name.Coherent.Exact.Arithmetic.exact_mul (0 : Canonical) 0
    rewrite [Data.Gaussian.Basic.zero_mul] at square
    exact square
  exact ofSquare site parameter point (Coherence.exact 0)
    (NamedEquivalent.transport rfl (congrArg Named.exact branch.symm) zeroSquare) (UnitRoot.owner site point inside)

/-- The original fixed collision branch belongs to its computed spatial patch. -/
theorem fixed_inside (site : Fin 2) : (spatialBox site).Contains (criticalValue site) :=
  Geometry.Rational.Box.Square.Centered.centeredSquare_contains_center (criticalValue site) (1 / 2)
    (by decide +kernel)

/-- Construct actual zero-ordinate coordinates at the original fixed collision branch on any parameter fibre. -/
def atFixed (site : Fin 2) (parameter : Canonical) :
    CoordinateChannels site parameter (criticalValue site) (Coherence.exact 0)
      (UnitRoot.owner site (criticalValue site) (fixed_inside site)) := by
  apply atBranch site parameter (criticalValue site) (fixed_inside site)
  rewrite [polynomial_eq_pair, Data.Gaussian.Basic.sub_self,
    Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.zero_mul]
  rfl

/-- Construct actual zero-ordinate coordinates at the same original moving branch in its admitted parameter patch. -/
def atMoving (site : Fin 2) (parameter : Canonical) (inside : (parameterBox site).Contains parameter) :
    CoordinateChannels site parameter parameter (Coherence.exact 0)
      (UnitRoot.owner site parameter (moving_strictContains site inside).contains) := by
  apply atBranch site parameter parameter (moving_strictContains site inside).contains
  rewrite [Paths.polynomial_eval, Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.mul_zero]
  rfl

/-- The actual normalized ordinate of an original zero curve ordinate remains operationally zero.

Recovery and multiplication by the same apart cofactor root derive zero by
scalar cancellation. The proof uses no exact-zero assumption about the finite
samples produced by the normalized quotient program.
-/
def ordinate_zero {site : Fin 2} {parameter point : Canonical}
    {unit : Owner ((unitPolynomial site).eval point)}
    (channels : CoordinateChannels site parameter point (Coherence.exact 0) unit) :
    NamedEquivalent channels.ordinate.name (Named.exact 0) := by
  have returnZero := (Coherent.Arithmetic.Product.Laws.coherentMul_comm
    channels.unitRoot.value channels.ordinate).trans channels.recovers
  exact Division.Cancellation.coherentMul_cancel_left channels.unitRoot.value channels.ordinate
    (Coherence.exact 0) channels.unitRoot.apart
    (returnZero.trans (Arithmetic.Mul.coherentMul_zero_right channels.unitRoot.value).symm)

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
  {unit : Owner ((unitPolynomial site).eval point)}

/-- Reconstruct the original base coordinate from the two actual conic channels and original collision midpoint. -/
def readPoint (channels : CoordinateChannels site parameter point source unit) : CoherentNamed :=
  (Coherence.exact (center site parameter)).add
    ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus))

/-- Reconstruct the original ordinate from the two actual conic channels and the same retained cofactor root. -/
def readOrdinate (channels : CoordinateChannels site parameter point source unit) : CoherentNamed :=
  channels.unitRoot.value.mul
    ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus.neg))

/-- Read the complete original named base reconstruction without exposing its implementation. -/
theorem readPoint_eq (channels : CoordinateChannels site parameter point source unit) :
    channels.readPoint = (Coherence.exact (center site parameter)).add
      ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus)) := by
  unfold readPoint
  rfl

/-- Read the complete original signed-ordinate reconstruction with its SAME retained cofactor root. -/
theorem readOrdinate_eq (channels : CoordinateChannels site parameter point source unit) :
    channels.readOrdinate = channels.unitRoot.value.mul
      ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus.neg)) := by
  unfold readOrdinate
  rfl

/-- The actual reconstructed base-coordinate program agrees with the original displayed curve coordinate. -/
def readPoint_agrees (channels : CoordinateChannels site parameter point source unit) :
    NamedEquivalent channels.readPoint.name (Named.exact point) := by
  have centered : NamedEquivalent
      ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus)).name
      (Named.exact (coordinate site parameter point)) := by
    rewrite [channels.plus_eq, channels.minus_eq]
    exact (recoverPair (Coherence.exact (coordinate site parameter point)) channels.ordinate).1
  have translated := Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (Coherence.exact (center site parameter)) (Coherence.exact (center site parameter))
    ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus))
    (Coherence.exact (coordinate site parameter point)) (NamedEquivalent.refl _) centered
  have pointEq : center site parameter + coordinate site parameter point = point := by
    unfold coordinate
    ring1
  exact translated.trans (NamedEquivalent.transport rfl (congrArg Named.exact pointEq)
    (Name.Coherent.Exact.Arithmetic.exact_add _ _))

/-- The actual reconstructed ordinate agrees with the same original input channel, including a zero ordinate. -/
def readOrdinate_agrees (channels : CoordinateChannels site parameter point source unit) :
    NamedEquivalent channels.readOrdinate.name source.name := by
  have centered : NamedEquivalent
      ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus.neg)).name
      channels.ordinate.name := by
    rewrite [channels.plus_eq, channels.minus_eq]
    exact (recoverPair (Coherence.exact (coordinate site parameter point)) channels.ordinate).2
  exact (Coherent.Arithmetic.Product.Congruence.coherentMul_respects channels.unitRoot.value
    channels.unitRoot.value
    ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus.neg)) channels.ordinate
    (NamedEquivalent.refl _) centered).trans
    ((Coherent.Arithmetic.Product.Laws.coherentMul_comm channels.unitRoot.value channels.ordinate).trans
      channels.recovers)

end CoordinateChannels

set_option genInjectivity false in
/-- Cached nodal coordinate programs retaining the complete original cubic and cofactor owners.

The two owner equalities preserve the input parents, and the root caches are
their exact original certificates. The normalized ordinate and both conic
coordinates retain their defining operations, operational square, recovery
and smoothing-product comparisons.
-/
structure Coordinates (site : Fin 2) (parameter point : Canonical)
    (source : Owner ((Paths.polynomial parameter).eval point))
    (unit : Owner ((unitPolynomial site).eval point)) where
  /-- The complete original sheet owner retained by this coordinate construction. -/
  sourceOwner : Owner ((Paths.polynomial parameter).eval point)
  /-- The retained sheet owner is exactly the original input parent. -/
  sourceOwner_eq : sourceOwner = source
  /-- The complete original cofactor owner retained by this coordinate construction. -/
  unitOwner : Owner ((unitPolynomial site).eval point)
  /-- The retained cofactor owner is exactly the original input parent. -/
  unitOwner_eq : unitOwner = unit
  /-- The original sheet owner's cached certificate and numerical channel. -/
  sourceRoot : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval point)
  /-- The sheet-root cache belongs to the same complete retained owner. -/
  sourceRoot_eq : sourceRoot = sourceOwner.certificate sourceOwner.parameterNonzero
  /-- The original cofactor owner's cached certificate and numerical channel. -/
  unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point)
  /-- The cofactor-root cache belongs to the same complete retained owner. -/
  unitRoot_eq : unitRoot = unitOwner.certificate unitOwner.parameterNonzero
  /-- The actual normalized nodal ordinate program. -/
  ordinate : CoherentNamed
  /-- The ordinate divides the original sheet channel by the same retained cofactor channel. -/
  ordinate_eq : ordinate = sourceRoot.value.div unitRoot.value unitRoot.apart
  /-- The actual centered abscissa plus normalized ordinate program. -/
  plus : CoherentNamed
  /-- The first conic coordinate retains the original centered abscissa and normalized ordinate. -/
  plus_eq : plus = (Coherence.exact (coordinate site parameter point)).add ordinate
  /-- The actual centered abscissa minus normalized ordinate program. -/
  minus : CoherentNamed
  /-- The second conic coordinate retains the original centered abscissa and normalized ordinate. -/
  minus_eq : minus = (Coherence.exact (coordinate site parameter point)).add ordinate.neg
  /-- The normalized ordinate squares operationally to the original centered quadratic factor. -/
  square : NamedEquivalent (ordinate.mul ordinate).name
    (Named.exact (coordinate site parameter point ^ 2 - smoothing site parameter))
  /-- Multiplication by the same retained cofactor root recovers the original sheet channel. -/
  recovers : NamedEquivalent (ordinate.mul unitRoot.value).name sourceRoot.value.name
  /-- The actual two conic coordinate programs have the original computed smoothing product. -/
  product : NamedEquivalent (plus.mul minus).name (Named.exact (smoothing site parameter))

constructive_injectivity Coordinates

namespace Coordinates

/-- Construct actual nodal coordinates from the complete original sheet and cofactor owners.

The owner certificates are cached once and reused by every arithmetic program
and comparison. Their square identities and the original cubic factorization
derive the nodal equation; no caller-supplied conic identity or sample equality
is used.
-/
def ofOwners (site : Fin 2) (parameter point : Canonical)
    (source : Owner ((Paths.polynomial parameter).eval point))
    (unit : Owner ((unitPolynomial site).eval point)) : Coordinates site parameter point source unit := by
  let sourceRoot := source.certificate source.parameterNonzero
  let channels := CoordinateChannels.ofSquare site parameter point sourceRoot.value sourceRoot.square unit
  exact
    { sourceOwner := source
      sourceOwner_eq := rfl
      unitOwner := channels.unitOwner
      unitOwner_eq := channels.unitOwner_eq
      sourceRoot := sourceRoot
      sourceRoot_eq := rfl
      unitRoot := channels.unitRoot
      unitRoot_eq := channels.unitRoot_eq
      ordinate := channels.ordinate
      ordinate_eq := channels.ordinate_eq
      plus := channels.plus
      plus_eq := channels.plus_eq
      minus := channels.minus
      minus_eq := channels.minus_eq
      square := channels.square
      recovers := channels.recovers
      product := channels.product }

/-- Construct the original signed cofactor owner and actual nodal coordinates of a retained original sheet owner.

Intrinsic spatial admission computes the cofactor owner internally. The
original cubic sheet owner remains a nominal input parent, including its
sheet choice, track and original dependent certificates.
-/
def build (site : Fin 2) (parameter point : Canonical) (inside : (spatialBox site).Contains point)
    (source : Owner ((Paths.polynomial parameter).eval point)) :
    Coordinates site parameter point source (UnitRoot.owner site point inside) :=
  ofOwners site parameter point source (UnitRoot.owner site point inside)

variable {site : Fin 2} {parameter point : Canonical}
  {source : Owner ((Paths.polynomial parameter).eval point)}
  {unit : Owner ((unitPolynomial site).eval point)}

/-- View the same retained owner-based coordinate caches as the shared curve-channel construction.

Every field reuses the existing complete unit owner, root certificate and
coordinate program. The original cubic owner's cached square supplies the
curve-channel witness, without rebuilding any numerical root or quotient.
-/
def toChannels (coordinates : Coordinates site parameter point source unit) :
    CoordinateChannels site parameter point coordinates.sourceRoot.value unit :=
  { unitOwner := coordinates.unitOwner
    unitOwner_eq := coordinates.unitOwner_eq
    unitRoot := coordinates.unitRoot
    unitRoot_eq := coordinates.unitRoot_eq
    sourceSquare := coordinates.sourceRoot.square
    ordinate := coordinates.ordinate
    ordinate_eq := coordinates.ordinate_eq
    plus := coordinates.plus
    plus_eq := coordinates.plus_eq
    minus := coordinates.minus
    minus_eq := coordinates.minus_eq
    square := coordinates.square
    recovers := coordinates.recovers
    product := coordinates.product }

/-- The cached sheet-root name belongs to the same complete original sheet owner. -/
theorem sourceRoot_name (coordinates : Coordinates site parameter point source unit) :
    coordinates.sourceRoot.value.name = ownerRootName source.parameterNonzero source := by
  have ownerCertificate := congrArg (fun original : Owner ((Paths.polynomial parameter).eval point) =>
    original.certificate original.parameterNonzero) coordinates.sourceOwner_eq
  exact congrArg (fun certificate : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval point) =>
    certificate.value.name) (coordinates.sourceRoot_eq.trans ownerCertificate)

/-- The cached cofactor-root name belongs to the same complete original cofactor owner. -/
theorem unitRoot_name (coordinates : Coordinates site parameter point source unit) :
    coordinates.unitRoot.value.name = ownerRootName unit.parameterNonzero unit := by
  have ownerCertificate := congrArg (fun original : Owner ((unitPolynomial site).eval point) =>
    original.certificate original.parameterNonzero) coordinates.unitOwner_eq
  exact congrArg (fun certificate : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point) =>
    certificate.value.name) (coordinates.unitRoot_eq.trans ownerCertificate)

/-- Compare the actual normalized ordinates through both original sheet and cofactor owner comparisons.

Each coordinate record keeps its original root caches and denominator
apartness. Division congruence consumes those exact caches; owner-name
readbacks transport the two supplied comparisons without re-isolation.
-/
def ordinate_agrees
    {otherSource : Owner ((Paths.polynomial parameter).eval point)}
    {otherUnit : Owner ((unitPolynomial site).eval point)}
    (first : Coordinates site parameter point source unit)
    (second : Coordinates site parameter point otherSource otherUnit)
    (sources : NamedEquivalent (ownerRootName source.parameterNonzero source)
      (ownerRootName otherSource.parameterNonzero otherSource))
    (units : NamedEquivalent (ownerRootName unit.parameterNonzero unit)
      (ownerRootName otherUnit.parameterNonzero otherUnit)) :
    NamedEquivalent first.ordinate.name second.ordinate.name := by
  let sourceComparison := NamedEquivalent.transport first.sourceRoot_name.symm second.sourceRoot_name.symm sources
  let unitComparison := NamedEquivalent.transport first.unitRoot_name.symm second.unitRoot_name.symm units
  let divided := Name.Coherent.Division.Equivalence.coherentDiv_respects
    first.sourceRoot.value second.sourceRoot.value first.unitRoot.value second.unitRoot.value
    first.unitRoot.apart second.unitRoot.apart sourceComparison unitComparison
  exact NamedEquivalent.transport (congrArg CoherentNamed.name first.ordinate_eq.symm)
    (congrArg CoherentNamed.name second.ordinate_eq.symm) divided

/-- A path-transported cofactor produces the same normalized ordinate as the independent signed endpoint cofactor.

Both coordinate records retain the same original cubic sheet owner. The
actual prepared path's stored finish owner and internally derived agreement
supply the cofactor comparison; no coordinate or root comparison is required
from the caller.
-/
def path_ordinate_agrees {first last : Canonical}
    (path : UnitRoot.PreparedTransport.Path site first last) (within : path.WithinAmbient)
    (inside : (spatialBox site).Contains first)
    (traced : TracedPath path (UnitRoot.owner site first inside))
    (sheet : Owner ((Paths.polynomial parameter).eval last))
    (transported : Coordinates site parameter last sheet traced.finishOwner)
    (independent : Coordinates site parameter last sheet
      (UnitRoot.owner site last (UnitRoot.PreparedTransport.path_finish_inside path within inside))) :
    NamedEquivalent transported.ordinate.name independent.ordinate.name := by
  have agreement := UnitRoot.PreparedTransport.buildPath_agrees path within inside traced
  unfold UnitRoot.PreparedTransport.ReadingAgreement at agreement
  exact ordinate_agrees transported independent (NamedEquivalent.refl _) agreement

end Coordinates

end Purelib.Curves.Legendre.Degeneration

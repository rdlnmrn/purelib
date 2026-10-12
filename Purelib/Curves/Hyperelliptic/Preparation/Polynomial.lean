module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Compute
public import Purelib.Curves.Hyperelliptic.Topology.Profile
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.BranchedCover
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor

public section

/-!
# Polynomial-first finite hyperelliptic input

Genus and curve-validity evidence are computed from finite coefficients.
Square factors are removed with their exact reconstruction certificate.
The resulting curve describes `z^2 = q`; preserving an original differential
on `y^2 = p` additionally requires transport under `y = s(x) * z`.
-/

namespace Purelib.Curves.Hyperelliptic.Preparation.Polynomial

open Purelib.Riemann.Curves.AlgebraicDifferentials

/-- The certified square-factor decomposition of the original Gaussian polynomial. -/
abbrev Reduction := SquareFactor.Basic.Reduction

/-- The positive-degree hyperelliptic genus formula. Degree zero is handled separately by the public constructor, not
accepted as a degree shape. -/
@[expose] def genusOfDegree (degree : Nat) : Nat := (degree - 1) / 2

/-- Derive the degree-shape evidence from arithmetic, without asking for either a genus or a parity witness. -/
@[expose] def degreeShape (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (positive : 0 <
  polynomial.natDegree) :
    Hyperelliptic.Basic.HyperellipticDegreeShape polynomial
      (Purelib.Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree polynomial.natDegree) := by
  if even : polynomial.natDegree % 2 = 0 then
    apply HyperellipticDegreeShape.even
    unfold Purelib.Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree
    omega
  else
    apply HyperellipticDegreeShape.odd
    unfold Purelib.Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree
    omega

/-- Existing indexed curves already determine their genus uniquely. The new constructor computes that same index rather
than requiring it as input. -/
theorem indexedGenus_eq {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    genus = Purelib.Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree curve.polynomial.natDegree := by
  cases curve.degreeShape with
  | odd degree => unfold Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree; omega
  | even degree => unfold Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree; omega

set_option genInjectivity false in
/-- Retain the computed decomposition, genus and curve together. Consumers use these cached values; they need not repeat
factorization or preparation. -/
structure Prepared (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The cached square-factor decomposition with exact reconstruction evidence. -/ reduction :
    Curves.Hyperelliptic.Preparation.Polynomial.Reduction polynomial
  /-- The retained squarefree radicand has positive degree. -/ degreePositive : 0 < reduction.radicand.natDegree
  /-- The cached genus computed from the reduced radicand degree. -/ genus : Nat
  /-- The cached genus equals the explicit degree formula for the retained radicand. -/ genus_eq : genus =
    Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree reduction.radicand.natDegree
  /-- The retained hyperelliptic curve indexed by the computed genus. -/ curve : Hyperelliptic.Basic.HyperellipticCurve
    genus
  /-- The retained curve polynomial is exactly the cached reduced radicand. -/ polynomial_eq : curve.polynomial =
    reduction.radicand

constructive_injectivity Prepared

namespace Prepared

/-- Construct the indexed curve and cached genus from an existing positive-degree square-factor reduction. -/
@[expose] def ofReduction {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (reduction :
  Curves.Hyperelliptic.Preparation.Polynomial.Reduction polynomial)
    (positive : 0 < reduction.radicand.natDegree) : Curves.Hyperelliptic.Preparation.Polynomial.Prepared polynomial :=
  let genus := Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree reduction.radicand.natDegree
  let curve : Hyperelliptic.Basic.HyperellipticCurve genus :=
    { polynomial := reduction.radicand
      nonzero := reduction.radicandNonzero
      squarefree := reduction.squarefree
      degreeShape := Curves.Hyperelliptic.Preparation.Polynomial.degreeShape reduction.radicand positive }
  { reduction := reduction
    degreePositive := positive
    genus := genus
    genus_eq := rfl
    curve := curve
    polynomial_eq := rfl }

/-- The computed index has the existing finite branch-profile meaning. -/
theorem computedGenus {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (prepared :
  Curves.Hyperelliptic.Preparation.Polynomial.Prepared polynomial) :
    prepared.curve.genusCertificate.genus = Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree
      prepared.reduction.radicand.natDegree :=
  prepared.curve.computedGenus.trans prepared.genus_eq

/-- The retained prepared curve cell model has Euler characteristic two minus twice its cached genus. -/
theorem eulerCharacteristic {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (prepared :
  Curves.Hyperelliptic.Preparation.Polynomial.Prepared polynomial) :
    prepared.curve.cellModel.eulerCharacteristic = (2 : Int) - 2 * prepared.genus :=
  prepared.curve.cellModel_eulerCharacteristic

end Prepared

set_option genInjectivity false in
/-- Distinguish genuine input degeneracies from the regular positive-degree reduced curve. Degrees one and two are
regular genus-zero outcomes, whose standard differential and cycle index types are empty. -/
inductive Outcome (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original input polynomial is certified zero. -/ | zero (certificate : polynomial.isZero = true)
  /-- The original input is nonzero constant and its retained reduced radicand has degree zero. -/ | constantInput
    (nonzero : polynomial.isZero = false)
      (degreeZero : polynomial.natDegree = 0)
      (reduction : Curves.Hyperelliptic.Preparation.Polynomial.Reduction polynomial) (radicandDegreeZero :
        reduction.radicand.natDegree = 0)
  /-- The original input has positive degree but the retained squarefree radicand is constant. -/ | squareTimesConstant
    (nonzero : polynomial.isZero = false)
      (degreePositive : 0 < polynomial.natDegree)
      (reduction : Curves.Hyperelliptic.Preparation.Polynomial.Reduction polynomial) (radicandDegreeZero :
        reduction.radicand.natDegree = 0)
  /-- The original input is nonzero and retains a prepared positive-degree reduced curve. -/ | regular (nonzero :
    polynomial.isZero = false) (prepared : Curves.Hyperelliptic.Preparation.Polynomial.Prepared polynomial)

constructive_injectivity Outcome

/-- Classify retained reduction data, without recomputing its Euclidean or multiplicity calculations. This is also the
internal certified-data adapter. -/
@[expose] def classify {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (nonzero :
  polynomial.isZero = false)
    (reduction : Curves.Hyperelliptic.Preparation.Polynomial.Reduction polynomial) :
      Curves.Hyperelliptic.Preparation.Polynomial.Outcome polynomial :=
  if reducedConstant : reduction.radicand.natDegree = 0 then
    if inputConstant : polynomial.natDegree = 0 then
      .constantInput nonzero inputConstant reduction reducedConstant
    else
      .squareTimesConstant nonzero (Nat.pos_of_ne_zero inputConstant) reduction reducedConstant
  else
    .regular nonzero (Curves.Hyperelliptic.Preparation.Polynomial.Prepared.ofReduction reduction (Nat.pos_of_ne_zero
      reducedConstant))

/-- Total raw-coefficient entry point. No genus, nonzero proof, squarefreeness certificate or successful-check witness
is a caller argument. -/
@[expose] def prepare (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Curves.Hyperelliptic.Preparation.Polynomial.Outcome polynomial :=
  match Compute.reduce polynomial with
  | .zero certificate => .zero certificate
  | .reduced nonzero reduction => Curves.Hyperelliptic.Preparation.Polynomial.classify nonzero reduction

namespace Outcome

/-- A regular genus-zero curve is distinct from a constant reduced radicand. -/
@[expose] def genus? {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} :
  Curves.Hyperelliptic.Preparation.Polynomial.Outcome polynomial → Option Nat
  | .zero _ | .constantInput .. | .squareTimesConstant .. => none
  | .regular _ prepared => some prepared.genus

end Outcome

/-- Degrees one and two have genus zero, while degrees three and four have genus one. -/
theorem genusOfDegree_lowDegrees :
    Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree 1 = 0 ∧
      Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree 2 = 0 ∧
      Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree 3 = 1 ∧
        Curves.Hyperelliptic.Preparation.Polynomial.genusOfDegree 4 = 1 := by
  decide +kernel

end Purelib.Curves.Hyperelliptic.Preparation.Polynomial

end

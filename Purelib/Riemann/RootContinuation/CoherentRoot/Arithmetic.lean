module

public import Purelib.Polynomial.Approximation.Gaussian.Arithmetic
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Arithmetic retaining both original isolated root owners

Both complete original root certificates remain stored. The shared numerical
arithmetic consumes their actual quantitative residual views and retains one
companion elimination, result sample program and computed budget. Its output
comparison concerns the unchanged operation on both original coherent channels.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
variable {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
variable {secondTrack : WindingOneTrack secondPolynomial secondAmbient}

set_option genInjectivity false in
/-- Both original isolated root owners with the shared arithmetic cache on their same retained sample programs.

The numerical arithmetic is indexed by the original roots' quantitative
residual views. It retains their actual samples, coefficients and computed
elimination once; neither mathematical root owner is replaced by that evidence.
-/
structure Arithmetic (operation : Operation) (originalFirst : CertifiedName firstTrack)
    (originalSecond : CertifiedName secondTrack) where
  /-- The complete actual first original root certificate and cache. -/
  first : CertifiedName firstTrack
  /-- The stored first root is the original input. -/
  first_eq : first = originalFirst
  /-- The complete actual second original root certificate and cache. -/
  second : CertifiedName secondTrack
  /-- The stored second root is the original input. -/
  second_eq : second = originalSecond
  /-- The shared arithmetic cache on both same retained original-root residual programs. -/
  numeric : PolynomialArithmetic operation first.residualCertificate second.residualCertificate

constructive_injectivity Arithmetic

namespace Arithmetic

/-- Compute shared polynomial arithmetic on both same original root caches without additional result bounds. -/
def ofRoots (operation : Operation) (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) :
    Arithmetic operation first second :=
  let numeric := PolynomialArithmetic.ofResiduals operation first.residualCertificate second.residualCertificate
  ⟨first, rfl, second, rfl, numeric⟩

/-- The original root-arithmetic constructor retains both complete inputs and its computed numeric record. -/
private theorem ofRoots_readback (operation : Operation) (first : CertifiedName firstTrack)
    (second : CertifiedName secondTrack) :
    ofRoots operation first second =
      ⟨first, rfl, second, rfl,
        PolynomialArithmetic.ofResiduals operation first.residualCertificate second.residualCertificate⟩ := rfl

/-- Read the complete original root-arithmetic result through its actual residual construction. -/
theorem ofRoots_eq (operation : Operation) (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) :
    ofRoots operation first second =
      ⟨first, rfl, second, rfl,
        PolynomialArithmetic.ofResiduals operation first.residualCertificate second.residualCertificate⟩ :=
  ofRoots_readback operation first second

variable {operation : Operation} {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}

/-- Read the same retained arithmetic elimination's coefficient polynomial. -/
@[expose] def polynomial (arithmetic : Arithmetic operation first second) : GaussianPolynomial :=
  arithmetic.numeric.polynomial

/-- Read the actual stored result sample program of the same shared arithmetic cache. -/
@[expose] def result (arithmetic : Arithmetic operation first second) : GeometricApproximation :=
  arithmetic.numeric.result

/-- The retained arithmetic result applies its operation to the same two original root samples.

Both numerical residual readbacks and the original root-cache equalities are
consumed at this one finite index. No replacement root or equality between
different parameter values is used.
-/
theorem result_sample (arithmetic : Arithmetic operation first second) (index : Nat) :
    arithmetic.result.sample index =
      operation.value (first.approximation.sample index) (second.approximation.sample index) := by
  have reading := arithmetic.numeric.result_sample index
  rewrite [arithmetic.numeric.first_eq, arithmetic.numeric.second_eq] at reading
  change arithmetic.result.sample index =
    operation.value (arithmetic.first.approximation.sample index)
      (arithmetic.second.approximation.sample index) at reading
  rewrite [arithmetic.first_eq, arithmetic.second_eq] at reading
  exact reading

/-- Read the actual stored residual scale of the same shared arithmetic cache. -/
@[expose] def residualScale (arithmetic : Arithmetic operation first second) : Rational :=
  arithmetic.numeric.residualScale

/-- The retained original arithmetic polynomial is nonzero. -/
theorem nonzero (arithmetic : Arithmetic operation first second) : arithmetic.polynomial.isZero = false :=
  arithmetic.numeric.elimination.nonzero

/-- The retained original arithmetic polynomial has positive degree. -/
theorem degree_pos (arithmetic : Arithmetic operation first second) : 0 < arithmetic.polynomial.natDegree :=
  arithmetic.numeric.degreePositive

/-- The same stored computed arithmetic residual scale is nonnegative. -/
theorem residualScale_nonnegative (arithmetic : Arithmetic operation first second) : 0 ≤ arithmetic.residualScale :=
  arithmetic.numeric.residualScale_nonnegative

/-- Every original arithmetic sample obeys the same cached polynomial residual budget. -/
theorem sample_residual (arithmetic : Arithmetic operation first second) (index : Nat) :
    normSq (arithmetic.polynomial.eval (arithmetic.result.sample index)) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius arithmetic.residualScale index :=
  arithmetic.numeric.sample_residual index

/-- The unchanged coherent operation on both original input roots agrees with the actual stored result samples. -/
def equivalent (arithmetic : Arithmetic operation first second) :
    NamedEquivalent (PolynomialArithmetic.channel operation first.value second.value).name
      arithmetic.result.toApproximation.toNamed := by
  have agreement := arithmetic.numeric.equivalent
  have channels := congrArg₂
    (fun (left : CertifiedName firstTrack) (right : CertifiedName secondTrack) =>
      PolynomialArithmetic.channel operation left.value right.value) arithmetic.first_eq arithmetic.second_eq
  have identity := congrArg
    (fun channel : CoherentNamed => NamedEquivalent channel.name arithmetic.result.toApproximation.toNamed) channels
  exact identity.mp agreement

/-- Retain the actual stored arithmetic result program and residual scale for further original-channel operations. -/
def residualCertificate (arithmetic : Arithmetic operation first second) :
    Polynomial.Approximation.Gaussian.Residual arithmetic.polynomial
      (PolynomialArithmetic.channel operation first.value second.value) :=
  Polynomial.Approximation.Gaussian.Residual.ofGeometric arithmetic.degree_pos arithmetic.result arithmetic.equivalent
    arithmetic.residualScale arithmetic.residualScale_nonnegative arithmetic.sample_residual

/-- The unchanged original coherent arithmetic channel satisfies the same computed polynomial equation operationally. -/
def equation (arithmetic : Arithmetic operation first second) :
    NamedEquivalent (Horner.polynomialEval arithmetic.polynomial
      (PolynomialArithmetic.channel operation first.value second.value)).name (CoherentNamed.Coherence.exact 0).name :=
  arithmetic.residualCertificate.equation

end Arithmetic

end Purelib.Riemann.RootContinuation.CoherentRoot

end

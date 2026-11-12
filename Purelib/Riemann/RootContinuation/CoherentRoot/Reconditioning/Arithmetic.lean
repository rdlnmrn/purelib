module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning
public import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Arithmetic comparisons consuming actual retained root restarts -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning

open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

variable {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
variable {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
variable {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
variable {operation : Operation} {first : CertifiedName firstTrack} {second : CertifiedName secondTrack}
variable {firstStart secondStart : Nat}

set_option genInjectivity false in
/-- The original arithmetic cache with a computed arithmetic cache on two actual retained restarts.

Both restarts preserve their original input root witnesses. The result polynomial
may have repeated roots; arithmetic correctness uses the original numerical
residuals and requires no simple-root contract for that result polynomial.
-/
structure Arithmetic (before : CoherentRoot.Arithmetic operation first second)
    (firstRestart : Reconditioning first firstStart) (secondRestart : Reconditioning second secondStart) where
  /-- The actual arithmetic cache consuming the two retained restarted root certificates. -/
  after : CoherentRoot.Arithmetic operation firstRestart.root secondRestart.root
  /-- The retained cache is the original arithmetic builder on those exact restarted inputs. -/
  after_eq : after = CoherentRoot.Arithmetic.ofRoots operation firstRestart.root secondRestart.root

constructive_injectivity Arithmetic

namespace Arithmetic

/-- Compute arithmetic on two already retained root restarts, preserving the original arithmetic input cache. -/
@[expose] def ofRestarts (before : CoherentRoot.Arithmetic operation first second)
    (firstRestart : Reconditioning first firstStart) (secondRestart : Reconditioning second secondStart) :
    Arithmetic before firstRestart secondRestart :=
  ⟨CoherentRoot.Arithmetic.ofRoots operation firstRestart.root secondRestart.root, rfl⟩

variable {before : CoherentRoot.Arithmetic operation first second}
variable {firstRestart : Reconditioning first firstStart} {secondRestart : Reconditioning second secondStart}

/-- The two unchanged original arithmetic channels agree after both original branches are reconditioned.

The supplied inputs prove squarefreeness of the original root polynomials.
Their nested-winding comparisons derive the operation comparison and its
finite budget through the existing coherent addition or multiplication law.
-/
def channelEquivalent (_arithmetic : Arithmetic before firstRestart secondRestart)
    (firstInput : FTA.Squarefree.Input firstPolynomial) (secondInput : FTA.Squarefree.Input secondPolynomial) :
    NamedEquivalent (PolynomialArithmetic.channel operation first.value second.value).name
      (PolynomialArithmetic.channel operation firstRestart.root.value secondRestart.root.value).name := by
  have left := firstRestart.namedEquivalent firstInput
  have right := secondRestart.namedEquivalent secondInput
  cases operation with
  | add => exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects _ _ _ _ left right
  | mul => exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects _ _ _ _ left right

/-- Compare both actual stored arithmetic sample programs using their original input and restart certificates. -/
def resultEquivalent (arithmetic : Arithmetic before firstRestart secondRestart)
    (firstInput : FTA.Squarefree.Input firstPolynomial) (secondInput : FTA.Squarefree.Input secondPolynomial) :
    NamedEquivalent before.result.toApproximation.toNamed arithmetic.after.result.toApproximation.toNamed :=
  NamedEquivalent.trans (NamedEquivalent.symm before.equivalent)
    (NamedEquivalent.trans (arithmetic.channelEquivalent firstInput secondInput) arithmetic.after.equivalent)

end Arithmetic

end Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning

end

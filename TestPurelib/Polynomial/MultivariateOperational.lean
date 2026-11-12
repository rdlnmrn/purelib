module

import Purelib.Polynomial.Multivariate.Gaussian.Operational
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Coherent.Additive

/-!
# Operational polynomial normalization regressions

The finite coefficient calculation is composed with the general operational
soundness laws at the original opaque channels. The comparison therefore
covers every pair of starting indices and every positive rational tolerance.
-/

namespace TestPurelib.Polynomial.MultivariateOperational

open Purelib.Polynomial.Multivariate
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Coherent

/-- The retained original first variable index. -/
private def firstIndex : Fin 2 := ⟨0, by decide⟩

/-- The retained original second variable index. -/
private def secondIndex : Fin 2 := ⟨1, by decide⟩

/-- The sparse polynomial of the original first variable. -/
private def x : Sparse Gaussian 2 := Sparse.atom firstIndex

/-- The sparse polynomial of the original second variable. -/
private def y : Sparse Gaussian 2 := Sparse.atom secondIndex

/-- Empty canonical coefficients give the exact zero interpretation at the original environment. -/
private def zeroReading (environment : Fin 2 → CoherentNamed) (polynomial : Sparse Gaussian 2)
    (empty : polynomial.terms = []) :
    NamedEquivalent (Sparse.denote environment polynomial).name (Coherence.exact 0).name := by
  unfold Sparse.denote
  rewrite [empty]
  exact NamedEquivalent.refl _

example (environment : Fin 2 → CoherentNamed) : NamedEquivalent
    (CoherentNamed.add (CoherentNamed.add (environment firstIndex) (environment secondIndex))
      (CoherentNamed.neg (CoherentNamed.add (environment secondIndex) (environment firstIndex)))).name
    (Coherence.exact 0).name := by
  let xy := Sparse.add x y
  let yx := Sparse.add y x
  have xLaw := NamedEquivalent.symm (Sparse.denote_atom environment firstIndex)
  have yLaw := NamedEquivalent.symm (Sparse.denote_atom environment secondIndex)
  have leftLaw : NamedEquivalent
      (CoherentNamed.add (environment firstIndex) (environment secondIndex)).name
      (Sparse.denote environment xy).name :=
    NamedEquivalent.trans
      (Congruence.coherentAdd_respects (environment firstIndex) (Sparse.denote environment x)
        (environment secondIndex) (Sparse.denote environment y) xLaw yLaw)
      (NamedEquivalent.symm (Sparse.denote_add environment x y))
  have rightLaw : NamedEquivalent
      (CoherentNamed.add (environment secondIndex) (environment firstIndex)).name
      (Sparse.denote environment yx).name :=
    NamedEquivalent.trans
      (Congruence.coherentAdd_respects (environment secondIndex) (Sparse.denote environment y)
        (environment firstIndex) (Sparse.denote environment x) yLaw xLaw)
      (NamedEquivalent.symm (Sparse.denote_add environment y x))
  have negativeLaw := Additive.coherentNeg_respects
    (CoherentNamed.add (environment secondIndex) (environment firstIndex))
    (Sparse.denote environment yx) rightLaw
  have differenceLaw := NamedEquivalent.trans
    (Congruence.coherentAdd_respects
      (CoherentNamed.add (environment firstIndex) (environment secondIndex)) (Sparse.denote environment xy)
      (CoherentNamed.neg (CoherentNamed.add (environment secondIndex) (environment firstIndex)))
      (CoherentNamed.neg (Sparse.denote environment yx)) leftLaw negativeLaw)
    (NamedEquivalent.symm (Sparse.denote_sub environment xy yx))
  exact NamedEquivalent.trans differenceLaw
    (zeroReading environment (Sparse.sub xy yx) (by decide))

end TestPurelib.Polynomial.MultivariateOperational

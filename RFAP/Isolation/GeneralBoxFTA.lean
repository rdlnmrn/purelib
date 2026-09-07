import mathlib.Data.ConstructiveList
import RFAP.Isolation.BoxFTA
import RFAP.Polynomial.Multiplicity

/-!
# Box-only general-polynomial isolation after squarefree preprocessing

This is the Paper-I general-polynomial layer.  It computes the exact
pairwise-coprime positive multiplicity basis and runs the standalone box
theorem once for every displayed basis factor.  No finite-name or cylinder
module is imported.
-/

namespace RFAP.GeneralBoxFTA

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Factor := RFAP.Factorization.Factor
abbrev MultiplicityFactor :=
  RFAP.Multiplicity.PositiveEntry

/-- One pairwise-coprime squarefree basis factor and its box-only isolation. -/
structure BoxFactor where
  entry : MultiplicityFactor
  result : RFAP.BoxFTA.PositiveResult entry.part.polynomial

namespace BoxFactor

def factor (boxed : BoxFactor) : Factor := boxed.entry.factor

def occurrenceCount (boxed : BoxFactor) : Nat := boxed.entry.multiplicity

theorem occurrenceCountPositive (boxed : BoxFactor) :
    0 < boxed.occurrenceCount :=
  boxed.entry.multiplicityPositive

end BoxFactor

def isolateBoxFactor (entry : MultiplicityFactor) : BoxFactor :=
  { entry := entry
    result := RFAP.BoxFTA.provePositive
      { squarefree := entry.factor.squarefree
        degreePositive := entry.factor.degreePositive } }

/-- Total box-only result for an arbitrary displayed polynomial. -/
inductive BoxResult (p : GaussianPolynomial) where
  | zero (certificate : p.isZero = true)
  | constant (nonzero : p.isZero = false) (degreeZero : p.natDegree = 0)
  | positive
      (preprocessing : RFAP.Factorization.PositivePreprocessing p)
      (factors : List BoxFactor)
      (factorsNonempty : factors ≠ [])
      (factorsPairwiseCoprime : factors.Pairwise fun left right =>
        RFAP.Multiplicity.CoprimeRelation
          (RFAP.Multiplicity.Factor.toPart left.factor)
          (RFAP.Multiplicity.Factor.toPart right.factor))

private theorem map_ne_nil
    {A B : Type*} (function : A → B) {values : List A}
    (nonempty : values ≠ []) : values.map function ≠ [] := by
  cases values with
  | nil => exact (nonempty rfl).elim
  | cons value values => exact List.cons_ne_nil _ _

/-- Run the standalone box theorem once for each positive multiplicity-basis
factor. -/
def isolateByBoxes (p : GaussianPolynomial) : BoxResult p :=
  match _preprocessing : RFAP.Factorization.preprocess p with
  | .zero certificate => .zero certificate
  | .constant nonzero degreeZero => .constant nonzero degreeZero
  | .positive positive =>
      let entries := positive.decomposition.positiveMultiplicityEntries
      .positive positive (entries.map isolateBoxFactor)
        (map_ne_nil isolateBoxFactor
          positive.decomposition.positiveMultiplicityEntries_nonempty)
        (by
          rw [QuotientFreeList.pairwise_map]
          simpa only [isolateBoxFactor,
            BoxFactor.factor,
            RFAP.Multiplicity.PositiveEntry.factor,
            RFAP.Multiplicity.Part.toFactor,
            RFAP.Multiplicity.Factor.toPart] using
              positive.decomposition.positiveMultiplicityEntries_pairwise)

end RFAP.GeneralBoxFTA

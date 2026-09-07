import mathlib.Data.ConstructiveList
import CCL.Bridge.Box
import RFAP.Isolation.GeneralBoxFTA

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `RFAP.GeneralBoxFTA`.
-/

namespace CCL.GeneralRFAP

abbrev GaussianPolynomial :=
  RFAP.GeneralBoxFTA.GaussianPolynomial
abbrev Factor := RFAP.GeneralBoxFTA.Factor
abbrev MultiplicityFactor :=
  RFAP.GeneralBoxFTA.MultiplicityFactor

/-- One pairwise-coprime squarefree basis factor and its CCL-coupled isolation. -/
structure CCLFactor where
  factor : Factor
  occurrenceCount : Nat
  result : CCL.BoxRFAPBridge.PositiveResult factor.polynomial

def isolateCCLFactor (entry : MultiplicityFactor) : CCLFactor :=
  { factor := entry.factor
    occurrenceCount := entry.multiplicity
    result := CCL.BoxRFAPBridge.provePositive
      { squarefree := entry.factor.squarefree
        degreePositive := entry.factor.degreePositive } }

/-- Total CCL-coupled result for an arbitrary displayed polynomial. -/
inductive CCLResult (p : GaussianPolynomial) where
  | zero (certificate : p.isZero = true)
  | constant (nonzero : p.isZero = false) (degreeZero : p.natDegree = 0)
  | positive
      (preprocessing : RFAP.Factorization.PositivePreprocessing p)
      (factors : List CCLFactor)
      (factorsNonempty : factors ≠ [])
      (factorsPairwiseCoprime : factors.Pairwise fun left right =>
        RFAP.Multiplicity.CoprimeRelation
          (RFAP.Multiplicity.Factor.toPart left.factor)
          (RFAP.Multiplicity.Factor.toPart right.factor))

private theorem map_ne_nil_ccl
    {A B : Type*} (function : A → B) {values : List A}
    (nonempty : values ≠ []) : values.map function ≠ [] := by
  cases values with
  | nil => exact (nonempty rfl).elim
  | cons value values => exact List.cons_ne_nil _ _

/-- Run the CCL-coupled theorem once for each positive multiplicity-basis
factor. -/
def isolateWithCCL (p : GaussianPolynomial) : CCLResult p :=
  match _preprocessing : RFAP.Factorization.preprocess p with
  | .zero certificate => .zero certificate
  | .constant nonzero degreeZero => .constant nonzero degreeZero
  | .positive positive =>
      let entries := positive.decomposition.positiveMultiplicityEntries
      .positive positive (entries.map isolateCCLFactor)
        (map_ne_nil_ccl isolateCCLFactor
          positive.decomposition.positiveMultiplicityEntries_nonempty)
        (by
          rw [QuotientFreeList.pairwise_map]
          simpa only [isolateCCLFactor,
            RFAP.Multiplicity.PositiveEntry.factor,
            RFAP.Multiplicity.Part.toFactor,
            RFAP.Multiplicity.Factor.toPart] using
              positive.decomposition.positiveMultiplicityEntries_pairwise)

end CCL.GeneralRFAP

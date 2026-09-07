import CCL.Knot.TorusInvariants
import CCL.Knot.LinkingNumber
import CCL.Knot.ExactPolynomialLoops

/-!
# Worked finite torus-knot and torus-link examples

Each non-trivial knot below carries the same finite outputs expected from the
standard torus-knot formulas: one component, crossing count and writhe of the
displayed positive braid, genus `(p-1)(q-1)/2`, and the complete normalized
Alexander polynomial.  Every polynomial also carries the exact finite
quotient identity from `TorusInvariants.AlexanderCertificate`.

The final link examples check the non-coprime component theorem, and the
one-strand example is a trivial normalization sanity check.
-/

namespace CCL.Knot.Examples

open CCL.Knot.FiniteBraid
open CCL.Knot.TorusBraid
open CCL.Knot.TorusInvariants
open CCL.Knot.LinkingNumber

/-! ## Five non-trivial torus knots -/

def trefoil : PowerSingularity := ⟨2, 3, by decide, by decide⟩

def trefoilInvariants : TorusKnotInvariantCertificate trefoil where
  gcdOne := by decide
  surface := canonicalSurfaceCertificate trefoil (by decide)
  alexander := alexanderCertificate 2 3
    (by decide) (by decide) (by decide) (IntPolynomial.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

theorem trefoil_componentCount : trefoil.componentCount = 1 := by decide
theorem trefoil_crossingCount : trefoil.braidWord.length = 3 := by decide
theorem trefoil_writhe : trefoil.braidWord.writhe = 3 := by decide
theorem trefoil_genus : trefoilInvariants.surface.genus = 1 := by decide
theorem trefoil_alexander :
    trefoilInvariants.alexander.polynomial = [1, -1, 1] := by decide
theorem trefoil_isKnot : trefoil.closure.IsKnot :=
  trefoilInvariants.isKnot

def cinquefoil : PowerSingularity := ⟨2, 5, by decide, by decide⟩

def cinquefoilInvariants : TorusKnotInvariantCertificate cinquefoil where
  gcdOne := by decide
  surface := canonicalSurfaceCertificate cinquefoil (by decide)
  alexander := alexanderCertificate 2 5
    (by decide) (by decide) (by decide) (IntPolynomial.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

theorem cinquefoil_componentCount : cinquefoil.componentCount = 1 := by decide
theorem cinquefoil_crossingCount : cinquefoil.braidWord.length = 5 := by decide
theorem cinquefoil_writhe : cinquefoil.braidWord.writhe = 5 := by decide
theorem cinquefoil_genus : cinquefoilInvariants.surface.genus = 2 := by decide
theorem cinquefoil_alexander :
    cinquefoilInvariants.alexander.polynomial = [1, -1, 1, -1, 1] := by decide
theorem cinquefoil_isKnot : cinquefoil.closure.IsKnot :=
  cinquefoilInvariants.isKnot

def torusKnot34 : PowerSingularity := ⟨3, 4, by decide, by decide⟩

def torusKnot34Invariants : TorusKnotInvariantCertificate torusKnot34 where
  gcdOne := by decide
  surface := canonicalSurfaceCertificate torusKnot34 (by decide)
  alexander := alexanderCertificate 3 4
    (by decide) (by decide) (by decide) (IntPolynomial.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

theorem torusKnot34_componentCount : torusKnot34.componentCount = 1 := by decide
theorem torusKnot34_crossingCount : torusKnot34.braidWord.length = 8 := by decide
theorem torusKnot34_writhe : torusKnot34.braidWord.writhe = 8 := by decide
theorem torusKnot34_genus : torusKnot34Invariants.surface.genus = 3 := by decide
theorem torusKnot34_alexander :
    torusKnot34Invariants.alexander.polynomial =
      [1, -1, 0, 1, 0, -1, 1] := by decide
theorem torusKnot34_isKnot : torusKnot34.closure.IsKnot :=
  torusKnot34Invariants.isKnot

def torusKnot35 : PowerSingularity := ⟨3, 5, by decide, by decide⟩

def torusKnot35Invariants : TorusKnotInvariantCertificate torusKnot35 where
  gcdOne := by decide
  surface := canonicalSurfaceCertificate torusKnot35 (by decide)
  alexander := alexanderCertificate 3 5
    (by decide) (by decide) (by decide) (IntPolynomial.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

theorem torusKnot35_componentCount : torusKnot35.componentCount = 1 := by decide
theorem torusKnot35_crossingCount : torusKnot35.braidWord.length = 10 := by decide
theorem torusKnot35_writhe : torusKnot35.braidWord.writhe = 10 := by decide
theorem torusKnot35_genus : torusKnot35Invariants.surface.genus = 4 := by decide
theorem torusKnot35_alexander :
    torusKnot35Invariants.alexander.polynomial =
      [1, -1, 0, 1, -1, 1, 0, -1, 1] := by decide
theorem torusKnot35_isKnot : torusKnot35.closure.IsKnot :=
  torusKnot35Invariants.isKnot

def torusKnot45 : PowerSingularity := ⟨4, 5, by decide, by decide⟩

def torusKnot45Invariants : TorusKnotInvariantCertificate torusKnot45 where
  gcdOne := by decide
  surface := canonicalSurfaceCertificate torusKnot45 (by decide)
  alexander := alexanderCertificate 4 5
    (by decide) (by decide) (by decide) (IntPolynomial.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

theorem torusKnot45_componentCount : torusKnot45.componentCount = 1 := by decide
theorem torusKnot45_crossingCount : torusKnot45.braidWord.length = 15 := by decide
theorem torusKnot45_writhe : torusKnot45.braidWord.writhe = 15 := by decide
theorem torusKnot45_genus : torusKnot45Invariants.surface.genus = 6 := by decide
theorem torusKnot45_alexander :
    torusKnot45Invariants.alexander.polynomial =
      [1, -1, 0, 0, 1, 0, -1, 0, 1, 0, 0, -1, 1] := by decide
theorem torusKnot45_isKnot : torusKnot45.closure.IsKnot :=
  torusKnot45Invariants.isKnot

/-! ## Non-coprime links -/

def torusLink24 : PowerSingularity := ⟨2, 4, by decide, by decide⟩

theorem torusLink24_componentCount : torusLink24.componentCount = 2 := by decide
theorem torusLink24_orbitLength : torusLink24.componentOrbitLength = 1 := by
  decide
theorem torusLink24_crossingCount : torusLink24.braidWord.length = 4 := by
  decide
theorem torusLink24_notKnot : ¬torusLink24.closure.IsKnot := by
  intro single
  exact single.no_early_return ⟨0, by decide⟩ 1
    (by decide) (by decide) (by decide)

def torusLink24Components : ComponentLabeling torusLink24.closure 2 where
  componentOfStrand := residueComponent (by decide)
  preserved := by decide
  represented := by
    intro component
    exact ⟨⟨component.val, component.isLt⟩, by
      apply Fin.ext
      exact Nat.mod_eq_of_lt component.isLt⟩

def torusLink24Linking : PairCertificate torusLink24Components
    ⟨0, by decide⟩ ⟨1, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

theorem torusLink24_pairwiseLinking : torusLink24Linking.linking = 2 := rfl

def torusLink36 : PowerSingularity := ⟨3, 6, by decide, by decide⟩

theorem torusLink36_componentCount : torusLink36.componentCount = 3 := by decide
theorem torusLink36_orbitLength : torusLink36.componentOrbitLength = 1 := by
  decide
theorem torusLink36_crossingCount : torusLink36.braidWord.length = 12 := by
  decide
theorem torusLink36_notKnot : ¬torusLink36.closure.IsKnot := by
  intro single
  exact single.no_early_return ⟨0, by decide⟩ 1
    (by decide) (by decide) (by decide)

def torusLink36Components : ComponentLabeling torusLink36.closure 3 where
  componentOfStrand := residueComponent (by decide)
  preserved := by decide
  represented := by
    intro component
    exact ⟨⟨component.val, component.isLt⟩, by
      apply Fin.ext
      exact Nat.mod_eq_of_lt component.isLt⟩

def torusLink36Linking01 : PairCertificate torusLink36Components
    ⟨0, by decide⟩ ⟨1, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

def torusLink36Linking02 : PairCertificate torusLink36Components
    ⟨0, by decide⟩ ⟨2, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

def torusLink36Linking12 : PairCertificate torusLink36Components
    ⟨1, by decide⟩ ⟨2, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

theorem torusLink36_pairwiseLinking01 : torusLink36Linking01.linking = 2 := rfl
theorem torusLink36_pairwiseLinking02 : torusLink36Linking02.linking = 2 := rfl
theorem torusLink36_pairwiseLinking12 : torusLink36Linking12.linking = 2 := rfl

/-! ## Trivial normalization -/

def oneStrandUnknot : PowerSingularity := ⟨1, 1, by decide, by decide⟩

def oneStrandUnknotInvariants :
    TorusKnotInvariantCertificate oneStrandUnknot where
  gcdOne := by decide
  surface := canonicalSurfaceCertificate oneStrandUnknot (by decide)
  alexander := alexanderCertificate 1 1
    (by decide) (by decide) (by decide) (IntPolynomial.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

theorem oneStrandUnknot_crossingCount :
    oneStrandUnknot.braidWord.length = 0 := by decide
theorem oneStrandUnknot_genus :
    oneStrandUnknotInvariants.surface.genus = 0 := by decide
theorem oneStrandUnknot_alexander :
    oneStrandUnknotInvariants.alexander.polynomial = [1] := by decide
theorem oneStrandUnknot_isKnot : oneStrandUnknot.closure.IsKnot :=
  oneStrandUnknotInvariants.isKnot

/-! ## Exact split-polynomial realizations -/

namespace Exact

open CCL.Knot.ExactPolynomialLoops

/-- The five nontrivial knot words above also have fully explicit rational
coefficient loops, independently of the specialized power-polynomial model.
-/
def trefoilLoop : RealizedLoop trefoil.braidWord := realizeWord _
def cinquefoilLoop : RealizedLoop cinquefoil.braidWord := realizeWord _
def torusKnot34Loop : RealizedLoop torusKnot34.braidWord := realizeWord _
def torusKnot35Loop : RealizedLoop torusKnot35.braidWord := realizeWord _
def torusKnot45Loop : RealizedLoop torusKnot45.braidWord := realizeWord _

@[simp] theorem trefoilLoop_coefficientCount :
    trefoilLoop.coefficientVertices.length = 13 := by
  rw [trefoilLoop, realizeWord_coefficientCount, trefoil_crossingCount]

@[simp] theorem cinquefoilLoop_coefficientCount :
    cinquefoilLoop.coefficientVertices.length = 21 := by
  rw [cinquefoilLoop, realizeWord_coefficientCount, cinquefoil_crossingCount]

@[simp] theorem torusKnot34Loop_coefficientCount :
    torusKnot34Loop.coefficientVertices.length = 33 := by
  rw [torusKnot34Loop, realizeWord_coefficientCount,
    torusKnot34_crossingCount]

@[simp] theorem torusKnot35Loop_coefficientCount :
    torusKnot35Loop.coefficientVertices.length = 41 := by
  rw [torusKnot35Loop, realizeWord_coefficientCount,
    torusKnot35_crossingCount]

@[simp] theorem torusKnot45Loop_coefficientCount :
    torusKnot45Loop.coefficientVertices.length = 61 := by
  rw [torusKnot45Loop, realizeWord_coefficientCount,
    torusKnot45_crossingCount]

theorem torusKnot45Loop_vertices_monic :
    ∀ polynomial ∈ torusKnot45Loop.coefficientVertices,
      polynomial.natDegree = 4 ∧ polynomial.leadingCoeff = 1 :=
  realizeWord_vertices_monic _

def fiveStrandFirst : Generator 5 :=
  ⟨⟨0, by decide⟩, .positive⟩

def fiveStrandLast : Generator 5 :=
  ⟨⟨3, by decide⟩, .negative⟩

def fiveStrandFarCell : FarCommutationCell fiveStrandFirst fiveStrandLast
    (by decide) :=
  farCommutationCell fiveStrandFirst fiveStrandLast (by decide)

@[simp] theorem fiveStrandFarCell_center_degree :
    fiveStrandFarCell.simultaneousMidpoint.polynomial.natDegree = 5 :=
  Vertex.polynomial_natDegree _

def threeStrandIndex : Fin (3 - 2) := ⟨0, by decide⟩

def positiveArtinCell : ArtinCell threeStrandIndex .positive :=
  artinCell threeStrandIndex .positive

@[simp] theorem positiveArtinCell_center_degree :
    positiveArtinCell.centralVertex.polynomial.natDegree = 3 :=
  Vertex.polynomial_natDegree _

def positiveArtinHomotopy :
    PolynomialHomotopic
      [CCL.Knot.ArtinRelations.Generator.lower threeStrandIndex .positive,
        CCL.Knot.ArtinRelations.Generator.upper threeStrandIndex .positive,
        CCL.Knot.ArtinRelations.Generator.lower threeStrandIndex .positive]
      [CCL.Knot.ArtinRelations.Generator.upper threeStrandIndex .positive,
        CCL.Knot.ArtinRelations.Generator.lower threeStrandIndex .positive,
        CCL.Knot.ArtinRelations.Generator.upper threeStrandIndex .positive] := by
  simpa using PolynomialHomotopic.artin
    ([] : Word 3) [] threeStrandIndex .positive

end Exact

end CCL.Knot.Examples

module
public import Purelib.Data.Nat.Remainder
public import Purelib.Topology.Knot.Torus.Components
import Purelib.Polynomial.Ascending.Integer.Comparison
import Purelib.Topology.Knot.Torus.Alexander
public import Purelib.Topology.Knot.Torus.Invariants
import Purelib.Topology.Knot.Torus.Surface

public import Purelib.Data.Fin.Residue
import Purelib.Topology.Knot.Closure.Labeling
public import Purelib.Topology.Knot.Closure.Linking.Certificate
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Nat.GCD.Extended
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Topology.Knot.Closure.Basic
import Purelib.Topology.Knot.Closure.Linking.Scan
import Purelib.Topology.Knot.Torus.Basic

open Purelib

open Purelib.Polynomial

open Purelib.Topology

section
@[expose] public section

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

namespace Purelib.Examples.Topology.Knot.Torus.WorkedExamples

open Purelib.Examples
open Purelib.Data.Nat

open Purelib.Topology.Knot.Torus
open Purelib.Topology.Knot.Torus.Basic (PowerSingularity)
open Purelib.Topology.Knot.Torus.Invariants (TorusKnotInvariantCertificate)
open Purelib.Topology.Knot.Closure.Linking

open Purelib.Topology.Knot.Braid

/-! ## Five non-trivial torus knots -/

/-- The displayed power singularity with exponents 2 and 3. -/
def trefoil : PowerSingularity := ⟨2, 3, by
  decide, by decide⟩

section
/-- The finite surface and Alexander certificates for the (2, 3) torus knot.

The certificate retains coprimality, the canonical surface, the exact polynomial quotient identity and equality of
Alexander degree with twice the genus. -/
def trefoilInvariants :
  TorusKnotInvariantCertificate trefoil where
  gcdOne := by decide
  surface := Surface.canonicalSurfaceCertificate trefoil (by decide)
  alexander := Alexander.alexanderCertificate 2 3
    (by decide) (by decide) (by decide) (Ascending.Integer.Comparison.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

/-- The displayed (2, 3) closure has one component. -/
theorem trefoil_componentCount :
  trefoil.componentCount = 1 := by decide
/-- The positive braid for the (2, 3) torus knot has 3 crossings. -/
theorem trefoil_crossingCount :
  trefoil.braidWord.length = 3 := by decide
/-- The positive braid for the (2, 3) torus knot has writhe 3. -/
theorem trefoil_writhe :
  trefoil.braidWord.writhe = 3 := by decide
/-- The retained surface for the (2, 3) torus knot has genus 1. -/
theorem trefoil_genus :
  trefoilInvariants.surface.genus = 1 := by decide
/-- The normalized Alexander coefficient list for the (2, 3) torus knot is `[1, -1, 1]`. -/
theorem trefoil_alexander :
    trefoilInvariants.alexander.polynomial = [1, -1, 1] := by decide
/-- The displayed closure of the (2, 3) torus knot is a knot. -/
theorem trefoil_isKnot : (Closure.IsKnot
  trefoil.closure) :=
  trefoilInvariants.isKnot

end

/-- The displayed power singularity with exponents 2 and 5. -/
def cinquefoil : PowerSingularity := ⟨2, 5,
  by decide, by decide⟩

section
/-- The finite surface and Alexander certificates for the (2, 5) torus knot.

The certificate retains coprimality, the canonical surface, the exact polynomial quotient identity and equality of
Alexander degree with twice the genus. -/
def cinquefoilInvariants :
  TorusKnotInvariantCertificate cinquefoil where
  gcdOne := by decide
  surface := Surface.canonicalSurfaceCertificate cinquefoil (by decide)
  alexander := Alexander.alexanderCertificate 2 5
    (by decide) (by decide) (by decide) (Ascending.Integer.Comparison.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

/-- The displayed (2, 5) closure has one component. -/
theorem cinquefoil_componentCount :
  cinquefoil.componentCount = 1 := by decide
/-- The positive braid for the (2, 5) torus knot has 5 crossings. -/
theorem cinquefoil_crossingCount :
  cinquefoil.braidWord.length = 5 := by decide
/-- The positive braid for the (2, 5) torus knot has writhe 5. -/
theorem cinquefoil_writhe :
  cinquefoil.braidWord.writhe = 5 := by decide
/-- The retained surface for the (2, 5) torus knot has genus 2. -/
theorem cinquefoil_genus :
  cinquefoilInvariants.surface.genus = 2 := by decide
/-- The normalized Alexander coefficient list for the (2, 5) torus knot is `[1, -1, 1, -1, 1]`. -/
theorem cinquefoil_alexander :
    cinquefoilInvariants.alexander.polynomial = [1, -1, 1, -1, 1] := by decide
/-- The displayed closure of the (2, 5) torus knot is a knot. -/
theorem cinquefoil_isKnot : (Closure.IsKnot
  cinquefoil.closure) :=
  cinquefoilInvariants.isKnot

end

/-- The displayed power singularity with exponents 3 and 4. -/
def torusKnot34 : PowerSingularity := ⟨3, 4,
  by decide, by decide⟩

section
/-- The finite surface and Alexander certificates for the (3, 4) torus knot.

The certificate retains coprimality, the canonical surface, the exact polynomial quotient identity and equality of
Alexander degree with twice the genus. -/
def torusKnot34Invariants :
  TorusKnotInvariantCertificate torusKnot34 where
  gcdOne := by decide
  surface := Surface.canonicalSurfaceCertificate torusKnot34 (by decide)
  alexander := Alexander.alexanderCertificate 3 4
    (by decide) (by decide) (by decide) (Ascending.Integer.Comparison.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

/-- The displayed (3, 4) closure has one component. -/
theorem torusKnot34_componentCount :
  torusKnot34.componentCount = 1 := by decide
/-- The positive braid for the (3, 4) torus knot has 8 crossings. -/
theorem torusKnot34_crossingCount :
  torusKnot34.braidWord.length = 8 := by decide
/-- The positive braid for the (3, 4) torus knot has writhe 8. -/
theorem torusKnot34_writhe :
  torusKnot34.braidWord.writhe = 8 := by decide
/-- The retained surface for the (3, 4) torus knot has genus 3. -/
theorem torusKnot34_genus :
  torusKnot34Invariants.surface.genus = 3 := by decide
/-- The normalized Alexander coefficient list for the (3, 4) torus knot is `[1, -1, 0, 1, 0, -1, 1]`. -/
theorem torusKnot34_alexander :
    torusKnot34Invariants.alexander.polynomial =
      [1, -1, 0, 1, 0, -1, 1] := by decide
/-- The displayed closure of the (3, 4) torus knot is a knot. -/
theorem torusKnot34_isKnot : (Closure.IsKnot
  torusKnot34.closure) :=
  torusKnot34Invariants.isKnot

end

/-- The displayed power singularity with exponents 3 and 5. -/
def torusKnot35 : PowerSingularity := ⟨3, 5,
  by decide, by decide⟩

section
/-- The finite surface and Alexander certificates for the (3, 5) torus knot.

The certificate retains coprimality, the canonical surface, the exact polynomial quotient identity and equality of
Alexander degree with twice the genus. -/
def torusKnot35Invariants :
  TorusKnotInvariantCertificate torusKnot35 where
  gcdOne := by decide
  surface := Surface.canonicalSurfaceCertificate torusKnot35 (by decide)
  alexander := Alexander.alexanderCertificate 3 5
    (by decide) (by decide) (by decide) (Ascending.Integer.Comparison.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

/-- The displayed (3, 5) closure has one component. -/
theorem torusKnot35_componentCount :
  torusKnot35.componentCount = 1 := by decide
/-- The positive braid for the (3, 5) torus knot has 10 crossings. -/
theorem torusKnot35_crossingCount :
  torusKnot35.braidWord.length = 10 := by decide
/-- The positive braid for the (3, 5) torus knot has writhe 10. -/
theorem torusKnot35_writhe :
  torusKnot35.braidWord.writhe = 10 := by decide
/-- The retained surface for the (3, 5) torus knot has genus 4. -/
theorem torusKnot35_genus :
  torusKnot35Invariants.surface.genus = 4 := by decide
/-- The normalized Alexander coefficient list for the (3, 5) torus knot is `[1, -1, 0, 1, -1, 1, 0, -1, 1]`. -/
theorem torusKnot35_alexander :
    torusKnot35Invariants.alexander.polynomial =
      [1, -1, 0, 1, -1, 1, 0, -1, 1] := by decide
/-- The displayed closure of the (3, 5) torus knot is a knot. -/
theorem torusKnot35_isKnot : (Closure.IsKnot
  torusKnot35.closure) :=
  torusKnot35Invariants.isKnot

end

/-- The displayed power singularity with exponents 4 and 5. -/
def torusKnot45 : PowerSingularity := ⟨4, 5,
  by decide, by decide⟩

section
/-- The finite surface and Alexander certificates for the (4, 5) torus knot.

The certificate retains coprimality, the canonical surface, the exact polynomial quotient identity and equality of
Alexander degree with twice the genus. -/
def torusKnot45Invariants :
  TorusKnotInvariantCertificate torusKnot45 where
  gcdOne := by decide
  surface := Surface.canonicalSurfaceCertificate torusKnot45 (by decide)
  alexander := Alexander.alexanderCertificate 4 5
    (by decide) (by decide) (by decide) (Ascending.Integer.Comparison.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

/-- The displayed (4, 5) closure has one component. -/
theorem torusKnot45_componentCount :
  torusKnot45.componentCount = 1 := by decide
/-- The positive braid for the (4, 5) torus knot has 15 crossings. -/
theorem torusKnot45_crossingCount :
  torusKnot45.braidWord.length = 15 := by decide
/-- The positive braid for the (4, 5) torus knot has writhe 15. -/
theorem torusKnot45_writhe :
  torusKnot45.braidWord.writhe = 15 := by decide
/-- The retained surface for the (4, 5) torus knot has genus 6. -/
theorem torusKnot45_genus :
  torusKnot45Invariants.surface.genus = 6 := by decide
/-- The normalized Alexander coefficient list for the (4, 5) torus knot is `[1, -1, 0, 0, 1, 0, -1, 0, 1, 0, 0, -1, 1]`.
-/
theorem torusKnot45_alexander :
    torusKnot45Invariants.alexander.polynomial =
      [1, -1, 0, 0, 1, 0, -1, 0, 1, 0, 0, -1, 1] := by decide
/-- The displayed closure of the (4, 5) torus knot is a knot. -/
theorem torusKnot45_isKnot : (Closure.IsKnot
  torusKnot45.closure) :=
  torusKnot45Invariants.isKnot

/-! ## Non-coprime links -/

end

/-- The displayed power singularity with exponents 2 and 4. -/
def torusLink24 : PowerSingularity := ⟨2, 4,
  by decide, by decide⟩

section
/-- The displayed (2, 4) torus link has 2 components. -/
theorem torusLink24_componentCount :
  torusLink24.componentCount = 2 := by decide
/-- Each component orbit of the (2, 4) torus link has length one. -/
theorem torusLink24_orbitLength :
  torusLink24.componentOrbitLength = 1 := by
  decide
/-- The positive braid for the (2, 4) torus link has 4 crossings. -/
theorem torusLink24_crossingCount :
  torusLink24.braidWord.length = 4 := by
  decide
/-- The (2, 4) torus link is not a knot.

A strand returns after one step, contradicting the required absence of an early return in a single component. -/
theorem torusLink24_notKnot : ¬(Closure.IsKnot
  torusLink24.closure) := by
  intro single
  exact single.no_early_return ⟨0, by decide⟩ 1
    (by decide) (by decide) (by decide)

end

/-- The 2 retained component labels of the (2, 4) torus link.

Residue labels are preserved by the closure permutation and each label has its original finite strand representative. -/
def torusLink24Components :
  Knot.Closure.Labeling.ComponentLabeling torusLink24.closure 2 where
  componentOfStrand := Data.Fin.Residue.residueComponent (by decide)
  preserved := by decide
  represented := by
    intro component
    exact ⟨⟨component.val, component.isLt⟩, by
      apply Fin.ext
      exact Remainder.mod_eq_of_lt component.isLt⟩

section
/-- The linking certificate for components 0 and 1 of the (2, 4) torus link.

The retained labels are distinct and the signed crossing sum is twice the certified linking number two. -/
def torusLink24Linking :
  Certificate.PairCertificate torusLink24Components
    ⟨0, by decide⟩ ⟨1, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

/-- Components 0 and 1 of the (2, 4) torus link have linking number two. -/
theorem torusLink24_pairwiseLinking :
  torusLink24Linking.linking = 2 := rfl

end

/-- The displayed power singularity with exponents 3 and 6. -/
def torusLink36 : PowerSingularity := ⟨3, 6,
  by decide, by decide⟩

section
/-- The displayed (3, 6) torus link has 3 components. -/
theorem torusLink36_componentCount :
  torusLink36.componentCount = 3 := by decide
/-- Each component orbit of the (3, 6) torus link has length one. -/
theorem torusLink36_orbitLength :
  torusLink36.componentOrbitLength = 1 := by
  decide
/-- The positive braid for the (3, 6) torus link has 12 crossings. -/
theorem torusLink36_crossingCount :
  torusLink36.braidWord.length = 12 := by
  decide
/-- The (3, 6) torus link is not a knot.

A strand returns after one step, contradicting the required absence of an early return in a single component. -/
theorem torusLink36_notKnot : ¬(Closure.IsKnot
  torusLink36.closure) := by
  intro single
  exact single.no_early_return ⟨0, by decide⟩ 1
    (by decide) (by decide) (by decide)

end

/-- The 3 retained component labels of the (3, 6) torus link.

Residue labels are preserved by the closure permutation and each label has its original finite strand representative. -/
def torusLink36Components :
  Knot.Closure.Labeling.ComponentLabeling torusLink36.closure 3 where
  componentOfStrand := Data.Fin.Residue.residueComponent (by decide)
  preserved := by decide
  represented := by
    intro component
    exact ⟨⟨component.val, component.isLt⟩, by
      apply Fin.ext
      exact Remainder.mod_eq_of_lt component.isLt⟩

section
/-- The linking certificate for components 0 and 1 of the (3, 6) torus link.

The retained labels are distinct and the signed crossing sum is twice the certified linking number two. -/
def torusLink36Linking01 :
  Certificate.PairCertificate torusLink36Components
    ⟨0, by decide⟩ ⟨1, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

/-- The linking certificate for components 0 and 2 of the (3, 6) torus link.

The retained labels are distinct and the signed crossing sum is twice the certified linking number two. -/
def torusLink36Linking02 :
  Certificate.PairCertificate torusLink36Components
    ⟨0, by decide⟩ ⟨2, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

/-- The linking certificate for components 1 and 2 of the (3, 6) torus link.

The retained labels are distinct and the signed crossing sum is twice the certified linking number two. -/
def torusLink36Linking12 :
  Certificate.PairCertificate torusLink36Components
    ⟨1, by decide⟩ ⟨2, by decide⟩ where
  different := by decide
  linking := 2
  twice_linking := by decide

/-- Components 0 and 1 of the (3, 6) torus link have linking number two. -/
theorem torusLink36_pairwiseLinking01 :
  torusLink36Linking01.linking = 2 := rfl
/-- Components 0 and 2 of the (3, 6) torus link have linking number two. -/
theorem torusLink36_pairwiseLinking02 :
  torusLink36Linking02.linking = 2 := rfl
/-- Components 1 and 2 of the (3, 6) torus link have linking number two. -/
theorem torusLink36_pairwiseLinking12 :
  torusLink36Linking12.linking = 2 := rfl

/-! ## Trivial normalization -/

end

/-- The displayed power singularity with exponents 1 and 1. -/
def oneStrandUnknot : PowerSingularity :=
  ⟨1, 1, by decide, by decide⟩

section
/-- The finite surface and Alexander certificates for the one-strand unknot.

The certificate retains coprimality, the canonical surface, the exact polynomial quotient identity and equality of
Alexander degree with twice the genus. -/
def oneStrandUnknotInvariants :
    TorusKnotInvariantCertificate oneStrandUnknot where
  gcdOne := by decide
  surface := Surface.canonicalSurfaceCertificate oneStrandUnknot (by
    decide)
  alexander := Alexander.alexanderCertificate 1 1
    (by decide) (by decide) (by decide) (Ascending.Integer.Comparison.same_refl _)
  alexanderDegree_eq_twiceGenus := by decide

/-- The positive braid for the one-strand unknot has 0 crossings. -/
theorem oneStrandUnknot_crossingCount :
    oneStrandUnknot.braidWord.length = 0 := by decide
/-- The retained surface for the one-strand unknot has genus 0. -/
theorem oneStrandUnknot_genus :
    oneStrandUnknotInvariants.surface.genus = 0 := by decide
/-- The normalized Alexander coefficient list for the one-strand unknot is `[1]`. -/
theorem oneStrandUnknot_alexander :
    oneStrandUnknotInvariants.alexander.polynomial = [1] := by decide
/-- The displayed closure of the one-strand unknot is a knot. -/
theorem oneStrandUnknot_isKnot : (Closure.IsKnot
  oneStrandUnknot.closure) :=
  oneStrandUnknotInvariants.isKnot

/-! ## Exact split-polynomial realizations -/

end

end Purelib.Examples.Topology.Knot.Torus.WorkedExamples

end

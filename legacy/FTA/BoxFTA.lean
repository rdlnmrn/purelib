import FTA.AxisExecutableResultant
import FTA.GaussianDenseSquarefree
import FTA.Maximality

/-!
# Box-only finite constructive FTA

This module is the standalone numerical FTA layer.  From positive degree and
an explicit dense squarefree certificate it computes the two axis eliminants,
isolates exactly `p.natDegree` pairwise separated winding-one tracks in the
coefficient-computed large square, and proves the degree-sharp maximality
bound for every other pairwise separated family.

No CCL controller, parser, word, or projective envelope is needed by this
module.  `FTA.FiniteConstructiveFTA` imports this result and adds the symbolic
CCL layer without changing the underlying box theorem.
-/

namespace FTA.BoxFTA

open CCL
open FTA.AxisExecutableResultant
open FTA.AxisSafeCuts
open FTA.ComputablePolynomial
open FTA.GlobalWinding
open FTA.LocalExtraction

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

/-- Minimal mathematical input for both the box-only and CCL-coupled finite
FTA constructions.  Axis eliminants are computed internally. -/
structure Input (p : GaussianPolynomial) where
  squarefree : GaussianSquarefreeCertificate p
  degreePositive : 0 < p.natDegree

namespace Input

/-- Primitive inputs of degree greater than one obtain their squarefree
certificate constructively from dense Gaussian extended Euclid. -/
def ofPrimitiveDegreeGtOne
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) : Input p where
  squarefree :=
    FTA.GaussianDenseSquarefree.primitiveSquarefreeCertificate primitive
      (Nat.zero_lt_of_lt degree)
  degreePositive := Nat.zero_lt_of_lt degree

/-- Common explicit degree bound for the two computed axis resultants. -/
def eliminationDegree {p : GaussianPolynomial} (_input : Input p) : ℕ :=
  2 * p.natDegree ^ 2

/-- Closed dense-Sylvester elimination certificate computed from the input
coefficient list. -/
def elimination {p : GaussianPolynomial} (input : Input p) :
    AxisEliminationCertificate p input.eliminationDegree :=
  computedAxisEliminationCertificate p
    (isZero_false_of_natDegree_pos input.degreePositive)
    input.degreePositive

theorem sparseDegreeNonzero
    {p : GaussianPolynomial} (input : Input p) :
    p.toPolynomial.natDegree ≠ 0 := by
  have nonzero := isZero_false_of_natDegree_pos input.degreePositive
  rw [DensePolynomial.natDegree_toPolynomial nonzero]
  exact Nat.ne_of_gt input.degreePositive

/-- Exact degree-many winding-box isolation in the computed large square. -/
def isolation
    {p : GaussianPolynomial} (input : Input p) :
    ExactIsolation.Output p (largeSquareBox p) p.natDegree :=
  ExactIsolation.isolateLargeSquare input.squarefree input.degreePositive
    input.elimination

/-- Degree-sharp bound for arbitrary pairwise separated winding-one tracks in
the computed large square. -/
theorem familyCardLe
    {p : GaussianPolynomial} (input : Input p) {familyCount : ℕ}
    (family : Fin familyCount →
      RootTrackSeparation.WindingOneTrack p (largeSquareBox p))
    (pairwise : ∀ i j, i ≠ j →
      (family i).initial.box.Separated (family j).initial.box) :
    familyCount ≤ p.natDegree :=
  Maximality.finite_family_card_le_natDegree input.squarefree
    input.degreePositive input.elimination family pairwise

end Input

/-- Complete box-only FTA result: exact degree-many isolation together with
the degree-sharp maximality theorem. -/
structure Result (p : GaussianPolynomial) where
  isolation : ExactIsolation.Output p (largeSquareBox p) p.natDegree
  maximality :
    ∀ {familyCount : ℕ}
      (family : Fin familyCount →
        RootTrackSeparation.WindingOneTrack p (largeSquareBox p)),
      (∀ i j, i ≠ j →
        (family i).initial.box.Separated (family j).initial.box) →
      familyCount ≤ p.natDegree

/-- Standalone box-only finite constructive FTA. -/
def prove {p : GaussianPolynomial} (input : Input p) : Result p where
  isolation := input.isolation
  maximality := input.familyCardLe

/-- Primitive degree-greater-than-one specialization of the box theorem. -/
def provePrimitive
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degree : 1 < p.natDegree) : Result p :=
  prove (Input.ofPrimitiveDegreeGtOne primitive degree)

end FTA.BoxFTA

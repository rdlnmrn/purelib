module

public import Purelib.Geometry.Projective.Hermitian.Parabola
public import Purelib.Geometry.Projective.Hermitian.Affine
public import Purelib.Polynomial.Dense.Rational.Product.List
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.List
import Purelib.Approximation.Rational.Grid.Interior
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Interior rational samples avoiding finite Hermitian boundaries

One retained parabolic arc and one product of its guarded restrictions give
a finite degree-bounded rational search. The selected point stays strictly
inside the original box and avoids every non-universal input form.
-/

public section

namespace Purelib.Geometry.Projective.Hermitian.Box

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.Nonzero
open Purelib.Approximation.Rational

set_option genInjectivity false in
/-- Retain an interior rational sample avoiding every non-universal form in one original finite family.

The original arc, guarded polynomial restrictions, product and selected
parameter are all cached. Their exact receipts bind the resulting point
to the same original forms and parent box used by the bounded search.
-/
structure Sample (forms : List HermitianForm) (outer : Rational.Box) where
  /-- The actual retained parabolic sampling arc. -/ arc : Rational.Box.Sample.Parabola outer
  /-- The guarded restriction cache in original form order. -/ polynomials :
    List (Dense.Basic.DensePolynomial Fraction.Rational)
  /-- The polynomial cache uses the exact original forms and retained arc. -/ polynomialsSpec :
    polynomials = forms.map (fun form => form.guardedRestriction arc)
  /-- The cached product of the actual guarded restriction list. -/ product :
    Dense.Basic.DensePolynomial Fraction.Rational
  /-- The product uses this exact polynomial cache, preserving repeated occurrences. -/ productSpec :
    product = Dense.Rational.Product.List.polynomialProduct polynomials
  /-- The computed product is a represented nonzero polynomial. -/ productNonzero : product.isZero = false
  /-- The exact ordered interior candidate list, materialized once. -/ candidates : List Fraction.Rational
  /-- The finite candidate list uses this retained product's degree and the original unit interval. -/ candidatesSpec :
    candidates = Grid.Interior.interiorCandidates 0 1 product.natDegree
  /-- The actual original candidate scan and every polynomial value it computed. -/ search :
    Search.List.Scan product candidates
  /-- The retained search is the exact once-computed scan of this cached product and list. -/ searchSpec :
    search = Search.List.scan product candidates
  /-- The same actual finite search succeeded. -/ searchSuccess : search.result.isSome
  /-- The rational parameter selected by the finite nonzero search. -/ parameter : Fraction.Rational
  /-- The parameter is projected from this retained scan, without another polynomial evaluation. -/ parameterSpec :
    parameter = search.result.get searchSuccess
  /-- The selected parameter is strictly above zero. -/ parameterPositive : 0 < parameter
  /-- The selected parameter is strictly below one. -/ parameterLessOne : parameter < 1
  /-- The actual cached product is nonzero at the selected parameter. -/ productValueNonzero :
    product.eval parameter ≠ 0
  /-- The actual cached Gaussian rational sample point. -/ point : Gaussian.Basic.Canonical
  /-- The point is the exact arc sample at the selected parameter. -/ pointSpec : point = arc.point parameter
  /-- The actual sample lies strictly inside its original parent box. -/ inside : outer.StrictContains point
  /-- Every non-universal original form is nonzero at this same sample. -/ regular :
    ∀ form ∈ forms, ¬form.IsZero → form.eval point ≠ 0

/-- Compute a rational interior point avoiding every non-universal form in an arbitrary finite family.

The builder materializes the guarded restrictions once and computes their
product once. The original polynomial-degree bound certifies the finite
interior scan, whose actual result supplies the retained sample parameter.
Coefficientwise zero forms retain their separate universal-zero semantics.
-/
def sampleAvoidingForms (forms : List HermitianForm) (outer : Rational.Box) (proper : outer.Proper) :
    Sample forms outer := by
  let arc := Rational.Box.Sample.Parabola.ofBox outer proper
  let polynomials := forms.map (fun form => form.guardedRestriction arc)
  have allNonzero : ∀ polynomial ∈ polynomials, polynomial.isZero = false := by
    intro polynomial member
    rcases List.Map.mem_map.mp member with ⟨form, _, equal⟩
    rewrite [← equal]
    exact form.guardedRestriction_nonzero arc
  let product := Dense.Rational.Product.List.polynomialProduct polynomials
  have productNonzero : product.isZero = false :=
    Dense.Rational.Product.List.polynomialProduct_isZero_false allNonzero
  have intervalProper : (0 : Fraction.Rational) < 1 := by decide
  let candidates := Grid.Interior.interiorCandidates 0 1 product.natDegree
  let search := Search.Interval.interiorSearch product 0 1 product.natDegree
  have searchSuccess : search.result.isSome :=
    Search.Interval.interiorSearch_isSome product
      product.natDegree intervalProper productNonzero (Nat.le_refl _)
  let parameter := search.result.get searchSuccess
  have parameterSpec := Search.Interval.interiorSearchValue_spec product
    product.natDegree intervalProper productNonzero (Nat.le_refl _)
  rewrite [Search.Interval.interiorSearchValue_eq_get] at parameterSpec
  let point := arc.point parameter
  refine
    { arc := arc
      polynomials := polynomials
      polynomialsSpec := rfl
      product := product
      productSpec := rfl
      productNonzero := productNonzero
      candidates := candidates
      candidatesSpec := rfl
      search := search
      searchSpec := Search.Interval.interiorSearch_eq product 0 1 product.natDegree
      searchSuccess := searchSuccess
      parameter := parameter
      parameterSpec := rfl
      parameterPositive := parameterSpec.2.1
      parameterLessOne := parameterSpec.2.2
      productValueNonzero := parameterSpec.1
      point := point
      pointSpec := rfl
      inside := arc.point_strictContains parameterSpec.2.1.le parameterSpec.2.2.le
      regular := ?_ }
  intro form member nonzero
  apply form.eval_ne_zero_of_guardedRestriction arc nonzero
  have polynomialMember : form.guardedRestriction arc ∈ polynomials :=
    List.Map.mem_map_of_mem (f := fun retained => retained.guardedRestriction arc) member
  exact Dense.Rational.Product.List.eval_ne_zero_of_mem_of_polynomialProduct
    polynomialMember parameterSpec.1

namespace Sample

/-- The original finite search evaluates at most the retained product's degree plus one candidates. -/
theorem evaluationCount_le {forms : List HermitianForm} {outer : Rational.Box}
    (sample : Sample forms outer) : sample.search.evaluations.length ≤ sample.product.natDegree + 1 := by
  have bounded := Search.List.scan_length_le sample.product sample.candidates
  rewrite [← sample.searchSpec] at bounded
  have length : sample.candidates.length = sample.product.natDegree + 1 :=
    (congrArg List.length sample.candidatesSpec).trans (Grid.Interior.interiorCandidates_length _ _ _)
  exact Nat.le_trans bounded (Nat.le_of_eq length)

/-- Every actual cached polynomial evaluation belongs to the same retained candidate list and product. -/
theorem evaluation {forms : List HermitianForm} {outer : Rational.Box}
    (sample : Sample forms outer) (entry : Fraction.Rational × Fraction.Rational)
    (member : entry ∈ sample.search.evaluations) :
    entry.1 ∈ sample.candidates ∧ entry.2 = sample.product.eval entry.1 := by
  rewrite [sample.searchSpec] at member
  exact Search.List.scan_evaluation _ _ _ member

/-- A retained squared-distance guard excludes its exact original centre from the regular sample. -/
theorem ne_center {forms : List HermitianForm} {outer : Rational.Box}
    (sample : Sample forms outer) (center : Gaussian.Basic.Canonical)
    (member : distanceSqForm center ∈ forms) : sample.point ≠ center := by
  have guarded := sample.regular (distanceSqForm center) member (distanceSqForm_nonzero center)
  intro equal
  rewrite [eval_distanceSqForm, equal, Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero] at guarded
  exact guarded rfl

end Sample

end Purelib.Geometry.Projective.Hermitian.Box

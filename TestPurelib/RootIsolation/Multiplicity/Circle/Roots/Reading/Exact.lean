module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Exact
import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.Data.Gaussian.Field

/-!
# An exact nonmonic linear factor over a nonmultiplicative parent

The original quadratic coefficient algebra has zero divisors. Its parent
reading evaluates the original generator at a nonroot and has positive
multiplication error. The nonmonic formal linear source nevertheless reads
as the original Gaussian linear factor, whose exact root is read exactly
by the actual original paid source-expansion construction.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Exact

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense (Companion)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Request)
open Purelib.Polynomial.Dense.Gaussian.Roots.Certificate (ExactRoot)
open Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading (Exact)
open Purelib.RootIsolation.Multiplicity.Circle (ExactLocation)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Monogenic (Cyclic)
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

/-- The original quadratic supplies the exact coefficient algebra and its genuine source relation. -/
private def baseSource : DensePolynomial Canonical := ⟨[1, 0, -1]⟩

/-- The original companion supplies its retained adjunction without any field on the resulting algebra. -/
private def baseAdjunction := (Companion.ofUnit baseSource (by decide +kernel) 1 (by decide +kernel)).adjoin

/-- The same original coefficient algebra has actual zero divisors. -/
private theorem zero_divisors :
    (baseAdjunction.root - 1) * (baseAdjunction.root + 1) = 0 ∧
      baseAdjunction.root - 1 ≠ 0 ∧ baseAdjunction.root + 1 ≠ 0 := by decide +kernel

/-- The original cyclic parent parameters are fixed at unit coefficient gain and quadrance radius. -/
private def baseParameters :=
  Cyclic.Element.Reading.Parameters.prepare baseAdjunction.table Norm.weight 1 1 (by decide) (by decide)

/-- The original parent reads its formal generator at the rational nonroot one half. -/
private def parentReading := baseParameters.toReading GaussianReading.identity rfl (1/2) (by decide +kernel)
  (9/16) (by decide +kernel) (by decide +kernel)

/-- The actual parent has positive multiplication error and does not preserve the original generator square. -/
private theorem parent_nonmultiplicative :
    0 < parentReading.error ∧ parentReading.read baseAdjunction.root = 1/2 ∧
      parentReading.read (baseAdjunction.root ^ 2) = 1 ∧
        parentReading.read (baseAdjunction.root ^ 2) ≠ parentReading.read baseAdjunction.root ^ 2 := by decide +kernel

/-- The same original scalar embedding is retained for the formal linear source. -/
private abbrev scalar := Cyclic.Element.scalar baseAdjunction.table

/-- The actual nonmonic formal polynomial retains the original quadratic generator as its constant coefficient. -/
private def source : DensePolynomial (Companion.Adjunction.Scalar baseAdjunction.companion baseAdjunction.table) :=
  ⟨[scalar 2, -baseAdjunction.root]⟩

/-- Reading those same formal coefficients gives this original nonmonic Gaussian linear polynomial. -/
private def observed : DensePolynomial Canonical := ⟨[2, -1/2]⟩

/-- The original observed factor has its exact Gaussian root at one quarter. -/
private def root : ExactRoot observed := ⟨1/4, by decide +kernel⟩

/-- The original automatic formal tower uses its actual leading-unit inverse one half. -/
private def tower := Tower.prepare source (by decide +kernel) (scalar (1/2)) (by decide +kernel)

/-- The same retained root quadrance determines the fixed pre-construction radius. -/
private def pointNorm := Norm.Basic.normSq root.point

/-- All original formal-tower parameters use the same parent reading gain and fixed exact-root radius. -/
private def parameters := Parameters.prepare tower (Cyclic.Element.weight baseAdjunction.table Norm.weight)
  parentReading.gain (1 + pointNorm) parentReading.gainNonnegative (by decide +kernel)

/-- The complete original budget is fixed before the exact branch is assembled. -/
private def request := Request.prepare parameters 1 (by decide +kernel)

/-- The same nonmonic formal source retains its original Gaussian scalar leading coefficient. -/
private theorem leading : Tower.Leading tower scalar observed.leadingCoeff :=
  Tower.Leading.ofSource tower scalar observed.leadingCoeff (by decide +kernel) (by decide +kernel)
    (Cyclic.Element.scalar_zero _) (Cyclic.Element.scalar_one _) (Cyclic.Element.scalar_mul _)

/-- The original coefficient reading identifies the complete same Gaussian polynomial, without a product-map premise. -/
private theorem observed_source : observed = Purelib.Polynomial.Dense.Map.map parentReading.read source :=
  by decide +kernel

/-- One actual original source expansion constructs the same exact branch using the already cached point quadrance. -/
private def retained := Exact.ofNorm request.budget leading parentReading rfl root (by decide +kernel)
  (by decide +kernel) observed_source pointNorm rfl (by decide +kernel)

/-- The retained point quadrance and source-leading inverse cache have their independent expected values. -/
private theorem caches : retained.pointNorm = 1/16 ∧ retained.sources.coefficientInverse = 1/2 ∧
    retained.sources.inverseNorm = 1/4 := by decide +kernel

/-- The general exact association reads the same original formal tower root as the original exact observed point. -/
private theorem exact_reading :
    retained.sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point = root.point :=
  retained.read_root ⟨0, by decide +kernel⟩

/-- The exact formal root reading keeps its cached quadrance despite positive parent multiplication error. -/
private theorem exact_quadrance :
    Norm.Basic.normSq (retained.sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point) =
      retained.pointNorm := retained.normSq_root ⟨0, by decide +kernel⟩

/-- The original scaled linear clearance supplies the observed nonmonic factor's whole-circle margin. -/
private def clearance : Certificate observed :=
  have same : DensePolynomial.scale (2 : Canonical) (LinearFactor.linearFactor root.point) = observed :=
    by decide +kernel
  same ▸ (Certificate.linearInside root.point (by decide +kernel)).scale 2 (by decide +kernel)

/-- The original exact location procedure classifies this same observed root from its retained whole-circle margin. -/
private def location := ExactLocation.prepare clearance root

/-- The same original location yields a genuine source-fixed ceiling for the actual formal-root reading. -/
private theorem radial_inside : retained.pointNorm < 1 ∧
    Norm.Basic.normSq (retained.sampled.realization.finalReading.read (tower.blocks[0]'(by decide +kernel)).point) ≤
      retained.pointNorm := retained.radial location ⟨0, by decide +kernel⟩

/-- The complete retained constructor is restored from its original caches and certificates. -/
private theorem restoration :
    retained = Exact.prepare request.budget leading parentReading rfl root (by decide +kernel)
      (by decide +kernel) observed_source (by decide +kernel) :=
  Exact.ofNorm_eq_prepare _ _ _ pointNorm rfl _

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Exact

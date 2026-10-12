module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transition
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Product

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

public section

/-!
# Finite geometry for transporting and selecting logarithm branches

An anchored complex logarithm is local data.  This file supplies the missing
geometric constructors around that data.

* `SafeOverlapExtension` rechecks one chart's rational denominator and
  reduced-disk inequalities on a second coherent name and records an actual
  rational point admitted by both finite enclosures.  The original factor,
  correction process, and correction certificate can then be transported.
* `LocalExpInjectivity` is a displayed finite cell, membership certificates
  for two particular coherent names, and the local exponential-injectivity
  rule for that pair.  It is deliberately local and never chooses a global
  logarithm branch.
* `SelectedLogarithm.ofOverlap` combines those two pieces of finite data.  It
  constructs an anchored chart over the computed exponential and derives the
  zero-alignment certificate required for `log (exp x) = x`.

The local complex-log congruence proved first is quantitative: it compares
finite reduced-argument samples with the existing rational sensitivity bound
and finite truncation bounds.  No completed logarithm or limiting argument is
introduced.
-/

open Purelib.Approximation

/-- Explicit finite data for the guarded logarithm product law: the displayed product input must be the actual CCL
product, and the selected product branch must have zero discrepancy from the selected sum branch. -/
@[expose] def ProductAlignment
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : Anchored.AnchoredChart leftInput)
    (rightBranch : Anchored.AnchoredChart rightInput)
    (productBranch : Anchored.AnchoredChart productInput) : Type :=
  Gaussian.Equivalence.NamedEquivalent productInput.name
      (Named.mul
        leftInput.name rightInput.name) ×
    Difference.LocalAlignment
      (CoherentNamed.add
        leftBranch.output rightBranch.output) productBranch.output

namespace ProductAlignment

/-- Read the retained operational equivalence between the displayed product input and the actual coherent product. -/
@[expose] def productEquivalent
    {leftInput rightInput productInput : CoherentNamed}
    {leftBranch : Anchored.AnchoredChart leftInput}
    {rightBranch : Anchored.AnchoredChart rightInput}
    {productBranch : Anchored.AnchoredChart productInput}
    (alignment : Approximation.Gaussian.Logarithm.Chart.Product.ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    Gaussian.Equivalence.NamedEquivalent productInput.name
      (Named.mul
        leftInput.name rightInput.name) :=
  alignment.1

/-- Read the retained zero discrepancy between the selected product branch and the selected sum of logarithms. -/
@[expose] def zeroDiscrepancy
    {leftInput rightInput productInput : CoherentNamed}
    {leftBranch : Anchored.AnchoredChart leftInput}
    {rightBranch : Anchored.AnchoredChart rightInput}
    {productBranch : Anchored.AnchoredChart productInput}
    (alignment : Approximation.Gaussian.Logarithm.Chart.Product.ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    Difference.LocalAlignment
      (CoherentNamed.add
        leftBranch.output rightBranch.output) productBranch.output :=
  alignment.2

end ProductAlignment

/-- The same finite product certificate also recovers the weaker but unconditional branch statement: its discrepancy
exponentiates to one. -/
@[expose] def logarithm_product_discrepancy_unit
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : Anchored.AnchoredChart leftInput)
    (rightBranch : Anchored.AnchoredChart rightInput)
    (productBranch : Anchored.AnchoredChart productInput)
    (alignment : Approximation.Gaussian.Logarithm.Chart.Product.ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Transition.productBranchDiscrepancy
          leftInput rightInput productInput leftBranch rightBranch
            productBranch).name)
      (Named.exact 1) :=
  Transition.exp_productBranchDiscrepancy_unit
    leftInput rightInput productInput leftBranch rightBranch productBranch
      alignment.productEquivalent

/-- On an explicitly zero-aligned product branch, the actual logarithm CCL equals the actual sum of the two logarithm
CCLs. -/
@[expose] def logarithm_product_of_alignment
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : Anchored.AnchoredChart leftInput)
    (rightBranch : Anchored.AnchoredChart rightInput)
    (productBranch : Anchored.AnchoredChart productInput)
    (alignment : Approximation.Gaussian.Logarithm.Chart.Product.ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    Gaussian.Equivalence.NamedEquivalent productBranch.output.name
      (CoherentNamed.add
        leftBranch.output rightBranch.output).name :=
  Difference.equivalent_of_difference_zero _ _ alignment.zeroDiscrepancy

/-- Bit-producing form of the guarded logarithm product law. -/
@[expose] def logarithm_product_bitLaw
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : Anchored.AnchoredChart leftInput)
    (rightBranch : Anchored.AnchoredChart rightInput)
    (productBranch : Anchored.AnchoredChart productInput)
    (alignment : Approximation.Gaussian.Logarithm.Chart.Product.ProductAlignment leftInput rightInput productInput
      leftBranch rightBranch productBranch) :
    Law.Basic.BitLaw productBranch.output
      (CoherentNamed.add
        leftBranch.output rightBranch.output) :=
  BitLaw.ofEquivalent
    (Approximation.Gaussian.Logarithm.Chart.Product.logarithm_product_of_alignment leftInput rightInput productInput
      leftBranch rightBranch productBranch alignment)

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Product

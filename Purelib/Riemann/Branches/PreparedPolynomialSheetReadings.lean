module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic

public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Normalization.InverseModelBackwardSigns
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# Read an aligned operational patch at its retained polynomial index

The operational alignment relation uses two extra Newton steps only in its
proof. Backwards sign preservation removes that floor from the polynomial
actually consumed by a primitive request, including indices zero and one.
-/

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetReadings

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Normalization in
/-- Root alignment gives nearestness against any original independent polynomial refinement index.

The original model and continued patch both contain the same point, and the supplied operational root-name equivalence
connects their retained owners. Backward two-step comparison removes the extra refinements without changing the selected
sign. -/
theorem nearest_at_index {polynomial : Polynomial} {box : Box}
    {model : OverlapReady polynomial box} {point : Gaussian} {root : Name.Basic.Named}
    (aligned : RootAligned model point root) (pointInside : box.Contains point)
    {count : Nat} (patch : ContinuedNeighborhood polynomial count) (inside : patch.box.Contains point)
    (sample : ContinuedNeighborhood.Point patch point) (roots : Equivalence.NamedEquivalent root
      sample.certificate.value.name)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (model.model.value.eval point - (patch.base.refine index).value.eval point) ≤
      Data.Gaussian.Norm.Basic.normSq (model.model.value.eval point + (patch.base.refine index).value.eval point) := by
  have nearest : Basic.Canonical.normSq (model.model.value.eval point - (patch.base.refine index).step.step.value.eval
    point) ≤
      Basic.Canonical.normSq (model.model.value.eval point + (patch.base.refine index).step.step.value.eval point) := by
    have scalar := aligned patch inside sample roots index
    simpa only [Norm.Basic.normSq_eq_canonical, OwnerSeededInverseRoot.SeededNeighborhood.refine,
      InverseRootPolynomial.Model.refine] using scalar
  have scalar := model.nearest_before_two_steps (patch.base.refine index) pointInside
    (patch.box_refines.contains inside) nearest
  simpa only [Norm.Basic.normSq_eq_canonical] using scalar

end Purelib.Riemann.Branches.PreparedPolynomialSheetReadings

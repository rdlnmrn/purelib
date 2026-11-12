module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Cells
public import Purelib.Polynomial.Clearance.Box.Region.Factor
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
public import Purelib.Riemann.Normalization.InverseRootPolynomial.Factor
public import Purelib.Geometry.Rational.Box.Intersection
public import Purelib.Geometry.Rational.Box.Point
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring

/-! # The retained ramified coordinate as an original inverse-root source

The original reciprocal source has q=wP. Its actual positive clearance
therefore supplies clearance for w and P on the SAME box. At an original
cap overlap, the retained attached t owner seeds the existing inverse-root
continuation constructor for w; no independent sheet label is selected.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Dense.Gaussian.Factorization
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}

/-- The original coordinate and cap factor give a checked finite factorization of the actual reciprocal radicand. -/
theorem coordinateFactor :
    Identity.ProductIdentity (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))
      coordinate cap.polynomial := by
  apply Identity.factorizationOfCandidateEvals
  intro point _
  rewrite [radicand_eq (frame := frame) (cap := cap), eval_shift, pow_one, coordinate_eval]
  exact Basic.mul_comm _ _

/-- The same original factorization in reversed factor order retains the whole cap polynomial. -/
theorem regularFactor :
    Identity.ProductIdentity (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))
      cap.polynomial coordinate := by
  apply Identity.factorizationOfCandidateEvals
  intro point _
  rewrite [radicand_eq (frame := frame) (cap := cap), eval_shift, pow_one, coordinate_eval]
  rfl

/-- The original reciprocal clearance derives a positive ramified-coordinate clearance on the same closed box. -/
def coordinateClearance {box : Box}
    (original : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box) :
    RegionClearance coordinate box :=
  original.ofFactor (coordinateFactor (frame := frame) (cap := cap))

/-- The same reciprocal clearance derives a positive regular-factor clearance without changing the box. -/
def regularClearance {box : Box}
    (original : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box) :
    RegionClearance cap.polynomial box :=
  original.ofFactor (regularFactor (frame := frame) (cap := cap))

section Preparation

variable {count : Nat} {center : Canonical}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {differential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal differential}

/-- Derive both actual factor clearances from the SAME already retained reciprocal source preparation. -/
def sourceClearances (preparation : PotentialComparison.Preparation comparison) :
    RegionClearance coordinate terminal.neighborhood.patch.base.box ×
      RegionClearance cap.polynomial terminal.neighborhood.patch.base.box :=
  let ramified := coordinateClearance (frame := frame) (cap := cap) preparation.2.2.clearance
  let regular := regularClearance (frame := frame) (cap := cap) preparation.2.2.clearance
  ⟨ramified, regular⟩

/-- The complete factor-clearance factory consumes the same original retained clearance twice without rebuilding it. -/
private theorem packaged_sourceClearances_factory (preparation : PotentialComparison.Preparation comparison) :
    sourceClearances preparation =
      (let ramified := coordinateClearance (frame := frame) (cap := cap) preparation.2.2.clearance
       let regular := regularClearance (frame := frame) (cap := cap) preparation.2.2.clearance
       ⟨ramified, regular⟩ :
        RegionClearance coordinate terminal.neighborhood.patch.base.box ×
          RegionClearance cap.polynomial terminal.neighborhood.patch.base.box) := by rfl

/-- The complete factor-clearance factory consumes the same original retained clearance twice without rebuilding it. -/
theorem sourceClearances_factory (preparation : PotentialComparison.Preparation comparison) :
    sourceClearances preparation =
      (let ramified := coordinateClearance (frame := frame) (cap := cap) preparation.2.2.clearance
       let regular := regularClearance (frame := frame) (cap := cap) preparation.2.2.clearance
       ⟨ramified, regular⟩ :
        RegionClearance coordinate terminal.neighborhood.patch.base.box ×
          RegionClearance cap.polynomial terminal.neighborhood.patch.base.box) :=
  packaged_sourceClearances_factory preparation

/-- Intersect the two original model boxes using the actual retained physical point as the common witness. -/
def coordinateModelBox (terminal : TerminalModels.Terminal cap centerOwner count) (point : Canonical)
    (inSource : terminal.neighborhood.patch.base.box.Contains point) (inCap : collar.box.Contains point) : Box :=
  Box.Intersection.intersection terminal.neighborhood.patch.base.box collar.box (Box.Point.pointBox point)
    inSource inCap

/-- The whole common box is the original intersection of the two retained domains at their actual physical witness. -/
private theorem packaged_coordinateModelBox_factory (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) :
    coordinateModelBox terminal point inSource inCap =
      Box.Intersection.intersection terminal.neighborhood.patch.base.box collar.box (Box.Point.pointBox point)
        inSource inCap := by rfl

/-- The whole common box is the original intersection of the two retained domains at their actual physical witness. -/
theorem coordinateModelBox_factory (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) :
    coordinateModelBox terminal point inSource inCap =
      Box.Intersection.intersection terminal.neighborhood.patch.base.box collar.box (Box.Point.pointBox point)
        inSource inCap := packaged_coordinateModelBox_factory terminal point inSource inCap

/-- The actual coordinate-model box retains its original reciprocal model domain. -/
private theorem packaged_coordinateModelBox_source (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) :
    (coordinateModelBox terminal point inSource inCap).Refines terminal.neighborhood.patch.base.box := by
  unfold coordinateModelBox
  exact Box.Intersection.intersection_refines_first

/-- The actual coordinate-model box retains its original reciprocal model domain. -/
theorem coordinateModelBox_source (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) :
    (coordinateModelBox terminal point inSource inCap).Refines terminal.neighborhood.patch.base.box :=
  packaged_coordinateModelBox_source terminal point inSource inCap

/-- The same actual coordinate-model box retains its original regular cap model domain. -/
private theorem packaged_coordinateModelBox_cap (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) :
    (coordinateModelBox terminal point inSource inCap).Refines collar.box := by
  unfold coordinateModelBox
  exact Box.Intersection.intersection_refines_second

/-- The same actual coordinate-model box retains its original regular cap model domain. -/
theorem coordinateModelBox_cap (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) :
    (coordinateModelBox terminal point inSource inCap).Refines collar.box :=
  packaged_coordinateModelBox_cap terminal point inSource inCap

/-- Any physical point in both original model boxes remains in their actual computed intersection. -/
private theorem packaged_coordinateModelBox_contains (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) (sample : Canonical)
    (sampleSource : terminal.neighborhood.patch.base.box.Contains sample) (sampleCap : collar.box.Contains sample) :
    (coordinateModelBox terminal point inSource inCap).Contains sample :=
  ⟨Data.Rat.Fraction.Order.Basic.max_le sampleSource.1 sampleCap.1,
    Data.Rat.Fraction.Order.Basic.le_min sampleSource.2.1 sampleCap.2.1,
    Data.Rat.Fraction.Order.Basic.max_le sampleSource.2.2.1 sampleCap.2.2.1,
    Data.Rat.Fraction.Order.Basic.le_min sampleSource.2.2.2 sampleCap.2.2.2⟩

/-- Any physical point in both original model boxes remains in their actual computed intersection. -/
theorem coordinateModelBox_contains (terminal : TerminalModels.Terminal cap centerOwner count)
    (point : Canonical) (inSource : terminal.neighborhood.patch.base.box.Contains point)
    (inCap : collar.box.Contains point) (sample : Canonical)
    (sampleSource : terminal.neighborhood.patch.base.box.Contains sample) (sampleCap : collar.box.Contains sample) :
    (coordinateModelBox terminal point inSource inCap).Contains sample :=
  packaged_coordinateModelBox_contains terminal point inSource inCap sample sampleSource sampleCap

variable {start finish : Canonical} {physicalCoordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Data.Rat.Fraction.Rational} {nonnegative : 0 ≤ allowance}
    {numerator : InverseRootPolynomial.Polynomial} {regularIndex : Nat} {regularBox : Box}

/-- The actual supplied reciprocal cell meets the factor-model ceiling when its original stage is at least two. -/
theorem coordinateModel_source_small (preparation : PotentialComparison.Preparation comparison)
    (retained : Cell preparation.2.1 physicalCoordinate stage allowance nonnegative) (later : 2 ≤ stage) :
    retained.inverse.bound ≤ 1 / 256 :=
  (congrArg (fun model : InverseRootPolynomial.Model
    (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) terminal.neighborhood.patch.base.box => model.bound)
    retained.inverse_eq).trans_le
      (InverseRootPolynomial.Model.refine_bound_small_two terminal.neighborhood.patch.base.model stage later)

/-- The actual supplied regular cap sample retains its original1/256 ceiling at every finite stage. -/
theorem coordinateModel_cap_small (regular : PolynomialSample cap numerator regularIndex regularBox) :
    regular.1.val.bound ≤ 1 / 256 :=
  (congrArg (fun model : InverseRootPolynomial.Model cap.polynomial collar.box => model.bound)
    regular.1.property).trans_le
      ((InverseRootPolynomial.Model.refine_bound_le cap.model regularIndex).trans cap.model_small)

/-- Construct an original inverse-w model from the same reciprocal and regular sample caches on their actual common box.

The new value is P*B*A and the residual is rho_q+rho_P-rho_q*rho_P.
The physical witness computes the intersection rather than equating either
old domain with a new one. A cell below stage two requires that genuine
future floor; this operation never refines the supplied cell silently.
-/
def coordinateModel (preparation : PotentialComparison.Preparation comparison)
    (retained : Cell preparation.2.1 physicalCoordinate stage allowance nonnegative)
    (regular : PolynomialSample cap numerator regularIndex regularBox)
    (inSource : terminal.neighborhood.patch.base.box.Contains start) (inCap : collar.box.Contains start)
    (later : 2 ≤ stage) :
    InverseRootPolynomial.Model coordinate
      (coordinateModelBox terminal start inSource inCap) :=
  InverseRootPolynomial.Model.ofFactors (coordinateFactor (frame := frame) (cap := cap))
    retained.inverse regular.1.val
    (coordinateModelBox_source terminal start inSource inCap)
    (coordinateModelBox_cap terminal start inSource inCap)
    (coordinateModel_source_small preparation retained later) (coordinateModel_cap_small regular)

/-- The whole coordinate model is the original factor-model constructor on these same two actual supplied inverses. -/
private theorem packaged_coordinateModel_factory (preparation : PotentialComparison.Preparation comparison)
    (retained : Cell preparation.2.1 physicalCoordinate stage allowance nonnegative)
    (regular : PolynomialSample cap numerator regularIndex regularBox)
    (inSource : terminal.neighborhood.patch.base.box.Contains start) (inCap : collar.box.Contains start)
    (later : 2 ≤ stage) :
    coordinateModel preparation retained regular inSource inCap later =
      InverseRootPolynomial.Model.ofFactors (coordinateFactor (frame := frame) (cap := cap))
        retained.inverse regular.1.val
        (coordinateModelBox_source terminal start inSource inCap)
        (coordinateModelBox_cap terminal start inSource inCap)
        (coordinateModel_source_small preparation retained later) (coordinateModel_cap_small regular) := by rfl

/-- The whole coordinate model is the original factor-model constructor on these same two actual supplied inverses. -/
theorem coordinateModel_factory (preparation : PotentialComparison.Preparation comparison)
    (retained : Cell preparation.2.1 physicalCoordinate stage allowance nonnegative)
    (regular : PolynomialSample cap numerator regularIndex regularBox)
    (inSource : terminal.neighborhood.patch.base.box.Contains start) (inCap : collar.box.Contains start)
    (later : 2 ≤ stage) :
    coordinateModel preparation retained regular inSource inCap later =
      InverseRootPolynomial.Model.ofFactors (coordinateFactor (frame := frame) (cap := cap))
        retained.inverse regular.1.val
        (coordinateModelBox_source terminal start inSource inCap)
        (coordinateModelBox_cap terminal start inSource inCap)
        (coordinateModel_source_small preparation retained later) (coordinateModel_cap_small regular) :=
  packaged_coordinateModel_factory preparation retained regular inSource inCap later

end Preparation

variable {point : Canonical}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}

/-- Transport only the exact parameter index of the retained attached operational t owner. -/
def coordinateOwner (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) : Owner (coordinate.eval point) := by
  have actual : point ^ HyperellipticReciprocal.originOrder (Fibre.frameCurve frame) = coordinate.eval point := by
    rewrite [frame_originOrder frame, pow_one, coordinate_eval]
    rfl
  exact actual ▸ overlap.attached.owner

/-- Construct an original w inverse-root neighborhood from the SAME retained operational t owner.

The new observation site and seed alignment perform actual new preparation
and root-reading work. The complete original winding owner is retained;
its sheet is not independently chosen. The returned positive neighborhood
has its own literal box, so coverage of a requested whole physical segment
must subsequently be checked or subdivided.
-/
def coordinateSource (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    (owner : Owner (coordinate.eval point)) ×
    { patch : ContinuedInverseRoot.ContinuedNeighborhood coordinate count //
      patch = ContinuedInverseRoot.ContinuedNeighborhood.ofOwner
        (ObservationNeighborhood.ofPoint coordinate count point owner.parameterNonzero) owner } :=
  let owner := coordinateOwner overlap
  let site := ObservationNeighborhood.ofPoint coordinate count point owner.parameterNonzero
  let patch := ContinuedInverseRoot.ContinuedNeighborhood.ofOwner site owner
  ⟨owner, ⟨patch, rfl⟩⟩

/-- The whole w-source factory retains the original t owner, its actual observation site and one new alignment. -/
private theorem packaged_coordinateSource_factory
    (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    coordinateSource overlap count =
      (let owner := coordinateOwner overlap
       let site := ObservationNeighborhood.ofPoint coordinate count point owner.parameterNonzero
       let patch := ContinuedInverseRoot.ContinuedNeighborhood.ofOwner site owner
       ⟨owner, ⟨patch, rfl⟩⟩ :
        (owner : Owner (coordinate.eval point)) ×
        { patch : ContinuedInverseRoot.ContinuedNeighborhood coordinate count //
          patch = ContinuedInverseRoot.ContinuedNeighborhood.ofOwner
            (ObservationNeighborhood.ofPoint coordinate count point owner.parameterNonzero) owner }) := by rfl

/-- The whole w-source factory retains the original t owner, its actual observation site and one new alignment. -/
theorem coordinateSource_factory (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    coordinateSource overlap count =
      (let owner := coordinateOwner overlap
       let site := ObservationNeighborhood.ofPoint coordinate count point owner.parameterNonzero
       let patch := ContinuedInverseRoot.ContinuedNeighborhood.ofOwner site owner
       ⟨owner, ⟨patch, rfl⟩⟩ :
        (owner : Owner (coordinate.eval point)) ×
        { patch : ContinuedInverseRoot.ContinuedNeighborhood coordinate count //
          patch = ContinuedInverseRoot.ContinuedNeighborhood.ofOwner
            (ObservationNeighborhood.ofPoint coordinate count point owner.parameterNonzero) owner }) :=
  packaged_coordinateSource_factory overlap count

/-- Parameter-index transport preserves the complete original root owner as a heterogeneous equality. -/
private theorem owner_index_heq {source target : Canonical} (equal : source = target) (owner : Owner source) :
    HEq (equal ▸ owner) owner := by
  cases equal
  rfl

/-- The retained coordinate owner is the original attached t owner with only its proven parameter index changed. -/
private theorem packaged_coordinateOwner_original (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) :
    HEq (coordinateOwner overlap) overlap.attached.owner := by
  unfold coordinateOwner
  apply owner_index_heq

/-- The retained coordinate owner is the original attached t owner with only its proven parameter index changed. -/
theorem coordinateOwner_original (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) :
    HEq (coordinateOwner overlap) overlap.attached.owner := packaged_coordinateOwner_original overlap

/-- The original coordinate-source factory retains its exact supplied owner cache. -/
private theorem packaged_coordinateSource_owner
    (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    (coordinateSource overlap count).1 = coordinateOwner overlap := by rfl

/-- The original coordinate-source factory retains its exact supplied owner cache. -/
theorem coordinateSource_owner (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    (coordinateSource overlap count).1 = coordinateOwner overlap := packaged_coordinateSource_owner overlap count

/-- The new observation and continuation source remains centered at the original supplied overlap coordinate. -/
private theorem packaged_coordinateSource_center
    (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    (coordinateSource overlap count).2.val.base.site.center = point := by rfl

/-- The new observation and continuation source remains centered at the original supplied overlap coordinate. -/
theorem coordinateSource_center (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    (coordinateSource overlap count).2.val.base.site.center = point := packaged_coordinateSource_center overlap count

/-- The complete continuation origin is the same retained t owner at its original point, with no owner replacement. -/
private theorem packaged_coordinateSource_origin
    (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    HEq (coordinateSource overlap count).2.val.origin (coordinateSource overlap count).1 := by rfl

/-- The complete continuation origin is the same retained t owner at its original point, with no owner replacement. -/
theorem coordinateSource_origin (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) (count : Nat) :
    HEq (coordinateSource overlap count).2.val.origin (coordinateSource overlap count).1 :=
  packaged_coordinateSource_origin overlap count

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

end

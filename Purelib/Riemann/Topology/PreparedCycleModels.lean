module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.Constant
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Compatible
public import Purelib.Integration.Program.Gaussian.Sequential
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
public import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily
public import Purelib.Data.Task.Parallel
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Data.List.Append
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Prepared finite models for lifted hyperelliptic cycles

Prepared clear paths already carry uniform algebraic certificates on a fixed
sheet.  This module concatenates those finite pieces with exact stationary
switch cells.  Owner-boundary cycles keep their winding-one boundary paths
explicit before each switch, so a sheet transition is never represented by
an unrelated nonbranch shortcut.
-/

namespace Purelib.Riemann.Topology.PreparedCycleModels

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Geometry.Path.Gaussian
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Approximation.Gaussian
open Purelib.RootIsolation
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Periods

set_option backward.match.sparseCases false

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

/-- The canonical Gaussian rational carrier of the original cycle models. -/
abbrev Gaussian := Basic.Canonical
/-- The rational coordinate carrier of the retained cycle schedules and allowances. -/
abbrev Coordinate := Fraction.Rational
/-- The rational rectangle carrier of the original clear-path ambient regions. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root continuation owner at its exact polynomial parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original certified polynomial cell model used by the retained lifted paths. -/
abbrev CellModel := Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel
/-- The original ordered polynomial path model of the retained cycle cells. -/
abbrev PathModel := Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
/-- The original wedge chart indexed by the same curve and ordered differential pair. -/
abbrev WedgeChart {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedSubdivisionModelCore.WedgeChart curve leftDifferential
    rightDifferential
/-- The original executable Gaussian integral refinement program. -/
abbrev RefinementProgram :=
  Purelib.Integration.Program.Gaussian.Basic.RefinementProgram
/-- The original compatibility certificate between exact constant-cell path models. -/
abbrev CompatibleConstantPathRefinement :=
  Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel.CompatibleConstantPathRefinement
/-- The original prepared clear path retaining its starting square-root owner. -/
abbrev PreparedPath
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) :=
  Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath path owner
/-- The original checked dyadic path bank at its retained depth and positive root diameter. -/
abbrev DyadicBank
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) :=
  Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank depth
    rootDiameter rootDiameterPositive path owner

set_option genInjectivity false in
/-- Original polynomial cells certified along one exact lifted path.

The uniform differential certificates retain the same curve, differential, ordered cells and lifted endpoints, so
geometric and integral readbacks share those exact owners. -/
structure CertifiedLift {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (path : Lifted.Basic.LiftedPath 2 start finish) where
  /-- The ordered polynomial cell models for this exact lifted path. -/ cells : List CellModel
  /-- A differential integral certificate for each retained cell at its original position. -/ certificates :
    Algebraic.Path.Basis.UniformPathCertificates curve differential cells path

constructive_injectivity CertifiedLift

/-- The original one-cell stationary path changing to the other sheet at the same coordinate. -/
@[expose] def stationarySwitchPath (coordinate : Gaussian) (sheet : Fin 2) :
    Lifted.Basic.LiftedPath 2
      { coordinate := coordinate, sheet := sheet }
      { coordinate := coordinate, sheet := BranchCutLifts.otherSheet sheet } :=
  .cons (BranchCutLifts.switchCell coordinate sheet)
    (.nil { coordinate := coordinate, sheet := BranchCutLifts.otherSheet sheet })

/-- The exact zero wedge chart for the original stationary sheet-switch segment. -/
@[expose] def stationaryWedgeChart {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    WedgeChart curve leftDifferential rightDifferential where
  coefficient := fun _fraction _inside =>
    Name.Coherent.CoherentNamed.Coherence.exact 0
  zero := fun _fraction _inside =>
    Equivalence.NamedEquivalent.refl
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name

namespace CertifiedLift

open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Paths

/-- Append the original certified lifted paths and their ordered cell certificates. -/
@[expose] def append {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {start middle finish : Lifted.Basic.LiftedPoint 2}
    {firstPath : Lifted.Basic.LiftedPath 2 start middle}
    {secondPath : Lifted.Basic.LiftedPath 2 middle finish}
    (first : CertifiedLift curve differential firstPath)
    (second : CertifiedLift curve differential secondPath) :
    CertifiedLift curve differential (firstPath.append secondPath) where
  cells := first.cells ++ second.cells
  certificates := Algebraic.Path.Basis.UniformPathCertificates.append firstPath first.certificates
    second.certificates

/-- The integral sample of the appended original certified lifts is the sum of their exact samples. -/
@[simp] theorem append_integralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {start middle finish : Lifted.Basic.LiftedPoint 2}
    {firstPath : Lifted.Basic.LiftedPath 2 start middle}
    {secondPath : Lifted.Basic.LiftedPath 2 middle finish}
    (first : CertifiedLift curve differential firstPath)
    (second : CertifiedLift curve differential secondPath) :
    (Basic.PathModel.mk
      (first.append second).cells).integralSample =
        (Basic.PathModel.mk
          first.cells).integralSample +
          (Basic.PathModel.mk
            second.cells).integralSample := by
  exact Basic.PathModel.integralSample_mk_append
    first.cells second.cells

/-- Certify the stationary sheet switch with the original exact zero constant cell. -/
@[expose] def switch {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    (coordinate : Gaussian) (sheet : Fin 2) :
    CertifiedLift curve differential (stationarySwitchPath coordinate sheet) := by
  let model := Basic.CellModel.exact
    coordinate coordinate (Ascending.Gaussian.Basic.constant 0)
  exact
    { cells := [model]
      certificates := .cons rfl rfl (.stationary rfl) (.nil _) }

/-- The original stationary switch contributes exactly zero integral sample.

The exact stationary cell has zero displacement. Reducing its singleton sum and transporting the scalar zero identities
retains the displayed Gaussian sample. -/
@[simp] theorem switch_integralSample {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    (coordinate : Gaussian) (sheet : Fin 2) :
    (Basic.PathModel.mk
      (switch curve differential coordinate sheet).cells).integralSample = 0 := by
  unfold switch Basic.PathModel.integralSample
    Basic.CellModel.integralSample
    Basic.CellModel.displacement
    Basic.CellModel.exact
  rewrite [List.foldr_cons, List.foldr_nil, Basic.sub_self, Basic.zero_mul, Basic.zero_add]
  exact Eq.refl _

/-- Read the original prepared path's cells and uniform differential certificates on the retained sheet. -/
@[expose] def ofPreparedPath {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    CertifiedLift curve differential
      (BranchCutLifts.ClearPath.liftOnSheet sheet
        prepared.toClearPath) :=
  let certified := prepared.certify curve differential sheet
  { cells := certified.cells
    certificates := certified.certificates }

/-- The original certified prepared-path cells retain their constant-cell certificates. -/
@[expose] def ofPreparedPath_constantCells {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    Basic.PathModel.ConstantCells
      (ofPreparedPath curve differential sheet prepared).cells :=
  PreparedClearPathModels.PreparedPath.certify_constantCells
    curve differential sheet prepared

/-- The original zero stationary switch has an exact constant-cell certificate. -/
@[expose] def switch_constantCells {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus)
    (coordinate : Gaussian) (sheet : Fin 2) :
    Basic.PathModel.ConstantCells
      (switch curve differential coordinate sheet).cells :=
  .cons
    (Basic.CellModel.exactConstantCertificate
      coordinate coordinate 0)
    .nil

/-- Append the original constant-cell certificates alongside the same retained certified lifts. -/
@[expose] def append_constantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {start middle finish : Lifted.Basic.LiftedPoint 2}
    {firstPath : Lifted.Basic.LiftedPath 2 start middle}
    {secondPath : Lifted.Basic.LiftedPath 2 middle finish}
    (first : CertifiedLift curve differential firstPath)
    (second : CertifiedLift curve differential secondPath)
    (firstConstant :
      Basic.PathModel.ConstantCells first.cells)
    (secondConstant :
      Basic.PathModel.ConstantCells second.cells) :
    Basic.PathModel.ConstantCells
      (first.append second).cells :=
  Constant.PathModel.ConstantCells.append firstConstant secondConstant

/-- The original certified cell list has exactly the retained lifted path's cell count. -/
theorem cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (certified : CertifiedLift curve differential path) :
    certified.cells.length = path.cellCount :=
  Lifted.Basic.LiftedPath.followedBy_length
    (Algebraic.Path.Basis.UniformPathCertificates.toFollowedBy certified.certificates)

end CertifiedLift

set_option genInjectivity false in
/-- A closed lifted path with its exact original polynomial cells and differential certificates.

The closed geometric owner and ordered cell list remain linked by the retained uniform path certificates for the same
curve and differential. -/
structure CertifiedClosedModel {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus) where
  /-- The closed lifted path whose ordered cells are certified. -/ lifted : Lifted.Closed.ClosedLiftedPath 2
  /-- The ordered polynomial cell models for this exact lifted path. -/ cells : List CellModel
  /-- A differential integral certificate for each retained cell at its original position. -/ certificates :
    Algebraic.Path.Basis.UniformPathCertificates curve differential cells lifted.path

constructive_injectivity CertifiedClosedModel

namespace CertifiedClosedModel

/-- The original certified cell list has exactly the retained lifted path's cell count. -/
@[simp] theorem cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (model : CertifiedClosedModel curve differential) :
    model.cells.length = model.lifted.cellCount :=
  Lifted.Basic.LiftedPath.followedBy_length
    (Algebraic.Path.Basis.UniformPathCertificates.toFollowedBy model.certificates)

end CertifiedClosedModel

set_option genInjectivity false in
/-- A clear connector with retained forward and reverse dyadic root banks.

Both banks use the exact original path and its reversal, a common selected depth and positive root diameter, while
retaining their distinct endpoint root owners. -/
structure PreparedDoublePath {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The rational rectangle containing the original connector. -/ ambient : Box
  /-- The connector's exact starting parameter. -/ start : Gaussian
  /-- The connector's exact final parameter. -/ finish : Gaussian
  /-- The original polynomial-clear connector between the retained endpoints. -/ basePath :
    Polynomial.Geometry.ClearPath
    curve.polynomial ambient start finish
  /-- The common selected dyadic depth of the forward and reverse root banks. -/ depth : Nat
  /-- The requested upper bound on the retained root diameters. -/ rootDiameter : Coordinate
  /-- The retained root-diameter request is strictly positive. -/ rootDiameterPositive : 0 < rootDiameter
  /-- The square-root continuation owner at the forward path's exact starting parameter. -/ forwardOwner : Owner
    (curve.polynomial.eval start)
  /-- The checked dyadic bank for the retained forward path and starting owner. -/ forwardChecked : DyadicBank depth
    rootDiameter rootDiameterPositive
    basePath forwardOwner
  /-- The square-root continuation owner at the reverse path's exact starting parameter. -/ backwardOwner : Owner
    (curve.polynomial.eval finish)
  /-- The checked dyadic bank for the retained reverse path and starting owner. -/ backwardChecked : DyadicBank depth
    rootDiameter rootDiameterPositive
    (BranchCutLifts.ClearPath.reverse basePath) backwardOwner

constructive_injectivity PreparedDoublePath

namespace PreparedDoublePath

open Purelib.Data
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths

/-- Prepare the original connector and its reversal together at one selected dyadic depth.

Both exact endpoint owners and the positive root-diameter request feed a single adaptive task bank; the returned forward
and reverse banks retain that shared selected depth. -/
@[expose] def total {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {ambient : Box} {start finish : Gaussian}
    (basePath : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
    (within : basePath.WithinAmbient)
    (forwardOwner : Owner (curve.polynomial.eval start))
    (backwardOwner : Owner (curve.polynomial.eval finish))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    PreparedDoublePath curve := by
  let backwardPath :=
    BranchCutLifts.ClearPath.reverse basePath
  let selected := SquareRoot.Preparation.Bank.Adaptive.select
    [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath basePath within forwardOwner,
      SquareRoot.Preparation.Bank.Adaptive.Task.ofPath backwardPath
        (BranchCutLifts.ClearPath.reverse_withinAmbient basePath within) backwardOwner]
    rootDiameter rootDiameterPositive
  exact
    { ambient := ambient
      start := start
      finish := finish
      basePath := basePath
      depth := selected.depth
      rootDiameter := rootDiameter
      rootDiameterPositive := rootDiameterPositive
      forwardOwner := forwardOwner
      forwardChecked := selected.banks.head
      backwardOwner := backwardOwner
      backwardChecked := selected.banks.tail.head }

/-- Prepare the original refined branch connector using the supplied exact endpoint root owners. -/
@[expose] def ofConnectorAtWithOwners {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat)
    (forwardOwner : Owner (curve.polynomial.eval
      (Cuts.refinedTrackAnchor branches degreeGtOne left refinement)))
    (backwardOwner : Owner (curve.polynomial.eval
      (Cuts.refinedTrackAnchor branches degreeGtOne right refinement))) :
    PreparedDoublePath curve :=
  total
    (Cuts.connectorAt branches degreeGtOne left right refinement)
    (Cuts.connectorAt_withinAmbient branches degreeGtOne left right refinement)
    forwardOwner backwardOwner 1 (by decide)

/-- Prepare the original refined branch connector with executable independent endpoint owners. -/
@[expose] def ofConnectorAt {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat) : PreparedDoublePath curve :=
  let owners := Task.Parallel.two
    (fun _ => SquareRootContinuationChain.Owner.independent
      (Cuts.connectorAt_start_eval_ne_zero branches degreeGtOne left right refinement) 0)
    (fun _ => SquareRootContinuationChain.Owner.independent
      (Cuts.connectorAt_finish_eval_ne_zero branches degreeGtOne left right refinement) 1)
  total
    (Cuts.connectorAt branches degreeGtOne left right refinement)
    (Cuts.connectorAt_withinAmbient branches degreeGtOne left right refinement)
    owners.1 owners.2
    1 (by decide)

/-- The original forward checked bank certifies containment of the retained connector in its ambient box. -/
theorem within {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve) : data.basePath.WithinAmbient :=
  data.forwardChecked.within

/-- Read the original forward prepared path from its retained checked root bank. -/
@[expose] def forward {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve) :
    PreparedPath data.basePath data.forwardOwner :=
  data.forwardChecked.prepared

/-- Read the original reverse prepared path from its retained checked root bank. -/
@[expose] def backward {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve) :
    PreparedPath
      (BranchCutLifts.ClearPath.reverse data.basePath)
        data.backwardOwner :=
  data.backwardChecked.prepared

/-- Assemble the original checked pieces and stationary sheet switches into the retained closed lifted path. -/
@[expose] def closedLift {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve) : Lifted.Closed.ClosedLiftedPath 2 :=
  { basepoint := { coordinate := data.start, sheet := 0 }
    path :=
      (BranchCutLifts.ClearPath.liftOnSheet 0
        data.forward.toClearPath).append
          ((stationarySwitchPath data.finish 0).append
            ((BranchCutLifts.ClearPath.liftOnSheet 1
              data.backward.toClearPath).append
                (stationarySwitchPath data.start 1))) }

/-- Assemble the original ordered checked pieces and zero sheet switches into a certified closed differential model.

Every component keeps its retained path bank, sheet and original uniform differential certificate; the resulting cell
order matches the exact closed lift. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    CertifiedClosedModel curve differential := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let atFinish := CertifiedLift.switch curve differential data.finish 0
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let atStart := CertifiedLift.switch curve differential data.start 1
  let combined := forward.append
    (atFinish.append (backward.append atStart))
  exact
    { lifted := data.closedLift
      cells := combined.cells
      certificates := combined.certificates }

/-- The sum of the original prepared pieces' retained real integral lower bounds. -/
@[expose] def integralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus) : Coordinate :=
  data.forward.integralRealLower curve differential 0 +
    data.backward.integralRealLower curve differential 1

/-- The sum of original prepared pieces' integral lower bounds in the specified Gaussian direction. -/
@[expose] def directionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus)
    (direction : Gaussian) : Coordinate :=
  data.forward.directionalIntegralLower curve differential 0 direction +
    data.backward.directionalIntegralLower curve differential 1 direction

/-- The certified closed model's sample is exactly the ordered sum of its original moving-piece samples.

The retained moving pieces remain in their original order. Each intervening stationary switch contributes zero, so
append readbacks give the displayed ordered sum. -/
theorem certifiedModel_integralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    (Basic.PathModel.mk
      (data.certifiedModel differential).cells).integralSample =
        (Basic.PathModel.mk
          (CertifiedLift.ofPreparedPath curve differential 0
            data.forward).cells).integralSample +
          (Basic.PathModel.mk
            (CertifiedLift.ofPreparedPath curve differential 1
              data.backward).cells).integralSample := by
  unfold certifiedModel
  repeat' rewrite [CertifiedLift.append_integralSample]
  repeat' rewrite [CertifiedLift.switch_integralSample]
  repeat' first | rewrite [Basic.zero_add] | rewrite [Basic.add_zero]
  exact Eq.refl _

/-- For exponent-zero differentials, the retained real lower bound controls the original certified cycle sample. -/
theorem integralRealLower_le_certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus)
    (exponentZero : differential.exponent = 0) :
    data.integralRealLower differential <=
      (Basic.PathModel.mk
        (data.certifiedModel differential).cells).integralSample.re := by
  have forwardLower :=
    PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 0 exponentZero data.forward
  have backwardLower :=
    PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 1 exponentZero data.backward
  rw [data.certifiedModel_integralSample differential,
    Basic.add_re]
  exact add_le_add forwardLower backwardLower

/-- For exponent-zero differentials, the retained directional lower bound controls the original cycle sample projection.
-/
theorem directionalIntegralLower_le_certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    data.directionalIntegralLower differential direction <=
      direction.re *
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.re +
        direction.im *
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.im := by
  have forwardLower :=
    PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 0 direction exponentZero data.forward
  have backwardLower :=
    PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 1 direction exponentZero data.backward
  rw [data.certifiedModel_integralSample differential]
  unfold CertifiedLift.ofPreparedPath
  simp only [Basic.add_re,
    Basic.add_im]
  exact (add_le_add forwardLower backwardLower).trans_eq (by ring1)

/-- Every cell of the original assembled closed model retains its constant-cell certificate. -/
@[expose] def certifiedModel_constantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    Basic.PathModel.ConstantCells
      (data.certifiedModel differential).cells := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let atFinish := CertifiedLift.switch curve differential data.finish 0
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let atStart := CertifiedLift.switch curve differential data.start 1
  exact
    (Constant.PathModel.ConstantCells.append (CertifiedLift.ofPreparedPath_constantCells curve differential 0
      data.forward))
      ((Constant.PathModel.ConstantCells.append (CertifiedLift.switch_constantCells curve differential data.finish 0))
        ((Constant.PathModel.ConstantCells.append (CertifiedLift.ofPreparedPath_constantCells curve differential 1
          data.backward))
            (CertifiedLift.switch_constantCells curve differential data.start 1)))

/-- The ordered original moving-piece wedge charts and exact zero charts for stationary switches. -/
@[expose] def wedgeCharts {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    List (WedgeChart curve leftDifferential rightDifferential) :=
  PreparedClearPathModels.PreparedPath.wedgeCharts curve
      leftDifferential rightDifferential 0 data.forward ++
    [stationaryWedgeChart curve leftDifferential rightDifferential] ++
      PreparedClearPathModels.PreparedPath.wedgeCharts curve
          leftDifferential rightDifferential 1 data.backward ++
        [stationaryWedgeChart curve leftDifferential rightDifferential]

/-- The original certified cycle count is the sum of retained moving-piece counts and its two switches.

Appending the retained moving cell lists and singleton switch cells preserves their order. The exact finite length
readbacks determine the displayed natural count. -/
@[simp] theorem certifiedModel_cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      data.forward.stepCount + 1 + (data.backward.stepCount + 1) := by
  rw [← CertifiedClosedModel.cellCount]
  simp only [certifiedModel, CertifiedLift.append, CertifiedLift.switch,
    CertifiedLift.ofPreparedPath, Purelib.Data.List.Append.length_append, List.length_cons,
    List.length_nil, PreparedClearPathModels.PreparedPath.certify_cellCount]
  omega0

/-- The exact certified cycle count is determined by the original segment counts and retained dyadic depths. -/
theorem certifiedModel_cellCount_eq_dyadic {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      2 * (2 ^ data.depth * data.basePath.segmentCount) + 2 := by
  rw [certifiedModel_cellCount]
  simp only [forward, backward]
  rw [
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked,
    BranchCutLifts.ClearPath.segmentCount_reverse]
  omega0

/-- The retained wedge-chart list has the same length as the original certified model's cell list. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    (data.wedgeCharts leftDifferential rightDifferential).length =
      (data.certifiedModel leftDifferential).cells.length := by
  rw [CertifiedClosedModel.cellCount,
    data.certifiedModel_cellCount leftDifferential]
  simp only [wedgeCharts, Purelib.Data.List.Append.length_append, List.length_cons,
    List.length_nil,
    PreparedClearPathModels.PreparedPath.wedgeCharts_length]
  omega0

end PreparedDoublePath

set_option genInjectivity false in
/-- The original connector and two winding-one boundary paths with four retained root banks.

The forward, right-boundary, reverse and left-boundary pieces keep distinct exact owners and selected dyadic depths,
sharing the same positive requested root diameter. -/
structure PreparedBoundaryDoublePath {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The ambient rectangle for the original left boundary path. -/ leftAmbient : Box
  /-- The ambient rectangle for the original right boundary path. -/ rightAmbient : Box
  /-- The ambient rectangle for the original connecting path. -/ connectorAmbient : Box
  /-- The retained left root-isolation state and its exact box. -/ leftState : State.WindingOne.Basic.WindingOneState
    curve.polynomial leftAmbient
  /-- The retained right root-isolation state and its exact box. -/ rightState : State.WindingOne.Basic.WindingOneState
    curve.polynomial rightAmbient
  /-- The original clear path from the left box anchor to the right box anchor. -/ connector :
    Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient
    leftState.box.anchor rightState.box.anchor
  /-- The original clear boundary path based at the right box anchor. -/ rightBoundaryPath :
    Polynomial.Geometry.ClearPath curve.polynomial rightState.box
    rightState.box.anchor rightState.box.anchor
  /-- The original clear boundary path based at the left box anchor. -/ leftBoundaryPath : Polynomial.Geometry.ClearPath
    curve.polynomial leftState.box
    leftState.box.anchor leftState.box.anchor
  /-- The selected dyadic depth of the forward connector bank. -/ forwardDepth : Nat
  /-- The selected dyadic depth of the right boundary bank. -/ rightBoundaryDepth : Nat
  /-- The selected dyadic depth of the reverse connector bank. -/ backwardDepth : Nat
  /-- The selected dyadic depth of the left boundary bank. -/ leftBoundaryDepth : Nat
  /-- The requested upper bound on the retained root diameters. -/ rootDiameter : Coordinate
  /-- The retained root-diameter request is strictly positive. -/ rootDiameterPositive : 0 < rootDiameter
  /-- The square-root continuation owner at the forward path's exact starting parameter. -/ forwardOwner : Owner
    (curve.polynomial.eval leftState.box.anchor)
  /-- The checked dyadic bank for the retained forward path and starting owner. -/ forwardChecked : DyadicBank
    forwardDepth rootDiameter rootDiameterPositive
    connector forwardOwner
  /-- The square-root owner at the right boundary's exact starting parameter. -/ rightBoundaryOwner : Owner
    (curve.polynomial.eval rightState.box.anchor)
  /-- The checked dyadic bank for the retained right boundary path and owner. -/ rightBoundaryChecked : DyadicBank
    rightBoundaryDepth rootDiameter
    rootDiameterPositive
    rightBoundaryPath rightBoundaryOwner
  /-- The square-root continuation owner at the reverse path's exact starting parameter. -/ backwardOwner : Owner
    (curve.polynomial.eval rightState.box.anchor)
  /-- The checked dyadic bank for the retained reverse path and starting owner. -/ backwardChecked : DyadicBank
    backwardDepth rootDiameter rootDiameterPositive
    (BranchCutLifts.ClearPath.reverse connector) backwardOwner
  /-- The square-root owner at the left boundary's exact starting parameter. -/ leftBoundaryOwner : Owner
    (curve.polynomial.eval leftState.box.anchor)
  /-- The checked dyadic bank for the retained left boundary path and owner. -/ leftBoundaryChecked : DyadicBank
    leftBoundaryDepth rootDiameter
    rootDiameterPositive
    leftBoundaryPath leftBoundaryOwner

constructive_injectivity PreparedBoundaryDoublePath

namespace PreparedBoundaryDoublePath

open Purelib.Data
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths

/-- Prepare the original four boundary-cycle root banks with the selected execution mode.

Each connector or winding-one boundary piece keeps its own original path and root owner. The Boolean chooses parallel or
sequential execution of the same four retained finite preparations. -/
@[expose] def totalWithExecution (parallel : Bool) {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial
      leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial
      rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient
      leftState.box.anchor rightState.box.anchor)
    (connectorWithin : connector.WithinAmbient)
    (forwardOwner : Owner
      (curve.polynomial.eval leftState.box.anchor))
    (rightBoundaryOwner : Owner
      (curve.polynomial.eval rightState.box.anchor))
    (backwardOwner : Owner
      (curve.polynomial.eval rightState.box.anchor))
    (leftBoundaryOwner : Owner
      (curve.polynomial.eval leftState.box.anchor))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    PreparedBoundaryDoublePath curve := by
  let rightBoundary := BranchCutLifts.ownerBoundaryPath rightState
  let backward := BranchCutLifts.ClearPath.reverse connector
  let leftBoundary := BranchCutLifts.ownerBoundaryPath leftState
  let prepareForward := fun (_ : Unit) => SquareRoot.Preparation.Bank.Adaptive.select
    [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath connector connectorWithin forwardOwner]
    rootDiameter rootDiameterPositive
  let prepareRight := fun (_ : Unit) => SquareRoot.Preparation.Bank.Adaptive.select
    [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath rightBoundary
      (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState) rightBoundaryOwner]
    rootDiameter rootDiameterPositive
  let prepareBackward := fun (_ : Unit) => SquareRoot.Preparation.Bank.Adaptive.select
    [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath backward
      (BranchCutLifts.ClearPath.reverse_withinAmbient connector connectorWithin) backwardOwner]
    rootDiameter rootDiameterPositive
  let prepareLeft := fun (_ : Unit) => SquareRoot.Preparation.Bank.Adaptive.select
    [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath leftBoundary
      (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState) leftBoundaryOwner]
    rootDiameter rootDiameterPositive
  let selected := if parallel then
      Task.Parallel.four prepareForward prepareRight prepareBackward prepareLeft
    else (prepareForward (), prepareRight (), prepareBackward (), prepareLeft ())
  let forward := selected.1
  let right := selected.2.1
  let backwardSelected := selected.2.2.1
  let left := selected.2.2.2
  exact
    { leftAmbient := leftAmbient
      rightAmbient := rightAmbient
      connectorAmbient := connectorAmbient
      leftState := leftState
      rightState := rightState
      connector := connector
      rightBoundaryPath := rightBoundary
      leftBoundaryPath := leftBoundary
      forwardDepth := forward.depth
      rightBoundaryDepth := right.depth
      backwardDepth := backwardSelected.depth
      leftBoundaryDepth := left.depth
      rootDiameter := rootDiameter
      rootDiameterPositive := rootDiameterPositive
      forwardOwner := forwardOwner
      forwardChecked := forward.banks.head
      rightBoundaryOwner := rightBoundaryOwner
      rightBoundaryChecked := right.banks.head
      backwardOwner := backwardOwner
      backwardChecked := backwardSelected.banks.head
      leftBoundaryOwner := leftBoundaryOwner
      leftBoundaryChecked := left.banks.head }

/-- Prepare the original four boundary-cycle banks with parallel execution. -/
@[expose] def total := @totalWithExecution true

/-- Prepare the original four boundary-cycle banks with sequential execution. -/
@[expose] def sequentialTotal := @totalWithExecution false

/-- Parallel and sequential preparation of the original four retained banks are definitionally equal. -/
theorem total_eq_sequential : @total = @sequentialTotal := rfl

/-- Prepare the original refined branch connector using the supplied exact endpoint root owners. -/
@[expose] def ofConnectorAtWithOwners {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat)
    (forwardOwner : Owner (curve.polynomial.eval
      (Cuts.refinedTrackAnchor branches degreeGtOne left refinement)))
    (rightBoundaryOwner : Owner (curve.polynomial.eval
      (Cuts.refinedTrackAnchor branches degreeGtOne right refinement)))
    (backwardOwner : Owner (curve.polynomial.eval
      (Cuts.refinedTrackAnchor branches degreeGtOne right refinement)))
    (leftBoundaryOwner : Owner (curve.polynomial.eval
      (Cuts.refinedTrackAnchor branches degreeGtOne left refinement))) :
    PreparedBoundaryDoublePath curve :=
  total
    (Cuts.refinedState branches degreeGtOne left refinement)
    (Cuts.refinedState branches degreeGtOne right refinement)
    (Cuts.connectorAt branches degreeGtOne left right refinement)
    (Cuts.connectorAt_withinAmbient branches degreeGtOne left right refinement)
    forwardOwner rightBoundaryOwner backwardOwner leftBoundaryOwner
    1 (by decide)

/-- Prepare the original finite-cut connector with two cached independent root-owner families.

The exact left and right isolation results supply both sheets at their respective endpoints; the four original path
banks retain those owners and their individual selected depths. -/
@[expose] def ofConnectorAt {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat) : PreparedBoundaryDoublePath curve := by
  let leftNonzero :=
    Cuts.connectorAt_start_eval_ne_zero branches degreeGtOne left right
      refinement
  let rightNonzero :=
    Cuts.connectorAt_finish_eval_ne_zero branches degreeGtOne left right
      refinement
  let families := Task.Parallel.two
    (fun _ => SquareRootOwnerFamily.independentFamily leftNonzero)
    (fun _ => SquareRootOwnerFamily.independentFamily rightNonzero)
  exact total
    (Cuts.refinedState branches degreeGtOne left refinement)
    (Cuts.refinedState branches degreeGtOne right refinement)
    (Cuts.connectorAt branches degreeGtOne left right refinement)
    (Cuts.connectorAt_withinAmbient branches degreeGtOne left right refinement)
    (families.1.owner 0)
    (families.2.owner 0)
    (families.2.owner 1)
    (families.1.owner 1)
    1 (by decide)

/-- The original cached-family connector preparation equals the explicit sequential construction with the same four
independent owners. -/
theorem ofConnectorAt_eq_sequential {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches) (refinement : Nat) :
    ofConnectorAt branches higher left right refinement =
      sequentialTotal
        (Cuts.refinedState branches higher left refinement)
        (Cuts.refinedState branches higher right refinement)
        (Cuts.connectorAt branches higher left right refinement)
        (Cuts.connectorAt_withinAmbient branches higher left right refinement)
        (SquareRootContinuationChain.Owner.independent
          (Cuts.connectorAt_start_eval_ne_zero branches higher left right refinement) 0)
        (SquareRootContinuationChain.Owner.independent
          (Cuts.connectorAt_finish_eval_ne_zero branches higher left right refinement) 0)
        (SquareRootContinuationChain.Owner.independent
          (Cuts.connectorAt_finish_eval_ne_zero branches higher left right refinement) 1)
        (SquareRootContinuationChain.Owner.independent
          (Cuts.connectorAt_start_eval_ne_zero branches higher left right refinement) 1)
        1 (by decide) := rfl

/-- The retained forward bank certifies the original connector's ambient containment. -/
theorem connectorWithin {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    data.connector.WithinAmbient :=
  data.forwardChecked.within

/-- Read the original forward prepared path from its retained checked root bank. -/
@[expose] def forward {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath data.connector data.forwardOwner :=
  data.forwardChecked.prepared

/-- Read the original right-boundary prepared path from its exact retained checked bank. -/
@[expose] def rightBoundary {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath data.rightBoundaryPath
      data.rightBoundaryOwner :=
  data.rightBoundaryChecked.prepared

/-- Read the original reverse prepared path from its retained checked root bank. -/
@[expose] def backward {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath
      (BranchCutLifts.ClearPath.reverse data.connector)
        data.backwardOwner :=
  data.backwardChecked.prepared

/-- Read the original left-boundary prepared path from its exact retained checked bank. -/
@[expose] def leftBoundary {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath data.leftBoundaryPath data.leftBoundaryOwner :=
  data.leftBoundaryChecked.prepared

/-- Assemble the original checked pieces and stationary sheet switches into the retained closed lifted path. -/
@[expose] def closedLift {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) : Lifted.Closed.ClosedLiftedPath 2 :=
  { basepoint := { coordinate := data.leftState.box.anchor, sheet := 0 }
    path :=
      (BranchCutLifts.ClearPath.liftOnSheet 0
        data.forward.toClearPath).append
        ((BranchCutLifts.ClearPath.liftOnSheet 0
          data.rightBoundary.toClearPath).append
          ((stationarySwitchPath data.rightState.box.anchor 0).append
            ((BranchCutLifts.ClearPath.liftOnSheet 1
              data.backward.toClearPath).append
              ((BranchCutLifts.ClearPath.liftOnSheet 1
                data.leftBoundary.toClearPath).append
                  (stationarySwitchPath data.leftState.box.anchor 1))))) }

/-- Assemble the original ordered checked pieces and zero sheet switches into a certified closed differential model.

Every component keeps its retained path bank, sheet and original uniform differential certificate; the resulting cell
order matches the exact closed lift. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    CertifiedClosedModel curve differential := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let rightBoundary :=
    CertifiedLift.ofPreparedPath curve differential 0 data.rightBoundary
  let rightSwitch := CertifiedLift.switch curve differential
    data.rightState.box.anchor 0
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let leftBoundary :=
    CertifiedLift.ofPreparedPath curve differential 1 data.leftBoundary
  let leftSwitch := CertifiedLift.switch curve differential
    data.leftState.box.anchor 1
  let combined := forward.append
    (rightBoundary.append (rightSwitch.append
      (backward.append (leftBoundary.append leftSwitch))))
  exact
    { lifted := data.closedLift
      cells := combined.cells
      certificates := combined.certificates }

/-- The sum of the original prepared pieces' retained real integral lower bounds. -/
@[expose] def integralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus) : Coordinate :=
  data.forward.integralRealLower curve differential 0 +
    (data.rightBoundary.integralRealLower curve differential 0 +
      (data.backward.integralRealLower curve differential 1 +
        data.leftBoundary.integralRealLower curve differential 1))

/-- The sum of original prepared pieces' integral lower bounds in the specified Gaussian direction. -/
@[expose] def directionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus)
    (direction : Gaussian) : Coordinate :=
  data.forward.directionalIntegralLower curve differential 0 direction +
    (data.rightBoundary.directionalIntegralLower curve differential 0 direction +
      (data.backward.directionalIntegralLower curve differential 1 direction +
        data.leftBoundary.directionalIntegralLower curve differential 1
          direction))

/-- The certified closed model's sample is exactly the ordered sum of its original moving-piece samples.

The retained moving pieces remain in their original order. Each intervening stationary switch contributes zero, so
append readbacks give the displayed ordered sum. -/
theorem certifiedModel_integralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    (Basic.PathModel.mk
      (data.certifiedModel differential).cells).integralSample =
        (Basic.PathModel.mk
          (CertifiedLift.ofPreparedPath curve differential 0
            data.forward).cells).integralSample +
          ((Basic.PathModel.mk
            (CertifiedLift.ofPreparedPath curve differential 0
              data.rightBoundary).cells).integralSample +
            ((Basic.PathModel.mk
              (CertifiedLift.ofPreparedPath curve differential 1
                data.backward).cells).integralSample +
              (Basic.PathModel.mk
                (CertifiedLift.ofPreparedPath curve differential 1
                  data.leftBoundary).cells).integralSample)) := by
  unfold certifiedModel
  repeat' rewrite [CertifiedLift.append_integralSample]
  repeat' rewrite [CertifiedLift.switch_integralSample]
  repeat' first | rewrite [Basic.zero_add] | rewrite [Basic.add_zero]
  exact Eq.refl _

/-- For exponent-zero differentials, the retained real lower bound controls the original certified cycle sample. -/
theorem integralRealLower_le_certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus)
    (exponentZero : differential.exponent = 0) :
    data.integralRealLower differential <=
      (Basic.PathModel.mk
        (data.certifiedModel differential).cells).integralSample.re := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let rightBoundary :=
    CertifiedLift.ofPreparedPath curve differential 0 data.rightBoundary
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let leftBoundary :=
    CertifiedLift.ofPreparedPath curve differential 1 data.leftBoundary
  have forwardLower :
      data.forward.integralRealLower curve differential 0 <=
        (Basic.PathModel.mk
          forward.cells).integralSample.re :=
    PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 0 exponentZero data.forward
  have rightLower :
      data.rightBoundary.integralRealLower curve differential 0 <=
        (Basic.PathModel.mk
          rightBoundary.cells).integralSample.re :=
    PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 0 exponentZero data.rightBoundary
  have backwardLower :
      data.backward.integralRealLower curve differential 1 <=
        (Basic.PathModel.mk
          backward.cells).integralSample.re :=
    PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 1 exponentZero data.backward
  have leftLower :
      data.leftBoundary.integralRealLower curve differential 1 <=
        (Basic.PathModel.mk
          leftBoundary.cells).integralSample.re :=
    PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 1 exponentZero data.leftBoundary
  have componentLower := add_le_add forwardLower
    (add_le_add rightLower (add_le_add backwardLower leftLower))
  rw [data.certifiedModel_integralSample differential]
  simp only [Basic.add_re]
  exact componentLower

/-- For exponent-zero differentials, the retained directional lower bound controls the original cycle sample projection.
-/
theorem directionalIntegralLower_le_certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    data.directionalIntegralLower differential direction <=
      direction.re *
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.re +
        direction.im *
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.im := by
  have forwardLower :=
    PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 0 direction exponentZero data.forward
  have rightLower :=
    PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 0 direction exponentZero data.rightBoundary
  have backwardLower :=
    PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 1 direction exponentZero data.backward
  have leftLower :=
    PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 1 direction exponentZero data.leftBoundary
  have componentLower := add_le_add forwardLower
    (add_le_add rightLower (add_le_add backwardLower leftLower))
  rw [data.certifiedModel_integralSample differential]
  unfold CertifiedLift.ofPreparedPath
  simp only [Basic.add_re,
    Basic.add_im]
  exact componentLower.trans_eq (by ring1)

/-- Every cell of the original assembled closed model retains its constant-cell certificate. -/
@[expose] def certifiedModel_constantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    Basic.PathModel.ConstantCells
      (data.certifiedModel differential).cells := by
  exact
    (Constant.PathModel.ConstantCells.append (CertifiedLift.ofPreparedPath_constantCells curve differential 0
      data.forward))
      ((Constant.PathModel.ConstantCells.append (CertifiedLift.ofPreparedPath_constantCells curve differential 0
        data.rightBoundary))
        ((Constant.PathModel.ConstantCells.append (CertifiedLift.switch_constantCells curve differential
          data.rightState.box.anchor 0))
          ((Constant.PathModel.ConstantCells.append (CertifiedLift.ofPreparedPath_constantCells curve differential 1
            data.backward))
            ((Constant.PathModel.ConstantCells.append (CertifiedLift.ofPreparedPath_constantCells curve differential 1
              data.leftBoundary))
              (CertifiedLift.switch_constantCells curve differential
                data.leftState.box.anchor 1)))))

/-- The ordered original moving-piece wedge charts and exact zero charts for stationary switches. -/
@[expose] def wedgeCharts {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    List (WedgeChart curve leftDifferential rightDifferential) :=
  PreparedClearPathModels.PreparedPath.wedgeCharts curve
      leftDifferential rightDifferential 0 data.forward ++
    PreparedClearPathModels.PreparedPath.wedgeCharts curve
        leftDifferential rightDifferential 0 data.rightBoundary ++
      [stationaryWedgeChart curve leftDifferential rightDifferential] ++
        PreparedClearPathModels.PreparedPath.wedgeCharts curve
            leftDifferential rightDifferential 1 data.backward ++
          PreparedClearPathModels.PreparedPath.wedgeCharts curve
              leftDifferential rightDifferential 1 data.leftBoundary ++
            [stationaryWedgeChart curve leftDifferential rightDifferential]

/-- The original certified cycle count is the sum of retained moving-piece counts and its two switches.

Appending the retained moving cell lists and singleton switch cells preserves their order. The exact finite length
readbacks determine the displayed natural count. -/
@[simp] theorem certifiedModel_cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      data.forward.stepCount +
        (data.rightBoundary.stepCount + 1 +
          (data.backward.stepCount +
            (data.leftBoundary.stepCount + 1))) := by
  rw [← CertifiedClosedModel.cellCount]
  simp only [certifiedModel, CertifiedLift.append, CertifiedLift.switch,
    CertifiedLift.ofPreparedPath, Purelib.Data.List.Append.length_append, List.length_cons,
    List.length_nil, PreparedClearPathModels.PreparedPath.certify_cellCount]
  omega0

/-- The exact certified cycle count is determined by the original segment counts and retained dyadic depths. -/
theorem certifiedModel_cellCount_eq_dyadic {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differentials.Basic.Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      2 ^ data.forwardDepth * data.connector.segmentCount +
        2 ^ data.rightBoundaryDepth *
            data.rightBoundaryPath.segmentCount +
          2 ^ data.backwardDepth * data.connector.segmentCount +
            2 ^ data.leftBoundaryDepth *
                data.leftBoundaryPath.segmentCount + 2 := by
  rw [certifiedModel_cellCount]
  simp only [forward, rightBoundary, backward, leftBoundary]
  rw [
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.rightBoundaryChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.leftBoundaryChecked,
    BranchCutLifts.ClearPath.segmentCount_reverse]
  omega0

/-- The retained wedge-chart list has the same length as the original certified model's cell list. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    (data.wedgeCharts leftDifferential rightDifferential).length =
      (data.certifiedModel leftDifferential).cells.length := by
  rw [CertifiedClosedModel.cellCount,
    data.certifiedModel_cellCount leftDifferential]
  simp only [wedgeCharts, Purelib.Data.List.Append.length_append, List.length_cons,
    List.length_nil,
    PreparedClearPathModels.PreparedPath.wedgeCharts_length]
  omega0

end PreparedBoundaryDoublePath

set_option genInjectivity false in
/-- An original prepared bridge cycle or finite-cut boundary cycle.

Each alternative retains its complete checked path data, root owners and geometric construction, keeping the two kinds
of cycle realization explicit. -/
inductive PreparedCycleData {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) : Type
  /-- A prepared double path with stationary sheet switches at its two endpoints. -/ | bridge (data : PreparedDoublePath
    curve)
  /-- A prepared connector cycle with both retained owner-boundary paths. -/ | finiteCut (data :
    PreparedBoundaryDoublePath curve)

constructive_injectivity PreparedCycleData

namespace PreparedCycleData

open Purelib.Riemann.Paths

/-- Assemble the original checked pieces and stationary sheet switches into the retained closed lifted path. -/
@[expose] def closedLift {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} :
    PreparedCycleData curve -> Lifted.Closed.ClosedLiftedPath 2
  | .bridge data => data.closedLift
  | .finiteCut data => data.closedLift

/-- Assemble the original ordered checked pieces and zero sheet switches into a certified closed differential model.

Every component keeps its retained path bank, sheet and original uniform differential certificate; the resulting cell
order matches the exact closed lift. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus) :
    (data : PreparedCycleData curve) -> CertifiedClosedModel curve differential
  | .bridge data => data.certifiedModel differential
  | .finiteCut data => data.certifiedModel differential

/-- The sum of the original prepared pieces' retained real integral lower bounds. -/
@[expose] def integralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus) :
    PreparedCycleData curve -> Coordinate
  | .bridge data => data.integralRealLower differential
  | .finiteCut data => data.integralRealLower differential

/-- The sum of original prepared pieces' integral lower bounds in the specified Gaussian direction. -/
@[expose] def directionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian) :
    PreparedCycleData curve -> Coordinate
  | .bridge data => data.directionalIntegralLower differential direction
  | .finiteCut data => data.directionalIntegralLower differential direction

/-- For exponent-zero differentials, the retained real lower bound controls the original certified cycle sample. -/
theorem integralRealLower_le_certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differentials.Basic.Differential genus)
    (exponentZero : differential.exponent = 0) :
    data.integralRealLower differential <=
      (Basic.PathModel.mk
        (data.certifiedModel differential).cells).integralSample.re := by
  cases data with
  | bridge bridge =>
      exact bridge.integralRealLower_le_certifiedModel differential exponentZero
  | finiteCut finiteCut =>
      exact finiteCut.integralRealLower_le_certifiedModel differential
        exponentZero

/-- For exponent-zero differentials, the retained directional lower bound controls the original cycle sample projection.
-/
theorem directionalIntegralLower_le_certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differentials.Basic.Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    data.directionalIntegralLower differential direction <=
      direction.re *
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.re +
        direction.im *
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.im := by
  cases data with
  | bridge bridge =>
      exact bridge.directionalIntegralLower_le_certifiedModel differential
        direction exponentZero
  | finiteCut finiteCut =>
      exact finiteCut.directionalIntegralLower_le_certifiedModel differential
        direction exponentZero

/-- A positive original directional lower bound squares below direction norm times cycle-sample norm. -/
theorem directionalIntegralLower_sq_le_normSq_mul {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differentials.Basic.Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0)
    (positive : 0 < data.directionalIntegralLower differential direction) :
    data.directionalIntegralLower differential direction ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq direction *
        Data.Gaussian.Norm.Basic.normSq
          (Basic.PathModel.mk
            (data.certifiedModel differential).cells).integralSample := by
  let sample :=
    (Basic.PathModel.mk
      (data.certifiedModel differential).cells).integralSample
  let dot := direction.re * sample.re + direction.im * sample.im
  have lowerLe :
      data.directionalIntegralLower differential direction <= dot :=
    data.directionalIntegralLower_le_certifiedModel differential direction
      exponentZero
  have lowerSqLe :
      data.directionalIntegralLower differential direction ^ 2 <= dot ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct positive.le lowerLe 2
  have dotSqLe : dot ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq direction *
        Data.Gaussian.Norm.Basic.normSq sample := by
    exact Norm.Bounds.projection_sq_le_normSq_mul
      direction sample
  exact lowerSqLe.trans dotSqLe

/-- The ordered original moving-piece wedge charts and exact zero charts for stationary switches. -/
@[expose] def wedgeCharts {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    (data : PreparedCycleData curve) ->
      List (WedgeChart curve leftDifferential rightDifferential)
  | .bridge data => data.wedgeCharts leftDifferential rightDifferential
  | .finiteCut data => data.wedgeCharts leftDifferential rightDifferential

/-- The retained wedge-chart list has the same length as the original certified model's cell list. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    (data.wedgeCharts leftDifferential rightDifferential).length =
      (data.certifiedModel leftDifferential).cells.length := by
  cases data with
  | bridge bridge => exact bridge.wedgeCharts_length _ _
  | finiteCut finiteCut => exact finiteCut.wedgeCharts_length _ _

set_option genInjectivity false in
/-- The two original differential cycle models with their common ordered wedge-chart list.

The retained length equalities bind the same chart list separately to each exact model's cell list; the original curve
and differential order are preserved. -/
structure HolomorphicCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) where
  /-- The certified closed model for the left differential on this cycle. -/ leftModel : CertifiedClosedModel curve
    leftDifferential
  /-- The certified closed model for the right differential on this cycle. -/ rightModel : CertifiedClosedModel curve
    rightDifferential
  /-- The ordered wedge charts for the retained pair of differentials. -/ charts : List (WedgeChart curve
    leftDifferential rightDifferential)
  /-- The chart list has one entry for each cell of the left certified model. -/ charts_match_left : charts.length =
    leftModel.cells.length
  /-- The chart list has one entry for each cell of the right certified model. -/ charts_match_right : charts.length =
    rightModel.cells.length

constructive_injectivity HolomorphicCertificate

/-- Retain both original differential models and their exact common wedge charts with matching lengths. -/
@[expose] def holomorphicCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :
    HolomorphicCertificate data leftDifferential rightDifferential where
  leftModel := data.certifiedModel leftDifferential
  rightModel := data.certifiedModel rightDifferential
  charts := data.wedgeCharts leftDifferential rightDifferential
  charts_match_left := data.wedgeCharts_length _ _
  charts_match_right := by
    calc
      (data.wedgeCharts leftDifferential rightDifferential).length =
          (data.certifiedModel leftDifferential).cells.length :=
        data.wedgeCharts_length _ _
      _ = data.closedLift.cellCount := by
        rw [CertifiedClosedModel.cellCount]
        cases data <;> rfl
      _ = (data.certifiedModel rightDifferential).cells.length := by
        rw [CertifiedClosedModel.cellCount]
        cases data <;> rfl

/-- Read the exact original certified cycle cell list as a polynomial path model. -/
@[expose] def pathModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus)
    (data : PreparedCycleData curve) : PathModel :=
  ⟨(data.certifiedModel differential).cells⟩

/-- The original cycle path model retains the same constant-cell certificates. -/
@[expose] def pathModel_constantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus)
    (data : PreparedCycleData curve) :
    Basic.PathModel.ConstantCells
      (data.pathModel differential).cells := by
  cases data with
  | bridge bridge => exact bridge.certifiedModel_constantCells differential
  | finiteCut finiteCut =>
      exact finiteCut.certifiedModel_constantCells differential

/-- The cycle path model contains exactly the original certified model's cells. -/
@[simp] theorem pathModel_cells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (differential : Differentials.Basic.Differential genus)
    (data : PreparedCycleData curve) :
    (data.pathModel differential).cells =
      (data.certifiedModel differential).cells := rfl

/-- The original certified model keeps the exact prepared cycle's closed lift. -/
@[simp] theorem certifiedModel_lifted {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differentials.Basic.Differential genus) :
    (data.certifiedModel differential).lifted = data.closedLift := by
  cases data <;> rfl

/-- An explicit original prepared-cycle realization of a retained raw closed lift.

Its constructors retain bridge or finite-cut owners, with exact original paths and any uniform or scheduled
dyadic-refinement equations; geometric realization is kept separate from integral comparison. -/
inductive RealizesRaw {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} :
    (data : PreparedCycleData curve) -> Lifted.Closed.ClosedLiftedPath 2 -> Prop
  /-- A prepared double path with stationary sheet switches at its two endpoints. -/ | bridge (data : PreparedDoublePath
    curve) :
      RealizesRaw (.bridge data)
        (BranchCutLifts.doubleLift data.basePath)
  /-- A prepared connector cycle with both retained owner-boundary paths. -/ | finiteCut (data :
    PreparedBoundaryDoublePath curve)
      (_rightBoundary : data.rightBoundaryPath = BranchCutLifts.ownerBoundaryPath data.rightState)
      (_leftBoundary : data.leftBoundaryPath = BranchCutLifts.ownerBoundaryPath data.leftState) :
      RealizesRaw (.finiteCut data)
        (BranchCutLifts.doubleLiftWithBoundaryOwners
          data.leftState data.rightState data.connector)
  /-- An exact uniform dyadic refinement of the retained raw bridge path. -/ | bridgeDyadic (data : PreparedDoublePath
    curve)
      (rawPath : Polynomial.Geometry.ClearPath curve.polynomial data.ambient data.start data.finish)
      (rawWithin : rawPath.WithinAmbient) (outerDepth : Nat)
      (_refined : data.basePath =
        PreparedClearPathModels.dyadicRefinePath rawPath rawWithin
          outerDepth) :
      RealizesRaw (.bridge data)
        (BranchCutLifts.doubleLift rawPath)
  /-- An exact dyadic refinement of the raw bridge with a retained per-segment depth list. -/ | bridgeDyadicScheduled
    (data : PreparedDoublePath curve)
      (rawPath : Polynomial.Geometry.ClearPath curve.polynomial data.ambient data.start data.finish)
      (rawWithin : rawPath.WithinAmbient) (outerDepths : List Nat)
      (_refined : data.basePath =
        PreparedClearPathModels.dyadicRefinePathScheduled rawPath
          rawWithin outerDepths) :
      RealizesRaw (.bridge data)
        (BranchCutLifts.doubleLift rawPath)
  /-- Exact uniform dyadic refinements of the raw connector and both original owner-boundary paths. -/ | finiteCutDyadic
    (data : PreparedBoundaryDoublePath curve)
      (rawConnector : Polynomial.Geometry.ClearPath curve.polynomial data.connectorAmbient
        data.leftState.box.anchor data.rightState.box.anchor)
      (rawWithin : rawConnector.WithinAmbient) (outerDepth : Nat)
      (_refined : data.connector =
        PreparedClearPathModels.dyadicRefinePath rawConnector
          rawWithin outerDepth)
      (rightRawWithin : (BranchCutLifts.ownerBoundaryPath data.rightState).WithinAmbient)
      (rightOuterDepth : Nat)
      (_rightRefined : data.rightBoundaryPath =
        PreparedClearPathModels.dyadicRefinePath
          (BranchCutLifts.ownerBoundaryPath data.rightState) rightRawWithin rightOuterDepth)
      (leftRawWithin : (BranchCutLifts.ownerBoundaryPath data.leftState).WithinAmbient)
      (leftOuterDepth : Nat)
      (_leftRefined : data.leftBoundaryPath =
        PreparedClearPathModels.dyadicRefinePath
          (BranchCutLifts.ownerBoundaryPath data.leftState) leftRawWithin leftOuterDepth) :
      RealizesRaw (.finiteCut data)
        (BranchCutLifts.doubleLiftWithBoundaryOwners
          data.leftState data.rightState rawConnector)
  /-- Exact independently scheduled dyadic refinements of the connector and both original owner-boundary paths. -/ |
    finiteCutDyadicScheduled (data : PreparedBoundaryDoublePath curve)
      (rawConnector : Polynomial.Geometry.ClearPath curve.polynomial data.connectorAmbient
        data.leftState.box.anchor data.rightState.box.anchor)
      (rawWithin : rawConnector.WithinAmbient) (connectorDepths : List Nat)
      (_refined : data.connector =
        PreparedClearPathModels.dyadicRefinePathScheduled
          rawConnector rawWithin connectorDepths)
      (rightRawWithin : (BranchCutLifts.ownerBoundaryPath data.rightState).WithinAmbient)
      (rightDepths : List Nat)
      (_rightRefined : data.rightBoundaryPath =
        PreparedClearPathModels.dyadicRefinePathScheduled
          (BranchCutLifts.ownerBoundaryPath data.rightState) rightRawWithin rightDepths)
      (leftRawWithin : (BranchCutLifts.ownerBoundaryPath data.leftState).WithinAmbient)
      (leftDepths : List Nat)
      (_leftRefined : data.leftBoundaryPath =
        PreparedClearPathModels.dyadicRefinePathScheduled
          (BranchCutLifts.ownerBoundaryPath data.leftState) leftRawWithin leftDepths) :
      RealizesRaw (.finiteCut data)
        (BranchCutLifts.doubleLiftWithBoundaryOwners
          data.leftState data.rightState rawConnector)

namespace RealizesRaw

/-- The original raw bridge lift has twice its connector segment count plus two switches. -/
theorem bridge_raw_cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedDoublePath curve) :
    (BranchCutLifts.doubleLift data.basePath).cellCount =
      2 * data.basePath.segmentCount + 2 :=
  BranchCutLifts.doubleLift_cellCount data.basePath

/-- The original raw finite-cut lift has twice its connector segment count plus eight boundary and switch cells. -/
theorem cut_raw_cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    (BranchCutLifts.doubleLiftWithBoundaryOwners
        data.leftState data.rightState data.connector).cellCount =
      2 * data.connector.segmentCount + 8 :=
  BranchCutLifts.doubleLiftWithBoundaryOwners_cellCount
    data.leftState data.rightState data.connector

end RealizesRaw

end PreparedCycleData

set_option genInjectivity false in
/-- The indexed family of original prepared cycle data.

Each natural stage retains a complete original geometric cycle owner, from which its exact closed lift is read. -/
structure CycleSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The prepared cycle data retained at every natural-number stage. -/ data : Nat -> PreparedCycleData curve

constructive_injectivity CycleSchedule

namespace CycleSchedule

/-- Read the exact original closed lifted path at every retained schedule stage. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : CycleSchedule curve) : Lifted.Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun index => (schedule.data index).closedLift

/-- Stagewise explicit realization of the exact original raw cycle family.

Each retained witness binds the same prepared schedule to its original raw lift at that index, preserving the geometric
cycle owners. -/
structure Realizes {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (schedule : CycleSchedule curve)
    (raw : Lifted.Refinement.LiftedCycleRefinement 2) where
  /-- Every prepared stage explicitly realizes the same retained raw closed lifted path. -/ refinement : forall index,
    PreparedCycleData.RealizesRaw (schedule.data index) (raw.liftedPath index)

end CycleSchedule

set_option genInjectivity false in
/-- Original certified closed differential models with a matching executable integral program.

The stagewise cell equalities bind each program model to its exact retained certified cell list, preserving the closed
lifted geometry and differential certificates. -/
structure Schedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus) where
  /-- The certified closed model retained at each refinement stage. -/ model : Nat -> CertifiedClosedModel curve
    differential
  /-- The finite integral refinement program associated with these exact geometric models. -/ integral :
    RefinementProgram
  /-- Each integral model uses exactly the cells of the corresponding retained certified model. -/ cells_eq : forall
    index, (integral.model index).cells = (model index).cells

constructive_injectivity Schedule

namespace Schedule

/-- Read the exact original closed lifted path at every retained schedule stage. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : Schedule curve differential) : Lifted.Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun index => (schedule.model index).lifted

/-- Expose the retained integral program with the original differential certificates transported along its exact cell
identities. -/
@[expose] def toCertifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : Schedule curve differential) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve differential schedule.cycle where
  integral := schedule.integral
  certificates := by
    intro index
    rw [schedule.cells_eq index]
    exact (schedule.model index).certificates

/-- The integral program's original cell count equals its retained lifted cycle count at every stage. -/
@[simp] theorem refinement_cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (schedule : Schedule curve differential) (index : Nat) :
    (schedule.integral.model index).cells.length =
      (schedule.cycle.liftedPath index).cellCount :=
  schedule.toCertifiedPeriodProgram.refinement_cellCount index

end Schedule

set_option genInjectivity false in
/-- An integral refinement program on one exact original geometric cycle schedule.

The stagewise equations identify its cells with the same prepared cycle's certified model for the retained differential.
-/
structure DifferentialSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differentials.Basic.Differential genus) where
  /-- The finite integral refinement program associated with these exact geometric models. -/ integral :
    RefinementProgram
  /-- Each integral model uses exactly the cells of the corresponding retained certified model. -/ cells_eq : forall
    index, (integral.model index).cells =
    ((geometry.data index).certifiedModel differential).cells

constructive_injectivity DifferentialSchedule

namespace DifferentialSchedule

/-- Expose the retained integral program with the original differential certificates transported along its exact cell
identities. -/
@[expose] def toCertifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (schedule : DifferentialSchedule curve geometry differential) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve differential geometry.cycle where
  integral := schedule.integral
  certificates := by
    intro index
    rw [schedule.cells_eq index]
    let certificates :=
      ((geometry.data index).certifiedModel differential).certificates
    have liftedEqual := PreparedCycleData.certifiedModel_lifted
      (geometry.data index) differential
    rw [liftedEqual] at certificates
    exact certificates

/-- The integral program's original cell count equals its retained lifted cycle count at every stage. -/
@[simp] theorem refinement_cellCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (schedule : DifferentialSchedule curve geometry differential)
    (index : Nat) :
    (schedule.integral.model index).cells.length =
      (geometry.cycle.liftedPath index).cellCount :=
  schedule.toCertifiedPeriodProgram.refinement_cellCount index

end DifferentialSchedule

set_option genInjectivity false in
/-- Original consecutive constant-cell refinements with paid geometric step allowances.

The record retains every exact stage-to-next-stage certificate, its nonnegative scale, the original initial allowance
and the quarter-decaying comparison payment. -/
structure SequentialCompatibleDifferentialCore {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differentials.Basic.Differential genus) where
  /-- A compatible constant-cell refinement from each stage to its immediate successor. -/ steps : forall index,
    CompatibleConstantPathRefinement
      ((geometry.data index).pathModel differential).cells
      ((geometry.data (index + 1)).pathModel differential).cells
  /-- The rational scale controlling consecutive comparison allowances. -/ stepScale : Coordinate
  /-- The consecutive comparison scale is nonnegative. -/ stepScale_nonnegative : 0 <= stepScale
  /-- The initial model allowance is bounded by four times the consecutive comparison scale. -/ initialAllowance_le :
    ((geometry.data 0).pathModel differential).aggregateAllowance <=
      4 * stepScale
  /-- The retained comparison allowance satisfies its stated geometric radius bound at the earlier stage. -/
    comparisonAllowance_le : forall index,
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (steps index)) <=
      Geometric.Basic.quarterRadius stepScale index

constructive_injectivity SequentialCompatibleDifferentialCore

namespace SequentialCompatibleDifferentialCore

open Purelib.Integration.Program

/-- Construct an integral differential schedule from the original retained refinement certificates and bounds.

The resulting program reads the same original geometric stage models, with exact cell identities and the existing
comparison and sample-bound proofs. -/
@[expose] def toDifferentialSchedule {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : SequentialCompatibleDifferentialCore curve geometry differential) :
    DifferentialSchedule curve geometry differential where
  integral :=
    ({ model := fun index => (geometry.data index).pathModel differential
       steps := core.steps
       stepScale := core.stepScale
       stepScale_nonneg := core.stepScale_nonnegative
       initialAllowance_le := core.initialAllowance_le
       comparisonAllowance_le := core.comparisonAllowance_le } :
      Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram).toRefinementProgram
  cells_eq := fun _ => rfl

/-- The derived integral model keeps exactly the original certified cycle cells at each stage. -/
@[simp] theorem integral_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : SequentialCompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    (core.toDifferentialSchedule.integral.model index).cells =
      ((geometry.data index).certifiedModel differential).cells := rfl

end SequentialCompatibleDifferentialCore

set_option genInjectivity false in
/-- Original strict-later constant-cell refinements with geometric model and comparison bounds.

The retained model scale pays each exact stage allowance and all strict comparisons with the original factor-four bound.
-/
structure StrictCompatibleDifferentialCore {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differentials.Basic.Differential genus) where
  /-- A compatible constant-cell refinement for every strictly later stage. -/ laterRefinements : forall {earlier later
    : Nat}, earlier < later ->
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells
  /-- The rational scale controlling the individual model allowances. -/ modelScale : Coordinate
  /-- The model-allowance scale is nonnegative. -/ modelScale_nonnegative : 0 <= modelScale
  /-- Each stage's aggregate allowance satisfies its retained geometric radius bound. -/ modelAllowance_le : forall
    index,
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      Geometric.Basic.quarterRadius modelScale index
  /-- The retained comparison allowance satisfies its stated geometric radius bound at the earlier stage. -/
    comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier < later),
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (laterRefinements order)) <=
      Geometric.Basic.quarterRadius (4 * modelScale) earlier

constructive_injectivity StrictCompatibleDifferentialCore

set_option genInjectivity false in
/-- Original weakly ordered constant-cell refinements with a common geometric comparison scale.

Every retained certificate connects the exact earlier and later cycle models, including equal stages, and is paid at the
original earlier index. -/
structure CompatibleDifferentialCore {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differentials.Basic.Differential genus) where
  /-- A compatible constant-cell refinement for every ordered pair of stages, including equality. -/ refinements :
    forall {earlier later : Nat}, earlier <= later ->
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells
  /-- The rational scale controlling all retained comparison allowances. -/ errorScale : Coordinate
  /-- The all-stage comparison scale is nonnegative. -/ errorScale_nonnegative : 0 <= errorScale
  /-- The retained comparison allowance satisfies its stated geometric radius bound at the earlier stage. -/
    comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (refinements order)) <=
      Geometric.Basic.quarterRadius errorScale earlier

constructive_injectivity CompatibleDifferentialCore

namespace StrictCompatibleDifferentialCore

/-- Four times the original strict core's retained model scale. -/
@[expose] def errorScale {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential) :
    Coordinate :=
  4 * core.modelScale

/-- The derived factor-four comparison scale is nonnegative. -/
theorem errorScale_nonnegative {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential) :
    0 <= core.errorScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    core.modelScale_nonnegative

/-- A nonnegative model scale's quarter allowance is bounded by that of its factor-four comparison scale. -/
private theorem quarterRadius_model_le_errorScale
    {scale : Coordinate} (nonnegative : 0 <= scale) (index : Nat) :
    Geometric.Basic.quarterRadius scale index <=
      Geometric.Basic.quarterRadius (4 * scale) index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  have powerNonnegative :
      0 <= (1 / 4 : Coordinate) ^ index :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by
      calc
        scale = 1 * scale := by ring1
        _ <= 4 * scale :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) nonnegative)
    powerNonnegative

/-- Extend the original strict refinement family to equal stages using its exact constant-cell reflexive certificate. -/
@[expose] def refinements {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential)
    {earlier later : Nat} (order : earlier <= later) :
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells := by
  by_cases equal : earlier = later
  · subst later
    exact CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.refl
      ((geometry.data earlier).pathModel_constantCells differential)
  · exact core.laterRefinements (Nat.lt_of_le_of_ne order equal)

/-- The original model allowance is paid by the retained factor-four geometric comparison scale. -/
theorem modelAllowance_le_errorScale {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      Geometric.Basic.quarterRadius core.errorScale index :=
  (core.modelAllowance_le index).trans
    (quarterRadius_model_le_errorScale core.modelScale_nonnegative index)

/-- Both strict and equal-stage original refinement certificates satisfy the retained comparison-scale bound.

Equal stages use the retained constant-cell self-refinement and its factor-four allowance. Strictly later stages use the
original comparison certificate with the same error scale. -/
theorem refinements_comparisonAllowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential)
    {earlier later : Nat} (order : earlier <= later) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (core.refinements order)) <=
      Geometric.Basic.quarterRadius core.errorScale earlier := by
  by_cases equal : earlier = later
  · subst later
    unfold refinements
    rewrite [dif_pos (Eq.refl earlier)]
    rw [CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance_refl_eq]
    calc
      4 * ((geometry.data earlier).pathModel differential).aggregateAllowance <=
          4 * Geometric.Basic.quarterRadius core.modelScale earlier :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (core.modelAllowance_le earlier) (by decide)
      _ = Geometric.Basic.quarterRadius core.errorScale earlier := by
        unfold errorScale
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  · unfold refinements
    rewrite [dif_neg equal]
    exact core.comparisonAllowance_le (Nat.lt_of_le_of_ne order equal)

/-- Retain the exact original strict core as a weak-order core with its certified factor-four comparison scale. -/
@[expose] def toCompatibleDifferentialCore {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential) :
    CompatibleDifferentialCore curve geometry differential where
  refinements := core.refinements
  errorScale := core.errorScale
  errorScale_nonnegative := core.errorScale_nonnegative
  comparisonAllowance_le := core.refinements_comparisonAllowance_le

end StrictCompatibleDifferentialCore

set_option genInjectivity false in
/-- Original compatible cycle refinements with paid model errors and a uniform sample bound.

The record keeps the exact stage models and comparison witnesses, their nonnegative geometric scale and a separate
nonnegative squared bound on every original integral sample. -/
structure CompatibleDifferentialSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differentials.Basic.Differential genus) where
  /-- A compatible constant-cell refinement for every ordered pair of stages, including equality. -/ refinements :
    forall {earlier later : Nat}, earlier <= later ->
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells
  /-- The rational scale controlling all retained comparison allowances. -/ errorScale : Coordinate
  /-- The all-stage comparison scale is nonnegative. -/ errorScale_nonnegative : 0 <= errorScale
  /-- Each stage's aggregate allowance satisfies its retained geometric radius bound. -/ modelAllowance_le : forall
    index,
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      Geometric.Basic.quarterRadius errorScale index
  /-- The retained comparison allowance satisfies its stated geometric radius bound at the earlier stage. -/
    comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (refinements order)) <=
      Geometric.Basic.quarterRadius errorScale earlier
  /-- A uniform rational bound on the squared norms of the integral samples. -/ centerBound : Coordinate
  /-- The uniform squared-norm bound is nonnegative. -/ centerBound_nonnegative : 0 <= centerBound
  /-- Every retained model's integral sample satisfies the uniform squared-norm bound. -/ sample_bounded : forall index,
    Data.Gaussian.Norm.Basic.normSq
      ((geometry.data index).pathModel differential).integralSample <=
        centerBound

constructive_injectivity CompatibleDifferentialSchedule

namespace CompatibleDifferentialSchedule

open Purelib.Integration.Program

/-- Construct an integral differential schedule from the original retained refinement certificates and bounds.

The resulting program reads the same original geometric stage models, with exact cell identities and the existing
comparison and sample-bound proofs. -/
@[expose] def toDifferentialSchedule {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (schedule : CompatibleDifferentialSchedule curve geometry differential) :
    DifferentialSchedule curve geometry differential where
  integral :=
    ({ model := fun index => (geometry.data index).pathModel differential
       refinements := schedule.refinements
       errorScale := schedule.errorScale
       errorScale_nonneg := schedule.errorScale_nonnegative
       modelAllowance_le := schedule.modelAllowance_le
       comparisonAllowance_le := schedule.comparisonAllowance_le
       centerBound := schedule.centerBound
       centerBound_nonneg := schedule.centerBound_nonnegative
       sample_bounded := by
         intro index
         simpa only [Norm.Basic.normSq_eq_canonical] using schedule.sample_bounded index } :
      Gaussian.Compatible.CompatibleConstantRefinementProgram).toRefinementProgram
  cells_eq := fun _ => rfl

/-- The derived integral model keeps exactly the original certified cycle cells at each stage. -/
@[simp] theorem integral_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (schedule : CompatibleDifferentialSchedule curve geometry differential)
    (index : Nat) :
    ((schedule.toDifferentialSchedule).integral.model index).cells =
      ((geometry.data index).certifiedModel differential).cells := rfl

end CompatibleDifferentialSchedule

namespace CompatibleDifferentialCore

/-- Equal-stage original compatibility bounds the exact model allowance by its retained geometric error scale. -/
theorem modelAllowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      Geometric.Basic.quarterRadius core.errorScale index := by
  calc
    ((geometry.data index).pathModel differential).aggregateAllowance <=
        (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (core.refinements
          (Nat.le_refl index))) :=
      (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.childAggregateAllowance_le_comparisonAllowance
        (core.refinements
        (Nat.le_refl index)))
    _ <= Geometric.Basic.quarterRadius core.errorScale index :=
      core.comparisonAllowance_le (Nat.le_refl index)

/-- Twice the sum of the initial sample squared norm and the retained comparison scale. -/
@[expose] def centerBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential) :
    Coordinate :=
  2 * (Data.Gaussian.Norm.Basic.normSq
      ((geometry.data 0).pathModel differential).integralSample +
    core.errorScale)

/-- The original initial-sample center bound is nonnegative. -/
theorem centerBound_nonnegative {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential) :
    0 <= core.centerBound := by
  unfold centerBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Norm.Basic.normSq_nonneg _)
      core.errorScale_nonnegative)

/-- A retained movement bound controls the current squared norm by twice the initial norm plus allowance. -/
private theorem normSq_le_initial_bound
    (current initial : Basic.Canonical)
    (scale : Coordinate)
    (movement : Data.Gaussian.Norm.Basic.normSq
      (current - initial) <= scale) :
    Data.Gaussian.Norm.Basic.normSq current <=
      2 * (Data.Gaussian.Norm.Basic.normSq initial + scale) := by
  have sumBound :=
    Norm.Bounds.normSq_add_le_two
      (current - initial) initial
  have identity : current - initial + initial = current := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  rw [identity] at sumBound
  apply sumBound.trans
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
    (show (0 : Coordinate) <= 2 by decide)
  calc
    Data.Gaussian.Norm.Basic.normSq (current - initial) +
        Data.Gaussian.Norm.Basic.normSq initial <=
      scale + Data.Gaussian.Norm.Basic.normSq initial :=
        add_le_add movement (le_refl _)
    _ = Data.Gaussian.Norm.Basic.normSq initial + scale := by ring1

/-- Every original cycle sample differs from the exact initial sample within the retained comparison scale. -/
private theorem sample_sub_initial_bounded {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (((geometry.data index).pathModel differential).integralSample -
          ((geometry.data 0).pathModel differential).integralSample) <=
      core.errorScale := by
  calc
    _ <= (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (core.refinements
      (Nat.zero_le index))) :=
      by simpa only [Norm.Basic.normSq_eq_canonical] using
        (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.integral_difference_le (core.refinements
        (Nat.zero_le index)))
    _ <= Geometric.Basic.quarterRadius core.errorScale 0 :=
      core.comparisonAllowance_le (Nat.zero_le index)
    _ <= core.errorScale :=
      Geometric.Basic.quarterRadius_le_scale
        core.errorScale_nonnegative 0

/-- Every original cycle sample satisfies the bound derived from its exact initial sample and comparison scale. -/
theorem sample_bounded {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        ((geometry.data index).pathModel differential).integralSample <=
      core.centerBound := by
  let initial := ((geometry.data 0).pathModel differential).integralSample
  let current := ((geometry.data index).pathModel differential).integralSample
  exact normSq_le_initial_bound current initial core.errorScale
    (sample_sub_initial_bounded core index)

/-- Add the derived original model and sample bounds to the same retained compatibility core. -/
@[expose] def toCompatibleDifferentialSchedule {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differentials.Basic.Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential) :
    CompatibleDifferentialSchedule curve geometry differential where
  refinements := core.refinements
  errorScale := core.errorScale
  errorScale_nonnegative := core.errorScale_nonnegative
  modelAllowance_le := core.modelAllowance_le
  comparisonAllowance_le := core.comparisonAllowance_le
  centerBound := core.centerBound
  centerBound_nonnegative := core.centerBound_nonnegative
  sample_bounded := core.sample_bounded

end CompatibleDifferentialCore

set_option genInjectivity false in
/-- The two original indexed cycle-schedule families for the retained curve.

The A and B families keep separate original genus indices and geometric data at every refinement stage. -/
structure SymplecticCycleSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) where
  /-- The original A-cycle schedules, indexed by the curve's genus. -/ aCycle : Fin genus -> CycleSchedule curve
  /-- The original B-cycle schedules, indexed by the curve's genus. -/ bCycle : Fin genus -> CycleSchedule curve

constructive_injectivity SymplecticCycleSchedule

namespace SymplecticCycleSchedule

/-- Read the original paired A and B lifted-cycle families from their exact retained schedules. -/
@[expose] def cycles {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (geometry : SymplecticCycleSchedule curve) :
    Lifted.Family.PairedCycleRefinements 2 genus where
  aCycle := fun index => (geometry.aCycle index).cycle
  bCycle := fun index => (geometry.bCycle index).cycle

/-- Stagewise realization of both original indexed cycle families.

Every A and B schedule retains explicit realization witnesses for its corresponding raw cycle, with the original genus
index preserved. -/
structure Realizes {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (geometry : SymplecticCycleSchedule curve)
    (raw : Lifted.Family.PairedCycleRefinements 2 genus) where
  /-- Each A-cycle schedule explicitly realizes the corresponding original raw A cycle. -/ aCycle : forall index,
    CycleSchedule.Realizes
    (geometry.aCycle index) (raw.aCycle index)
  /-- Each B-cycle schedule explicitly realizes the corresponding original raw B cycle. -/ bCycle : forall index,
    CycleSchedule.Realizes
    (geometry.bCycle index) (raw.bCycle index)

end SymplecticCycleSchedule

/-- Exact equality or an explicit original prepared realization of paired cycle families.

The relation preserves both input families and the retained A and B realization witnesses without replacing the original
geometric owners. -/
inductive SymplecticCycleRealization {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) :
    Lifted.Family.PairedCycleRefinements 2 genus -> Lifted.Family.PairedCycleRefinements 2 genus -> Prop
  /-- The two cycle families are exactly equal. -/ | exact {cycles : Lifted.Family.PairedCycleRefinements 2 genus} :
      SymplecticCycleRealization curve cycles cycles
  /-- The retained prepared schedule explicitly realizes the given raw cycle family. -/ | prepared (geometry :
    SymplecticCycleSchedule curve)
      {raw : Lifted.Family.PairedCycleRefinements 2 genus}
      (realizes : geometry.Realizes raw) :
      SymplecticCycleRealization curve geometry.cycles raw

namespace SymplecticCycleRealization

/-- An exact equality of the original paired cycle families gives their realization certificate. -/
theorem ofEq {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {left right : Lifted.Family.PairedCycleRefinements 2 genus}
    (equal : left = right) : SymplecticCycleRealization curve left right := by
  cases equal
  exact .exact

end SymplecticCycleRealization

set_option genInjectivity false in
/-- Original integral schedules for every standard differential and retained A or B cycle.

Both finite indices keep their original order, and every entry is tied to the exact geometric cycle schedule for that
column. -/
structure PeriodSchedules {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  /-- The integral schedule at each standard-differential row and original A-cycle column. -/ aSchedule : forall
    differential cycle : Fin genus,
    DifferentialSchedule curve (geometry.aCycle cycle)
      (PeriodMatrix.standardDifferential differential)
  /-- The integral schedule at each standard-differential row and original B-cycle column. -/ bSchedule : forall
    differential cycle : Fin genus,
    DifferentialSchedule curve (geometry.bCycle cycle)
      (PeriodMatrix.standardDifferential differential)

constructive_injectivity PeriodSchedules

set_option genInjectivity false in
/-- Original consecutive-refinement cores for every differential and retained A or B cycle.

The dependent matrix keeps the exact original geometry and standard-differential indices in both period families. -/
structure SequentialCompatiblePeriodCores {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  /-- The compatibility core at each standard-differential row and original A-cycle column. -/ aCore : forall
    differential cycle : Fin genus,
    SequentialCompatibleDifferentialCore curve (geometry.aCycle cycle)
      (PeriodMatrix.standardDifferential differential)
  /-- The compatibility core at each standard-differential row and original B-cycle column. -/ bCore : forall
    differential cycle : Fin genus,
    SequentialCompatibleDifferentialCore curve (geometry.bCycle cycle)
      (PeriodMatrix.standardDifferential differential)

constructive_injectivity SequentialCompatiblePeriodCores

set_option genInjectivity false in
/-- Original bounded compatible schedules for every differential and retained A or B cycle.

Each entry preserves its original geometric column, standard-differential row and exact refinement and sample-bound
certificates. -/
structure CompatiblePeriodSchedules {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  /-- The integral schedule at each standard-differential row and original A-cycle column. -/ aSchedule : forall
    differential cycle : Fin genus,
    CompatibleDifferentialSchedule curve (geometry.aCycle cycle)
      (PeriodMatrix.standardDifferential differential)
  /-- The integral schedule at each standard-differential row and original B-cycle column. -/ bSchedule : forall
    differential cycle : Fin genus,
    CompatibleDifferentialSchedule curve (geometry.bCycle cycle)
      (PeriodMatrix.standardDifferential differential)

constructive_injectivity CompatiblePeriodSchedules

set_option genInjectivity false in
/-- Original strict-refinement cores for every differential and retained A or B cycle.

The dependent period matrices preserve the original geometric families, row differentials and strict comparison
payments. -/
structure StrictCompatiblePeriodCores {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  /-- The compatibility core at each standard-differential row and original A-cycle column. -/ aCore : forall
    differential cycle : Fin genus,
    StrictCompatibleDifferentialCore curve (geometry.aCycle cycle)
      (PeriodMatrix.standardDifferential differential)
  /-- The compatibility core at each standard-differential row and original B-cycle column. -/ bCore : forall
    differential cycle : Fin genus,
    StrictCompatibleDifferentialCore curve (geometry.bCycle cycle)
      (PeriodMatrix.standardDifferential differential)

constructive_injectivity StrictCompatiblePeriodCores

set_option genInjectivity false in
/-- Original weak-order compatibility cores for every differential and retained A or B cycle.

The dependent period matrices preserve the original geometric families, row differentials and exact comparison
witnesses. -/
structure CompatiblePeriodCores {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  /-- The compatibility core at each standard-differential row and original A-cycle column. -/ aCore : forall
    differential cycle : Fin genus,
    CompatibleDifferentialCore curve (geometry.aCycle cycle)
      (PeriodMatrix.standardDifferential differential)
  /-- The compatibility core at each standard-differential row and original B-cycle column. -/ bCore : forall
    differential cycle : Fin genus,
    CompatibleDifferentialCore curve (geometry.bCycle cycle)
      (PeriodMatrix.standardDifferential differential)

constructive_injectivity CompatiblePeriodCores

namespace SequentialCompatiblePeriodCores

/-- Read the original integral schedules from the retained differential cores at every A and B entry. -/
@[expose] def toPeriodSchedules {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : SequentialCompatiblePeriodCores curve geometry) :
    PeriodSchedules curve geometry where
  aSchedule := fun differential cycle =>
    (cores.aCore differential cycle).toDifferentialSchedule
  bSchedule := fun differential cycle =>
    (cores.bCore differential cycle).toDifferentialSchedule

end SequentialCompatiblePeriodCores

namespace CompatiblePeriodCores

/-- Construct the original compatible period schedules from the same retained A and B core entries. -/
@[expose] def toCompatiblePeriodSchedules {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : CompatiblePeriodCores curve geometry) :
    CompatiblePeriodSchedules curve geometry where
  aSchedule := fun differential cycle =>
    (cores.aCore differential cycle).toCompatibleDifferentialSchedule
  bSchedule := fun differential cycle =>
    (cores.bCore differential cycle).toCompatibleDifferentialSchedule

end CompatiblePeriodCores

namespace StrictCompatiblePeriodCores

/-- Extend the original strict period cores with their exact equal-stage refinement certificates. -/
@[expose] def toCompatiblePeriodCores {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : StrictCompatiblePeriodCores curve geometry) :
    CompatiblePeriodCores curve geometry where
  aCore := fun differential cycle =>
    (cores.aCore differential cycle).toCompatibleDifferentialCore
  bCore := fun differential cycle =>
    (cores.bCore differential cycle).toCompatibleDifferentialCore

/-- Construct the original compatible period schedules from the same retained A and B core entries. -/
@[expose] def toCompatiblePeriodSchedules {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : StrictCompatiblePeriodCores curve geometry) :
    CompatiblePeriodSchedules curve geometry :=
  cores.toCompatiblePeriodCores.toCompatiblePeriodSchedules

end StrictCompatiblePeriodCores

namespace CompatiblePeriodSchedules

/-- Read the underlying integral schedules from the retained compatible A and B period entries. -/
@[expose] def toPeriodSchedules {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry) :
    PeriodSchedules curve geometry where
  aSchedule := fun differential cycle =>
    (schedules.aSchedule differential cycle).toDifferentialSchedule
  bSchedule := fun differential cycle =>
    (schedules.bSchedule differential cycle).toDifferentialSchedule

end CompatiblePeriodSchedules

namespace PeriodSchedules

/-- Package the exact original cycle families and certified A and B differential integral programs as period data. -/
@[expose] def toPeriodData {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : PeriodSchedules curve geometry) :
    PeriodMatrix.PeriodData curve where
  cycles := geometry.cycles
  aProgram := fun differential cycle =>
    (schedules.aSchedule differential cycle).toCertifiedPeriodProgram
  bProgram := fun differential cycle =>
    (schedules.bSchedule differential cycle).toCertifiedPeriodProgram

/-- Attach the supplied inverse certificate for the exact retained A-period matrix to the original period data. -/
@[expose] def normalized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : PeriodSchedules curve geometry)
    (inverse : PeriodMatrix.ScaledInverseCertificate
      schedules.toPeriodData.aMatrix) :
    PeriodMatrix.NormalizedPeriodData curve where
  toPeriodData := schedules.toPeriodData
  aInverse := inverse

/-- The resulting original period data retains the supplied explicit geometric cycle realization. -/
theorem cyclesRealization {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : PeriodSchedules curve geometry)
    {raw : Lifted.Family.PairedCycleRefinements 2 genus}
    (realizes : geometry.Realizes raw) :
    SymplecticCycleRealization curve schedules.toPeriodData.cycles raw := by
  exact .prepared geometry realizes

end PeriodSchedules

namespace CompatiblePeriodSchedules

/-- Package the exact original cycle families and certified A and B differential integral programs as period data. -/
@[expose] def toPeriodData {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry) :
    PeriodMatrix.PeriodData curve :=
  schedules.toPeriodSchedules.toPeriodData

/-- Attach the supplied inverse certificate for the exact retained A-period matrix to the original period data. -/
@[expose] def normalized {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry)
    (inverse : PeriodMatrix.ScaledInverseCertificate
      schedules.toPeriodData.aMatrix) :
    PeriodMatrix.NormalizedPeriodData curve :=
  schedules.toPeriodSchedules.normalized inverse

/-- The resulting original period data retains the supplied explicit geometric cycle realization. -/
theorem cyclesRealization {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry)
    {raw : Lifted.Family.PairedCycleRefinements 2 genus}
    (realizes : geometry.Realizes raw) :
    SymplecticCycleRealization curve schedules.toPeriodData.cycles raw :=
  schedules.toPeriodSchedules.cyclesRealization realizes

end CompatiblePeriodSchedules

end Purelib.Riemann.Topology.PreparedCycleModels

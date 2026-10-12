module
import Purelib.Data.List.Map
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentSigns
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Integration
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes

/-! The actual root chain propagates one sign across the conjugate polygon
of all cached parent totals. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentSigns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Entry Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (capValues)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target : Coordinate} {minimum stage fine : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Request regular other parents
    target minimum}

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Integration.Path.PairedIncrementArea (total area)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (firstFlip)

/-- Negate both coordinates of the retained primitive point. -/
private def negate (point : Stokes.PrimitivePoint) : PrimitivePoint := ⟨-point.left, -point.right⟩

/-- Negating each original paired increment negates its complete total. -/
private theorem total_negate (points : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (points.map negate) =
      negate (PairedIncrementArea.total points) := by
  induction points with
  | nil => apply congrArg₂ PrimitivePoint.mk <;> exact (neg_zero).symm
  | cons head tail ih =>
      change (negate head).add
        (PairedIncrementArea.total (tail.map negate)) =
        negate (head.add (PairedIncrementArea.total
          tail))
      rw [ih]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp only
        [negate, PrimitivePoint.add] <;> ring1

/-- Negating both coordinates of every original paired increment preserves its complete area. -/
private theorem area_negate (points : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (points.map negate) =
      PairedIncrementArea.area points := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, PairedAreaBlocks.area_cons, PairedAreaBlocks.area_cons,
        total_negate, ih]
      simp only [Stokes.edgeArea, negate, -eq_self,
        -iff_self]
      ring1

/-- The actual retained signed cap total is the original unsigned cap-path total with the exact shared sheet sign. -/
private theorem Entry.signed_total (entry : PairedParentRequest.Request.Entry request sample otherSample fine) :
    entry.certified.compared.secondSummary.totalValue =
      if entry.certified.shared.flip then negate
        (PairedIncrementArea.total entry.pair.2)
      else PairedIncrementArea.total entry.pair.2 := by
  rw [entry.certified.compared.secondSummary.total_eq, Certified.cap_path entry.certified]
  change PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments _ _ 0 1) =
    if entry.certified.shared.flip then negate
      (PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments _ _ 0 1))
    else PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments _ _ 0 1)
  rw [DyadicPairedPrimitivePaths.increments_total, DyadicPairedPrimitivePaths.increments_total]
  cases bit : entry.certified.shared.flip with
  | false =>
      have point (parameter : InverseRootPolynomial.Coordinate) : entry.certified.shared.values parameter =
          CommonRibbonRequest.capValues (parent := entry.plan.parent) sample otherSample parameter := by
        apply congrArg₂ PrimitivePoint.mk <;>
          simp only [entry.certified.shared.first_eq, entry.certified.shared.second_eq, bit, if_neg (show ¬ (false =
            true) from by decide), -eq_self, -iff_self] <;> rfl
      rw [point 0, point 1]
      rfl
  | true =>
      have point (parameter : InverseRootPolynomial.Coordinate) : entry.certified.shared.values parameter =
          negate (CommonRibbonRequest.capValues (parent
            := entry.plan.parent) sample otherSample parameter) := by
        apply congrArg₂ PrimitivePoint.mk <;>
          simp only [CommonRibbonRequest.capValues, entry.certified.shared.first_eq,
            entry.certified.shared.second_eq, bit, if_pos (Eq.refl true), DensePolynomial.eval_neg, -eq_self, -iff_self]
              <;> rfl
      rw [point 0, point 1]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp only
        [negate, PrimitivePoint.sub] <;> ring1

/-- The polygon of cached signed cap totals is exactly the unsigned cap polygon once the actual parent root chain has
propagated the common sign. -/
theorem Evaluation.conjugate_cap_polygon_unsigned (evaluated : PairedParentRequest.Request.Evaluation request sample
  otherSample fine)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
    PairedIncrementArea.area (evaluated.retained.map (fun entry => ConjugateIncrementComparison.conjugateFirst
      entry.certified.compared.secondSummary.totalValue)) =
      PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).map (fun values =>
        ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total values))) := by
  have signs := evaluated.shared_signs chain roots
  have values : evaluated.retained.map (fun entry => ConjugateIncrementComparison.conjugateFirst
    entry.certified.compared.secondSummary.totalValue) =
      evaluated.retained.map (fun entry => if PairedParentRequest.Request.firstFlip evaluated.retained then
        negate
          (ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total entry.pair.2)) else
          ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total entry.pair.2)) := by
    generalize fixed : PairedParentRequest.Request.firstFlip evaluated.retained = bit at signs ⊢
    generalize retainedEq : evaluated.retained = retained at signs ⊢
    clear retainedEq
    induction retained with
    | nil => rfl
    | cons head tail ih =>
        apply congrArg₂ List.cons
        · change ConjugateIncrementComparison.conjugateFirst head.certified.compared.secondSummary.totalValue =
            if bit then negate
              (ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total head.pair.2)) else
              ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total head.pair.2)
          rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentSigns.Entry.signed_total head, signs head
            List.mem_cons_self]
          cases bit <;> rfl
        · exact ih (fun entry member => signs entry (List.mem_cons_of_mem head member))
  rw [values, evaluated.pairs_eq]
  cases bit : PairedParentRequest.Request.firstFlip evaluated.retained with
  | false =>
      change PairedIncrementArea.area (evaluated.retained.map (fun entry => ConjugateIncrementComparison.conjugateFirst
        (PairedIncrementArea.total entry.pair.2))) = _
      simp only [Data.List.Map.map_map, -eq_self, -iff_self]
      rfl
  | true =>
      change PairedIncrementArea.area (evaluated.retained.map (fun entry =>
        negate
        (ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total entry.pair.2)))) = _
      have result :=
        area_negate (evaluated.retained.map (fun entry
          => ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total entry.pair.2)))
      simp only [Data.List.Map.map_map, -eq_self, -iff_self] at result ⊢
      dsimp only [Function.comp_def] at result ⊢
      exact result

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentSigns

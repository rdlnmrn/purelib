module

public import Purelib.Riemann.Integration.PreparedSwitchedRefinements

/-! # Centered chains read from retained switch-free paths

The original endpoint-indexed switched chain supplies every complete parent.
A zero switch count rules out precisely the stationary constructor; no edge,
root observation or model is prepared again.
-/

public section

namespace Purelib.Riemann.Integration.PreparedSwitchedRefinements.SwitchedPathChain

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain closeLiftedPath)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- Read the complete original geometric parents when the retained chain has no stationary switches. -/
def centered {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus} :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) →
    chain.switchCount = 0 → CenteredPathChain parents (start := start) (finish := finish)
  | _, _, _, .nil point, _ => .nil point
  | _, _, _, .edge parent tail, zero => .cons parent (centered tail zero)
  | _, _, _, .stationary _ _ tail, zero => by
      rewrite [switchCount.eq_3] at zero
      exact False.elim (Nat.succ_ne_zero tail.switchCount ((Nat.add_one _).symm.trans zero))

/-- Embedding the recovered centered chain gives the whole identical original switched chain. -/
theorem ofCentered_centered {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) →
    (zero : chain.switchCount = 0) → ofCenteredPathChain (centered chain zero) = chain
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .edge parent tail, zero => congrArg (SwitchedPathChain.edge parent) (ofCentered_centered tail zero)
  | _, _, _, .stationary _ _ tail, zero => by
      rewrite [switchCount.eq_3] at zero
      exact False.elim (Nat.succ_ne_zero tail.switchCount ((Nat.add_one _).symm.trans zero))

/-- Recovering a switched chain embedded from centered parents preserves the whole original centered chain. -/
theorem centered_ofCentered {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    centered (ofCenteredPathChain chain) (switchCount_ofCenteredPathChain chain) = chain
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons parent tail => congrArg (CenteredPathChain.cons parent) (centered_ofCentered tail)

/-- The recovered centered spine follows the exact original lifted path, with every ordered edge retained. -/
theorem centered_path {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    {parents : List (CenteredEdge curve differential)} → {start finish : LiftedPoint 2} →
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) →
    (zero : chain.switchCount = 0) → (centered chain zero).path = chain.path
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .edge _ tail, zero => congrArg (LiftedPath.cons _) (centered_path tail zero)
  | _, _, _, .stationary _ _ tail, zero => by
      rewrite [switchCount.eq_3] at zero
      exact False.elim (Nat.succ_ne_zero tail.switchCount ((Nat.add_one _).symm.trans zero))

/-- Close the recovered original spine by transporting only its retained finishing-point index. -/
def closedCentered {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish))
    (zero : chain.switchCount = 0) (closed : finish = start) :
    CenteredPathChain parents (start := start) (finish := start) :=
  CenteredPathChain.castFinish closed (centered chain zero)

/-- Closing the recovered spine is exactly closing the original switched path by the same endpoint equality. -/
theorem closedCentered_path {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish))
    (zero : chain.switchCount = 0) (closed : finish = start) :
    (closedCentered chain zero closed).path = closeLiftedPath chain.path closed := by
  cases closed
  exact centered_path chain zero

end Purelib.Riemann.Integration.PreparedSwitchedRefinements.SwitchedPathChain

end

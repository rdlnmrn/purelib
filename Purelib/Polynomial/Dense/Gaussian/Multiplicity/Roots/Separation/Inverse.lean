module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Separation
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Origins

/-!
# Original cached difference inverses at retained factor-root occurrences

Same-factor views read their original twice-excluded cofactor cache.
Distinct-factor views read their original context-pair one-exclusion cache.
No scalar cofactor, derivative or original factor preprocessing is repeated.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Separation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Data.List
open Stages

variable {source opposite : DensePolynomial Canonical} {input : PositiveSideInput source opposite}

/-- Read the same retained original within-factor or cross-factor difference inverse. -/
@[expose] def inverse (retained : Separation input)
    (left right : Images.Origin retained.prepared.stages retained.images) : retained.prepared.stages.Scalar :=
  if equal : left.factor = right.factor then
    let rightRoot : Fin (Images.rootsAt retained.prepared.stages retained.images left.factor).length :=
      ⟨right.root.val, by rewrite [equal]; exact right.root.isLt⟩
    let jets := DependentProduct.get retained.prepared.indices retained.jets left.factor
    (jets.pairs.get left.root rightRoot).inverse
  else
    let pair := DependentProduct.get retained.prepared.indices
      (DependentProduct.get retained.prepared.indices retained.pairs left.factor) right.factor
    match pair with
    | .diagonal _ => 0
    | .separated _ cross => (cross.get left.root right.root).inverse.val

/-- Distinct original flattened positions read the same actual retained root-difference unit. -/
theorem inverse_unit (retained : Separation input)
    (left right : Images.Origin retained.prepared.stages retained.images)
    (different : Images.Origin.position retained.prepared.stages retained.images left ≠
      Images.Origin.position retained.prepared.stages retained.images right) :
    (left.point - right.point) * retained.inverse left right = 1 := by
  rcases left with ⟨leftFactor, leftRoot⟩
  rcases right with ⟨rightFactor, rightRoot⟩
  by_cases equal : leftFactor = rightFactor
  · subst rightFactor
    have distinct : rightRoot ≠ leftRoot := by
      intro same
      subst rightRoot
      exact different rfl
    unfold inverse
    dsimp only
    rewrite [dif_pos rfl]
    exact (Images.Pairs.get
      (DependentProduct.get retained.prepared.indices retained.jets leftFactor).pairs leftRoot rightRoot).unit distinct
  · unfold inverse
    dsimp only
    rewrite [dif_neg equal]
    cases pair : DependentProduct.get retained.prepared.indices
        (DependentProduct.get retained.prepared.indices retained.pairs leftFactor) rightFactor with
    | diagonal same => exact (equal same).elim
    | separated _ cross => exact (cross.get leftRoot rightRoot).inverse.property

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Separation

end

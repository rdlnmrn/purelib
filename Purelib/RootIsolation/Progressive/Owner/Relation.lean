module
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.RootIsolation.Progressive.Owner.Transfer
import Purelib.Approximation.Relation.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.RootIsolation.Owner.Relation.Basic
public import Purelib.RootIsolation.Owner.Relation.Refinement
import Purelib.Geometry.Rational.Box.Relation
import Purelib.Approximation.Relation.Fibre
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
-/

namespace Purelib.RootIsolation.Progressive.Owner.Relation

/-- Rouché transport followed by shrinking preserves the same explicit owner
labels even though the exact rational polynomial reading has changed. -/
def transportedRefinement
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable}
    {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer
      left right target positive)
    (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    Approximation.Relation.Refinement (Owner.Relation.Basic.ownerFibre transfer.family)
      (Owner.Relation.Basic.ownerFibre (transfer.refinedFamily epsilon epsilonPositive))
      Box.Relation.BoxContinues :=
  Owner.Relation.Refinement.sameLabelRefinement transfer.family
    (transfer.refinedFamily epsilon epsilonPositive)
    (transfer.refinedFamily_nested epsilon epsilonPositive)

/-- Coefficient transport followed by refinement continues each original label to its single corresponding later label.
-/
theorem transported_owner_is_same_label
    {left right : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable}
    {target : Fraction.Rational}
    {positive : 0 < target}
    (transfer : Progressive.Owner.Transfer.GuardedFamilyTransfer
      left right target positive)
    (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon)
    (label : Fin left.degree) :
    (transportedRefinement transfer epsilon epsilonPositive).continues label =
      [Owner.Relation.Refinement.sameLabelForward transfer.family
        (transfer.refinedFamily epsilon epsilonPositive) label] := rfl

end Purelib.RootIsolation.Progressive.Owner.Relation

end

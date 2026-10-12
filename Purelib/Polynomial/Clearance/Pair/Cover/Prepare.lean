module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bisection
public import Purelib.Polynomial.Clearance.Pair.Cover.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bounded polynomial clearance refinement

Finite depth bounds refinement of unresolved leaves. Positive quadrance floors stop before either child is built;
otherwise both half-interval results retain their exact floor indices and certificate trees.
-/

namespace Purelib.Polynomial.Clearance.Pair.Cover.Prepare

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

set_option genInjectivity false in
/-- A finite interval cover packaged with its exact quadrance and coordinate floor indices.

The cover retains the original polynomial source and parameter interval; a zero floor does not certify a root or failed
separation. -/
public structure Prepared {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
    (source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial) (parameters :
      Data.Rat.Interval.Bounds) where
  /-- The retained aggregate quadrance lower bound. -/ normFloor : Fraction.Rational
  /-- The retained aggregate maximum-coordinate lower bound. -/ coordinateFloor : Fraction.Rational
  /-- The actual finite certificate tree indexed by these exact floor values. -/ cover :
    Cover source parameters normFloor coordinateFloor

constructive_injectivity Prepared

/-- Package a cached leaf as a one-node prepared cover with unchanged floor values.

The package projects the cached leaf floors and retains that same leaf as its one-node certificate tree. -/
@[expose] public def Prepared.ofLeaf {realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial} {source : Clearance.Pair.Cover.Leaf.Source realPolynomial
  imagPolynomial}
    {parameters : Data.Rat.Interval.Bounds} (leaf : Leaf source parameters) :
      Clearance.Pair.Cover.Prepare.Prepared source parameters :=
  ⟨leaf.normFloor, leaf.coordinateFloor, .leaf leaf⟩

/-- Structural recursion gives a total finite proposal.  Already separated
nodes do not build either child, regardless of the unused depth budget.

The original positive-floor stop test is checked before constructing children. Unresolved successor-depth nodes retain
both half-interval covers and combine their floor indices with the baseline. -/
@[expose] public def refine {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  {source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial}
    {parameters : Data.Rat.Interval.Bounds} (leaf : Leaf source parameters) : Nat →
      Clearance.Pair.Cover.Prepare.Prepared source parameters
  | 0 => .ofLeaf leaf
  | depth + 1 =>
      if 0 < leaf.normFloor then .ofLeaf leaf
      else
        let left := Purelib.Polynomial.Clearance.Pair.Cover.Prepare.refine (Leaf.prepare
          source (Data.Rat.Interval.Bisection.leftHalf parameters)) depth
        let right := Purelib.Polynomial.Clearance.Pair.Cover.Prepare.refine (Leaf.prepare
          source (Data.Rat.Interval.Bisection.rightHalf parameters)) depth
        ⟨max leaf.normFloor (min left.normFloor right.normFloor),
          max leaf.coordinateFloor (min left.coordinateFloor right.coordinateFloor),
          .split leaf left.cover right.cover⟩

/-- At most eight bisections along each branch.  Exhaustion is a zero
proposal, not a root claim; the public path constructor needs no fuel input.

The displayed depth is eight. It bounds only the finite refinement procedure and carries no eventual-separation
guarantee. -/
@[expose] public def defaultDepth : Nat := 8

/-- Prepare the initial leaf and refine unresolved nodes up to the fixed default depth.

The initial leaf is constructed for the supplied source and interval. Refinement then consumes the fixed depth budget
and retains its actual certificate tree. -/
@[expose] public def prepare {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  (source : Clearance.Pair.Cover.Leaf.Source realPolynomial imagPolynomial)
    (parameters : Data.Rat.Interval.Bounds) : Clearance.Pair.Cover.Prepare.Prepared source parameters :=
  Clearance.Pair.Cover.Prepare.refine (Leaf.prepare source parameters)
    Clearance.Pair.Cover.Prepare.defaultDepth

/-- Coverage and aggregate soundness are the universal results, not an
acceptance-tag check or a finite sample substitution for uniform bounds.

Every contained parameter has an explicit retained leaf region. The same prepared tree bounds pair quadrance and the
larger coordinate magnitude through its exact floor indices. -/
public theorem retained_cover_contract (realPolynomial imagPolynomial :
  Dense.Rational.Basic.CoordinatePolynomial) (parameters : Data.Rat.Interval.Bounds)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    let result := Clearance.Pair.Cover.Prepare.prepare (Clearance.Pair.Cover.Leaf.Source.prepare realPolynomial
      imagPolynomial) parameters
    (∃ region, region ∈ result.cover.regions ∧ region.Contains parameter) ∧
      result.normFloor ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 ∧
      result.coordinateFloor ≤ max (Fraction.abs (realPolynomial.eval parameter)) (Fraction.abs (imagPolynomial.eval
        parameter)) :=
  ⟨(Clearance.Pair.Cover.Prepare.prepare _ _).cover.covers inside, (Clearance.Pair.Cover.Prepare.prepare _
    _).cover.norm_le inside,
    (Clearance.Pair.Cover.Prepare.prepare _ _).cover.coordinate_le inside⟩

end Purelib.Polynomial.Clearance.Pair.Cover.Prepare

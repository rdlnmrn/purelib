module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.Polynomial.Winding.Box.Rouche.Connection

/-! ## Rouché-connected rational owner boxes -/

set_option genInjectivity false in
/-- One oriented finite Rouché comparison on one displayed rational box. -/
structure OrientedRouche
    (base target : CoefficientPolynomial) (box : Box) where
  /-- The retained polynomial perturbation from the base reading. -/ perturbation :
    CoefficientPolynomial
  /-- The target is exactly the base plus the retained perturbation. -/ target_eq_add : target = base + perturbation
  /-- Strict boundary norm dominance on the same rational box. -/ dominance :
    Clearance.Box.Dominance.Basic.BoundaryNormDominance
    base perturbation box

constructive_injectivity OrientedRouche

set_option genInjectivity false in
/-- A symmetric record that the two polynomial readings are joined on one
rational box by a finite Rouché calculation.  Equality is the zero-length
piece; the two oriented cases make path reversal data-preserving. -/
inductive RoucheConnection
    (left right : CoefficientPolynomial) (box : Box) : Type
  /-- Connect identical polynomial readings on the retained box. -/ | equal (same : left = right)
  /-- Retain a Rouché comparison oriented from left to right. -/ | forward (certificate :
    OrientedRouche left right box)
  /-- Retain a Rouché comparison oriented from right to left. -/ | backward (certificate :
    OrientedRouche right left box)

constructive_injectivity RoucheConnection

namespace RoucheConnection

/-- Reverse a Rouché connection while preserving its comparison certificate.

Equality is reversed; forward and backward constructors exchange roles without recomputing a perturbation. -/
def reverse {left right :
  CoefficientPolynomial} {box : Box} :
    RoucheConnection left right box → RoucheConnection right
      left box
  | .equal same => .equal same.symm
  | .forward certificate => .backward certificate
  | .backward certificate => .forward certificate

end RoucheConnection

end Purelib.Polynomial.Winding.Box.Rouche.Connection

end

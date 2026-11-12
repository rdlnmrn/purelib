module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
public import Purelib.Topology.Chain.PathBoundary
public import Purelib.Topology.Polygon.Stokes
public import Purelib.Data.Vector.Basic
public import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact algebraic primitives and original endpoint banks

The primitive checker computes a formal derivative and both cleared
coefficient differences. Retained endpoint banks keep each original radicand,
chart, coordinate, selected sheet and numerical denotation separate. Integer
boundary coefficients cancel occurrences of the same retained endpoint;
unlike quadratic pair parameters are never multiplied together.
-/

public section

namespace Purelib.Integration.Path.Primitive.Algebraic

open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Quadratic.Pair.Polynomial.Expression
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

set_option genInjectivity false in
/-- A cached exact differential check on two original quadratic expressions.

The original differential and primitive remain indexed and retained. The
computed derivative and cleared coefficient comparison are reusable data,
independent of any numerical integration program or endpoint observation. -/
structure Attempt {radicand : Coefficients} (differential primitive : Expression radicand) where
  /-- The actual original differential expression. -/
  sourceDifferential : Expression radicand
  /-- The retained differential is the original input. -/
  sourceDifferential_eq : sourceDifferential = differential
  /-- The actual original primitive expression. -/
  sourcePrimitive : Expression radicand
  /-- The retained primitive is the original input. -/
  sourcePrimitive_eq : sourcePrimitive = primitive
  /-- The computed and retained formal derivative. -/
  derivative : Expression radicand
  /-- The derivative belongs to the original retained primitive. -/
  derivative_eq : derivative = primitive.derivative
  /-- The cached cleared coefficient comparison of the original differential and derivative. -/
  comparison : Comparison differential derivative

constructive_injectivity Attempt

/-- Compute the derivative and exact coefficient comparison once from the two original expressions. -/
@[expose] def prepare {radicand : Coefficients} (differential primitive : Expression radicand) :
    Attempt differential primitive :=
  let derivative := primitive.derivative
  let comparison := differential.compare derivative
  ⟨differential, rfl, primitive, rfl, derivative, rfl, comparison⟩

set_option genInjectivity false in
/-- An established exact primitive with its original cached derivative calculation.

The certificate is the finite coefficient equality, with no numerical
integration comparison supplied as a premise. -/
structure Exact {radicand : Coefficients} (differential primitive : Expression radicand) where
  /-- The full retained derivative-and-comparison attempt. -/
  attempt : Attempt differential primitive
  /-- The original differential equals this computed derivative after exact coefficient clearing. -/
  equal : differential.Equal attempt.derivative

constructive_injectivity Exact

set_option genInjectivity false in
/-- A certified primitive identity or the identified coefficient obstruction to its finite check.

Failure concerns the proposed coefficient identity alone. It implies neither
numerical inequality at a chosen sheet nor impossibility of another primitive. -/
inductive Attempt.Outcome {radicand : Coefficients} {differential primitive : Expression radicand}
    (attempt : Attempt differential primitive) where
  /-- The original proposed primitive has the claimed exact differential. -/
  | exact (certificate : Exact differential primitive)
  /-- The real cleared coefficient difference does not vanish. -/
  | realObstructed (nonzero : attempt.comparison.real.isZero = false)
  /-- The real difference vanishes and the imaginary coefficient difference does not. -/
  | imaginaryObstructed (realZero : attempt.comparison.real.isZero = true)
      (nonzero : attempt.comparison.imaginary.isZero = false)

constructive_injectivity Attempt.Outcome

/-- Check the cached coefficient comparison and construct its explanatory mathematical outcome. -/
@[expose] def Attempt.check {radicand : Coefficients} {differential primitive : Expression radicand}
    (attempt : Attempt differential primitive) : attempt.Outcome :=
  match attempt.comparison.check with
  | .equal certificate => .exact ⟨attempt, certificate⟩
  | .realObstructed nonzero => .realObstructed nonzero
  | .imaginaryObstructed realZero nonzero => .imaginaryObstructed realZero nonzero

/-- An established exact primitive gives the canonical formal derivative identity. -/
theorem Exact.derivative_eq {radicand : Coefficients} {differential primitive : Expression radicand}
    (certificate : Exact differential primitive) : differential.Equal primitive.derivative := by
  rewrite [← certificate.attempt.derivative_eq]
  exact certificate.equal

/-- One cached original square-root channel with its actual provenance owner. -/
@[expose] def RootReading : Type 1 :=
  (channel : CoherentNamed) × SquareRootSidecar.Sidecar channel

set_option genInjectivity false in
/-- An original chart-owned lifted endpoint and its retained algebraic primitive value.

The chart and lifted point remain original nominal owners. The cached root is
tied to their original root-reading operation, and its polynomial parameter,
primitive, source domain and denotation belong to that same chart. -/
structure Endpoint (Chart : Type) (sheets : Nat)
    (polynomialAt : Chart → Coefficients) (rootAt : Chart → LiftedPoint sheets → RootReading) where
  /-- The original chart owner. -/
  chart : Chart
  /-- The original lifted coordinate and selected sheet label. -/
  point : LiftedPoint sheets
  /-- The primitive expression in this original chart's polynomial pair algebra. -/
  primitive : Expression (polynomialAt chart)
  /-- The cached original selected root reading with its original provenance. -/
  root : RootReading
  /-- The cached root belongs to this exact original chart, point and sheet. -/
  root_eq : root = rootAt chart point
  /-- The original root polynomial evaluates to the retained square parameter. -/
  parameter_eq : root.2.parameter = (polynomialAt chart).eval point.coordinate
  /-- The cached primitive value at this exact original selected root. -/
  denotation : Denotation primitive point.coordinate root.1

constructive_injectivity Endpoint

namespace Endpoint

/-- Retain the original selected root once and derive its primitive denotation from its square provenance. -/
@[expose] def retain {Chart : Type} {sheets : Nat}
    (polynomialAt : Chart → Coefficients) (rootAt : Chart → LiftedPoint sheets → RootReading)
    (chart : Chart) (point : LiftedPoint sheets) (primitive : Expression (polynomialAt chart))
    (parameter : (rootAt chart point).2.parameter = (polynomialAt chart).eval point.coordinate)
    (defined : primitive.Defined point.coordinate) : Endpoint Chart sheets polynomialAt rootAt := by
  let root := rootAt chart point
  have identity := PowerIdentity.ofSquare root.2.square
  rewrite [parameter] at identity
  exact ⟨chart, point, primitive, root, rfl, parameter,
    Expression.retain primitive point.coordinate root.1 defined identity⟩

/-- The cached primitive channel at the original retained chart, point and selected root. -/
@[expose] def channel {Chart : Type} {sheets : Nat} {polynomialAt : Chart → Coefficients}
    {rootAt : Chart → LiftedPoint sheets → RootReading} (endpoint : Endpoint Chart sheets polynomialAt rootAt) :
    CoherentNamed := endpoint.denotation.channel

end Endpoint

/-- A retained finite bank of original chart-owned primitive endpoints. -/
abbrev EndpointBank (Chart : Type) (sheets count : Nat)
    (polynomialAt : Chart → Coefficients) (rootAt : Chart → LiftedPoint sheets → RootReading) :=
  Data.Vector (Endpoint Chart sheets polynomialAt rootAt) count

/-- The initial bank key of one original oriented endpoint occurrence. -/
@[expose] def edgeStart {count : Nat} (edge : OrientedEdge count) : Fin count := edge.start

/-- The final bank key of one original oriented endpoint occurrence. -/
@[expose] def edgeFinish {count : Nat} (edge : OrientedEdge count) : Fin count := edge.finish

set_option genInjectivity false in
/-- A retained algebraic endpoint boundary on an exact original finite path.

Every integer coefficient belongs to the original oriented edge occurrences
and bank keys. Keys remain separate even when base coordinates agree on
different sheets or when radicands differ. -/
structure Boundary {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (original : EndpointBank Chart sheets count polynomialAt rootAt)
    (edges : List (OrientedEdge count)) (start finish : Fin count) where
  /-- The full retained original endpoint bank. -/
  bank : EndpointBank Chart sheets count polynomialAt rootAt
  /-- The retained bank is the original owner. -/
  bank_eq : bank = original
  /-- The actual ordered original edge occurrences retained as executable data. -/
  occurrences : List (OrientedEdge count)
  /-- The retained word is the original finite path word. -/
  occurrences_eq : occurrences = edges
  /-- The exact original endpoint path in the original bank. -/
  path : PathBoundary.PathEndpoints edgeStart edgeFinish edges start finish
  /-- The computed and cached integer coefficient at every original endpoint key. -/
  coefficients : Data.Vector Int count
  /-- Each retained coefficient is the actual boundary count of these edge occurrences. -/
  coefficient_eq : ∀ index : Fin count,
    coefficients index = PathBoundary.wordBoundaryAt edgeStart edgeFinish edges index

constructive_injectivity Boundary

/-- Compute and retain the original endpoint-bank boundary coefficients once. -/
@[expose] def boundary {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (bank : EndpointBank Chart sheets count polynomialAt rootAt)
    (edges : List (OrientedEdge count)) (start finish : Fin count)
    (path : PathBoundary.PathEndpoints edgeStart edgeFinish edges start finish) : Boundary bank edges start finish :=
  let coefficients := Data.Vector.Basic.vectorOfFn
    (fun index : Fin count => PathBoundary.wordBoundaryAt edgeStart edgeFinish edges index)
  ⟨bank, rfl, edges, rfl, path, coefficients, fun index => Data.Vector.Basic.vectorOfFn_apply _ index⟩

namespace Boundary

/-- The original finite path's cached coefficient telescopes to its two original endpoint keys. -/
theorem telescopes {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {bank : EndpointBank Chart sheets count polynomialAt rootAt}
    {edges : List (OrientedEdge count)} {start finish : Fin count}
    (retained : Boundary bank edges start finish) (index : Fin count) :
    retained.coefficients index =
      PathBoundary.vertexIndicator finish index - PathBoundary.vertexIndicator start index :=
  (retained.coefficient_eq index).trans (PathBoundary.wordBoundaryAt_eq_endpoints retained.path index)

/-- A path closed at the same original lifted endpoint has every retained coefficient zero. -/
theorem closed {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {bank : EndpointBank Chart sheets count polynomialAt rootAt}
    {edges : List (OrientedEdge count)} {start : Fin count}
    (retained : Boundary bank edges start start) (index : Fin count) : retained.coefficients index = 0 := by
  rewrite [retained.telescopes index]
  ring1

/-- Reverse the original word while negating its cached coefficients by a structural vector traversal. -/
@[expose] def reverse {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {bank : EndpointBank Chart sheets count polynomialAt rootAt}
    {edges : List (OrientedEdge count)} {start finish : Fin count}
    (retained : Boundary bank edges start finish) :
    Boundary bank (edges.reverse.map OrientedEdge.reverse) finish start :=
  { bank := retained.bank
    bank_eq := retained.bank_eq
    occurrences := retained.occurrences.reverse.map OrientedEdge.reverse
    occurrences_eq := congrArg (fun word : List (OrientedEdge count) => word.reverse.map OrientedEdge.reverse)
      retained.occurrences_eq
    path := retained.path.reverse OrientedEdge.reverse (fun _ => rfl) (fun _ => rfl)
    coefficients := Data.Vector.map (fun coefficient : Int => -coefficient) retained.coefficients
    coefficient_eq := by
      intro index
      have reading := Data.Vector.Basic.map_apply (fun coefficient : Int => -coefficient) retained.coefficients index
      rewrite [retained.coefficient_eq index] at reading
      exact reading.trans (PathBoundary.wordBoundaryAt_reverse edgeStart edgeFinish OrientedEdge.reverse
        (fun _ => rfl) (fun _ => rfl) edges index).symm }

/-- Concatenate the two original bank paths and combine their actual cached coefficient vectors. -/
@[expose] def append {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {bank : EndpointBank Chart sheets count polynomialAt rootAt}
    {first second : List (OrientedEdge count)} {start middle finish : Fin count}
    (left : Boundary bank first start middle) (right : Boundary bank second middle finish) :
    Boundary bank (first ++ second) start finish :=
  { bank := left.bank
    bank_eq := left.bank_eq
    occurrences := left.occurrences ++ right.occurrences
    occurrences_eq := congrArg₂ (fun first second : List (OrientedEdge count) => first ++ second)
      left.occurrences_eq right.occurrences_eq
    path := left.path.append right.path
    coefficients := Data.Vector.zipWith (fun first second : Int => first + second) left.coefficients right.coefficients
    coefficient_eq := by
      intro index
      have reading := Data.Vector.Basic.zipWith_apply (fun first second : Int => first + second)
        left.coefficients right.coefficients index
      rewrite [left.coefficient_eq index, right.coefficient_eq index] at reading
      exact reading.trans (PathBoundary.wordBoundaryAt_append edgeStart edgeFinish first second index).symm }

/-- Different original selected sheets prevent the endpoint bank path from being a closed lift. -/
theorem sheetChanging_not_closed {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {bank : EndpointBank Chart sheets count polynomialAt rootAt}
    {edges : List (OrientedEdge count)} {start finish : Fin count}
    (_retained : Boundary bank edges start finish)
    (different : (bank start).point.sheet ≠ (bank finish).point.sheet) : start ≠ finish := by
  intro equal
  exact different (congrArg (fun index : Fin count => (bank index).point.sheet) equal)

/-- A sheet-changing path retains a nonzero finish coefficient in its original endpoint bank. -/
theorem sheetChanging_finish {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {bank : EndpointBank Chart sheets count polynomialAt rootAt}
    {edges : List (OrientedEdge count)} {start finish : Fin count}
    (retained : Boundary bank edges start finish)
    (different : (bank start).point.sheet ≠ (bank finish).point.sheet) : retained.coefficients finish = 1 := by
  have distinct := retained.sheetChanging_not_closed different
  rewrite [retained.telescopes finish]
  unfold PathBoundary.vertexIndicator
  rewrite [if_pos rfl, if_neg (fun equal => distinct equal.symm)]
  ring1

end Boundary

end Purelib.Integration.Path.Primitive.Algebraic

end

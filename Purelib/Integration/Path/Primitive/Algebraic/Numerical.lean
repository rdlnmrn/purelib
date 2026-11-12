module

public import Purelib.Integration.Path.Primitive.Algebraic
public import Purelib.Integration.Path.Primitive.Polynomial
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Approximation.Gaussian.Equivalence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Numerical primitive edges at original algebraic endpoints

Each endpoint's retained sampler realizes its exact original denotation.
Actual cell derivative residuals and finite budgets construct the integration
comparison. The endpoint realization comparison follows from the original
sampler theorem and is never supplied by the caller.
-/

public section

namespace Purelib.Integration.Path.Primitive.Algebraic

open Purelib
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Periods
open Purelib.Integration.Program.Comparison (RefinementProgram)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

namespace Endpoint

set_option genInjectivity false in
/-- The cached geometric sampler of one original algebraic endpoint channel.

The entire original endpoint remains indexed and retained. The sampler realizes
that same denotation, selected generator and process, preserving the source
primitive and its denominator guard. -/
structure Sampling {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (original : Endpoint Chart sheets polynomialAt rootAt) where
  /-- The full original chart-owned algebraic endpoint. -/
  owner : Endpoint Chart sheets polynomialAt rootAt
  /-- The retained endpoint is the original owner. -/
  owner_eq : owner = original
  /-- The computed and cached geometric sampler of the original endpoint channel. -/
  source : GeometricApproximation
  /-- The original cached numerical denotation realizes this same retained sampler. -/
  realizes : NamedEquivalent original.channel.name (PeriodMatrix.geometricNamed source).name

constructive_injectivity Sampling

/-- Cache the canonical sampler of the exact retained algebraic endpoint channel once. -/
@[expose] def sample {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (original : Endpoint Chart sheets polynomialAt rootAt) : Sampling original :=
  ⟨original, rfl, GeometricApproximation.ofNamed original.channel.name,
    PeriodMatrix.ScaledInverseCertificate.named_equivalent_geometricOfNamed original.channel⟩

/-- The canonical endpoint sampler uses the same original cached denotation. -/
theorem sample_source {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (original : Endpoint Chart sheets polynomialAt rootAt) :
    original.sample.source = GeometricApproximation.ofNamed original.channel.name := rfl

/-- The original retained endpoint channel realizes its actual cached sampler. -/
@[noinline, nospecialize] def Sampling.equivalent {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {original : Endpoint Chart sheets polynomialAt rootAt} (retained : Sampling original) :
    NamedEquivalent original.channel.name (PeriodMatrix.geometricNamed retained.source).name := retained.realizes

/-- Cache the exact sampler of a scalar polynomial primitive at its original selected-root endpoint.

The scalar equality identifies the actual retained primitive. Its numerical
comparison follows from the original polynomial-pair denotation law, so the
selected generator and all original endpoint data remain retained. -/
@[noinline, nospecialize] def sampleScalar {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (original : Endpoint Chart sheets polynomialAt rootAt) (scalar : Coefficients)
    (identity : original.primitive = Expression.scalar scalar) : Sampling original := by
  let source := GeometricApproximation.exact (scalar.eval original.point.coordinate)
  have realization : NamedEquivalent original.channel.name
      (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
        (scalar.eval original.point.coordinate)).name := by
    change NamedEquivalent original.denotation.channel.name _
    rewrite [original.denotation.channel_readback, identity]
    exact Expression.denote_scalar scalar original.point.coordinate original.root.1
  exact ⟨original, rfl, source, NamedEquivalent.trans realization
    (Approximation.Gaussian.Geometric.Coherent.Comparison.geometricExact_equivalent_exact _).symm⟩

/-- The scalar endpoint sampler retains the exact evaluation of the original scalar polynomial. -/
theorem sampleScalar_source {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    (original : Endpoint Chart sheets polynomialAt rootAt) (scalar : Coefficients)
    (identity : original.primitive = Expression.scalar scalar) :
    (original.sampleScalar scalar identity).source =
      GeometricApproximation.exact (scalar.eval original.point.coordinate) := by
  unfold sampleScalar
  rfl

/-- Derive a primitive edge between the original algebraic endpoints from actual cell-model data.

The source program, lifted endpoints, retained samplers, polynomial
primitives, derivative residual caches and finite budget are those of the
supplied models. The endpoint and integral comparisons are constructed here,
so neither conclusion is an extra premise. -/
@[noinline, nospecialize] def Sampling.edgeTo {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {start finish : Endpoint Chart sheets polynomialAt rootAt}
    (left : Sampling start) (right : Sampling finish) (program : RefinementProgram)
    (models : PrimitiveEdge.PolynomialModels start.point finish.point left.source right.source program) :
    PrimitiveEdge start.channel finish.channel :=
  models.edge.changeEndpoints start.channel finish.channel left.equivalent.symm right.equivalent.symm

/-- The original program is retained exactly by the algebraic endpoint edge adapter. -/
theorem Sampling.edgeTo_program {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}
    {start finish : Endpoint Chart sheets polynomialAt rootAt}
    (left : Sampling start) (right : Sampling finish) (program : RefinementProgram)
    (models : PrimitiveEdge.PolynomialModels start.point finish.point left.source right.source program) :
    (left.edgeTo right program models).program = program := by
  change models.edge.program = program
  exact models.edge_program

end Endpoint

end Purelib.Integration.Path.Primitive.Algebraic

end

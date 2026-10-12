module
import Test.Calculus.Jet.Progressive.TraceProgram
import Test.Approximation.Rational.SquareRoot.Radius.Scaled
import Test.Geometry.Rotations.MinkowskiPublication
import Test.Geometry.Rotations.EuclideanPublication
import Test.Data.ByteArray.UTF8
meta import Test.Meta.FunInfo
import Test.Data.Json
public import Test.Elab.ConstructiveInjectivity
import Test.Elab.ConstructorContracts
import Test.Elab.ConstructorExposure
import Test.Elab.ConstructorContexts
import Test.Elab.ConstructorNames
import Test.Elab.ConstructorDomains
public import Test.Geometry.CoordinateFormulas

public import Test.Polynomial.ProgramContracts

public import Test.Integration.CachedProgramContracts

public import Test.LinearAlgebra.Gaussian.QuadraticForms

public import Test.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
public import Test.Curves.Hyperelliptic.Integration.Preparation.Reports
public import Purelib.Topology.Surface.Sewing.AreaChainTests
public import Test.Topology.Cut.BoundaryContraction
public import Test.Riemann.JoinedCenteredAreaTests
public import Test.Integration.Path.RamifiedJoining
public import Test.Topology.Surface.Sewing.Diagnostics
public import Test.Riemann.PolynomialCurveTests
public import Test.Riemann.PolynomialPeriodTests
public import Test.LinearAlgebra.Matrix.Approximation.ScalarTailLower
public import Test.Riemann.SquareFactorAccuracyTests
public import Test.Riemann.SquareFactorCellTests
public import Test.Riemann.SquareFactorInconclusiveTests
public import Test.Riemann.SquareFactorObservationInputTests
public import Test.Integration.Algebraic.SquareFactor.Transport
public import Test.Data.Rat.Fraction.Regression
public import Test.Data.Gaussian.Regression
import Test.Data.List.Membership
public import Test.Polynomial.Dense.Gaussian.Regression
public import Test.Polynomial.Evaluation.Gaussian.NewtonResidual
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay

public import Test.Geometry.Rotations.CoordinateRepresentations

public import Test.Data.GaussianRepresentations

import Test.Algebra.Power.Gaussian
import Test.Approximation.Gaussian.Grid.Nearest
import Test.Approximation.Gaussian.Logarithm.ChartSafety
import Test.Curves.Hyperelliptic.Integration.SourceCache
import Test.Curves.Legendre.PositivityAcquisition
import Test.Curves.Legendre.PositivityObstructions
import Test.Curves.Legendre.Separated
import Test.Curves.Legendre.SignedAcquisition
import Test.Curves.Legendre.SignedGap
import Test.Data.Json.Number
import Test.Data.String.Regression
import Test.Integration.Surface.Coercivity
import Test.Measure.QuantileCongruenceCache
import Test.NumberTheory.Approximation.Homography
import Test.NumberTheory.Approximation.Publication
import Test.Polynomial.ClearanceCover
import Test.Polynomial.Enclosure
import Test.Polynomial.QuadraticBounds
import Test.Riemann.Prepared.ModelProjections
import Test.Riemann.Prepared.SubdivisionProjections
import Test.RootIsolation.SquareRoot.ExactDecision
import Test.RootIsolation.SquareRoot.LineClearance
import Test.RootIsolation.SquareRoot.Newton
import Test.RootIsolation.SquareRoot.Sidecar
import Test.Tactic.Omega
import Test.Tactic.Ring

import Test.Riemann.PreparedNormalizedEntry
import Test.Riemann.PreparedObservationRequests
import Test.Riemann.CheckedPreparationReports
import Test.Riemann.Prepared.PathExecution
import Test.Curves.Hyperelliptic.ReadingInterfaces

@[expose] public section

/-!
# Purelib regression tests

Engineering and regression modules are built through the separate Test target.
-/

module
import Purelib.Algebra.Quadratic.Pair.Coordinates
public import Purelib.Algebra.Quadratic.Pair.Prime
import Purelib.Approximation.Gaussian.Grid.Resource
public import Purelib.Approximation.Rational.Grid.Bounds
import Purelib.Approximation.Rational.QuadraticTarget.Resource
public import Purelib.Curves
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Encoding
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
public import Purelib.Data.ContinuedFraction.Matrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Fraction.NaturalDenominator
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Norm
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.Resource
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Resource
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Cancellation
public import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Data.GaussianInt.Enumeration
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Fraction.Resource
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.GaussianInt.Power
public import Purelib.Data.GaussianInt.Projective
import Purelib.Data.GaussianInt.Resource
import Purelib.Data.Int.BitWidth
import Purelib.Data.Int.Interval
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.List.Maximum
import Purelib.Data.Nat.SquareThreshold.Resource
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Resource.Clauses
import Purelib.Data.Rat.Fraction.Resource.Width
public import Purelib.Geometry
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Plane.AffineChart
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
public import Purelib.Geometry.Rotations
import Purelib.Geometry.Space.Metric
import Purelib.Geometry.Triangles.Similarity.Entries
public import Purelib.Integration.Algebraic.SquareFactor.ObservationTransport
import Purelib.Integration.Path.AreaComparison
public import Purelib.Integration.Program.Rational.Cached.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.LinearAlgebra.Coordinates3.Vector.Permutation
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Operation
public import Purelib.Measure
public import Purelib.Measure.CCL.EncodedPrefix.Variance
public import Purelib.Measure.CCL.Prefix.Cumulative
public import Purelib.Measure.CCL.Prefix.Interval.Basic
import Purelib.Measure.CCL.Prefix.Threshold.Basic
import Purelib.NumberTheory.Prime.ChebyshevSum
public import Purelib.Polynomial.Approximation.Resource.Certificate
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Resource
import Purelib.Polynomial.Dense.Gaussian.Newton.Resource
import Purelib.Polynomial.Dense.GaussianInt.Evaluation.Homogeneous.NaturalDenominator.Resource
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Horner.Pair
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation
import Purelib.Polynomial.Winding.Box.Resource
import Purelib.Polynomial.Winding.Edge.Resource
public import Purelib.RationalFunctions.Approximation.Height.Resource
public import Purelib.Riemann
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
public import Purelib.Riemann.Branches.NewtonRequestedCutBoundaryComparison
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.ReconditionedClearSheetContinuation
public import Purelib.Riemann.Integration.PreparedCompatiblePrimitives
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Integration.PreparedLiteralCenters
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
public import Purelib.Riemann.Integration.PreparedSubdivisionModels
public import Purelib.Riemann.Integration.PreparedSubedgePrimitiveContacts
public import Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedVertexConnections
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.Riemann.Paths.PreparedCoveredTraceRequest
import Purelib.Riemann.Paths.PreparedTraceEdges
public import Purelib.Riemann.Paths.RectangularCenteredTrace
public import Purelib.Riemann.Paths.RectangularSeamTraceBounds
public import Purelib.Riemann.Periods.NewtonRequestedBilinear
public import Purelib.Riemann.Periods.NewtonRequestedRemainingBilinear
public import Purelib.Riemann.Periods.PeriodCurves
public import Purelib.Riemann.Periods.PolynomialPeriodObservation
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Readings.PreparedBoundaryGluing
public import Purelib.Riemann.Readings.PrimitiveDyadicBoundary
public import Purelib.Riemann.Readings.ReconditionedDifferentialObservations
public import Purelib.Riemann.Readings.RectangularBoundaryAccuracy
import Purelib.Riemann.Readings.RectangularExteriorBoundary
public import Purelib.Riemann.Readings.RectangularRequestedClippedBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Riemann.RootContinuation.NewtonFinePhysicalExcision
public import Purelib.Riemann.RootContinuation.NewtonObservationEnergyRefinement
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonObservationPartitions
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
public import Purelib.Riemann.RootContinuation.NewtonRawOddExteriorEnergy
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
public import Purelib.Riemann.RootContinuation.NewtonStandardPairedBoundary
public import Purelib.Riemann.RootContinuation.PreparedCheckedBridgeRoots
public import Purelib.Riemann.RootContinuation.PreparedInitialRootReplay
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandArea
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBoundaryRoots
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSideTrace
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveTotals
public import Purelib.Riemann.RootContinuation.PreparedRootConnectedRefinements
public import Purelib.Riemann.RootContinuation.PreparedRootSafeReplay
public import Purelib.Riemann.RootContinuation.RequestedNewtonPairedArea
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents
public import Purelib.Riemann.RootContinuation.RootOwnerFrameReplay
public import Purelib.Riemann.RootContinuation.RootTransportReplay
public import Purelib.Riemann.RootContinuation.SquareRootDecisionLaws
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
public import Purelib.Riemann.Topology.NewtonGlobalSewnEnergy
public import Purelib.Riemann.Topology.NewtonSewnAreaComparison
import Purelib.Riemann.Topology.NewtonSewnExcision
public import Purelib.Riemann.Topology.PreparedCanonicalCycleSamples
public import Purelib.Riemann.Topology.PreparedCycleBankReplay
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Riemann.Topology.PrimitiveSurfaceLower
public import Purelib.Riemann.Transport.AdaptivePreparedBankReplay
public import Purelib.Riemann.Transport.CheckedDirectGeometryReplay
public import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
public import Purelib.Riemann.Transport.PreparedEdgeReplay
public import Purelib.Riemann.Transport.PreparedForecastReplay
public import Purelib.Riemann.Transport.PreparedGeometryReplay
public import Purelib.Riemann.Transport.PreparedSourceRefinementReplay
public import Purelib.Riemann.Transport.PreparedUniformRefinementReplay
public import Purelib.RootIsolation.Isolation.InitialExtractionFallbackReplay
import Purelib.RootIsolation.Resource.Basic
import Purelib.RootIsolation.Resource.Budget
public import Purelib.RootIsolation.Resource.Build
import Purelib.RootIsolation.Resource.Input
public import Purelib.RootIsolation.SquareRoot.Preparation.Congruence
import Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Trace
public import Purelib.RootIsolation.SquareRoot.Preparation.StationaryObstruction
public import Purelib.RootIsolation.SquareRoot.Replay.BoundedMovingReplay
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
public import Purelib.RootIsolation.SquareRoot.Replay.ReconditioningAssignmentReplay
public import Purelib.RootIsolation.SquareRoot.Replay.TerminalAcquisitionReplay
public import Purelib.RootIsolation.SquareRoot.Replay.TracedSegmentReplay
public import Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
import Purelib.RootIsolation.Subdivision.Raw.Resource.Winding
public import Purelib.Topology.Knot
public import Purelib.Topology.Surface.Sewing.Bilinear.Coverage
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Topology.Surface.Sewing.SewnEnergyBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveAnalyticControl
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.Selection
import Purelib.Topology.Surface.Word.Surgery

@[expose] public section

/-!
# Purelib reusable library

Complete reusable surface for the transition layout. Concrete examples,
regression modules, archive code, and publication claims are excluded.
-/

module

import TestPurelib.Polynomial.Winding.Circle
import TestPurelib.Polynomial.Laurent.Circle
import TestPurelib.Polynomial.Laurent.Circle.Product
import TestPurelib.Polynomial.Laurent.Circle.Deformation
import TestPurelib.Polynomial.Laurent.Circle.Transport
import TestPurelib.Polynomial.Laurent.Toeplitz
import TestPurelib.Polynomial.Laurent.Toeplitz.Product
import TestPurelib.Polynomial.Laurent.Toeplitz.Transport
import TestPurelib.Polynomial.Laurent.Toeplitz.Deformation
import TestPurelib.Polynomial.Laurent.Toeplitz.Shift
import TestPurelib.Polynomial.Laurent.Toeplitz.SmallMargin
import TestPurelib.Polynomial.Laurent.Toeplitz.Recovery
import TestPurelib.Polynomial.Recurrence.Mode.Inverse
import TestPurelib.LinearAlgebra.Matrix.Reading
import TestPurelib.RootIsolation.Multiplicity.Circle
import TestPurelib.RootIsolation.Multiplicity.Circle.Checkpoint
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Owners
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Boundary
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Family
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Factor
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Family
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bank
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Selection
import TestPurelib.RationalFunctions.Winding.Circle
import TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
import TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Reading
import TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Source
import TestPurelib.Polynomial.Dense.Roots.Tower.Leading
import TestPurelib.Polynomial.Dense.Cyclic.Observation
import Purelib.System.IO

/-!
# Linked complete rational-circle regression groups

The default run executes every circle boundary, radial inventory, quotient,
original Laurent winding/deformation, exact factor-bank and checked higher-degree construction group.
Individual selectors allow one completed group to be retained without repeating
another group while checking the same executable.
-/

open TestPurelib.RootIsolation.Multiplicity
open TestPurelib.Polynomial

/-- Execute one independent complete rational-circle regression group. -/
private def runCase (name : String) : IO Unit :=
  match name with
  | "polynomial" => Winding.Circle.run
  | "inventory" => Circle.run
  | "quotient" => TestPurelib.RationalFunctions.Winding.Circle.run
  | "laurent" => Laurent.Circle.run
  | "laurent-product" => Laurent.Circle.Product.run
  | "laurent-transport" => Laurent.Circle.Transport.run
  | "toeplitz" => Laurent.Toeplitz.run
  | "toeplitz-product" => Laurent.Toeplitz.Product.run
  | "toeplitz-transport" => Laurent.Toeplitz.Transport.run
  | "toeplitz-deformation" => Laurent.Toeplitz.Deformation.run
  | "toeplitz-shift" => Laurent.Toeplitz.Shift.run
  | "toeplitz-small-margin" => Laurent.Toeplitz.SmallMargin.run
  | "toeplitz-recovery" => Laurent.Toeplitz.Recovery.run
  | "factor-bank" => Dense.Gaussian.Multiplicity.Roots.Stages.run
  | "stages-reading" => Dense.Gaussian.Multiplicity.Roots.Stages.Reading.run
  | "stages-source" => Dense.Gaussian.Multiplicity.Roots.Stages.Source.run
  | "tower-leading" => Dense.Roots.Tower.Leading.run
  | "generator-cache" => Dense.Cyclic.Observation.run
  | "owners" => Circle.Roots.Owners.run
  | "boundary" => Circle.Roots.Boundary.run
  | "factor-reading" => Circle.Roots.Reading.Factor.run
  | "family-reading" => Circle.Roots.Reading.Family.run
  | "bank-reading" => Circle.Roots.Reading.Bank.run
  | "positive-recurrence" => Circle.Roots.Recurrence.run
  | "combination" => Circle.Roots.Recurrence.Combination.run
  | "selection" => Circle.Roots.Recurrence.Selection.run
  | "inverse-mode" => Recurrence.Mode.Inverse.run
  | "matrix-reading" => TestPurelib.LinearAlgebra.Matrix.Reading.run
  | "laurent-deformation" => Laurent.Circle.Deformation.run
  | "higher" => Circle.Checkpoint.run ".lake/circle-inventory-checkpoints/default"
  | _ => throw (IO.userError "unknown complete rational-circle regression group")

/-- Execute all retained complete-boundary and independent-winding groups. -/
private def runAll : IO Unit := do
  runCase "polynomial"
  runCase "inventory"
  runCase "quotient"
  runCase "laurent"
  runCase "laurent-product"
  runCase "laurent-transport"
  runCase "toeplitz"
  runCase "toeplitz-product"
  runCase "toeplitz-transport"
  runCase "toeplitz-deformation"
  runCase "toeplitz-shift"
  runCase "toeplitz-small-margin"
  runCase "toeplitz-recovery"
  runCase "factor-bank"
  runCase "stages-reading"
  runCase "stages-source"
  runCase "tower-leading"
  runCase "generator-cache"
  runCase "owners"
  runCase "boundary"
  runCase "factor-reading"
  runCase "family-reading"
  runCase "bank-reading"
  runCase "positive-recurrence"
  runCase "combination"
  runCase "selection"
  runCase "inverse-mode"
  runCase "matrix-reading"
  runCase "laurent-deformation"
  runCase "higher"

/-- Run every linked circle regression or one explicitly selected independent group. -/
public def main (arguments : List String) : IO Unit :=
  match arguments with
  | [] => runAll
  | ["--case", name] => runCase name
  | ["--checkpoint", directory, mode] => Circle.Checkpoint.run directory mode
  | _ => throw (IO.userError
      "expected --case polynomial|inventory|quotient|laurent|laurent-product|laurent-transport|\
        toeplitz|toeplitz-product|toeplitz-transport|toeplitz-deformation|toeplitz-shift|toeplitz-small-margin|\
        toeplitz-recovery|\
        factor-bank|stages-reading|stages-source|tower-leading|generator-cache|owners|boundary|\
        factor-reading|family-reading|bank-reading|positive-recurrence|combination|selection|\
        inverse-mode|matrix-reading|\
        laurent-deformation|higher, \
        --checkpoint DIR MODE, or no arguments")

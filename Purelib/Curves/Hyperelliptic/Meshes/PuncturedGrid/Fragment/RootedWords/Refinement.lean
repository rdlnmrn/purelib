module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Data.List.Append

/-! # Signed replacement of one original rooted-word occurrence

Finite recursion preserves every original prefix and suffix occurrence and
its existing junction certificate. The local two-piece certificates are
computed by the strict-query-cut producer, not inferred from coordinates.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {mesh : LiftedMesh vertices edges base.faces} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {original left right : LiftedFragment axes domains mesh differential count target}
variable {middle : Canonical} {middleName : Named}

/-- Splice two actual singleton words at one literal old occurrence, retaining both signed subwords.

The old RootedWord supplies every unchanged junction. The two local
certificates supply only the replacement occurrence; the actual query
name is their shared cut name. The recursion never extracts runtime data
from the Prop-valued root certificates.
-/
theorem splice
    (leftRooted : RootedWord [left] original.first original.firstName middle middleName)
    (rightRooted : RootedWord [right] middle middleName original.last original.lastName) :
    ∀ (before : List (LiftedFragment axes domains mesh differential count target))
      {after : List (LiftedFragment axes domains mesh differential count target)}
      {first last : Canonical} {firstName lastName : Named},
    RootedWord (before ++ original :: after) first firstName last lastName →
      RootedWord (before ++ [left]) first firstName middle middleName ∧
        RootedWord (right :: after) middle middleName last lastName
  | [], _, _, _, _, _, .cons _ coordinate root tail =>
      ⟨leftRooted.changeStart coordinate root, rightRooted.append tail⟩
  | _ :: before, _, _, _, _, _, .cons head coordinate root tail => by
      have retained := splice leftRooted rightRooted before tail
      exact ⟨.cons head coordinate root retained.1, retained.2⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord

end

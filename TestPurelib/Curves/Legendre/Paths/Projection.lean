module

import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Projection
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Fin
import Purelib.Data.Fin.Cases
import Purelib.Data.Vector.Dependent

/-! # A common computed chart across original regular Legendre vertices -/

namespace TestPurelib.Curves.Legendre.Paths.Projection

open Purelib.Curves.Legendre.Paths
open Purelib
open Purelib.Data

/-- Paid charts preserve both original weak comparisons with every unit reading, including real endpoint ties. -/
example (parameter : Gaussian) (first last reading : Coordinate)
    (firstPaid : Projection.slopeCost parameter < first) (lastPaid : Projection.slopeCost parameter < last)
    (nonnegative : 0 ≤ reading) (atMostOne : reading ≤ 1) :
    (parameter.re + first * parameter.im ≤ reading ↔ parameter.re + last * parameter.im ≤ reading) ∧
      (reading ≤ parameter.re + first * parameter.im ↔ reading ≤ parameter.re + last * parameter.im) :=
  Projection.reading_comparisons_of_slopeCost parameter first last reading firstPaid lastPaid nonnegative atMostOne

/-- Intrinsic regularity derives both original fixed-reading exclusions in an arbitrary paid chart. -/
example (parameter : Gaussian) (slope : Coordinate) (paid : Projection.slopeCost parameter < slope)
    (nonzero : parameter ≠ 0) (notOne : parameter ≠ 1) :
    parameter.re + slope * parameter.im ≠ 0 ∧ parameter.re + slope * parameter.im ≠ 1 :=
  Projection.separates_of_slopeCost parameter slope paid nonzero notOne

/-- The computed chart puts every original positive-imaginary vertex beyond the one reading. -/
example {count : Nat} (original : Fin count → Gaussian) (index : Fin count) (positive : 0 < (original index).im) :
    1 < (original index).re + Projection.forParameters original * (original index).im :=
  Projection.forParameters_reading_above_one original index positive

/-- The computed chart puts every original negative-imaginary vertex below the zero reading. -/
example {count : Nat} (original : Fin count → Gaussian) (index : Fin count) (negative : (original index).im < 0) :
    (original index).re + Projection.forParameters original * (original index).im < 0 :=
  Projection.forParameters_reading_below_zero original index negative

/-- Different computed finite-family charts agree on the entire branch-order record at the same original parameter. -/
example {firstCount lastCount : Nat} (first : Fin firstCount → Gaussian) (last : Fin lastCount → Gaussian)
    (firstIndex : Fin firstCount) (lastIndex : Fin lastCount) (same : first firstIndex = last lastIndex) :
    branchOrder (first firstIndex) (Projection.forParameters first) =
      branchOrder (last lastIndex) (Projection.forParameters last) :=
  branchOrder_forParameters_eq first last firstIndex lastIndex same

/-- Adding repeated vertices changes the computed slopes while retaining the complete original branch-order record. -/
example :
    Projection.forParameters (fun _ : Fin 1 => gaussian 0 1) = 2 ∧
      Projection.forParameters (fun _ : Fin 2 => gaussian 0 1) = 3 ∧
        branchOrder (gaussian 0 1) 2 = branchOrder (gaussian 0 1) 3 := by
  refine ⟨by decide, by decide, ?_⟩
  exact branchOrder_eq_of_slopeCost _ _ _ (by decide) (by decide)

/-- The two actual original frame families read the same logical branch at every position in these paid charts. -/
example {parameter : Gaussian} {left right : Frame parameter} {first last : Coordinate}
    (source : left.InChart first) (target : right.InChart last)
    (firstPaid : Projection.slopeCost parameter < first) (lastPaid : Projection.slopeCost parameter < last)
    (position : Fin 3) : left.labels.backward (left.projectionOrder.forward position) =
      right.labels.backward (right.projectionOrder.forward position) :=
  source.logicalOrder_eq target firstPaid lastPaid position

/-- Three original regular vertices whose separately selected charts disagree. -/
def parameters : Fin 3 → Gaussian :=
  Data.Fin.cases (gaussian (1 / 2) 0)
    (fun rest => Data.Fin.cases (gaussian 0 1) (fun _ => gaussian 1 (-1)) rest)

/-- Every retained vertex excludes the singular value zero. -/
theorem nonzero (index : Fin 3) : parameters index ≠ 0 := by
  rcases Fin.Cases.three index with atZero | atOne | atTwo <;> subst index <;> decide

/-- Every retained vertex excludes the singular value one. -/
theorem notOne (index : Fin 3) : parameters index ≠ 1 := by
  rcases Fin.Cases.three index with atZero | atOne | atTwo <;> subst index <;> decide

/-- The original frames are materialized once with their original dependent vertex indices. -/
def frames : Vector.DependentVector (fun index => Frame (parameters index)) :=
  Frame.ofParameters parameters nonzero notOne

/-- The individual point algorithm uses different directions at these retained vertices. -/
example : projectionSlope (parameters 0) = 0 ∧ projectionSlope (parameters 1) = 2 := by decide

/-- The whole finite family computes the single exact common slope three. -/
example : Projection.forParameters parameters = 3 := by decide

/-- The displayed common slope separates the real midpoint and both exceptional imaginary readings. -/
example :
    [(branchProjection (parameters 0) 1 (Projection.forParameters parameters)).re,
      (branchProjection (parameters 1) 1 (Projection.forParameters parameters)).re,
      (branchProjection (parameters 2) 1 (Projection.forParameters parameters)).re] = [1 / 2, 3, -2] := by decide

/-- The first original stored frame retains that computed slope. -/
example : (frames.get 0).projectionSlope = 3 := by
  dsimp only [frames]
  rewrite [Frame.ofParameters_slope]
  decide

/-- Any two original stored frames agree on their computed chart. -/
example (left right : Fin 3) : (frames.get left).projectionSlope = (frames.get right).projectionSlope :=
  Frame.ofParameters_commonSlope parameters nonzero notOne left right

/-- The real midpoint retains its original moving-branch center with the radius paid in the common chart. -/
example : ((frames.get 0).chamber.owner ((frames.get 0).labels.forward 1)).box.xLower = 4 / 9 := by
  dsimp only [frames]
  rewrite [Frame.ofParameters_owner_box]
  decide

/-- An empty parameter family still computes a positive chart without inventing a vertex. -/
example : Projection.forParameters (fun index : Fin 0 => Fin.elim0 index) = 1 := rfl

/-- Repeated original vertices are allowed and keep the same computed family chart. -/
example : Projection.forParameters (fun _ : Fin 2 => gaussian 0 1) = 3 := by decide

/-- The public constructor proves common-chart agreement for every finite regular family. -/
example {count : Nat} (original : Fin count → Gaussian)
    (excludesZero : ∀ index, original index ≠ 0) (excludesOne : ∀ index, original index ≠ 1)
    (left right : Fin count) :
    ((Frame.ofParameters original excludesZero excludesOne).get left).projectionSlope =
      ((Frame.ofParameters original excludesZero excludesOne).get right).projectionSlope :=
  Frame.ofParameters_commonSlope original excludesZero excludesOne left right

end TestPurelib.Curves.Legendre.Paths.Projection

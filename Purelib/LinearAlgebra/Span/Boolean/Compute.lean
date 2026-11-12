module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
public import Purelib.Data.List.Map
public import Purelib.Data.List.Nodup
import Purelib.Data.Vector.Boolean.Basic
import Purelib.LinearAlgebra.Span.Boolean.Basic
public import Purelib.LinearAlgebra.Span.Boolean.Search

open Purelib.Data.Vector.Boolean

public section

/-!
# Finite Boolean spans with retained word witnesses

This module incrementally spans one supplied finite list of fixed-length
Boolean vectors under XOR.  It never forms a function space or an ambient
infinite vector space.  Every distinct image vector retains a Boolean word
witness; the result also caches closure, completeness, duplicate-freeness,
rank, and the exact power-of-two length formula.
-/

namespace Purelib.LinearAlgebra.Span.Boolean.Compute

open Purelib
open Purelib.LinearAlgebra.Span

/-- A retained entry remains a member after prepending false to every generator word. -/
private theorem falseMap_mem {width : Nat} {generator : Data.Vector.Boolean width}
    {generators : List (Data.Vector.Boolean width)} {entry : Basic.Entry generators}
    {entries : List (Basic.Entry generators)} (member : entry ∈ entries) :
    Basic.prependFalse generator entry ∈ entries.map (Basic.prependFalse generator) :=
  Data.List.Map.mem_map.mpr ⟨entry, member, rfl⟩

/-- A retained entry remains a member after prepending true to every generator word. -/
private theorem trueMap_mem {width : Nat} {generator : Data.Vector.Boolean width}
    {generators : List (Data.Vector.Boolean width)} {entry : Basic.Entry generators}
    {entries : List (Basic.Entry generators)} (member : entry ∈ entries) :
    Basic.prependTrue generator entry ∈ entries.map (Basic.prependTrue generator) :=
  Data.List.Map.mem_map.mpr ⟨entry, member, rfl⟩

/-- Incrementally compute the distinct XOR image and one Boolean word for
every image.

A dependent generator leaves the rank unchanged; an independent
generator produces a certified disjoint doubling. -/
@[expose] def compute {width : Nat} :
    (generators : List (Data.Vector.Boolean width)) → Basic.Result generators
  | [] =>
      let identity : Basic.Entry ([] : List (Data.Vector.Boolean width)) :=
        { vector := Basic.zero width
          choices := []
          choices_length := rfl
          evaluates := rfl }
      { rank := 0
        entries := [identity]
        vectors_nodup := by
          apply List.pairwise_cons.mpr
          exact ⟨(by intro value member; nomatch member), List.Pairwise.nil⟩
        length_eq := rfl
        complete := by
          intro choices lengthZero
          cases choices with
          | nil => exact ⟨identity, List.mem_cons_self, rfl⟩
          | cons _head _tail => nomatch lengthZero
        closed := by
          intro left leftMember right rightMember
          have leftEqual := Data.List.Membership.mem_singleton.mp leftMember
          have rightEqual := Data.List.Membership.mem_singleton.mp rightMember
          subst left
          subst right
          exact ⟨identity, List.mem_cons_self, Basic.xor_self (Basic.zero
            width)⟩ }
  | generator :: generators =>
      let previous := Compute.compute generators
      let falseEntries := previous.entries.map (Basic.prependFalse generator)
      match found : Search.search generator previous.entries with
      | Search.found generatorEntry generatorMember generatorVector =>
          { rank := previous.rank
            entries := falseEntries
            vectors_nodup := by
              rw [Basic.falseVectors]
              exact previous.vectors_nodup
            length_eq := by
              rw [Data.List.Map.length_map]
              exact previous.length_eq
            complete := by
              intro choices choicesLength
              cases choices with
              | nil => nomatch choicesLength
              | cons selected tailChoices =>
                  have tailLength : tailChoices.length = generators.length :=
                    Nat.succ.inj choicesLength
                  rcases previous.complete tailChoices tailLength with
                    ⟨tailEntry, tailMember, tailEvaluation⟩
                  cases selected with
                  | false =>
                      exact ⟨Basic.prependFalse generator tailEntry,
                        falseMap_mem tailMember, tailEvaluation⟩
                  | true =>
                      rcases previous.closed tailEntry tailMember
                        generatorEntry generatorMember with
                        ⟨output, outputMember, outputEquation⟩
                      refine ⟨Basic.prependFalse generator output,
                        falseMap_mem outputMember, ?_⟩
                      change Basic.xor generator (Basic.evaluate tailChoices generators) =
                        output.vector
                      rw [tailEvaluation, ← generatorVector]
                      exact (Basic.xor_comm generatorEntry.vector
                        tailEntry.vector).trans outputEquation
            closed := by
              intro left leftMember right rightMember
              rcases Data.List.Map.mem_map.mp leftMember with
                ⟨leftSource, leftSourceMember, leftEqual⟩
              rcases Data.List.Map.mem_map.mp rightMember with
                ⟨rightSource, rightSourceMember, rightEqual⟩
              subst left
              subst right
              rcases previous.closed leftSource leftSourceMember
                rightSource rightSourceMember with
                ⟨output, outputMember, outputEquation⟩
              exact ⟨Basic.prependFalse generator output,
                falseMap_mem outputMember, outputEquation⟩ }
      | Search.absent generatorAbsent =>
          let trueEntries := previous.entries.map (Basic.prependTrue generator)
          { rank := previous.rank + 1
            entries := falseEntries ++ trueEntries
            vectors_nodup := by
              rw [Data.List.Map.map_append, Basic.falseVectors, Basic.trueVectors]
              apply Data.List.Nodup.nodup_append previous.vectors_nodup
                (Data.List.Nodup.nodup_map_of_injective
                  (Basic.xor_left_injective generator) previous.vectors_nodup)
              intro leftVector leftVectorMember rightVector rightVectorMember
                equal
              rcases Data.List.Map.mem_map.mp leftVectorMember with
                ⟨leftEntry, leftEntryMember, leftEntryEqual⟩
              rcases Data.List.Map.mem_map.mp rightVectorMember with
                ⟨rightSourceVector, rightSourceVectorMember,
                  rightSourceEqual⟩
              rcases Data.List.Map.mem_map.mp rightSourceVectorMember with
                ⟨rightEntry, rightEntryMember, rightEntryEqual⟩
              have collision : leftEntry.vector =
                  Basic.xor generator rightEntry.vector := by
                calc
                  leftEntry.vector = leftVector := leftEntryEqual
                  _ = rightVector := equal
                  _ = Basic.xor generator rightSourceVector := rightSourceEqual.symm
                  _ = Basic.xor generator rightEntry.vector := by
                    rw [rightEntryEqual]
              rcases previous.closed leftEntry leftEntryMember
                rightEntry rightEntryMember with
                ⟨output, outputMember, outputEquation⟩
              apply generatorAbsent output outputMember
              exact ((Basic.generator_eq_xor_of_eq_xor collision).trans
                outputEquation).symm
            length_eq := by
              rw [Data.List.Append.length_append, Data.List.Map.length_map, Data.List.Map.length_map,
                previous.length_eq, Nat.pow_succ, Nat.mul_two]
            complete := by
              intro choices choicesLength
              cases choices with
              | nil => nomatch choicesLength
              | cons selected tailChoices =>
                  have tailLength : tailChoices.length = generators.length :=
                    Nat.succ.inj choicesLength
                  rcases previous.complete tailChoices tailLength with
                    ⟨tailEntry, tailMember, tailEvaluation⟩
                  cases selected with
                  | false =>
                      exact ⟨Basic.prependFalse generator tailEntry,
                        List.mem_append_left _ (falseMap_mem tailMember),
                        tailEvaluation⟩
                  | true =>
                      refine ⟨Basic.prependTrue generator tailEntry,
                        List.mem_append_right _ (trueMap_mem tailMember), ?_⟩
                      change Basic.xor generator (Basic.evaluate tailChoices generators) =
                        Basic.xor generator tailEntry.vector
                      rw [tailEvaluation]
            closed := by
              intro left leftMember right rightMember
              have leftCases := Data.List.Membership.mem_append.mp leftMember
              have rightCases := Data.List.Membership.mem_append.mp rightMember
              rcases leftCases with leftFalse | leftTrue
              · rcases Data.List.Map.mem_map.mp leftFalse with
                  ⟨leftSource, leftSourceMember, leftEqual⟩
                subst left
                rcases rightCases with rightFalse | rightTrue
                · rcases Data.List.Map.mem_map.mp rightFalse with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  exact ⟨Basic.prependFalse generator output,
                    List.mem_append_left _ (falseMap_mem outputMember),
                    outputEquation⟩
                · rcases Data.List.Map.mem_map.mp rightTrue with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  refine ⟨Basic.prependTrue generator output,
                    List.mem_append_right _ (trueMap_mem outputMember), ?_⟩
                  change Basic.xor leftSource.vector
                    (Basic.xor generator rightSource.vector) =
                      Basic.xor generator output.vector
                  rw [← outputEquation, ← Basic.xor_assoc,
                    Basic.xor_comm leftSource.vector generator, Basic.xor_assoc]
              · rcases Data.List.Map.mem_map.mp leftTrue with
                  ⟨leftSource, leftSourceMember, leftEqual⟩
                subst left
                rcases rightCases with rightFalse | rightTrue
                · rcases Data.List.Map.mem_map.mp rightFalse with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  refine ⟨Basic.prependTrue generator output,
                    List.mem_append_right _ (trueMap_mem outputMember), ?_⟩
                  change Basic.xor (Basic.xor generator leftSource.vector)
                    rightSource.vector = Basic.xor generator output.vector
                  rw [← outputEquation, Basic.xor_assoc]
                · rcases Data.List.Map.mem_map.mp rightTrue with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  refine ⟨Basic.prependFalse generator output,
                    List.mem_append_left _ (falseMap_mem outputMember), ?_⟩
                  change Basic.xor (Basic.xor generator leftSource.vector)
                    (Basic.xor generator rightSource.vector) = output.vector
                  rw [← outputEquation]
                  calc
                    Basic.xor (Basic.xor generator leftSource.vector)
                        (Basic.xor generator rightSource.vector) =
                      Basic.xor (Basic.xor (Basic.xor
                        generator leftSource.vector) generator)
                        rightSource.vector :=
                          (Basic.xor_assoc (Basic.xor generator
                            leftSource.vector)
                            generator rightSource.vector).symm
                    _ = Basic.xor (Basic.xor generator
                        (Basic.xor generator leftSource.vector))
                          rightSource.vector := by
                            rw [Basic.xor_comm
                              (Basic.xor generator leftSource.vector) generator]
                    _ = Basic.xor (Basic.xor (Basic.xor
                      generator generator)
                        leftSource.vector) rightSource.vector :=
                      congrArg (fun vector : Data.Vector.Boolean width =>
                        Basic.xor vector rightSource.vector)
                        (Basic.xor_assoc generator generator
                          leftSource.vector).symm
                    _ = Basic.xor leftSource.vector rightSource.vector := by
                      rw [Basic.xor_self, Basic.zero_xor] }

end Purelib.LinearAlgebra.Span.Boolean.Compute

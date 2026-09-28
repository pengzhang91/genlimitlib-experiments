import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set Filter
open GenLimit.KleinbergWei

namespace S2BProof

open Stage3S2B

private def candidate (n : ℕ) : ℕ := 2 * n + 3

private theorem candidate_injective : Function.Injective candidate := by
  intro a b h
  dsimp [candidate] at h
  omega

private theorem candidate_ordinary (n : ℕ) : candidate n ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  dsimp [candidate] at hk
  cases k with
  | zero => omega
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, by rw [pow_succ]; omega⟩
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      rw [← hk] at hodd
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff] at hodd
      omega

private def forbidden {t : ℕ} (x : Fin t → ℕ) (q : Fin t → Option ℕ)
    (y : Fin t → ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ.image x) ∪
    (Finset.univ.biUnion fun i => (q i).toFinset) ∪
    (Finset.univ.image y)

private theorem exists_fresh {t : ℕ} (x : Fin t → ℕ) (q : Fin t → Option ℕ)
    (y : Fin t → ℕ) : ∃ n, candidate n ∉ forbidden x q y := by
  classical
  obtain ⟨z, ⟨n, rfl⟩, hn⟩ :=
    (Set.infinite_range_of_injective candidate_injective).exists_not_mem_finset
      (forbidden x q y)
  exact ⟨n, hn⟩

private noncomputable def freshIndex {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  Nat.find (exists_fresh x q y)

private noncomputable def adaptivePresenter : CausalPresenter where
  next t x q _ y := if Even t then 2 ^ (t / 2) else candidate (freshIndex x q y)

private structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

private def Hist.nil : Hist 0 where
  x := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0

private def Hist.snoc {t : ℕ} (h : Hist t) (x : ℕ) (q : Option ℕ)
    (a : Option Bool) (y : ℕ) : Hist (t + 1) where
  x := Fin.lastCases x h.x
  q := Fin.lastCases q h.q
  a := Fin.lastCases a h.a
  y := Fin.lastCases y h.y

private noncomputable def build (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => Hist.nil
  | t + 1 =>
      let h := build gen t
      let x := adaptivePresenter.next t h.x h.q h.a h.y
      let xs : Fin (t + 1) → ℕ := Fin.lastCases x h.x
      let q := gen.query t xs h.a
      let a := match q with
        | none => none
        | some z => some (membershipAnswer
            (core ∪ {z | ∃ i : Fin (t + 1), xs i = z}) z)
      let y := gen.output t xs (Fin.lastCases a h.a)
      h.snoc x q a y

private noncomputable def diagonalTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (build gen (t + 1)).x (Fin.last t)
  query t := (build gen (t + 1)).q (Fin.last t)
  answer t := (build gen (t + 1)).a (Fin.last t)
  output t := (build gen (t + 1)).y (Fin.last t)

private noncomputable def diagonalTarget (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ r, (diagonalTranscript gen).presentation (2 * r + 1) = z}


private theorem build_succ_prefix (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen (t + 1)).x i.castSucc = (build gen t).x i ∧
    (build gen (t + 1)).q i.castSucc = (build gen t).q i ∧
    (build gen (t + 1)).a i.castSucc = (build gen t).a i ∧
    (build gen (t + 1)).y i.castSucc = (build gen t).y i := by
  simp [build, Hist.snoc]

private theorem transcript_build_prefix (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (diagonalTranscript gen).presentation i = (build gen t).x i ∧
    (diagonalTranscript gen).query i = (build gen t).q i ∧
    (diagonalTranscript gen).answer i = (build gen t).a i ∧
    (diagonalTranscript gen).output i = (build gen t).y i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [diagonalTranscript, build, Hist.snoc]
      · rcases ih j with ⟨hx, hq, ha, hy⟩
        rcases build_succ_prefix gen t j with ⟨hx', hq', ha', hy'⟩
        simpa only [Fin.coe_castSucc] using
          ⟨hx.trans hx'.symm, hq.trans hq'.symm, ha.trans ha'.symm, hy.trans hy'.symm⟩

private theorem build_succ_last_x (gen : FeedbackGenerator) (t : ℕ) :
    (build gen (t + 1)).x (Fin.last t) =
      adaptivePresenter.next t (build gen t).x (build gen t).q
        (build gen t).a (build gen t).y := by
  rfl

private theorem presented_by_diagonal (gen : FeedbackGenerator) :
    PresentedBy adaptivePresenter (diagonalTranscript gen) := by
  intro t
  have hp := transcript_build_prefix gen t
  have hx : (fun i : Fin t => (diagonalTranscript gen).presentation i) = (build gen t).x :=
    funext fun i => (hp i).1
  have hq : (fun i : Fin t => (diagonalTranscript gen).query i) = (build gen t).q :=
    funext fun i => (hp i).2.1
  have ha : (fun i : Fin t => (diagonalTranscript gen).answer i) = (build gen t).a :=
    funext fun i => (hp i).2.2.1
  have hy : (fun i : Fin t => (diagonalTranscript gen).output i) = (build gen t).y :=
    funext fun i => (hp i).2.2.2
  rw [hx, hq, ha, hy]
  exact build_succ_last_x gen t

private theorem presentation_even (gen : FeedbackGenerator) (r : ℕ) :
    (diagonalTranscript gen).presentation (2 * r) = 2 ^ r := by
  rw [presented_by_diagonal gen]
  simp [adaptivePresenter]

private theorem presentation_odd (gen : FeedbackGenerator) (r : ℕ) :
    (diagonalTranscript gen).presentation (2 * r + 1) =
      candidate (freshIndex
        (fun i : Fin (2 * r + 1) => (diagonalTranscript gen).presentation i)
        (fun i : Fin (2 * r + 1) => (diagonalTranscript gen).query i)
        (fun i : Fin (2 * r + 1) => (diagonalTranscript gen).output i)) := by
  rw [presented_by_diagonal gen]
  simp [adaptivePresenter]

end S2BProof

open Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  sorry

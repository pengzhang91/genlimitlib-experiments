import Section4.Staircase
import Section4.StaircasePareto
import Mathlib.Data.ENat.Lattice

namespace Section4.Staircase.Family

open Section4.StaircasePareto

variable (F : Family)

/-- The error-set cardinality is exactly the displayed binary-schedule formula. -/
theorem mistakeCount_eq_scheduleMistakes (σ : ℕ → Bool) (i : ℕ) :
    mistakeCount σ i = scheduleMistakes σ i := by
  classical
  have hfilter : (Finset.range i).filter (Charged σ i) =
      (Finset.range i).filter (fun k => σ k = true) := by
    apply Finset.filter_congr
    intro k hk
    have hki := Finset.mem_range.mp hk
    simp [Charged, hki, Nat.ne_of_lt hki]
  unfold mistakeCount errorIndices scheduleMistakes prefixCount
  rw [Finset.range_add_one, Finset.filter_insert, hfilter]
  cases hσ : σ i <;> simp [Charged, hσ, Finset.mem_filter, Finset.mem_range]

/-- Dominance means improvement of both targetwise worst-case bounds, including
infinite coordinates (which have no finite bound). -/
def Dominates (G H : Generator) : Prop :=
  (∀ i m, F.MistakeBound H i m → F.MistakeBound G i m) ∧
  (∀ i d, F.DeadlineBound H i d → F.DeadlineBound G i d)

def SameProfile (G H : Generator) : Prop := F.Dominates G H ∧ F.Dominates H G

def ParetoMinimal (G : Generator) : Prop :=
  Fresh G ∧ ∀ H, Fresh H → F.Dominates H G → F.Dominates G H

theorem dominates_refl (G : Generator) : F.Dominates G G :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem dominates_trans {G H K : Generator}
    (hGH : F.Dominates G H) (hHK : F.Dominates H K) : F.Dominates G K :=
  ⟨fun i m h => hGH.1 i m (hHK.1 i m h), fun i d h => hGH.2 i d (hHK.2 i d h)⟩

theorem exists_dominating_schedule (G : Generator) (hf : Fresh G) :
    ∃ σ, F.Dominates (F.scheduleGenerator σ) G := by
  obtain ⟨σ,hσ⟩ := F.arbitrary_generator_domination G hf
  refine ⟨σ,⟨?_,?_⟩⟩
  · intro i m hm
    exact (F.schedule_mistakeBound_iff σ i m).mpr ((hσ i).1 m hm)
  · intro i d hd
    exact (F.schedule_deadlineBound_iff σ i d).mpr ((hσ i).2 d hd)

theorem schedule_pareto_minimal (σ : ℕ → Bool) : F.ParetoMinimal (F.scheduleGenerator σ) := by
  refine ⟨F.schedule_fresh σ,?_⟩
  intro G hf hG
  obtain ⟨τ,hτ⟩ := F.exists_dominating_schedule G hf
  have hcomp := F.dominates_trans hτ hG
  have heq : τ = σ := by
    apply schedule_eq_of_mistakes_le
    intro i
    rw [← mistakeCount_eq_scheduleMistakes, ← mistakeCount_eq_scheduleMistakes]
    exact (F.schedule_mistakeBound_iff τ i _).mp
      (hcomp.1 i _ (F.schedule_mistakeBound σ i))
  simpa [heq] using hτ

/-- Completeness: the Pareto-minimal profiles of arbitrary fresh deterministic
ordered-history generators are precisely the binary-schedule profiles. -/
theorem pareto_iff_schedule_profile (G : Generator) (hf : Fresh G) :
    F.ParetoMinimal G ↔ ∃ σ, F.SameProfile G (F.scheduleGenerator σ) := by
  constructor
  · intro hG
    obtain ⟨σ,hσ⟩ := F.exists_dominating_schedule G hf
    exact ⟨σ,hG.2 _ (F.schedule_fresh σ) hσ,hσ⟩
  · rintro ⟨σ,hGσ,hσG⟩
    refine ⟨hf,?_⟩
    intro H hH hHG
    have hHσ := F.dominates_trans hHG hGσ
    have hσH := (F.schedule_pareto_minimal σ).2 H hH hHσ
    exact F.dominates_trans hGσ hσH

/-- Every arbitrary positive block-size sequence is represented. -/
def ofBlocks (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) : Family where
  size i := ∑ k ∈ Finset.range (i+1), a k
  positive := by simpa using ha 0
  increasing := by
    apply strictMono_nat_of_lt_succ
    intro i
    simp only [Finset.sum_range_succ]
    have := ha (i+1)
    omega

/-- Actual worst-case number of mistakes, as an extended natural number.
Taking the supremum over all legal finite histories counts every possible
finite initial segment of an injective positive stream. -/
noncomputable def worstMistakes (G : Generator) (i : ℕ) : ℕ∞ :=
  ⨆ (h : History) (_ : F.Legal i h), ((F.mistakeTimes G i h).card : ℕ∞)

/-- Exact uniform convergence deadline: the supremum of one plus every
possible error time, with supremum of the empty set equal to zero. -/
noncomputable def worstDeadline (G : Generator) (i : ℕ) : ℕ∞ := by
  classical
  exact ⨆ (h : History) (_ : F.Legal i h),
    if G h ∈ F.target i then 0 else (h.length + 1 : ℕ)

theorem worstMistakes_le_iff (G : Generator) (i m : ℕ) :
    F.worstMistakes G i ≤ (m : ℕ∞) ↔ F.MistakeBound G i m := by
  simp [worstMistakes, MistakeBound, iSup_le_iff]

theorem worstDeadline_le_iff (G : Generator) (i d : ℕ) :
    F.worstDeadline G i ≤ (d : ℕ∞) ↔ F.DeadlineBound G i d := by
  classical
  simp only [worstDeadline, iSup_le_iff]
  constructor
  · intro hw h hl hd
    by_contra he
    have hh := hw h hl
    simp only [if_neg he, ENat.coe_le_coe] at hh
    omega
  · intro hd h hl
    by_cases hv : G h ∈ F.target i
    · simp [hv]
    · simp only [if_neg hv, ENat.coe_le_coe]
      have hn : ¬ d ≤ h.length := fun h => hv (hd _ hl h)
      omega

theorem schedule_exact_mistakes (σ : ℕ → Bool) (i : ℕ) :
    F.worstMistakes (F.scheduleGenerator σ) i = (mistakeCount σ i : ℕ∞) := by
  apply le_antisymm
  · exact (F.worstMistakes_le_iff _ _ _).mpr (F.schedule_mistakeBound σ i)
  · classical
    have hsubset := F.charged_times_subset (i := i) (fun k hk => F.schedule_canonical_error σ hk)
    have hcard : mistakeCount σ i ≤
        (F.mistakeTimes (F.scheduleGenerator σ) i (F.canonical i)).card := by
      unfold mistakeCount
      rw [← Finset.card_image_of_injective _ F.increasing.injective]
      exact Finset.card_le_card hsubset
    exact (ENat.coe_le_coe.mpr hcard).trans
      (le_iSup_of_le (F.canonical i) (le_iSup_of_le (F.canonical_legal i) le_rfl))

theorem schedule_exact_deadline (σ : ℕ → Bool) (i : ℕ) :
    F.worstDeadline (F.scheduleGenerator σ) i = (F.deadline σ i : ℕ∞) := by
  classical
  apply le_antisymm
  · exact (F.worstDeadline_le_iff _ _ _).mpr (F.schedule_deadlineBound σ i)
  · by_cases hne : (errorIndices σ i).Nonempty
    · obtain ⟨k,hk,heq⟩ := Finset.exists_mem_eq_sup (errorIndices σ i) hne (fun k => F.size k + 1)
      change (((errorIndices σ i).sup (fun k => F.size k + 1) : ℕ) : ℕ∞) ≤ _
      rw [heq]
      have hc := (mem_errorIndices σ i k).mp hk
      have he := F.schedule_canonical_error σ hc
      have hl := F.canonical_legal_of_le (charged_le hc)
      have hh : ((F.size k + 1 : ℕ) : ℕ∞) =
          (if F.scheduleGenerator σ (F.canonical k) ∈ F.target i then 0 else ((F.canonical k).length + 1 : ℕ)) := by
        simp [he]
      rw [hh]
      exact le_iSup_of_le (F.canonical k) (le_iSup_of_le hl (by simp [he]))
    · have hz : errorIndices σ i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [deadline,hz]


theorem enat_le_of_nat_bounds {a b : ℕ∞}
    (h : ∀ n : ℕ, b ≤ n → a ≤ n) : a ≤ b := by
  by_cases hb : b = ⊤
  · simp [hb]
  · obtain ⟨n,rfl⟩ := ENat.ne_top_iff_exists.mp hb
    exact h n le_rfl

/-- The bound-predicate order is exactly the manuscript's coordinatewise
order on extended-natural worst-case mistake and deadline profiles. -/
theorem dominates_iff (G H : Generator) : F.Dominates G H ↔
    (∀ i, F.worstMistakes G i ≤ F.worstMistakes H i) ∧
    (∀ i, F.worstDeadline G i ≤ F.worstDeadline H i) := by
  constructor
  · intro h
    constructor
    · intro i
      apply enat_le_of_nat_bounds
      intro m hm
      exact (F.worstMistakes_le_iff _ _ _).mpr (h.1 i m ((F.worstMistakes_le_iff _ _ _).mp hm))
    · intro i
      apply enat_le_of_nat_bounds
      intro d hd
      exact (F.worstDeadline_le_iff _ _ _).mpr (h.2 i d ((F.worstDeadline_le_iff _ _ _).mp hd))
  · intro h
    constructor
    · intro i m hm
      exact (F.worstMistakes_le_iff _ _ _).mp ((h.1 i).trans ((F.worstMistakes_le_iff _ _ _).mpr hm))
    · intro i d hd
      exact (F.worstDeadline_le_iff _ _ _).mp ((h.2 i).trans ((F.worstDeadline_le_iff _ _ _).mpr hd))

/-- The full main-text theorem, with actual generators and actual
extended-natural worst-case guarantees. -/
theorem exact_staircase_frontier :
    (∀ σ : ℕ → Bool, Fresh (F.scheduleGenerator σ) ∧
      (∀ i, F.worstMistakes (F.scheduleGenerator σ) i = (mistakeCount σ i : ℕ∞) ∧
        F.worstDeadline (F.scheduleGenerator σ) i = (F.deadline σ i : ℕ∞)) ∧
      F.ParetoMinimal (F.scheduleGenerator σ)) ∧
    (∀ G : Generator, Fresh G → ∃ σ : ℕ → Bool, ∀ i,
      (mistakeCount σ i : ℕ∞) ≤ F.worstMistakes G i ∧
      (F.deadline σ i : ℕ∞) ≤ F.worstDeadline G i) ∧
    (∀ G : Generator, Fresh G → (F.ParetoMinimal G ↔
      ∃ σ : ℕ → Bool, F.SameProfile G (F.scheduleGenerator σ))) := by
  refine ⟨?_,?_,?_⟩
  · intro σ
    exact ⟨F.schedule_fresh σ, fun i => ⟨F.schedule_exact_mistakes σ i,
      F.schedule_exact_deadline σ i⟩, F.schedule_pareto_minimal σ⟩
  · intro G hf
    obtain ⟨σ,hσ⟩ := F.exists_dominating_schedule G hf
    have h := (F.dominates_iff _ _).mp hσ
    exact ⟨σ,fun i => ⟨by simpa only [F.schedule_exact_mistakes] using h.1 i,
      by simpa only [F.schedule_exact_deadline] using h.2 i⟩⟩
  · exact fun G hf => F.pareto_iff_schedule_profile G hf

end Section4.Staircase.Family

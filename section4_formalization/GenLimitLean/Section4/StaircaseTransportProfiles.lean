import Section4.StaircaseTransport

namespace Section4.Staircase.Realization

variable {X : Type*} (R : Realization X)

noncomputable def worstMistakes (G : GType (X := X)) (i : ℕ) : ℕ∞ :=
  ⨆ (h : List X) (_ : R.Legal i h), ((R.mistakeTimes G i h).card : ℕ∞)

noncomputable def worstDeadline (G : GType (X := X)) (i : ℕ) : ℕ∞ := by
  classical
  exact ⨆ (h : List X) (_ : R.Legal i h),
    if G h ∈ R.target i then 0 else (h.length + 1 : ℕ)

theorem worstMistakes_le_iff (G : GType (X := X)) (i m : ℕ) :
    R.worstMistakes G i ≤ (m : ℕ∞) ↔ R.MistakeBound G i m := by
  simp [worstMistakes,MistakeBound,iSup_le_iff]

theorem worstDeadline_le_iff (G : GType (X := X)) (i d : ℕ) :
    R.worstDeadline G i ≤ (d : ℕ∞) ↔ R.DeadlineBound G i d := by
  classical
  simp only [worstDeadline,iSup_le_iff]
  constructor
  · intro hw h hl hd
    by_contra he
    have hh := hw h hl
    simp only [if_neg he,ENat.coe_le_coe] at hh
    omega
  · intro hd h hl
    by_cases hv : G h ∈ R.target i
    · simp [hv]
    · simp only [if_neg hv,ENat.coe_le_coe]
      have hn : ¬ d ≤ h.length := fun h => hv (hd _ hl h)
      omega

theorem lift_worstMistakes (G : Generator) (i : ℕ) :
    R.worstMistakes (R.liftGenerator G) i = R.family.worstMistakes G i := by
  apply le_antisymm <;> apply Family.enat_le_of_nat_bounds
  · intro m hm
    exact (R.worstMistakes_le_iff _ _ _).mpr
      ((R.lift_mistakeBound_iff _ _ _).mpr ((R.family.worstMistakes_le_iff _ _ _).mp hm))
  · intro m hm
    exact (R.family.worstMistakes_le_iff _ _ _).mpr
      ((R.lift_mistakeBound_iff _ _ _).mp ((R.worstMistakes_le_iff _ _ _).mp hm))

theorem lift_worstDeadline (G : Generator) (i : ℕ) :
    R.worstDeadline (R.liftGenerator G) i = R.family.worstDeadline G i := by
  apply le_antisymm <;> apply Family.enat_le_of_nat_bounds
  · intro d hd
    exact (R.worstDeadline_le_iff _ _ _).mpr
      ((R.lift_deadlineBound_iff _ _ _).mpr ((R.family.worstDeadline_le_iff _ _ _).mp hd))
  · intro d hd
    exact (R.family.worstDeadline_le_iff _ _ _).mpr
      ((R.lift_deadlineBound_iff _ _ _).mp ((R.worstDeadline_le_iff _ _ _).mp hd))

theorem schedule_exact_mistakes (σ : ℕ → Bool) (i : ℕ) :
    R.worstMistakes (R.scheduleGenerator σ) i = (Family.mistakeCount σ i : ℕ∞) :=
  (R.lift_worstMistakes _ _).trans (R.family.schedule_exact_mistakes σ i)

theorem schedule_exact_deadline (σ : ℕ → Bool) (i : ℕ) :
    R.worstDeadline (R.scheduleGenerator σ) i = (R.family.deadline σ i : ℕ∞) :=
  (R.lift_worstDeadline _ _).trans (R.family.schedule_exact_deadline σ i)

theorem dominates_iff (G H : GType (X := X)) : R.Dominates G H ↔
    (∀ i, R.worstMistakes G i ≤ R.worstMistakes H i) ∧
    (∀ i, R.worstDeadline G i ≤ R.worstDeadline H i) := by
  constructor
  · intro h
    constructor
    · intro i
      apply Family.enat_le_of_nat_bounds
      intro m hm
      exact (R.worstMistakes_le_iff _ _ _).mpr (h.1 i m ((R.worstMistakes_le_iff _ _ _).mp hm))
    · intro i
      apply Family.enat_le_of_nat_bounds
      intro d hd
      exact (R.worstDeadline_le_iff _ _ _).mpr (h.2 i d ((R.worstDeadline_le_iff _ _ _).mp hd))
  · intro h
    constructor
    · intro i m hm
      exact (R.worstMistakes_le_iff _ _ _).mp ((h.1 i).trans ((R.worstMistakes_le_iff _ _ _).mpr hm))
    · intro i d hd
      exact (R.worstDeadline_le_iff _ _ _).mp ((h.2 i).trans ((R.worstDeadline_le_iff _ _ _).mpr hd))

/-- Exact realization, domination, and Pareto completeness in the arbitrary
ambient universe, stated using the actual worst-case extended-natural profiles. -/
theorem exact_staircase_frontier :
    (∀ σ : ℕ → Bool, R.Fresh (R.scheduleGenerator σ) ∧
      (∀ i, R.worstMistakes (R.scheduleGenerator σ) i = (Family.mistakeCount σ i : ℕ∞) ∧
        R.worstDeadline (R.scheduleGenerator σ) i = (R.family.deadline σ i : ℕ∞)) ∧
      R.ParetoMinimal (R.scheduleGenerator σ)) ∧
    (∀ G : GType (X := X), R.Fresh G → ∃ σ : ℕ → Bool, ∀ i,
      (Family.mistakeCount σ i : ℕ∞) ≤ R.worstMistakes G i ∧
      (R.family.deadline σ i : ℕ∞) ≤ R.worstDeadline G i) ∧
    (∀ G : GType (X := X), R.Fresh G → (R.ParetoMinimal G ↔
      ∃ σ : ℕ → Bool, R.SameProfile G (R.scheduleGenerator σ))) := by
  refine ⟨?_,?_,?_⟩
  · intro σ
    exact ⟨R.schedule_fresh σ,fun i => ⟨R.schedule_exact_mistakes σ i,
      R.schedule_exact_deadline σ i⟩,R.schedule_pareto_minimal σ⟩
  · intro G hf
    obtain ⟨σ,hσ⟩ := R.exists_dominating_schedule G hf
    have h := (R.dominates_iff _ _).mp hσ
    exact ⟨σ,fun i => ⟨by simpa only [R.schedule_exact_mistakes] using h.1 i,
      by simpa only [R.schedule_exact_deadline] using h.2 i⟩⟩
  · exact fun G hf => R.pareto_iff_schedule_profile G hf

/-- Every legal finite history in the arbitrary realization also has an
injective complete continuation. -/
theorem every_history_completes {i : ℕ} {h : List X} (hl : R.Legal i h) :
    ∃ u : ℕ → X, Function.Injective u ∧ (∀ n, u n ∈ R.target i) ∧
      (∀ p ∈ R.target i, ∃ n, u n = p) ∧ (List.range h.length).map u = h := by
  obtain ⟨u,hu,heq⟩ := R.family.every_history_completes (R.decoded_legal hl)
  refine ⟨fun n => R.embed (u n),R.embed.injective.comp hu.1.1,?_,?_,?_⟩
  · intro n
    exact (R.mem_target_embed i _).mpr (hu.1.2 n)
  · rintro p ⟨q,hq,rfl⟩
    obtain ⟨n,hn⟩ := hu.2 q hq
    exact ⟨n,congrArg R.embed hn⟩
  · have hh : (List.range h.length).map u = R.decoded h := by
      simpa only [Family.observations,R.decoded_length] using heq
    calc
      _ = ((List.range h.length).map u).map R.embed := by simp [List.map_map,Function.comp_def]
      _ = R.encoded (R.decoded h) := by rw [hh]; rfl
      _ = h := R.encoded_decoded hl

end Section4.Staircase.Realization

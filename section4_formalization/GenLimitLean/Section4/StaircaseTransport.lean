import Section4.StaircaseStreams

/-! Transport of the exact frontier to an arbitrary ambient universe.
The embedding need not be surjective: arbitrary competitors may output points
outside every target. These outputs are handled explicitly by projection. -/
namespace Section4.Staircase

structure Realization (X : Type*) where
  family : Family
  embed : Point ↪ X

namespace Realization

variable {X : Type*} (R : Realization X)

abbrev GType := List X → X

noncomputable def decode : X → Point := Function.invFun R.embed

@[simp] theorem decode_embed (p : Point) : R.decode (R.embed p) = p :=
  Function.leftInverse_invFun R.embed.injective p

def target (i : ℕ) : Set X := R.embed '' R.family.target i

def Legal (i : ℕ) (h : List X) : Prop := h.Nodup ∧ ∀ p ∈ h, p ∈ R.target i

def Fresh (R : Realization X) (G : GType (X := X)) : Prop := ∀ h, G h ∉ h

noncomputable def decoded (h : List X) : History := h.map R.decode

def encoded (h : History) : List X := h.map R.embed

@[simp] theorem decoded_length (h : List X) : (R.decoded h).length = h.length := by simp [decoded]
@[simp] theorem encoded_length (h : History) : (R.encoded h).length = h.length := by simp [encoded]
@[simp] theorem decoded_encoded (h : History) : R.decoded (R.encoded h) = h := by
  simp [decoded,encoded,List.map_map,Function.comp_def]
@[simp] theorem mem_target_embed (i : ℕ) (p : Point) :
    R.embed p ∈ R.target i ↔ p ∈ R.family.target i := by
  exact R.embed.injective.mem_set_image

theorem encoded_legal {i : ℕ} {h : History} (hl : R.family.Legal i h) :
    R.Legal i (R.encoded h) := by
  refine ⟨hl.1.map R.embed.injective,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact (R.mem_target_embed i q).mpr (hl.2 q hq)

theorem embed_decode {i : ℕ} {p : X} (hp : p ∈ R.target i) : R.embed (R.decode p) = p := by
  obtain ⟨q,hq,rfl⟩ := hp
  simp

theorem encoded_decoded {i : ℕ} {h : List X} (hl : R.Legal i h) :
    R.encoded (R.decoded h) = h := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    simp only [encoded,decoded,List.getElem_map]
    exact R.embed_decode (hl.2 _ (List.getElem_mem hn'))

theorem decoded_legal {i : ℕ} {h : List X} (hl : R.Legal i h) :
    R.family.Legal i (R.decoded h) := by
  constructor
  · have hn : (R.encoded (R.decoded h)).Nodup := by rw [R.encoded_decoded hl]; exact hl.1
    exact List.Nodup.of_map R.embed hn
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hqtarget := hl.2 q hq
    apply (R.mem_target_embed i (R.decode q)).mp
    rwa [R.embed_decode hqtarget]

noncomputable def liftGenerator (G : Generator) (h : List X) : X := R.embed (G (R.decoded h))

theorem lift_fresh {G : Generator} (hf : Family.Fresh G) : R.Fresh (R.liftGenerator G) := by
  intro h hm
  have hd : G (R.decoded h) ∈ R.decoded h := by
    have hh : R.decode (R.liftGenerator G h) ∈ h.map R.decode :=
      List.mem_map.mpr ⟨R.liftGenerator G h,hm,rfl⟩
    simpa [decoded,liftGenerator] using hh
  exact hf _ hd

noncomputable def projectGenerator (G : GType (X := X)) (h : History) : Point := by
  classical
  exact if ho : ∃ p, R.embed p = G (R.encoded h) then Classical.choose ho
    else Sum.inr (0,Classical.choose (R.family.exists_fresh_private h 0))

theorem project_fresh {G : GType (X := X)} (hf : R.Fresh G) : Family.Fresh (R.projectGenerator G) := by
  classical
  intro h
  unfold projectGenerator
  split_ifs with ho
  · intro hm
    have hout := Classical.choose_spec ho
    exact hf (R.encoded h) (hout ▸ List.mem_map.mpr ⟨_,hm,rfl⟩)
  · exact Classical.choose_spec (R.family.exists_fresh_private h 0)

theorem project_valid {G : GType (X := X)} {i : ℕ} {h : History}
    (hv : G (R.encoded h) ∈ R.target i) : R.projectGenerator G h ∈ R.family.target i := by
  classical
  obtain ⟨p,hp,heq⟩ := hv
  have ho : ∃ p, R.embed p = G (R.encoded h) := ⟨p,heq⟩
  unfold projectGenerator
  rw [dif_pos ho]
  have hchosen := Classical.choose_spec ho
  have : Classical.choose ho = p := R.embed.injective (hchosen.trans heq.symm)
  simpa [this] using hp

noncomputable def mistakeTimes (G : GType (X := X)) (i : ℕ) (h : List X) : Finset ℕ := by
  classical
  exact (Finset.range (h.length+1)).filter fun t => G (h.take t) ∉ R.target i

def MistakeBound (G : GType (X := X)) (i m : ℕ) : Prop :=
  ∀ h, R.Legal i h → (R.mistakeTimes G i h).card ≤ m

def DeadlineBound (G : GType (X := X)) (i d : ℕ) : Prop :=
  ∀ h, R.Legal i h → d ≤ h.length → G h ∈ R.target i

theorem lift_mistakeTimes (G : Generator) (i : ℕ) (h : List X) :
    R.mistakeTimes (R.liftGenerator G) i h = R.family.mistakeTimes G i (R.decoded h) := by
  classical
  ext t
  simp only [mistakeTimes,Family.mistakeTimes,Finset.mem_filter,Finset.mem_range,decoded_length]
  simp [liftGenerator,decoded,List.map_take]

theorem lift_mistakeBound_iff (G : Generator) (i m : ℕ) :
    R.MistakeBound (R.liftGenerator G) i m ↔ R.family.MistakeBound G i m := by
  constructor
  · intro hm h hl
    have hh := hm (R.encoded h) (R.encoded_legal hl)
    simpa only [R.lift_mistakeTimes,R.decoded_encoded] using hh
  · intro hm h hl
    rw [R.lift_mistakeTimes]
    exact hm _ (R.decoded_legal hl)

theorem lift_deadlineBound_iff (G : Generator) (i d : ℕ) :
    R.DeadlineBound (R.liftGenerator G) i d ↔ R.family.DeadlineBound G i d := by
  constructor
  · intro hd h hl hn
    have hh := hd (R.encoded h) (R.encoded_legal hl) (by simpa using hn)
    simpa [liftGenerator] using hh
  · intro hd h hl hn
    apply (R.mem_target_embed i _).mpr
    exact hd _ (R.decoded_legal hl) (by simpa using hn)

theorem project_mistakeBound {G : GType (X := X)} {i m : ℕ}
    (hm : R.MistakeBound G i m) : R.family.MistakeBound (R.projectGenerator G) i m := by
  classical
  intro h hl
  apply le_trans (b := (R.mistakeTimes G i (R.encoded h)).card)
  · apply Finset.card_le_card
    intro t ht
    simp only [mistakeTimes,Family.mistakeTimes,Finset.mem_filter,Finset.mem_range,encoded_length] at ht ⊢
    refine ⟨ht.1,?_⟩
    intro hv
    apply ht.2
    apply R.project_valid
    simpa only [encoded,List.map_take] using hv
  · exact hm _ (R.encoded_legal hl)

theorem project_deadlineBound {G : GType (X := X)} {i d : ℕ}
    (hd : R.DeadlineBound G i d) : R.family.DeadlineBound (R.projectGenerator G) i d := by
  intro h hl hn
  apply R.project_valid
  exact hd _ (R.encoded_legal hl) (by simpa using hn)

noncomputable def scheduleGenerator (σ : ℕ → Bool) : GType (X := X) :=
  R.liftGenerator (R.family.scheduleGenerator σ)

theorem schedule_mistakeBound_iff (σ : ℕ → Bool) (i m : ℕ) :
    R.MistakeBound (R.scheduleGenerator σ) i m ↔ Family.mistakeCount σ i ≤ m := by
  exact (R.lift_mistakeBound_iff _ _ _).trans (R.family.schedule_mistakeBound_iff σ i m)

theorem schedule_deadlineBound_iff (σ : ℕ → Bool) (i d : ℕ) :
    R.DeadlineBound (R.scheduleGenerator σ) i d ↔ R.family.deadline σ i ≤ d := by
  exact (R.lift_deadlineBound_iff _ _ _).trans (R.family.schedule_deadlineBound_iff σ i d)

def Dominates (G H : GType (X := X)) : Prop :=
  (∀ i m, R.MistakeBound H i m → R.MistakeBound G i m) ∧
  (∀ i d, R.DeadlineBound H i d → R.DeadlineBound G i d)

def SameProfile (G H : GType (X := X)) : Prop := R.Dominates G H ∧ R.Dominates H G

def ParetoMinimal (G : GType (X := X)) : Prop :=
  R.Fresh G ∧ ∀ H, R.Fresh H → R.Dominates H G → R.Dominates G H

theorem dominates_trans {G H K : GType (X := X)}
    (hGH : R.Dominates G H) (hHK : R.Dominates H K) : R.Dominates G K :=
  ⟨fun i m h => hGH.1 i m (hHK.1 i m h),fun i d h => hGH.2 i d (hHK.2 i d h)⟩

theorem exists_dominating_schedule (G : GType (X := X)) (hf : R.Fresh G) :
    ∃ σ, R.Dominates (R.scheduleGenerator σ) G := by
  obtain ⟨σ,hσ⟩ := R.family.arbitrary_generator_domination (R.projectGenerator G) (R.project_fresh hf)
  refine ⟨σ,⟨?_,?_⟩⟩
  · intro i m hm
    exact (R.schedule_mistakeBound_iff σ i m).mpr ((hσ i).1 m (R.project_mistakeBound hm))
  · intro i d hd
    exact (R.schedule_deadlineBound_iff σ i d).mpr ((hσ i).2 d (R.project_deadlineBound hd))

theorem schedule_fresh (σ : ℕ → Bool) : R.Fresh (R.scheduleGenerator σ) :=
  R.lift_fresh (R.family.schedule_fresh σ)

theorem schedule_pareto_minimal (σ : ℕ → Bool) : R.ParetoMinimal (R.scheduleGenerator σ) := by
  refine ⟨R.schedule_fresh σ,?_⟩
  intro G hf hG
  obtain ⟨τ,hτ⟩ := R.exists_dominating_schedule G hf
  have hcomp := R.dominates_trans hτ hG
  have heq : τ = σ := by
    apply StaircasePareto.schedule_eq_of_mistakes_le
    intro i
    rw [← Family.mistakeCount_eq_scheduleMistakes, ← Family.mistakeCount_eq_scheduleMistakes]
    exact (R.schedule_mistakeBound_iff τ i _).mp
      (hcomp.1 i _ ((R.schedule_mistakeBound_iff σ i _).mpr le_rfl))
  simpa [heq] using hτ

theorem pareto_iff_schedule_profile (G : GType (X := X)) (hf : R.Fresh G) :
    R.ParetoMinimal G ↔ ∃ σ, R.SameProfile G (R.scheduleGenerator σ) := by
  constructor
  · intro hG
    obtain ⟨σ,hσ⟩ := R.exists_dominating_schedule G hf
    exact ⟨σ,hG.2 _ (R.schedule_fresh σ) hσ,hσ⟩
  · rintro ⟨σ,hGσ,hσG⟩
    refine ⟨hf,?_⟩
    intro H hH hHG
    have hHσ := R.dominates_trans hHG hGσ
    have hσH := (R.schedule_pareto_minimal σ).2 H hH hHσ
    exact R.dominates_trans hGσ hσH

/-- The full exact frontier transported to an arbitrary ambient universe,
including all competing generators that can output unused ambient points. -/
theorem exact_frontier :
    (∀ σ : ℕ → Bool, R.Fresh (R.scheduleGenerator σ) ∧
      (∀ i m, R.MistakeBound (R.scheduleGenerator σ) i m ↔ Family.mistakeCount σ i ≤ m) ∧
      (∀ i d, R.DeadlineBound (R.scheduleGenerator σ) i d ↔ R.family.deadline σ i ≤ d) ∧
      R.ParetoMinimal (R.scheduleGenerator σ)) ∧
    (∀ G, R.Fresh G → ∃ σ, R.Dominates (R.scheduleGenerator σ) G) ∧
    (∀ G, R.Fresh G → (R.ParetoMinimal G ↔ ∃ σ, R.SameProfile G (R.scheduleGenerator σ))) := by
  exact ⟨fun σ => ⟨R.schedule_fresh σ,R.schedule_mistakeBound_iff σ,
    R.schedule_deadlineBound_iff σ,R.schedule_pareto_minimal σ⟩,
    R.exists_dominating_schedule,R.pareto_iff_schedule_profile⟩

end Realization
end Section4.Staircase

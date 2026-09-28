import S2BFormalization

open Set Function Filter
open scoped Topology
open Stage3S2B

namespace Stage3Proof

theorem admitted_bound (gen : FeedbackGenerator) (r : ℕ) :
    (round gen (2 * r + 1)).presentation ≤ 12 * r + 9 := by
  rw [presentation_odd]
  unfold oddCode
  have h := freshIndex_le (history gen (2 * r + 1))
  omega

theorem core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2))

theorem builtTarget_infinite (gen : FeedbackGenerator) : (builtTarget gen).Infinite := by
  exact core_infinite.mono (fun _ hx => Or.inl hx)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage := by
  classical
  letI : Infinite ↥(builtTarget gen) := (builtTarget_infinite gen).to_subtype
  exact {
    carrier := builtTarget gen
    enumeration := Nat.orderEmbeddingOfSet (builtTarget gen)
    enumeration_injective := (Nat.orderEmbeddingOfSet (builtTarget gen)).injective
    range_enumeration := Nat.orderEmbeddingOfSet_range (builtTarget gen)
  }

theorem orderedTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedTarget gen).enumeration := by
  classical
  letI : Infinite ↥(builtTarget gen) := (builtTarget_infinite gen).to_subtype
  exact (Nat.orderEmbeddingOfSet (builtTarget gen)).strictMono

end Stage3Proof

namespace Stage3Proof

theorem orderedTarget_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  letI : Infinite ↥(builtTarget gen) := (builtTarget_infinite gen).to_subtype
  let e := Nat.Subtype.orderIsoOfNat (builtTarget gen)
  by_contra hle
  have hbig : 12 * n + 9 < (orderedTarget gen).enumeration n := by omega
  let f : Fin (n + 1) → Fin n := fun i =>
    ⟨e.symm ⟨(round gen (2 * (i : ℕ) + 1)).presentation,
      Or.inr ⟨(i : ℕ), rfl⟩⟩, by
        have hv : (round gen (2 * (i : ℕ) + 1)).presentation <
            (orderedTarget gen).enumeration n :=
          lt_of_le_of_lt ((admitted_bound gen (i : ℕ)).trans (by omega)) hbig
        have he : e (e.symm ⟨(round gen (2 * (i : ℕ) + 1)).presentation,
            Or.inr ⟨(i : ℕ), rfl⟩⟩) < e n := by
          simpa [e, orderedTarget] using hv
        exact (e.lt_iff_lt).mp he⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hidx : (f i : ℕ) = (f j : ℕ) := congrArg Fin.val hij
    have hsub := congrArg e hidx
    have hp : (round gen (2 * (i : ℕ) + 1)).presentation =
        (round gen (2 * (j : ℕ) + 1)).presentation := by
      simpa [f, e] using congrArg Subtype.val hsub
    have ht : 2 * (i : ℕ) + 1 = 2 * (j : ℕ) + 1 :=
      presentation_injective gen hp
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective f hf
  simp at hc

end Stage3Proof

namespace Stage3Proof

noncomputable def coreExponent (z : ℕ) (hz : z ∈ core) : ℕ := Classical.choose hz

theorem pow_coreExponent (z : ℕ) (hz : z ∈ core) :
    2 ^ coreExponent z hz = z := Classical.choose_spec hz

theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 9) + 1 := by
  classical
  let B := 12 * n + 9
  let S := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let f : ↥S → Fin (Nat.log2 B + 1) := fun i => by
    have hi : (i : ℕ) < n := by
      simpa using (Finset.mem_filter.mp i.property).1
    have hcore : (orderedTarget gen).enumeration (i : ℕ) ∈ core :=
      (Finset.mem_filter.mp i.property).2
    have hmono : (orderedTarget gen).enumeration (i : ℕ) ≤
        (orderedTarget gen).enumeration n :=
      (orderedTarget_strictMono gen).monotone (by omega)
    have hval : (orderedTarget gen).enumeration (i : ℕ) ≤ B :=
      hmono.trans (by simpa [B] using orderedTarget_enumeration_le gen n)
    have hpow : 2 ^ coreExponent ((orderedTarget gen).enumeration (i : ℕ)) hcore ≤ B := by
      simpa [pow_coreExponent] using hval
    exact ⟨coreExponent ((orderedTarget gen).enumeration (i : ℕ)) hcore,
      by
        have hB : B ≠ 0 := by simp [B]
        have := (Nat.le_log2 hB).2 hpow
        omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hexp : coreExponent ((orderedTarget gen).enumeration (i : ℕ))
          (Finset.mem_filter.mp i.property).2 =
        coreExponent ((orderedTarget gen).enumeration (j : ℕ))
          (Finset.mem_filter.mp j.property).2 := congrArg Fin.val hij
    have hval : (orderedTarget gen).enumeration (i : ℕ) =
        (orderedTarget gen).enumeration (j : ℕ) := by
      rw [← pow_coreExponent ((orderedTarget gen).enumeration (i : ℕ))
        (Finset.mem_filter.mp i.property).2,
        ← pow_coreExponent ((orderedTarget gen).enumeration (j : ℕ))
        (Finset.mem_filter.mp j.property).2,
        hexp]
    apply Subtype.ext
    exact (orderedTarget gen).enumeration_injective hval
  have hc := Fintype.card_le_of_injective f hf
  simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, S, B] using hc

end Stage3Proof

namespace Stage3Proof

theorem log2_linear_bound (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (12 * n + 9) + 1 ≤ 6 + Nat.log2 n := by
  have harg : 12 * n + 9 ≤ 32 * n := by omega
  have hlog : Nat.log2 (12 * n + 9) ≤ Nat.log2 (32 * n) := by
    simpa [Nat.log2_eq_log_two] using (Nat.log_mono_right harg :
      Nat.log 2 (12 * n + 9) ≤ Nat.log 2 (32 * n))
  have heq : Nat.log2 (32 * n) = Nat.log2 n + 5 := by
    rw [show 32 * n = 2 * (16 * n) by omega, Nat.log2_two_mul (by omega),
      show 16 * n = 2 * (8 * n) by omega, Nat.log2_two_mul (by omega),
      show 8 * n = 2 * (4 * n) by omega, Nat.log2_two_mul (by omega),
      show 4 * n = 2 * (2 * n) by omega, Nat.log2_two_mul (by omega),
      Nat.log2_two_mul hn]
  omega

theorem core_prefixRatio_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤
      ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    simp only [hn, if_false]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (core_prefixCount_le gen n).trans (log2_linear_bound n hn)

theorem core_ratio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  apply squeeze_zero
  · exact (orderedTarget gen).prefixRatio_nonneg core
  · exact core_prefixRatio_le gen
  · simpa [add_comm] using GenLimit.tendsto_countingError_div 6

theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (core_ratio_tendsto_zero gen).limsup_eq

end Stage3Proof

namespace Stage3Proof

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtTranscript gen).presentation
      (builtTranscript gen).output ⊆ core := by
  rintro z ⟨hz, t, hout, hnew⟩
  by_contra hzcore
  rcases hz with hzcore' | ⟨r, hr⟩
  · exact hzcore hzcore'
  · have ht : t < 2 * r + 1 := by
      by_contra hlt
      apply hnew
      refine ⟨2 * r + 1, by omega, ?_⟩
      simpa [builtTranscript] using hr
    have hav := (odd_avoids_prior gen r t ht).2.1
    apply hav
    change (round gen (2 * r + 1)).presentation = (round gen t).output
    change (round gen t).output = z at hout
    exact hr.trans hout.symm

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) = 0 := by
  apply le_antisymm
  · exact ((orderedTarget gen).upperDensity_mono (scored_subset_core gen)).trans_eq
      (core_upperDensity_zero gen)
  · exact (orderedTarget gen).upperDensity_nonneg _

theorem faithful_negative_witness (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (builtTarget gen) (builtPresenter gen)
      (builtTranscript gen) (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_strictMono gen, presented_by gen,
    follows_protocol gen, presentation_clean gen, presentation_injective gen,
    presentation_complete gen, ?_⟩
  exact scored_upperDensity_zero gen

end Stage3Proof

namespace Stage3Proof

def encodedTarget (A : Set ℕ) : Language := core ∪ oddCode '' A

theorem encodedTarget_mem_class (A : Set ℕ) : encodedTarget A ∈ targetClass := by
  refine ⟨oddCode '' A, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact oddCode_not_core n

def encodedTargetSubtype (A : Set ℕ) : ↥targetClass :=
  ⟨encodedTarget A, encodedTarget_mem_class A⟩

theorem encodedTarget_injective : Function.Injective encodedTargetSubtype := by
  intro A B hab
  have hAB : encodedTarget A = encodedTarget B := by
    simpa [encodedTargetSubtype] using congrArg Subtype.val hab
  apply Set.ext
  intro n
  constructor
  · intro hn
    have hz : oddCode n ∈ encodedTarget A := Or.inr ⟨n, hn, rfl⟩
    have hzB : oddCode n ∈ encodedTarget B := by
      rw [← hAB]
      exact hz
    rcases hzB with hzcore | ⟨m, hm, heq⟩
    · exact False.elim (oddCode_not_core n hzcore)
    · have : m = n := oddCode_injective heq
      simpa [this] using hm
  · intro hn
    have hz : oddCode n ∈ encodedTarget B := Or.inr ⟨n, hn, rfl⟩
    have hzA : oddCode n ∈ encodedTarget A := by
      rw [hAB]
      exact hz
    rcases hzA with hzcore | ⟨m, hm, heq⟩
    · exact False.elim (oddCode_not_core n hzcore)
    · have : m = n := oddCode_injective heq
      simpa [this] using hm

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  letI : Countable ↥targetClass := hcount
  have hsets : Countable (Set ℕ) := encodedTarget_injective.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hsets

theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

theorem negative_claim : NegativeClaim := by
  intro gen hvalid
  refine ⟨builtTarget gen, builtTarget_mem_class gen, builtPresenter gen,
    builtTranscript gen, orderedTarget gen, ?_⟩
  exact faithful_negative_witness gen

end Stage3Proof

example : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable, Stage3Proof.uniform_generation,
    Stage3Proof.negative_claim⟩

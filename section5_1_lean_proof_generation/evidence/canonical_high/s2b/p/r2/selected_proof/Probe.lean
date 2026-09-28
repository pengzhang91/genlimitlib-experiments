import S2BFormalization

namespace Stage3Proof
open Set Filter Stage3S2B

def code (n : ℕ) := 2 ^ (n + 1) + 1

theorem code_injective : Function.Injective code := by
  intro m n h
  have hp : 2 ^ (m + 1) = 2 ^ (n + 1) := by
    simpa [code] using Nat.add_right_cancel h
  have := Nat.pow_right_injective (by omega : 1 < 2) hp
  omega

theorem code_not_core (n : ℕ) : code n ∉ core := by
  rintro ⟨k, hk⟩
  change 2 ^ k = 2 ^ (n + 1) + 1 at hk
  have hlo : 2 ^ (n + 1) < 2 ^ k := by omega
  have hp : 2 ≤ 2 ^ (n + 1) := by
    exact Nat.one_lt_pow (by omega) (by omega)
  have hhi : 2 ^ k < 2 ^ (n + 2) := by
    rw [hk, show n + 2 = (n + 1) + 1 by omega, pow_succ]
    omega
  have hklo : n + 1 < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hlo
  have hkhi : k < n + 2 := (Nat.pow_lt_pow_iff_right (by omega)).mp hhi
  omega

theorem uncountable_targetClass : ¬ targetClass.Countable := by
  intro hcount
  have hnonempty : targetClass.Nonempty := by
    refine ⟨core, ∅, ?_, ?_⟩
    · exact Set.empty_subset _
    · simp
  rcases hcount.exists_eq_range hnonempty with ⟨f, hf⟩
  let A : Language := code '' {n | code n ∉ f n}
  let L : Language := core ∪ A
  have hL : L ∈ targetClass := by
    refine ⟨A, ?_, rfl⟩
    rintro z ⟨n, hn, rfl⟩
    exact code_not_core n
  rw [hf] at hL
  rcases hL with ⟨m, hm⟩
  have hdiag : code m ∈ L ↔ code m ∉ f m := by
    simp only [L, A, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro (hc | ⟨n, hn, heq⟩)
      · exact False.elim (code_not_core m hc)
      · have : n = m := code_injective heq
        simpa [this] using hn
    · intro hn
      exact Or.inr ⟨m, hn, rfl⟩
  have hmem : code m ∈ f m ↔ code m ∈ L := by
    constructor <;> intro h <;> simpa only [hm] using h
  have : code m ∈ f m ↔ code m ∉ f m := hmem.trans hdiag
  tauto

theorem prefixCount_mono {K : OrderedLanguage} {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

theorem prefixRatio_mono {K : OrderedLanguage} {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixRatio A n ≤ K.prefixRatio B n := by
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
    GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  split
  · simp
  · exact div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono hAB n) (by positivity)

theorem scored_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedK gen).prefixRatio (scored (K gen) (x gen) (y gen)))
      atTop (nhds 0) := by
  apply squeeze_zero' (g := (orderedK gen).prefixRatio core)
  · filter_upwards with n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    positivity
  · filter_upwards with n
    exact prefixRatio_mono (scored_subset_core gen) n
  · exact core_prefixRatio_tendsto_zero gen

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedK gen).upperDensity (scored (K gen) (x gen) (y gen)) = 0 := by
  exact (scored_prefixRatio_tendsto_zero gen).limsup_eq

theorem negative : NegativeClaim := by
  intro gen _
  refine ⟨K gen, K_targetClass gen, presenter gen, tr gen, orderedK gen, ?_⟩
  exact ⟨rfl, orderedK_inherits gen, presented gen, follows gen,
    clean_x gen, x_injective gen, complete_x gen, scored_upperDensity_zero gen⟩

end Stage3Proof

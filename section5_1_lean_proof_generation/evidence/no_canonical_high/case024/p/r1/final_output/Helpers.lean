import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter MeasureTheory
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k * k

def squares : Language := {n | IsSquare n}

noncomputable instance squareDecidablePred : DecidablePred IsSquare := Classical.decPred _

lemma square_map_injective : Function.Injective (fun k : ℕ => k * k) := by
  intro a b h
  nlinarith

lemma squares_infinite : squares.Infinite := by
  rw [show squares = Set.range (fun k : ℕ => k * k) by
    ext n
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩]
  exact Set.infinite_range_of_injective square_map_injective

lemma between_not_square (k : ℕ) : ¬ IsSquare (k * k + 3 * k + 2) := by
  rintro ⟨m, hm⟩
  by_cases hmk : m ≤ k + 1
  · have : m * m ≤ (k + 1) * (k + 1) := Nat.mul_self_le_mul_self hmk
    nlinarith
  · have hkm : k + 2 ≤ m := by omega
    have : (k + 2) * (k + 2) ≤ m * m := Nat.mul_self_le_mul_self hkm
    nlinarith

lemma nonsquares_infinite : {n : ℕ | ¬ IsSquare n}.Infinite := by
  let f : ℕ → ℕ := fun k => k * k + 3 * k + 2
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    nlinarith
  have hr : Set.range f ⊆ {n : ℕ | ¬ IsSquare n} := by
    rintro _ ⟨k, rfl⟩
    exact between_not_square k
  exact (Set.infinite_range_of_injective hf).mono hr

noncomputable def swapStream (t : ℕ) : ℕ := by
  classical
  exact if ht : IsSquare t then
    Nat.nth (fun n => ¬ IsSquare n) (Nat.count IsSquare t)
  else
    Nat.nth IsSquare (Nat.count (fun n => ¬ IsSquare n) t)

lemma swapStream_square_iff (t : ℕ) : IsSquare (swapStream t) ↔ ¬ IsSquare t := by
  classical
  unfold swapStream
  split_ifs with ht
  · constructor
    · intro hs
      exact (Nat.nth_mem_of_infinite nonsquares_infinite _ hs).elim
    · intro h
      exact (h ht).elim
  · exact ⟨fun _ => ht, fun _ => Nat.nth_mem_of_infinite squares_infinite _⟩

lemma swapStream_injective : Function.Injective swapStream := by
  classical
  intro a b hab
  by_cases ha : IsSquare a <;> by_cases hb : IsSquare b
  · have hn : Nat.nth (fun n => ¬ IsSquare n) (Nat.count IsSquare a) =
        Nat.nth (fun n => ¬ IsSquare n) (Nat.count IsSquare b) := by
      simpa [swapStream, ha, hb] using hab
    have hc := Nat.nth_injective nonsquares_infinite hn
    exact Nat.count_injective ha hb hc
  · have hsa : ¬ IsSquare (swapStream a) := (swapStream_square_iff a).not.mpr (not_not.mpr ha)
    have hsb : IsSquare (swapStream b) := (swapStream_square_iff b).mpr hb
    exact (hsa (hab ▸ hsb)).elim
  · have hsa : IsSquare (swapStream a) := (swapStream_square_iff a).mpr ha
    have hsb : ¬ IsSquare (swapStream b) := (swapStream_square_iff b).not.mpr (not_not.mpr hb)
    exact (hsb (hab ▸ hsa)).elim
  · have hn : Nat.nth IsSquare (Nat.count (fun n => ¬ IsSquare n) a) =
        Nat.nth IsSquare (Nat.count (fun n => ¬ IsSquare n) b) := by
      simpa [swapStream, ha, hb] using hab
    have hc := Nat.nth_injective squares_infinite hn
    exact Nat.count_injective ha hb hc

lemma swapStream_surjective : Function.Surjective swapStream := by
  classical
  intro n
  by_cases hn : IsSquare n
  · let t := Nat.nth (fun m => ¬ IsSquare m) (Nat.count IsSquare n)
    have ht : ¬ IsSquare t := Nat.nth_mem_of_infinite nonsquares_infinite _
    refine ⟨t, ?_⟩
    rw [swapStream, dif_neg ht]
    rw [Nat.count_nth_of_infinite nonsquares_infinite]
    exact Nat.nth_count hn
  · let t := Nat.nth IsSquare (Nat.count (fun m => ¬ IsSquare m) n)
    have ht : IsSquare t := Nat.nth_mem_of_infinite squares_infinite _
    refine ⟨t, ?_⟩
    rw [swapStream, dif_pos ht]
    rw [Nat.count_nth_of_infinite squares_infinite]
    exact Nat.nth_count hn

end Case024

namespace Case024

lemma square_sqrt_mul_self {n : ℕ} (hn : IsSquare n) : n.sqrt * n.sqrt = n := by
  rcases hn with ⟨k, rfl⟩
  simp [Nat.sqrt_eq]

lemma sqrt_injective_on_squares : Set.InjOn Nat.sqrt squares := by
  intro a ha b hb hab
  have ha' := square_sqrt_mul_self ha
  have hb' := square_sqrt_mul_self hb
  calc
    a = a.sqrt * a.sqrt := ha'.symm
    _ = b.sqrt * b.sqrt := by rw [hab]
    _ = b := hb' 

lemma prefixCount_squares (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n = Nat.count IsSquare n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range, squares]

lemma count_squares_le (n : ℕ) : Nat.count IsSquare n ≤ n.sqrt + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let s : Finset ℕ := {x ∈ Finset.range n | IsSquare x}
  have hcard : (s.image Nat.sqrt).card = s.card := by
    rw [Finset.card_image_iff]
    intro a ha b hb hab
    apply sqrt_injective_on_squares
    · exact (Finset.mem_filter.mp ha).2
    · exact (Finset.mem_filter.mp hb).2
    · exact hab
  calc
    s.card = (s.image Nat.sqrt).card := hcard.symm
    _ ≤ (Finset.range (n.sqrt + 1)).card := by
      apply Finset.card_le_card
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
      apply Finset.mem_range.mpr
      have hxn : x ≤ n := Nat.le_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
      exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt hxn)
    _ = n.sqrt + 1 := Finset.card_range _

lemma tendsto_sqrt_nat_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

lemma tendsto_cast_sqrt_nat_atTop :
    Tendsto (fun n : ℕ => (n.sqrt : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_sqrt_nat_atTop

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun n : ℕ => ((n.sqrt + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  refine squeeze_zero' (g := fun n : ℕ => (1 : ℝ) / (n.sqrt : ℝ) + 1 / (n : ℝ)) ?_ ?_ ?_
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < n.sqrt := by
      exact_mod_cast (Nat.sqrt_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hsquare : (n.sqrt : ℝ) * n.sqrt ≤ n := by
      exact_mod_cast Nat.sqrt_le n
    have hmain : (n.sqrt : ℝ) / n ≤ 1 / (n.sqrt : ℝ) := by
      rw [div_le_div_iff₀ hn0 hs0]
      simpa [mul_comm] using hsquare
    rw [Nat.cast_add, Nat.cast_one, add_div]
    exact add_le_add hmain le_rfl
  · have h₁ : Tendsto (fun n : ℕ => (1 : ℝ) / (n.sqrt : ℝ)) atTop (nhds 0) :=
      tendsto_cast_sqrt_nat_atTop.const_div_atTop 1
    have h₂ : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    simpa using h₁.add h₂

lemma tendsto_square_prefix_ratio :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  refine squeeze_zero' (g := fun n : ℕ => ((n.sqrt + 1 : ℕ) : ℝ) / (n : ℝ)) ?_ ?_ ?_
  · filter_upwards with n
    positivity
  · exact Filter.Eventually.of_forall fun n => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [prefixCount_squares]
      exact_mod_cast count_squares_le n
  · simpa [prefixCount_squares] using tendsto_sqrt_add_one_div

end Case024

namespace Case024

lemma noiseCount_swapStream (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount swapStream squares n =
      GenLimit.PatientScope.prefixCount squares n := by
  classical
  simp only [GenLimit.InfiniteContamination.noiseCount,
    GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  congr 1
  ext t
  simp [squares, swapStream_square_iff]

lemma vanishingNoise_swapStream :
    GenLimit.InfiniteContamination.VanishingNoise swapStream squares := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  have h := tendsto_square_prefix_ratio
  apply h.congr'
  filter_upwards with n
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate, prefixCount_squares]
  · simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn, noiseCount_swapStream]

lemma legal_swapStream_squares : Stage3Case024.Legal swapStream squares := by
  refine ⟨squares_infinite, swapStream_injective, ?_, vanishingNoise_swapStream⟩
  intro n hn
  exact swapStream_surjective n

lemma legal_swapStream_of_superset {K : Language} (hsub : squares ⊆ K) :
    Stage3Case024.Legal swapStream K := by
  refine ⟨squares_infinite.mono hsub, swapStream_injective, ?_, ?_⟩
  · intro n hn
    exact swapStream_surjective n
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    have hsq := vanishingNoise_swapStream
    unfold GenLimit.InfiniteContamination.VanishingNoise at hsq
    refine squeeze_zero'
      (g := GenLimit.InfiniteContamination.empiricalNoiseRate swapStream squares) ?_ ?_ hsq
    · exact Filter.Eventually.of_forall fun n => by
        unfold GenLimit.InfiniteContamination.empiricalNoiseRate
        split_ifs
        · exact le_rfl
        · positivity
    · exact Filter.Eventually.of_forall fun n => by
        by_cases hn : n = 0
        · subst n
          simp [GenLimit.InfiniteContamination.empiricalNoiseRate]
        · simp only [GenLimit.InfiniteContamination.empiricalNoiseRate, hn, if_false]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card (by
            intro t ht
            simp only [GenLimit.InfiniteContamination.noiseCount, Finset.mem_filter,
              Finset.mem_range] at ht ⊢
            exact ⟨ht.1, fun h => ht.2 (hsub h)⟩)

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Language) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  exact Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩)

lemma prefixCount_union_finset_le (A : Language) (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ (F : Set ℕ)) n ≤
      GenLimit.PatientScope.prefixCount A n + F.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let s : Finset ℕ := (Finset.range n).filter (fun x => x ∈ A)
  let u : Finset ℕ := (Finset.range n).filter (fun x => x ∈ A ∪ (F : Set ℕ))
  have hus : u ⊆ s ∪ F := by
    intro x hx
    simp only [u, s, Finset.mem_filter, Finset.mem_range, Set.mem_union,
      Finset.mem_union, Finset.mem_coe] at hx ⊢
    exact hx.2.elim (fun h => Or.inl ⟨hx.1, h⟩) Or.inr
  simpa [u, s] using (Finset.card_le_card hus).trans (Finset.card_union_le s F)

lemma tendsto_square_plus_const_ratio (C : ℕ) :
    Tendsto (fun n : ℕ =>
      ((GenLimit.PatientScope.prefixCount squares n + C : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hC : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  convert tendsto_square_prefix_ratio.add hC using 1
  · funext n
    push_cast
    ring
  · ring

lemma relativeUpperDensity_univ_eq_zero_of_subset_finset
    {A : Language} {F : Finset ℕ} (hA : A ⊆ squares ∪ (F : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  simp only [Set.inter_univ]
  refine squeeze_zero'
    (g := fun n : ℕ =>
      ((GenLimit.PatientScope.prefixCount squares n + F.card : ℕ) : ℝ) / (n : ℝ)) ?_ ?_ ?_
  · filter_upwards with n
    positivity
  · exact Filter.Eventually.of_forall fun n => by
      rw [prefixCount_univ]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (prefixCount_mono hA n |>.trans (prefixCount_union_finset_le squares F n))
  · exact tendsto_square_plus_const_ratio F.card

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · apply Filter.isCoboundedUnder_le_of_le atTop
    intro n
    positivity
  · exact Filter.Eventually.of_forall fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono (Set.inter_subset_right : A ∩ K ⊆ K) n

end Case024

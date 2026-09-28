import Stage3Model
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

def IsSquare (n : ℕ) : Prop := Nat.sqrt n * Nat.sqrt n = n

instance (n : ℕ) : Decidable (IsSquare n) :=
  inferInstanceAs (Decidable (Nat.sqrt n * Nat.sqrt n = n))


def oddSet : Language := {x | ∃ k, x = 2 * k + 1}
def squareSet : Language := {x | IsSquare x}

noncomputable def input : Stream := fun t =>
  if IsSquare t then 2 * Nat.sqrt t + 1 else 4 * (t + 1) * (t + 1)

def K0 : Language := Set.range fun t : {t // ¬ IsSquare t} => 4 * (t.1 + 1) * (t.1 + 1)
def K1 : Language := K0 ∪ oddSet

lemma square_sqrt_sq {n : ℕ} (h : IsSquare n) : Nat.sqrt n * Nat.sqrt n = n := h

lemma isSquare_iff {n : ℕ} : IsSquare n ↔ ∃ k, k * k = n := by
  exact (Nat.exists_mul_self n).symm

lemma input_of_square {t : ℕ} (h : IsSquare t) : input t = 2 * Nat.sqrt t + 1 := by
  simp [input, h]

lemma input_of_not_square {t : ℕ} (h : ¬ IsSquare t) :
    input t = 4 * (t + 1) * (t + 1) := by
  simp [input, h]

lemma input_in_K0_of_not_square {t : ℕ} (h : ¬ IsSquare t) : input t ∈ K0 := by
  rw [input_of_not_square h]
  exact ⟨⟨t, h⟩, rfl⟩

lemma input_in_odd_of_square {t : ℕ} (h : IsSquare t) : input t ∈ oddSet := by
  rw [input_of_square h]
  exact ⟨Nat.sqrt t, rfl⟩

lemma K0_even {x : ℕ} (hx : x ∈ K0) : Even x := by
  rcases hx with ⟨t, rfl⟩
  exact ⟨2 * (t.1 + 1) * (t.1 + 1), by ring⟩

lemma oddSet_odd {x : ℕ} (hx : x ∈ oddSet) : Odd x := by
  rcases hx with ⟨k, rfl⟩
  exact ⟨k, by omega⟩

lemma K0_disjoint_odd : Disjoint K0 oddSet := by
  rw [Set.disjoint_left]
  intro x hx0 hxo
  exact (Nat.not_even_iff_odd.mpr (oddSet_odd hxo)) (K0_even hx0)

lemma input_not_K0_of_square {t : ℕ} (h : IsSquare t) : input t ∉ K0 := by
  intro hk
  exact Set.disjoint_left.1 K0_disjoint_odd hk (input_in_odd_of_square h)

lemma input_mem_K1 (t : ℕ) : input t ∈ K1 := by
  by_cases h : IsSquare t
  · exact Set.mem_union_right _ (input_in_odd_of_square h)
  · exact Set.mem_union_left _ (input_in_K0_of_not_square h)

lemma input_injective : Function.Injective input := by
  intro s t hst
  by_cases hs : IsSquare s <;> by_cases ht : IsSquare t
  · rw [input_of_square hs, input_of_square ht] at hst
    have hsqrt : Nat.sqrt s = Nat.sqrt t := by omega
    rw [← square_sqrt_sq hs, ← square_sqrt_sq ht, hsqrt]
  · have ho : Odd (input s) := oddSet_odd (input_in_odd_of_square hs)
    have he : Even (input t) := by
      rw [input_of_not_square ht]
      exact ⟨2 * (t + 1) * (t + 1), by ring⟩
    exact False.elim ((Nat.not_even_iff_odd.mpr ho) (hst ▸ he))
  · have he : Even (input s) := by
      rw [input_of_not_square hs]
      exact ⟨2 * (s + 1) * (s + 1), by ring⟩
    have ho : Odd (input t) := oddSet_odd (input_in_odd_of_square ht)
    exact False.elim ((Nat.not_even_iff_odd.mpr ho) (hst ▸ he))
  · rw [input_of_not_square hs, input_of_not_square ht] at hst
    have h4 : 4 * ((s + 1) * (s + 1)) = 4 * ((t + 1) * (t + 1)) := by
      simpa [mul_assoc] using hst
    have hsq : (s + 1) * (s + 1) = (t + 1) * (t + 1) :=
      Nat.eq_of_mul_eq_mul_left (by norm_num) h4
    nlinarith

lemma K0_no_omissions :
    GenLimit.InfiniteContamination.NoOmissions input K0 := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  exact ⟨t.1, input_of_not_square t.2⟩

lemma odd_no_omissions : oddSet ⊆ Set.range input := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  refine ⟨k * k, ?_⟩
  have hs : IsSquare (k * k) := by simp [IsSquare, Nat.sqrt_eq]
  rw [input_of_square hs, Nat.sqrt_eq]

lemma K1_no_omissions :
    GenLimit.InfiniteContamination.NoOmissions input K1 := by
  intro x hx
  rcases hx with hx | hx
  · exact K0_no_omissions hx
  · exact odd_no_omissions hx

lemma squareSet_mem_iff (n : ℕ) : n ∈ squareSet ↔ IsSquare n := Iff.rfl

noncomputable def squarePrefix (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter IsSquare

lemma squarePrefix_card_le (n : ℕ) : (squarePrefix n).card ≤ Nat.sqrt n + 1 := by
  classical
  have hcard : (Finset.range (Nat.sqrt n + 1)).card = Nat.sqrt n + 1 := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn Nat.sqrt ?_ ?_
  · intro x hx
    simp only [squarePrefix, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_coe, Finset.mem_range]
    exact lt_of_le_of_lt (Nat.sqrt_le_sqrt (Nat.le_of_lt hx.1)) (Nat.lt_succ_self _)
  · intro x hx y hy hxy
    simp only [squarePrefix, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    rw [← square_sqrt_sq hx.2, ← square_sqrt_sq hy.2, hxy]

lemma noise_mem_iff (t : ℕ) : input t ∉ K0 ↔ IsSquare t := by
  by_cases h : IsSquare t
  · exact ⟨fun _ => h, fun _ => input_not_K0_of_square h⟩
  · exact ⟨fun hn => (hn (input_in_K0_of_not_square h)).elim, fun hs => (h hs).elim⟩

lemma noiseCount_K0_eq (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input K0 n = (squarePrefix n).card := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount squarePrefix
  congr 1
  ext t
  simp [noise_mem_iff]

lemma sqrt_cast_tendsto_atTop :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨m : ℕ, hm : b < (m : ℝ)⟩ := exists_nat_gt b
  refine ⟨m * m, fun n hn => le_trans hm.le ?_⟩
  exact_mod_cast (Nat.le_sqrt.mpr hn)

lemma sqrt_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (2 : ℝ) / Nat.sqrt n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp sqrt_cast_tendsto_atTop) :
        Tendsto (fun n : ℕ => (2 : ℝ) * (Nat.sqrt n : ℝ)⁻¹) atTop (𝓝 (2 * 0)))
  refine squeeze_zero
    (f := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n)
    (g := fun n : ℕ => (2 : ℝ) / Nat.sqrt n) ?_ ?_ hinv
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hspos : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hnpos
    apply (div_le_div_iff₀ (by exact_mod_cast hnpos) (by exact_mod_cast hspos)).2
    exact_mod_cast (by
      have hsle : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
      nlinarith : (Nat.sqrt n + 1) * Nat.sqrt n ≤ 2 * n)

lemma vanishingNoise_K0 : GenLimit.InfiniteContamination.VanishingNoise input K0 := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero
    (f := GenLimit.InfiniteContamination.empiricalNoiseRate input K0)
    (g := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n) ?_ ?_ sqrt_ratio_tendsto_zero
  · intro n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split <;> positivity
  · intro n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · simp [hn]
    · rw [noiseCount_K0_eq]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast squarePrefix_card_le n
      · positivity

lemma vanishingNoise_mono {K : Language} (hsub : K0 ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise input K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero
    (f := GenLimit.InfiniteContamination.empiricalNoiseRate input K)
    (g := GenLimit.InfiniteContamination.empiricalNoiseRate input K0) ?_ ?_ vanishingNoise_K0
  · intro n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split <;> positivity
  · intro n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · simp [hn]
    · gcongr
      unfold GenLimit.InfiniteContamination.noiseCount
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      exact ⟨ht.1, fun hK => ht.2 (hsub hK)⟩

lemma K0_infinite : K0.Infinite := by
  let f : ℕ → ℕ := fun n => 4 * (((n + 1) * (n + 1) + (n + 1)) + 1) *
    (((n + 1) * (n + 1) + (n + 1)) + 1)
  have hns (n : ℕ) : ¬ IsSquare ((n + 1) * (n + 1) + (n + 1)) := by
    rw [isSquare_iff]
    rintro ⟨k, hk⟩
    have hlo : (n + 1) * (n + 1) < k * k := by omega
    have hhi : k * k < (n + 2) * (n + 2) := by nlinarith
    have hklo : n + 2 ≤ k := by
      by_contra h
      have : k ≤ n + 1 := by omega
      nlinarith
    nlinarith
  have hfmem (n : ℕ) : f n ∈ K0 := by
    refine ⟨⟨(n + 1) * (n + 1) + (n + 1), hns n⟩, ?_⟩
    rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have h4 :
        4 * (((a + 1) * (a + 1) + (a + 1) + 1) * ((a + 1) * (a + 1) + (a + 1) + 1)) =
        4 * (((b + 1) * (b + 1) + (b + 1) + 1) * ((b + 1) * (b + 1) + (b + 1) + 1)) := by
      simpa [mul_assoc] using hab
    have hsquare :
        ((a + 1) * (a + 1) + (a + 1) + 1) * ((a + 1) * (a + 1) + (a + 1) + 1) =
        ((b + 1) * (b + 1) + (b + 1) + 1) * ((b + 1) * (b + 1) + (b + 1) + 1) :=
      Nat.eq_of_mul_eq_mul_left (by norm_num) h4
    have hbase : (a + 1) * (a + 1) + (a + 1) + 1 =
        (b + 1) * (b + 1) + (b + 1) + 1 := by
      nlinarith
    nlinarith
  exact (Set.infinite_range_of_injective hfinj).mono (fun x hx => by
    rcases hx with ⟨n, rfl⟩
    exact hfmem n)

lemma oddSet_infinite : oddSet.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have htwo : 2 * a = 2 * b := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) htwo
  exact (Set.infinite_range_of_injective hinj).mono
    (fun x hx => by rcases hx with ⟨n, rfl⟩; exact ⟨n, rfl⟩)

lemma K1_infinite : K1.Infinite := oddSet_infinite.mono (Set.subset_union_right)

lemma legal_K0 : Stage3Case024.Legal input K0 := by
  exact ⟨K0_infinite, input_injective, K0_no_omissions, vanishingNoise_K0⟩

lemma legal_K1 : Stage3Case024.Legal input K1 := by
  exact ⟨K1_infinite, input_injective, K1_no_omissions, vanishingNoise_mono Set.subset_union_left⟩

lemma K0_ssubset_K1 : K0 ⊂ K1 := by
  refine ⟨Set.subset_union_left, ?_⟩
  intro h
  have h1 : 1 ∈ K0 := h (Set.mem_union_right _ ⟨0, by omega⟩)
  exact (Nat.not_even_iff_odd.mpr (by exact ⟨0, by omega⟩)) (K0_even h1)


lemma prefixCount_mono {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma K0_subset_squareSet : K0 ⊆ squareSet := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  rw [squareSet_mem_iff, isSquare_iff]
  refine ⟨2 * (t.1 + 1), ?_⟩
  ring

lemma prefixCount_squareSet_eq (n : ℕ) :
    GenLimit.PatientScope.prefixCount squareSet n = (squarePrefix n).card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset squarePrefix
  congr 1
  ext x
  simp [squareSet]

lemma prefixCount_K0_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount K0 n ≤ Nat.sqrt n + 1 := by
  exact le_trans (prefixCount_mono K0_subset_squareSet n)
    (by rw [prefixCount_squareSet_eq]; exact squarePrefix_card_le n)

lemma prefixCount_odd_lower (n : ℕ) :
    n / 2 ≤ GenLimit.PatientScope.prefixCount oddSet n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let f : ℕ → ℕ := fun k => 2 * k + 1
  have hcard : (Finset.range (n / 2)).card = n / 2 := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have hmul : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    exact ⟨by dsimp [f]; omega, ⟨k, rfl⟩⟩
  · intro a ha b hb hab
    have htwo : 2 * a = 2 * b := Nat.add_right_cancel hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) htwo

lemma prefixCount_K1_lower (n : ℕ) :
    n / 2 ≤ GenLimit.PatientScope.prefixCount K1 n :=
  le_trans (prefixCount_odd_lower n)
    (prefixCount_mono Set.subset_union_right n)

lemma density_ratio_nonneg (A K : Language) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

lemma density_ratio_le_one (A K : Language) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)).2
    exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma relativeUpperDensity_nonneg (A K : Language) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  refine Filter.le_limsup_of_frequently_le
    (Filter.Eventually.frequently
      (Filter.Eventually.of_forall (density_ratio_nonneg A K))) ?_
  exact Filter.isBoundedUnder_of_eventually_le
    (Filter.Eventually.of_forall (density_ratio_le_one A K))

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  exact Filter.limsup_le_of_le
    (hf := Filter.isCoboundedUnder_le_of_le atTop (density_ratio_nonneg A K))
    (h := Filter.Eventually.of_forall (density_ratio_le_one A K))

lemma generatorFirst_subset_range (output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  intro x hx
  rcases hx with ⟨t, ht, _⟩
  exact ⟨t, ht⟩

lemma generatorFirst_cover_of_eventual
    {output : Stream} (hvalid : GenLimit.NovelGeneratesInLimit input output K0) :
    ∃ T : ℕ, GenLimit.GeneratorFirst input output ⊆
      K0 ∪ (↑(Finset.image output (Finset.range T)) : Set ℕ) := by
  rcases hvalid with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro x hx
  rcases hx with ⟨t, hout, hfirst⟩
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hout ▸ (hT t ht).1)
  · apply Set.mem_union_right
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨t, by omega, hout⟩

lemma prefixCount_inter_K1_le_of_eventual
    {output : Stream} (hvalid : GenLimit.NovelGeneratesInLimit input output K0) :
    ∃ T : ℕ, ∀ n,
      GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ K1) n ≤ Nat.sqrt n + 1 + T := by
  rcases generatorFirst_cover_of_eventual hvalid with ⟨T, hsub⟩
  refine ⟨T, fun n => ?_⟩
  classical
  let early : Finset ℕ := Finset.image output (Finset.range T)
  have hinter : GenLimit.GeneratorFirst input output ∩ K1 ⊆ K0 ∪ (↑early : Set ℕ) := by
    exact Set.Subset.trans Set.inter_subset_left hsub
  calc
    GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ K1) n
        ≤ GenLimit.PatientScope.prefixCount (K0 ∪ (↑early : Set ℕ)) n :=
          prefixCount_mono hinter n
    _ ≤ GenLimit.PatientScope.prefixCount K0 n + early.card := by
      have hunion : GenLimit.PatientScope.prefixCount (K0 ∪ (↑early : Set ℕ)) n ≤
          GenLimit.PatientScope.prefixCount K0 n +
            GenLimit.PatientScope.prefixCount (↑early : Set ℕ) n := by
        unfold GenLimit.PatientScope.prefixCount
        rw [show GenLimit.PatientScope.prefixFinset (K0 ∪ (↑early : Set ℕ)) n =
            GenLimit.PatientScope.prefixFinset K0 n ∪
              GenLimit.PatientScope.prefixFinset (↑early : Set ℕ) n by
          classical
          ext x
          constructor
          · intro hx
            have hx' : x < n ∧ (x ∈ K0 ∨ x ∈ early) := by
              simpa [GenLimit.PatientScope.prefixFinset] using hx
            rcases hx' with ⟨hxn, hx0 | hxe⟩
            · apply Finset.mem_union_left
              simpa [GenLimit.PatientScope.prefixFinset] using And.intro hxn hx0
            · apply Finset.mem_union_right
              simpa [GenLimit.PatientScope.prefixFinset] using And.intro hxn hxe
          · intro hx
            have hx' : (x < n ∧ x ∈ K0) ∨ (x < n ∧ x ∈ early) := by
              simpa [GenLimit.PatientScope.prefixFinset] using hx
            simpa [GenLimit.PatientScope.prefixFinset] using
              hx'.elim (fun h => ⟨h.1, Or.inl h.2⟩) (fun h => ⟨h.1, Or.inr h.2⟩)]
        exact Finset.card_union_le _ _
      have hearly : GenLimit.PatientScope.prefixCount (↑early : Set ℕ) n ≤ early.card := by
        unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
        apply Finset.card_le_card
        intro x hx
        have hx' : x < n ∧ x ∈ early := by
          simpa [GenLimit.PatientScope.prefixFinset] using hx
        exact hx'.2
      omega
    _ ≤ (Nat.sqrt n + 1) + T := by
      apply Nat.add_le_add (prefixCount_K0_le n)
      exact le_trans Finset.card_image_le (by simp [early])

lemma eventual_density_ratio_tendsto_zero
    {output : Stream} (hvalid : GenLimit.NovelGeneratesInLimit input output K0) :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ K1) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K1 n : ℝ)) atTop (𝓝 0) := by
  rcases prefixCount_inter_K1_le_of_eventual hvalid with ⟨T, hbound⟩
  have hTdiv : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hmajor : Tendsto (fun n : ℕ =>
      3 * (((Nat.sqrt n + 1 : ℕ) : ℝ) / n + (T : ℝ) / n)) atTop (𝓝 0) := by
    convert (sqrt_ratio_tendsto_zero.add hTdiv).const_mul 3 using 1 <;> norm_num
  refine squeeze_zero
    (f := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ K1) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K1 n : ℝ))
    (g := fun n : ℕ =>
      3 * (((Nat.sqrt n + 1 : ℕ) : ℝ) / n + (T : ℝ) / n)) ?_ ?_ hmajor
  · intro n
    positivity
  · intro n
    by_cases hn : n < 2
    · interval_cases n
      · simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
      · refine le_trans (density_ratio_le_one _ _ 1) ?_
        have hT : (0 : ℝ) ≤ T := by positivity
        norm_num [Nat.sqrt]
        linarith
    have hnpos : 0 < n := by omega
    have hdenNat : n ≤ 3 * GenLimit.PatientScope.prefixCount K1 n := by
      have := prefixCount_K1_lower n
      omega
    have hden : (n : ℝ) / 3 ≤
        (GenLimit.PatientScope.prefixCount K1 n : ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
      exact_mod_cast (by simpa [mul_comm] using hdenNat)
    have hdenpos : 0 < (GenLimit.PatientScope.prefixCount K1 n : ℝ) :=
      lt_of_lt_of_le (by positivity) hden
    have hnum : (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ K1) n : ℝ) ≤
        ((Nat.sqrt n + 1 + T : ℕ) : ℝ) := by
      exact_mod_cast hbound n
    calc
      (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ K1) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K1 n : ℝ)
          ≤ ((Nat.sqrt n + 1 + T : ℕ) : ℝ) /
              (GenLimit.PatientScope.prefixCount K1 n : ℝ) :=
            div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ ((Nat.sqrt n + 1 + T : ℕ) : ℝ) / ((n : ℝ) / 3) := by
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 3 * (((Nat.sqrt n + 1 : ℕ) : ℝ) / n + (T : ℝ) / n) := by
            push_cast
            field_simp

lemma relativeUpperDensity_K1_zero_of_eventual
    {output : Stream} (hvalid : GenLimit.NovelGeneratesInLimit input output K0) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) K1 = 0 := by
  exact (eventual_density_ratio_tendsto_zero hvalid).limsup_eq


lemma pairObstruction : Stage3Case024.PairObstruction K0 K1 input := by
  intro Ω _ μ _ gen output hfollow hmeas hint0 hint1 hev0 hev1
  have hae1 : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) K1) =ᵐ[μ] (fun _ => 0) :=
    hev0.mono (fun ω hω => relativeUpperDensity_K1_zero_of_eventual hω)
  have hexp1 : Stage3Case024.expectedUpperDensity μ K1 input output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [MeasureTheory.integral_congr_ae hae1]
    simp
  have hexp0 : Stage3Case024.expectedUpperDensity μ K0 input output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst input (output ω)) K0 ∂μ)
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply MeasureTheory.integral_mono hint0 (MeasureTheory.integrable_const 1)
            intro ω
            exact relativeUpperDensity_le_one _ _
      _ = 1 := by
        rw [MeasureTheory.integral_const]
        simp [MeasureTheory.IsProbabilityMeasure.measure_univ,
          MeasureTheory.Measure.real]
  constructor
  · rw [hexp1, add_zero]
    exact hexp0
  · rw [hexp1]
    intro h
    linarith


noncomputable def freshCore (used : Finset ℕ) : ℕ :=
  Classical.choose (K0_infinite.exists_not_mem_finset used)

lemma freshCore_spec (used : Finset ℕ) : freshCore used ∈ K0 ∧ freshCore used ∉ used :=
  Classical.choose_spec (K0_infinite.exists_not_mem_finset used)

noncomputable def coreGenerator : Stage3Case024.OnlineGenerator := fun t inp out =>
  freshCore (Finset.image inp Finset.univ ∪ Finset.image out Finset.univ)

lemma coreGenerator_mem (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ) :
    coreGenerator t inp out ∈ K0 :=
  (freshCore_spec _).1

lemma coreGenerator_not_input (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ)
    (i : Fin (t + 1)) : coreGenerator t inp out ≠ inp i := by
  intro h
  apply (freshCore_spec
    (Finset.image inp Finset.univ ∪ Finset.image out Finset.univ)).2
  apply Finset.mem_union_left
  apply Finset.mem_image.2
  exact ⟨i, Finset.mem_univ _, h.symm⟩

lemma coreGenerator_not_output (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ)
    (i : Fin t) : coreGenerator t inp out ≠ out i := by
  intro h
  apply (freshCore_spec
    (Finset.image inp Finset.univ ∪ Finset.image out Finset.univ)).2
  apply Finset.mem_union_right
  apply Finset.mem_image.2
  exact ⟨i, Finset.mem_univ _, h.symm⟩

noncomputable def coreOutput (stream : Stream) : Stream :=
  Nat.lt_wfRel.wf.fix (fun t rec =>
    coreGenerator t (fun i => stream i) (fun i => rec i i.isLt))

lemma coreOutput_eq (stream : Stream) (t : ℕ) :
    coreOutput stream t = coreGenerator t
      (fun i => stream i) (fun i => coreOutput stream i) := by
  rw [coreOutput]
  rw [WellFounded.fix_eq]

lemma coreOutput_follows (stream : Stream) :
    Stage3Case024.Follows coreGenerator stream (coreOutput stream) := by
  intro t
  exact coreOutput_eq stream t

lemma coreOutput_novel {K : Language} (hsub : K0 ⊆ K) (stream : Stream) :
    GenLimit.NovelGeneratesInLimit stream (coreOutput stream) K := by
  refine ⟨0, fun t ht => ?_⟩
  have heq := coreOutput_eq stream t
  refine ⟨hsub (heq ▸ coreGenerator_mem t (fun i => stream i)
      (fun i => coreOutput stream i)), ?_, ?_⟩
  · intro hin
    unfold GenLimit.sample at hin
    rcases Finset.mem_image.1 hin with ⟨s, hs, hstream⟩
    have hslt : s < t + 1 := Finset.mem_range.1 hs
    exact coreGenerator_not_input t (fun i => stream i)
      (fun i => coreOutput stream i) ⟨s, hslt⟩ (heq ▸ hstream.symm)
  · intro s hst hearly
    exact coreGenerator_not_output t (fun i => stream i)
      (fun i => coreOutput stream i) ⟨s, hst⟩ (heq ▸ hearly.symm)

lemma globallyFeasible_of_core {r : ℕ} {family : Fin r → Language}
    (hcore : ∀ j, K0 ⊆ family j) : Stage3Case024.GloballyFeasible family := by
  refine ⟨coreGenerator, fun stream hlegal => ⟨coreOutput stream,
    coreOutput_follows stream, ?_⟩⟩
  intro j
  exact coreOutput_novel (hcore j) stream


def initialOdds (m : ℕ) : Language := {x | ∃ k < m, x = 2 * k + 1}

lemma initialOdds_mono {a b : ℕ} (hab : a ≤ b) : initialOdds a ⊆ initialOdds b := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hab, rfl⟩

lemma initialOdds_subset_oddSet (m : ℕ) : initialOdds m ⊆ oddSet := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, rfl⟩

lemma boundaryOdd_mem {a b : ℕ} (hab : a < b) : 2 * a + 1 ∈ initialOdds b :=
  ⟨a, hab, rfl⟩

lemma boundaryOdd_not_mem (a : ℕ) : 2 * a + 1 ∉ initialOdds a := by
  rintro ⟨k, hk, heq⟩
  have htwo : 2 * a = 2 * k := Nat.add_right_cancel heq
  have : a = k := Nat.eq_of_mul_eq_mul_left (by norm_num) htwo
  omega

noncomputable def targetFamily (r : ℕ) (i : Fin r) : Language :=
  if i.1 = r - 1 then K1 else K0 ∪ initialOdds i.1

lemma targetFamily_core_subset (r : ℕ) (i : Fin r) : K0 ⊆ targetFamily r i := by
  unfold targetFamily
  split
  · exact Set.subset_union_left
  · exact Set.subset_union_left

lemma targetFamily_subset_K1 (r : ℕ) (i : Fin r) : targetFamily r i ⊆ K1 := by
  unfold targetFamily
  split
  · exact Set.Subset.rfl
  · intro x hx
    rcases hx with hx | hx
    · exact Set.mem_union_left _ hx
    · exact Set.mem_union_right _ (initialOdds_subset_oddSet _ hx)

lemma legal_between {K : Language} (h0 : K0 ⊆ K) (h1 : K ⊆ K1) :
    Stage3Case024.Legal input K := by
  refine ⟨K0_infinite.mono h0, input_injective, ?_, vanishingNoise_mono h0⟩
  exact Set.Subset.trans h1 K1_no_omissions

lemma targetFamily_legal (r : ℕ) (i : Fin r) :
    Stage3Case024.Legal input (targetFamily r i) :=
  legal_between (targetFamily_core_subset r i) (targetFamily_subset_K1 r i)

lemma targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hiNot : i.1 ≠ r - 1 := by omega
  by_cases hjLast : j.1 = r - 1
  · have hfi : targetFamily r i = K0 ∪ initialOdds i.1 := by
      simp [targetFamily, hiNot]
    have hfj : targetFamily r j = K1 := by simp [targetFamily, hjLast]
    rw [hfi, hfj]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx0 | hxo
      · exact Set.mem_union_left _ hx0
      · exact Set.mem_union_right _ (initialOdds_subset_oddSet _ hxo)
    · intro hEq
      have hboundary : 2 * i.1 + 1 ∈ K1 :=
        Set.mem_union_right _ ⟨i.1, rfl⟩
      have hmem := hEq hboundary
      rcases hmem with hk0 | hsmall
      · exact (Nat.not_even_iff_odd.mpr ⟨i.1, by omega⟩) (K0_even hk0)
      · exact boundaryOdd_not_mem i.1 hsmall
  · have hfi : targetFamily r i = K0 ∪ initialOdds i.1 := by
      simp [targetFamily, hiNot]
    have hfj : targetFamily r j = K0 ∪ initialOdds j.1 := by
      simp [targetFamily, hjLast]
    rw [hfi, hfj]
    refine ⟨?_, ?_⟩
    · exact Set.union_subset_union_right K0 (initialOdds_mono (Nat.le_of_lt hij))
    · intro hEq
      have hboundary : 2 * i.1 + 1 ∈ K0 ∪ initialOdds j.1 :=
        Set.mem_union_right _ (boundaryOdd_mem hij)
      have hmem := hEq hboundary
      rcases hmem with hk0 | hsmall
      · exact (Nat.not_even_iff_odd.mpr ⟨i.1, by omega⟩) (K0_even hk0)
      · exact boundaryOdd_not_mem i.1 hsmall

lemma targetFamily_zero (r : ℕ) (hr : 2 ≤ r) :
    targetFamily r ⟨0, by omega⟩ = K0 := by
  have hnot : 0 ≠ r - 1 := by omega
  simp [targetFamily, hnot, initialOdds]

lemma targetFamily_last (r : ℕ) (hr : 2 ≤ r) :
    targetFamily r ⟨r - 1, by omega⟩ = K1 := by
  simp [targetFamily]

lemma targetFamily_manyObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) input := by
  intro Ω _ μ _ gen output hfollow hmeas hint hev
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hev0 : Stage3Case024.EventuallyFreshValid μ K0 input output := by
    simpa [first, targetFamily_zero r hr] using hev first
  have hae : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) K1) =ᵐ[μ] (fun _ => 0) :=
    hev0.mono (fun ω hω => relativeUpperDensity_K1_zero_of_eventual hω)
  refine ⟨last, ?_⟩
  have hlast : targetFamily r last = K1 := by
    simpa [last] using targetFamily_last r hr
  unfold Stage3Case024.expectedUpperDensity
  rw [hlast, MeasureTheory.integral_congr_ae hae]
  simp

lemma targetFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (targetFamily r) input := by
  refine ⟨targetFamily_strictlyNested hr, targetFamily_legal r,
    globallyFeasible_of_core (targetFamily_core_subset r),
    targetFamily_manyObstruction hr⟩

end Case024

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨K0, K1, input, K0_ssubset_K1, legal_K0, legal_K1, pairObstruction⟩
  · intro r hr
    exact ⟨targetFamily r, input, targetFamily_witness hr⟩

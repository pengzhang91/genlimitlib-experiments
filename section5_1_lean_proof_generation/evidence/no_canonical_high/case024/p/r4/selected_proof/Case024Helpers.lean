import Stage3Model
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable def squareTime (t : ℕ) : Prop := Nat.sqrt t ^ 2 = t

noncomputable instance (t : ℕ) : Decidable (squareTime t) := Classical.propDecidable _

def coreVal (t : ℕ) : ℕ := 2 * (t + 1) ^ 2 + 1

noncomputable def commonInput (t : ℕ) : ℕ :=
  if squareTime t then 2 * Nat.sqrt t else coreVal t

noncomputable def core : Language :=
  {x | ∃ t, ¬ squareTime t ∧ coreVal t = x}

noncomputable def full : Language := Set.range commonInput

lemma coreVal_injective : Function.Injective coreVal := by
  intro a b h
  simp only [coreVal] at h
  have hs : (a + 1) ^ 2 = (b + 1) ^ 2 := by omega
  nlinarith

lemma nonsquare_time (k : ℕ) : ¬ squareTime ((k + 1) ^ 2 + 1) := by
  intro h
  have hsqrt : Nat.sqrt ((k + 1) ^ 2 + 1) = k + 1 := by
    apply Nat.sqrt_add_eq'
    omega
  simp only [squareTime, hsqrt] at h
  omega

lemma nonsquare_time_injective :
    Function.Injective (fun k : ℕ => (k + 1) ^ 2 + 1) := by
  intro a b h
  nlinarith

lemma core_infinite : core.Infinite := by
  let f : ℕ → ℕ := fun k => coreVal ((k + 1) ^ 2 + 1)
  have hf : Function.Injective f :=
    coreVal_injective.comp nonsquare_time_injective
  apply (Set.infinite_range_of_injective hf).mono
  rintro x ⟨k, rfl⟩
  exact ⟨(k + 1) ^ 2 + 1, nonsquare_time k, rfl⟩

lemma commonInput_of_square {t : ℕ} (h : squareTime t) :
    commonInput t = 2 * Nat.sqrt t := by
  simp [commonInput, h]

lemma commonInput_of_not_square {t : ℕ} (h : ¬ squareTime t) :
    commonInput t = coreVal t := by
  simp [commonInput, h]

lemma commonInput_injective : Function.Injective commonInput := by
  intro a b h
  by_cases ha : squareTime a <;> by_cases hb : squareTime b
  · rw [commonInput_of_square ha, commonInput_of_square hb] at h
    have hr : Nat.sqrt a = Nat.sqrt b := by omega
    rw [← ha, ← hb, hr]
  · rw [commonInput_of_square ha, commonInput_of_not_square hb] at h
    simp only [coreVal] at h
    omega
  · rw [commonInput_of_not_square ha, commonInput_of_square hb] at h
    simp only [coreVal] at h
    omega
  · rw [commonInput_of_not_square ha, commonInput_of_not_square hb] at h
    exact coreVal_injective h

lemma core_subset_full : core ⊆ full := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, commonInput_of_not_square ht⟩

lemma zero_mem_full : 0 ∈ full := by
  refine ⟨0, ?_⟩
  have h : squareTime 0 := by simp [squareTime]
  simp [commonInput, h]

lemma zero_not_mem_core : 0 ∉ core := by
  rintro ⟨t, -, h⟩
  simp [coreVal] at h

lemma core_ssubset_full : core ⊂ full := by
  exact ⟨core_subset_full, fun h => zero_not_mem_core (h zero_mem_full)⟩

end Case024

namespace Case024

open Stage3Case024

noncomputable def coreIndex (x : ℕ) : ℕ := Nat.sqrt ((x - 1) / 2)

lemma coreIndex_coreVal (t : ℕ) : coreIndex (coreVal t) = t + 1 := by
  simp [coreIndex, coreVal, Nat.sqrt_eq']

lemma core_prefix_bound (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n ≤ Nat.sqrt n + 1 := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  rw [← Finset.card_range (Nat.sqrt n + 1)]
  apply Finset.card_le_card_of_injOn coreIndex
  · intro x hx
    change x ∈ GenLimit.PatientScope.prefixFinset core n at hx
    change coreIndex x ∈ Finset.range (Nat.sqrt n + 1)
    simp [GenLimit.PatientScope.prefixFinset] at hx
    rcases hx.2 with ⟨t, ht, rfl⟩
    simp only [coreIndex_coreVal, Finset.mem_range]
    have hlt : (t + 1) ^ 2 < n := by
      dsimp [coreVal] at hx
      omega
    exact Nat.lt_succ_of_le ((Nat.le_sqrt').2 (Nat.le_of_lt hlt))
  · intro x hx y hy hxy
    change x ∈ GenLimit.PatientScope.prefixFinset core n at hx
    change y ∈ GenLimit.PatientScope.prefixFinset core n at hy
    simp [GenLimit.PatientScope.prefixFinset] at hx hy
    rcases hx.2 with ⟨a, ha, rfl⟩
    rcases hy.2 with ⟨b, hb, rfl⟩
    simp only [coreIndex_coreVal] at hxy
    have : a = b := by omega
    subst b
    rfl

lemma square_time_prefix_bound (n : ℕ) :
    ((Finset.range n).filter squareTime).card ≤ Nat.sqrt n + 1 := by
  classical
  rw [← Finset.card_range (Nat.sqrt n + 1)]
  apply Finset.card_le_card_of_injOn Nat.sqrt
  · intro t ht
    change t ∈ (Finset.range n).filter squareTime at ht
    change Nat.sqrt t ∈ Finset.range (Nat.sqrt n + 1)
    simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
    exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (Nat.le_of_lt ht.1))
  · intro a ha b hb hab
    change a ∈ (Finset.range n).filter squareTime at ha
    change b ∈ (Finset.range n).filter squareTime at hb
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    rw [← ha.2, ← hb.2, hab]

lemma commonInput_mem_core_iff (t : ℕ) : commonInput t ∈ core ↔ ¬ squareTime t := by
  constructor
  · intro ht hs
    rcases ht with ⟨u, hu, hval⟩
    rw [commonInput_of_square hs] at hval
    simp only [coreVal] at hval
    omega
  · intro ht
    exact ⟨t, ht, (commonInput_of_not_square ht).symm⟩

lemma noiseCount_core (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonInput core n =
      ((Finset.range n).filter squareTime).card := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  congr 1
  ext t
  simp [commonInput_mem_core_iff]

lemma sqrt_cast_tendsto_atTop :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_atTop.2 ⟨b ^ 2, fun n hn => hn⟩] with n hn
  exact (Nat.le_sqrt').2 hn

lemma sqrt_add_one_div_tendsto_zero :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hspos : (0 : ℝ) < Nat.sqrt n := by
      exact_mod_cast (Nat.sqrt_pos.2 hn)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsle : ((Nat.sqrt n : ℝ) + 1) ≤ 2 * Nat.sqrt n := by
      have : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast (Nat.le_sqrt'.2 hn)
      linarith
    have hsquare : ((Nat.sqrt n : ℝ) ^ 2) ≤ n := by
      exact_mod_cast Nat.sqrt_le' n
    calc
      ((Nat.sqrt n + 1 : ℕ) : ℝ) / n = ((Nat.sqrt n : ℝ) + 1) / n := by norm_num
      _ ≤ (2 * Nat.sqrt n) / n := (div_le_div_iff_of_pos_right hnpos).2 hsle
      _ ≤ 2 * (Nat.sqrt n : ℝ)⁻¹ := by
        have hdiv : (2 * (Nat.sqrt n : ℝ)) / n ≤ 2 / (Nat.sqrt n : ℝ) := by
          apply (div_le_div_iff₀ hnpos hspos).2
          nlinarith [hsquare]
        simpa [div_eq_mul_inv] using hdiv
  · simpa using (tendsto_inv_atTop_zero.comp sqrt_cast_tendsto_atTop).const_mul (2 : ℝ)

lemma vanishingNoise_core :
    GenLimit.InfiniteContamination.VanishingNoise commonInput core := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero' ?_ ?_ sqrt_add_one_div_tendsto_zero
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · subst n
      norm_num
    · positivity
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · subst n
      norm_num
    · rw [noiseCount_core]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast square_time_prefix_bound n) (by positivity)

lemma legal_core : Stage3Case024.Legal commonInput core := by
  refine ⟨core_infinite, commonInput_injective, core_subset_full, vanishingNoise_core⟩

end Case024

namespace Case024

open Stage3Case024

lemma full_infinite : full.Infinite := core_infinite.mono core_subset_full

lemma noiseCount_mono_of_core_subset {K : Language} (hcore : core ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonInput K n ≤
      GenLimit.InfiniteContamination.noiseCount commonInput core n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hmem => ht.2 (hcore hmem)⟩

lemma vanishingNoise_of_core_subset {K : Language} (hcore : core ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise commonInput K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero' ?_ ?_ sqrt_add_one_div_tendsto_zero
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · subst n
      norm_num
    · positivity
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · subst n
      norm_num
    · exact div_le_div_of_nonneg_right
        (by
          exact_mod_cast (noiseCount_mono_of_core_subset hcore n).trans
            (by rw [noiseCount_core]; exact square_time_prefix_bound n))
        (by positivity)

lemma legal_of_between {K : Language} (hcore : core ⊆ K) (hfull : K ⊆ full) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨core_infinite.mono hcore, commonInput_injective, hfull,
    vanishingNoise_of_core_subset hcore⟩

lemma legal_full : Stage3Case024.Legal commonInput full :=
  legal_of_between core_subset_full (fun _ h => h)

lemma squareTime_sq (k : ℕ) : squareTime (k ^ 2) := by
  simp [squareTime, Nat.sqrt_eq']

lemma even_mem_full (k : ℕ) : 2 * k ∈ full := by
  refine ⟨k ^ 2, ?_⟩
  simp [commonInput, squareTime_sq, Nat.sqrt_eq']

lemma full_prefix_lower (n : ℕ) :
    n / 2 ≤ GenLimit.PatientScope.prefixCount full n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  rw [← Finset.card_range (n / 2)]
  apply Finset.card_le_card_of_injOn (fun k => 2 * k)
  · intro k hk
    change k ∈ Finset.range (n / 2) at hk
    change 2 * k ∈ GenLimit.PatientScope.prefixFinset full n
    simp only [Finset.mem_range] at hk
    simp [GenLimit.PatientScope.prefixFinset, even_mem_full]
    omega
  · intro a ha b hb hab
    exact Nat.mul_left_cancel (by omega) hab

lemma prefixCount_mono {A B : Language} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  simp [GenLimit.PatientScope.prefixFinset] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma core_union_finset_prefix_bound (s : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (core ∪ (↑s : Set ℕ)) n ≤
      Nat.sqrt n + 1 + s.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset (core ∪ (↑s : Set ℕ)) n).card ≤
        (GenLimit.PatientScope.prefixFinset core n ∪ s).card := by
      apply Finset.card_le_card
      intro x hx
      simp [GenLimit.PatientScope.prefixFinset] at hx ⊢
      rcases hx.2 with hxcore | hxs
      · exact Or.inl ⟨hx.1, hxcore⟩
      · exact Or.inr hxs
    _ ≤ (GenLimit.PatientScope.prefixFinset core n).card + s.card :=
      Finset.card_union_le _ _
    _ ≤ Nat.sqrt n + 1 + s.card := Nat.add_le_add_right (core_prefix_bound n) _

lemma sparse_ratio_tendsto_zero (A : Language) (s : Finset ℕ)
    (hA : A ⊆ core ∪ (↑s : Set ℕ)) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ full) n : ℝ) /
          (GenLimit.PatientScope.prefixCount full n : ℝ))
      atTop (nhds 0) := by
  have hbound : Tendsto
      (fun n : ℕ => (3 : ℝ) * (((Nat.sqrt n + 1 + s.card : ℕ) : ℝ) / n))
      atTop (nhds 0) := by
    have hc := tendsto_const_div_atTop_nhds_zero_nat (s.card : ℝ)
    have hadd : Tendsto
        (fun n : ℕ => (((Nat.sqrt n + 1 + s.card : ℕ) : ℝ) / n))
        atTop (nhds 0) := by
      convert sqrt_add_one_div_tendsto_zero.add hc using 1
      · ext n
        push_cast
        rw [add_div]
      · norm_num
    simpa using hadd.const_mul (3 : ℝ)
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with n
    positivity
  · filter_upwards [Filter.eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
    let numerator := GenLimit.PatientScope.prefixCount (A ∩ full) n
    let denominator := GenLimit.PatientScope.prefixCount full n
    have hnum_nat : numerator ≤ Nat.sqrt n + 1 + s.card := by
      apply (prefixCount_mono (n := n) ?_).trans (core_union_finset_prefix_bound s n)
      intro x hx
      exact hA hx.1
    have hden_nat : n / 2 ≤ denominator := full_prefix_lower n
    have hden_pos_nat : 0 < denominator := lt_of_lt_of_le (by omega : 0 < n / 2) hden_nat
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
    have hden_pos : (0 : ℝ) < denominator := by exact_mod_cast hden_pos_nat
    have hnum : (numerator : ℝ) ≤ (Nat.sqrt n + 1 + s.card : ℕ) := by exact_mod_cast hnum_nat
    have hn3_nat : n ≤ 3 * denominator := by
      have : n ≤ 3 * (n / 2) := by omega
      exact this.trans (Nat.mul_le_mul_left 3 hden_nat)
    have hn3 : (n : ℝ) ≤ 3 * denominator := by exact_mod_cast hn3_nat
    change (numerator : ℝ) / denominator ≤ 3 * (((Nat.sqrt n + 1 + s.card : ℕ) : ℝ) / n)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hden_pos hn_pos).2
    calc
      (numerator : ℝ) * n ≤ (Nat.sqrt n + 1 + s.card : ℕ) * n :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ (Nat.sqrt n + 1 + s.card : ℕ) * (3 * denominator) :=
        mul_le_mul_of_nonneg_left hn3 (by positivity)
      _ = (3 * ((Nat.sqrt n + 1 + s.card : ℕ) : ℝ)) * denominator := by ring

lemma relativeUpperDensity_sparse (A : Language) (s : Finset ℕ)
    (hA : A ⊆ core ∪ (↑s : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A full = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  exact (sparse_ratio_tendsto_zero A s hA).limsup_eq

end Case024

namespace Case024

open Stage3Case024

lemma ratio_nonneg (A K : Language) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

lemma ratio_le_one (A K : Language) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  let numerator := GenLimit.PatientScope.prefixCount (A ∩ K) n
  let denominator := GenLimit.PatientScope.prefixCount K n
  have hnum : numerator ≤ denominator := prefixCount_mono Set.inter_subset_right n
  by_cases hd : denominator = 0
  · simp [denominator, hd]
  · have hdpos : (0 : ℝ) < denominator := by exact_mod_cast Nat.pos_of_ne_zero hd
    exact (div_le_one hdpos).2 (by exact_mod_cast hnum)

lemma relativeUpperDensity_nonneg (A K : Language) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  exact Filter.le_limsup_of_frequently_le
    (Filter.Frequently.of_forall (ratio_nonneg A K))
    (isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (ratio_le_one A K)))

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  exact Filter.limsup_le_of_le
    (hf := isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall (ratio_nonneg A K)))
    (Filter.Eventually.of_forall (ratio_le_one A K))

lemma generatorFirst_subset_core_finite {output : Stream}
    (h : GenLimit.NovelGeneratesInLimit commonInput output core) :
    ∃ s : Finset ℕ, GenLimit.GeneratorFirst commonInput output ⊆ core ∪ (↑s : Set ℕ) := by
  rcases h with ⟨T, hT⟩
  refine ⟨(Finset.range T).image output, ?_⟩
  rintro x ⟨t, rfl, hfirst⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht).1
  · exact Or.inr (by simp; exact ⟨t, Nat.lt_of_not_ge ht, rfl⟩)

lemma generatorFirst_full_density_zero {output : Stream}
    (h : GenLimit.NovelGeneratesInLimit commonInput output core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst commonInput output) full = 0 := by
  rcases generatorFirst_subset_core_finite h with ⟨s, hs⟩
  exact relativeUpperDensity_sparse _ s hs

lemma expected_full_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (output : Ω → Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ core commonInput output) :
    Stage3Case024.expectedUpperDensity μ full commonInput output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [hvalid] with ω hω
  exact generatorFirst_full_density_zero hω

lemma pairObstruction_core_full :
    Stage3Case024.PairObstruction core full commonInput := by
  intro Ω _ μ _ gen output hfollows hmeas hintCore hintFull hvalidCore hvalidFull
  have hzero : Stage3Case024.expectedUpperDensity μ full commonInput output = 0 :=
    expected_full_zero μ output hvalidCore
  have hle : Stage3Case024.expectedUpperDensity μ core commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := MeasureTheory.integrable_const 1
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) core ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ :=
        MeasureTheory.integral_mono_ae hintCore hconst
          (Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rw [hzero]
    intro h
    linarith [h.2]

end Case024

namespace Case024

open Stage3Case024

noncomputable def chooseCoreFresh (seen : Finset ℕ) : ℕ :=
  Classical.choose (core_infinite.exists_not_mem_finset seen)

lemma chooseCoreFresh_mem (seen : Finset ℕ) : chooseCoreFresh seen ∈ core :=
  (Classical.choose_spec (core_infinite.exists_not_mem_finset seen)).1

lemma chooseCoreFresh_not_mem (seen : Finset ℕ) : chooseCoreFresh seen ∉ seen :=
  (Classical.choose_spec (core_infinite.exists_not_mem_finset seen)).2

noncomputable def coreGenerator : Stage3Case024.OnlineGenerator :=
  fun t input output =>
    chooseCoreFresh ((Finset.univ.image input) ∪ (Finset.univ.image output))


lemma coreGenerator_mem (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    coreGenerator t input output ∈ core := by
  exact chooseCoreFresh_mem _

lemma coreGenerator_ne_input (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (i : Fin (t + 1)) : coreGenerator t input output ≠ input i := by
  intro h
  apply chooseCoreFresh_not_mem ((Finset.univ.image input) ∪ (Finset.univ.image output))
  apply Finset.mem_union_left
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, h.symm⟩

lemma coreGenerator_ne_output (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (i : Fin t) : coreGenerator t input output ≠ output i := by
  intro h
  apply chooseCoreFresh_not_mem ((Finset.univ.image input) ∪ (Finset.univ.image output))
  apply Finset.mem_union_right
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, h.symm⟩

noncomputable def coreRun (input : Stream) (t : ℕ) : ℕ :=
  coreGenerator t (fun i => input i) (fun i => coreRun input i)
termination_by t
decreasing_by exact i.isLt

lemma coreRun_follows (input : Stream) :
    Stage3Case024.Follows coreGenerator input (coreRun input) := by
  intro t
  rw [coreRun]

lemma coreRun_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (coreRun input) core := by
  refine ⟨0, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · rw [coreRun]
    exact coreGenerator_mem _ _ _
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image] at hmem
    rcases hmem with ⟨s, hs, hsi⟩
    have hrun := coreRun_follows input t
    apply coreGenerator_ne_input t (fun i => input i) (fun i => coreRun input i) ⟨s, Finset.mem_range.mp hs⟩
    exact hrun.symm.trans hsi.symm
  · intro s hs heq
    have hrun := coreRun_follows input t
    apply coreGenerator_ne_output t (fun i => input i) (fun i => coreRun input i) ⟨s, hs⟩
    exact hrun.symm.trans heq.symm

lemma coreRun_novel_superset (input : Stream) {K : Language} (hcore : core ⊆ K) :
    GenLimit.NovelGeneratesInLimit input (coreRun input) K := by
  rcases coreRun_novel input with ⟨T, hT⟩
  exact ⟨T, fun t ht => ⟨hcore (hT t ht).1, (hT t ht).2.1, (hT t ht).2.2⟩⟩

lemma globallyFeasible_of_core_subset {r : ℕ} (family : Fin r → Language)
    (hcore : ∀ j, core ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨coreGenerator, fun input hlegal => ⟨coreRun input, coreRun_follows input, ?_⟩⟩
  intro j
  exact coreRun_novel_superset input (hcore j)

end Case024

namespace Case024

open Stage3Case024

noncomputable def extras (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun k => 2 * k)

lemma mem_extras_iff {x n : ℕ} : x ∈ extras n ↔ ∃ k < n, 2 * k = x := by
  simp [extras]

lemma even_not_mem_core (k : ℕ) : 2 * k ∉ core := by
  rintro ⟨t, ht, hval⟩
  simp only [coreVal] at hval
  omega

lemma extras_mono {a b : ℕ} (h : a ≤ b) : extras a ⊆ extras b := by
  intro x hx
  rcases mem_extras_iff.mp hx with ⟨k, hk, rfl⟩
  exact mem_extras_iff.mpr ⟨k, lt_of_lt_of_le hk h, rfl⟩

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if j.1 + 1 = r then full else core ∪ (↑(extras j.1) : Set ℕ)

lemma core_subset_nestedFamily {r : ℕ} (j : Fin r) : core ⊆ nestedFamily r j := by
  intro x hx
  simp only [nestedFamily]
  split_ifs
  · exact core_subset_full hx
  · exact Or.inl hx

lemma nestedFamily_subset_full {r : ℕ} (j : Fin r) : nestedFamily r j ⊆ full := by
  intro x hx
  simp only [nestedFamily] at hx
  split at hx
  next hlast => exact hx
  next hnot =>
    rcases hx with hx | hx
    · exact core_subset_full hx
    · rcases mem_extras_iff.mp hx with ⟨k, hk, rfl⟩
      exact even_mem_full k

lemma nestedFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal commonInput (nestedFamily r j) :=
  legal_of_between (core_subset_nestedFamily j) (nestedFamily_subset_full j)

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hi_not_last : i.1 + 1 ≠ r := by omega
  have hi_lt_j : i.1 < j.1 := hij
  constructor
  · intro x hx
    simp only [nestedFamily, hi_not_last, if_false] at hx ⊢
    by_cases hj : j.1 + 1 = r
    · simp [hj]
      rcases hx with hxcore | hxextra
      · exact core_subset_full hxcore
      · rcases mem_extras_iff.mp hxextra with ⟨k, hk, rfl⟩
        exact even_mem_full k
    · simp [hj]
      rcases hx with hxcore | hxextra
      · exact Or.inl hxcore
      · exact Or.inr (extras_mono (Nat.le_of_lt hi_lt_j) hxextra)
  · intro heq
    have hw_j : 2 * i.1 ∈ nestedFamily r j := by
      simp only [nestedFamily]
      by_cases hj : j.1 + 1 = r
      · simp [hj, even_mem_full]
      · simp [hj]
        exact Or.inr (mem_extras_iff.mpr ⟨i.1, hi_lt_j, rfl⟩)
    have hw_i : 2 * i.1 ∉ nestedFamily r i := by
      simp [nestedFamily, hi_not_last, even_not_mem_core, mem_extras_iff]
    exact hw_i (heq hw_j)

noncomputable def lastIndex (r : ℕ) (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

lemma nestedFamily_last_eq_full {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r (lastIndex r (by omega)) = full := by
  simp [nestedFamily, lastIndex]
  omega

lemma nestedFamily_zero_eq_core {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r (⟨0, by omega⟩ : Fin r) = core := by
  simp [nestedFamily, extras]
  omega

lemma manyTargetObstruction_nested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output hfollows hmeas hint hvalid
  let jlast : Fin r := lastIndex r (by omega)
  let jzero : Fin r := ⟨0, by omega⟩
  have hlast : nestedFamily r jlast = full := nestedFamily_last_eq_full hr
  have hzero : nestedFamily r jzero = core := nestedFamily_zero_eq_core hr
  have hcorevalid : Stage3Case024.EventuallyFreshValid μ core commonInput output := by
    filter_upwards [hvalid jzero] with ω hω
    simpa [hzero] using hω
  refine ⟨jlast, ?_⟩
  rw [hlast]
  exact expected_full_zero μ output hcorevalid

lemma manyTargetWitness_nested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_, globallyFeasible_of_core_subset _
    (fun j => core_subset_nestedFamily j), manyTargetObstruction_nested hr⟩
  intro j
  exact nestedFamily_legal j

end Case024

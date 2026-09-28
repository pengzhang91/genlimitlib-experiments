import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024

def squares : Set ℕ := {n | ∃ k, k * k = n}
def nonsquares : Set ℕ := squaresᶜ

lemma mem_nonsquares_iff (n : ℕ) : n ∈ nonsquares ↔ n ∉ squares := by
  simp [nonsquares]

lemma squares_iff (n : ℕ) : n ∈ squares ↔ Nat.sqrt n * Nat.sqrt n = n := by
  simp [squares, Nat.exists_mul_self]

lemma squares_infinite : squares.Infinite := by
  have hi : Function.Injective (fun n : ℕ => n * n) := fun a b h => Nat.mul_self_inj.mp h
  refine (Set.infinite_range_of_injective hi).mono ?_
  rintro x ⟨n, rfl⟩
  exact ⟨n, rfl⟩

lemma nonsquares_infinite : nonsquares.Infinite := by
  let f : ℕ → ℕ := fun n => (n + 1) * (n + 1) + (n + 1)
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    nlinarith
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro _ ⟨n, rfl⟩
  simp only [nonsquares, Set.mem_compl_iff, squares_iff]
  let v := (n + 1) * (n + 1) + (n + 1)
  have hsqrt : Nat.sqrt v = n + 1 := by
    symm
    apply Nat.eq_sqrt.mpr
    constructor <;> dsimp [v] <;> nlinarith
  rw [hsqrt]
  dsimp [v, f]
  nlinarith

noncomputable def swapEquiv : squares ≃ nonsquares := by
  classical
  letI : Infinite squares := squares_infinite.to_subtype
  letI : Infinite nonsquares := nonsquares_infinite.to_subtype
  letI : Denumerable squares := Nat.Subtype.denumerable squares
  letI : Denumerable nonsquares := Nat.Subtype.denumerable nonsquares
  exact Denumerable.equiv₂ squares nonsquares

noncomputable def input : ℕ → ℕ := by
  classical
  exact fun n =>
    if h : n ∈ squares then (swapEquiv ⟨n, h⟩ : ℕ)
    else (swapEquiv.symm ⟨n, (mem_nonsquares_iff n).2 h⟩ : ℕ)

lemma input_of_mem {n : ℕ} (h : n ∈ squares) : input n = swapEquiv ⟨n, h⟩ := by
  classical
  simp only [input, dif_pos h]

lemma input_of_not_mem {n : ℕ} (h : n ∉ squares) :
    input n = swapEquiv.symm ⟨n, (mem_nonsquares_iff n).2 h⟩ := by
  classical
  simp only [input, dif_neg h]

lemma input_mem_iff (n : ℕ) : input n ∈ squares ↔ n ∉ squares := by
  classical
  by_cases h : n ∈ squares
  · rw [input_of_mem h]
    exact iff_of_false ((mem_nonsquares_iff _).1 (swapEquiv ⟨n, h⟩).property) (not_not.mpr h)
  · rw [input_of_not_mem h]
    exact iff_of_true (swapEquiv.symm ⟨n, (mem_nonsquares_iff n).2 h⟩).property h

lemma input_injective : Function.Injective input := by
  classical
  intro a b hab
  by_cases ha : a ∈ squares <;> by_cases hb : b ∈ squares
  · rw [input_of_mem ha, input_of_mem hb] at hab
    exact congrArg Subtype.val (swapEquiv.injective (Subtype.ext hab))
  · have hia : input a ∉ squares := fun h => (input_mem_iff a).mp h ha
    have hib : input b ∈ squares := (input_mem_iff b).mpr hb
    exact False.elim (hia (hab ▸ hib))
  · have hia : input a ∈ squares := (input_mem_iff a).mpr ha
    have hib : input b ∉ squares := fun h => (input_mem_iff b).mp h hb
    exact False.elim (hib (hab ▸ hia))
  · rw [input_of_not_mem ha, input_of_not_mem hb] at hab
    exact congrArg Subtype.val (swapEquiv.symm.injective (Subtype.ext hab))

lemma input_surjective : Function.Surjective input := by
  classical
  intro y
  by_cases hy : y ∈ squares
  · let x : nonsquares := swapEquiv ⟨y, hy⟩
    refine ⟨x, ?_⟩
    have hx : (x : ℕ) ∉ squares := by exact (mem_nonsquares_iff _).1 x.property
    rw [input_of_not_mem hx]
    exact congrArg Subtype.val (swapEquiv.symm_apply_apply ⟨y, hy⟩)
  · let x : squares := swapEquiv.symm ⟨y, (mem_nonsquares_iff y).2 hy⟩
    refine ⟨x, ?_⟩
    rw [input_of_mem x.property]
    exact congrArg Subtype.val (swapEquiv.apply_symm_apply ⟨y, (mem_nonsquares_iff y).2 hy⟩)

lemma prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  classical
  let s := GenLimit.PatientScope.prefixFinset squares n
  have hinj : Set.InjOn Nat.sqrt (s : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a < n ∧ a ∈ squares := by
      simpa [s, GenLimit.PatientScope.prefixFinset] using ha
    have hb' : b < n ∧ b ∈ squares := by
      simpa [s, GenLimit.PatientScope.prefixFinset] using hb
    have has : a ∈ squares := ha'.2
    have hbs : b ∈ squares := hb'.2
    rw [squares_iff] at has hbs
    nlinarith
  have hsub : s.image Nat.sqrt ⊆ Finset.range (Nat.sqrt n + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨a, ha, rfl⟩
    have ha' : a < n ∧ a ∈ squares := by
      simpa [s, GenLimit.PatientScope.prefixFinset] using ha
    have han : a < n := ha'.1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_sqrt han.le))
  calc
    GenLimit.PatientScope.prefixCount squares n = s.card := rfl
    _ = (s.image Nat.sqrt).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (Nat.sqrt n + 1)).card := Finset.card_le_card hsub
    _ = Nat.sqrt n + 1 := Finset.card_range _

lemma tendsto_sqrt_nat_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b * b, fun a ha => ?_⟩
  exact Nat.le_sqrt.mpr ha

lemma tendsto_squares_ratio_zero :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_sqrt_nat_atTop).inv_tendsto_atTop
  have hn : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_atTop_nhds_zero_nat
  have hupper : Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ))⁻¹ + ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hsqrt.add hn
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hnpos
    have hc := prefixCount_squares_le n
    have hs := Nat.sqrt_le n
    have hspos : 0 < (Nat.sqrt n : ℝ) := by positivity
    have hnreal : 0 < (n : ℝ) := by positivity
    calc
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ)
          ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ) := by gcongr
      _ = (Nat.sqrt n : ℝ) / (n : ℝ) + ((n : ℝ))⁻¹ := by
        push_cast
        field_simp
      _ ≤ ((Nat.sqrt n : ℝ))⁻¹ + ((n : ℝ))⁻¹ := by
        gcongr
        rw [div_le_iff₀ hnreal]
        field_simp
        have hsreal : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hs
        simpa [pow_two] using hsreal
  · exact hupper

lemma prefixCount_inter_univ (A : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n =
      GenLimit.PatientScope.prefixCount A n := by
  rw [show A ∩ Set.univ = A by ext; simp]

lemma prefixCount_univ (n : ℕ) : GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma squares_density_zero :
    Stage3Case024.relativeUpperDensity squares Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  simpa [prefixCount_inter_univ, prefixCount_univ] using tendsto_squares_ratio_zero

end Case024

namespace Case024

lemma noOmissions_input (K : Set ℕ) :
    GenLimit.InfiniteContamination.NoOmissions input K := by
  intro x hx
  exact input_surjective x

lemma noiseCount_input_squares (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input squares n =
      GenLimit.PatientScope.prefixCount squares n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
    GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [input_mem_iff]
  tauto

lemma input_squares_vanishingNoise :
    GenLimit.InfiniteContamination.VanishingNoise input squares := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
    GenLimit.InfiniteContamination.empiricalNoiseRate
  refine (tendsto_congr' ?_).2 tendsto_squares_ratio_zero
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
  simp only [Nat.ne_of_gt hn, if_false, noiseCount_input_squares]

lemma input_univ_vanishingNoise :
    GenLimit.InfiniteContamination.VanishingNoise input Set.univ := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
    GenLimit.InfiniteContamination.empiricalNoiseRate
    GenLimit.InfiniteContamination.noiseCount
  simp

lemma legal_squares : Stage3Case024.Legal input squares := by
  refine ⟨squares_infinite, input_injective, noOmissions_input squares, ?_⟩
  exact input_squares_vanishingNoise

lemma legal_univ : Stage3Case024.Legal input Set.univ := by
  refine ⟨Set.infinite_univ, input_injective, noOmissions_input Set.univ, ?_⟩
  exact input_univ_vanishingNoise

end Case024

namespace Case024

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  let u := GenLimit.PatientScope.prefixFinset (A ∪ B) n
  let a := GenLimit.PatientScope.prefixFinset A n
  let b := GenLimit.PatientScope.prefixFinset B n
  have hu : u ⊆ a ∪ b := by
    intro x hx
    simp only [u, a, b, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range, Finset.mem_union] at hx ⊢
    rcases hx with ⟨hxn, hxA | hxB⟩
    · exact Or.inl ⟨hxn, hxA⟩
    · exact Or.inr ⟨hxn, hxB⟩
  change u.card ≤ a.card + b.card
  exact (Finset.card_le_card hu).trans (Finset.card_union_le a b)

lemma prefixCount_coe_finset_le (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (F : Set ℕ) n ≤ F.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_coe] at hx ⊢
  exact hx.2

lemma tendsto_const_div_nat_zero (c : ℕ) :
    Tendsto (fun n : ℕ => (c : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_atTop_nhds_zero_nat
  simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hn :
    Tendsto (fun n : ℕ => (c : ℝ) * ((n : ℝ))⁻¹) atTop (𝓝 ((c : ℝ) * 0)))

lemma tendsto_sparse_union_ratio_zero (A : Set ℕ) (F : Finset ℕ)
    (hA : A ⊆ squares ∪ (F : Set ℕ)) :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ) +
        (F.card : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_squares_ratio_zero.add (tendsto_const_div_nat_zero F.card)
  refine squeeze_zero' (g := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ) +
        (F.card : ℝ) / (n : ℝ)) ?_ ?_ hupper
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hcount := (prefixCount_mono hA n).trans (prefixCount_union_le squares (F : Set ℕ) n)
    have hF := prefixCount_coe_finset_le F n
    have hnreal : 0 < (n : ℝ) := by positivity
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hnreal).2
    exact_mod_cast hcount.trans (Nat.add_le_add_left hF _)

lemma relativeUpperDensity_univ_eq_zero_of_sparse (A : Set ℕ) (F : Finset ℕ)
    (hA : A ⊆ squares ∪ (F : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  simpa [prefixCount_inter_univ, prefixCount_univ] using
    tendsto_sparse_union_ratio_zero A F hA

lemma generatorFirst_sparse_of_novel {output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    ∃ F : Finset ℕ,
      GenLimit.GeneratorFirst input output ⊆ squares ∪ (F : Set ℕ) := by
  rcases h with ⟨T, hT⟩
  let F := (Finset.range T).image output
  refine ⟨F, ?_⟩
  intro x hx
  rcases hx with ⟨t, rfl, _⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht).1
  · exact Or.inr (by
      simp only [F, Finset.mem_coe, Finset.mem_image]
      exact ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge ht), rfl⟩)

lemma generatorFirst_univ_density_zero_of_novel {output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  rcases generatorFirst_sparse_of_novel h with ⟨F, hF⟩
  exact relativeUpperDensity_univ_eq_zero_of_sparse _ F hF

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  refine limsup_le_of_le (u := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) (hf := ?_) (h := ?_)
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  exact Eventually.of_forall fun n => by
    have hc : GenLimit.PatientScope.prefixCount (A ∩ K) n ≤
        GenLimit.PatientScope.prefixCount K n :=
      prefixCount_mono (Set.inter_subset_right) n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · have hnz : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 := by omega
      simp [hz, hnz]
    · have hden : 0 < (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity
      rw [div_le_one hden]
      exact_mod_cast hc

end Case024

namespace Case024

lemma squares_ssubset_univ : squares ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro hEq
  obtain ⟨x, hx⟩ := nonsquares_infinite.nonempty
  have hnot : x ∉ squares := (mem_nonsquares_iff x).1 hx
  exact hnot (by rw [hEq]; trivial)

lemma pairObstruction : Stage3Case024.PairObstruction squares Set.univ input := by
  intro Ω _ μ _ gen output _ _ hint0 _ hev0 _
  have hzero_ae : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 :=
    hev0.mono fun ω hω => generatorFirst_univ_density_zero_of_novel hω
  have hE1 : Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    simpa using integral_congr_ae hzero_ae
  have hE0le : Stage3Case024.expectedUpperDensity μ squares input output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst input (output ω)) squares ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hint0 (integrable_const 1)
        exact Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · linarith
  · intro hboth
    rcases hboth with ⟨_, h1⟩
    rw [hE1] at h1
    norm_num at h1

end Case024

namespace Case024

noncomputable def globalGen : Stage3Case024.OnlineGenerator := fun t inp out =>
  let b := (∑ i, inp i) + (∑ i, out i) + 1
  b * b

lemma globalGen_square (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ) :
    globalGen t inp out ∈ squares := by
  unfold globalGen
  exact ⟨(∑ i, inp i) + (∑ i, out i) + 1, rfl⟩

lemma globalGen_input_lt (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ)
    (i : Fin (t + 1)) : inp i < globalGen t inp out := by
  have hi : inp i ≤ ∑ j, inp j := by
    simpa using Finset.single_le_sum (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold globalGen
  let b := (∑ j, inp j) + (∑ j, out j) + 1
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hib : inp i < b := by dsimp [b]; omega
  have hbb : b ≤ b * b := by nlinarith
  exact hib.trans_le hbb

lemma globalGen_output_lt (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ)
    (i : Fin t) : out i < globalGen t inp out := by
  have hi : out i ≤ ∑ j, out j := by
    simpa using Finset.single_le_sum (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold globalGen
  let b := (∑ j, inp j) + (∑ j, out j) + 1
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hib : out i < b := by dsimp [b]; omega
  have hbb : b ≤ b * b := by nlinarith
  exact hib.trans_le hbb

noncomputable def globalOutput (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  globalGen t (fun i => stream i) (fun i => globalOutput stream i)
termination_by t

lemma globalOutput_follows (stream : ℕ → ℕ) :
    Stage3Case024.Follows globalGen stream (globalOutput stream) := by
  intro t
  rw [globalOutput]

lemma globalOutput_novel (stream : ℕ → ℕ) (K : Set ℕ) (hK : squares ⊆ K) :
    GenLimit.NovelGeneratesInLimit stream (globalOutput stream) K := by
  refine ⟨0, fun t _ => ?_⟩
  refine ⟨hK (by
    rw [globalOutput]
    exact globalGen_square t (fun i => stream i) (fun i => globalOutput stream i)), ?_, ?_⟩
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨s, hs, heq⟩
    have hslt : s < t + 1 := Finset.mem_range.mp hs
    have hlt := globalGen_input_lt t (fun i => stream i) (fun i => globalOutput stream i)
      ⟨s, hslt⟩
    rw [← globalOutput, heq] at hlt
    exact (Nat.lt_irrefl _ hlt)
  · intro s hs
    have hlt := globalGen_output_lt t (fun i => stream i) (fun i => globalOutput stream i)
      ⟨s, hs⟩
    rw [← globalOutput] at hlt
    exact Nat.ne_of_lt hlt

end Case024

namespace Case024

lemma noiseCount_mono_target {S K : Set ℕ} (hSK : S ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input K n ≤
      GenLimit.InfiniteContamination.noiseCount input S n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hs => ht.2 (hSK hs)⟩

lemma input_vanishingNoise_of_contains_squares (K : Set ℕ) (hSK : squares ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise input K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero' (g := GenLimit.InfiniteContamination.empiricalNoiseRate input squares) ?_ ?_ input_squares_vanishingNoise
  · exact Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split <;> positivity
  · exact Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false]
        have hcount := noiseCount_mono_target hSK n
        have hnreal : 0 < (n : ℝ) := by positivity
        exact (div_le_div_iff_of_pos_right hnreal).2 (by exact_mod_cast hcount)

lemma legal_of_contains_squares (K : Set ℕ) (hSK : squares ⊆ K) :
    Stage3Case024.Legal input K := by
  refine ⟨squares_infinite.mono hSK, input_injective, noOmissions_input K, ?_⟩
  exact input_vanishingNoise_of_contains_squares K hSK

end Case024

namespace Case024

def extra (n : ℕ) : ℕ := (n + 1) * (n + 1) + (n + 1)

lemma extra_injective : Function.Injective extra := by
  intro a b h
  dsimp [extra] at h
  nlinarith

lemma extra_not_square (n : ℕ) : extra n ∉ squares := by
  rw [squares_iff]
  have hsqrt : Nat.sqrt (extra n) = n + 1 := by
    symm
    apply Nat.eq_sqrt.mpr
    constructor <;> dsimp [extra] <;> nlinarith
  rw [hsqrt]
  dsimp [extra]
  nlinarith

def core (j : ℕ) : Set ℕ :=
  squares ∪ {x | ∃ k, k < j ∧ x = extra k}

def finiteFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if j.val = r - 1 then Set.univ else core j.val

lemma squares_subset_core (j : ℕ) : squares ⊆ core j := by
  intro x hx
  exact Or.inl hx

lemma extra_not_mem_core (i : ℕ) : extra i ∉ core i := by
  intro h
  rcases h with hs | ⟨k, hk, heq⟩
  · exact extra_not_square i hs
  · have hki : k = i := extra_injective (heq.symm)
    omega

lemma core_mono {i j : ℕ} (hij : i < j) : core i ⊆ core j := by
  intro x hx
  rcases hx with hs | ⟨k, hk, heq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨k, hk.trans hij, heq⟩

lemma core_ssubset_core {i j : ℕ} (hij : i < j) : core i ⊂ core j := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨core_mono hij, ?_⟩
  intro heq
  have hjmem : extra i ∈ core j := Or.inr ⟨i, hij, rfl⟩
  have himem : extra i ∈ core i := by rw [heq]; exact hjmem
  exact extra_not_mem_core i himem

lemma core_ssubset_univ (i : ℕ) : core i ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  apply extra_not_mem_core i
  rw [heq]
  trivial

lemma finiteFamily_contains_squares {r : ℕ} (j : Fin r) :
    squares ⊆ finiteFamily r j := by
  unfold finiteFamily
  split
  · exact Set.subset_univ _
  · exact squares_subset_core _

lemma finiteFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (finiteFamily r) := by
  intro i j hij
  have hi : i.val ≠ r - 1 := by omega
  rw [finiteFamily, if_neg hi, finiteFamily]
  by_cases hj : j.val = r - 1
  · rw [if_pos hj]
    exact core_ssubset_univ i.val
  · rw [if_neg hj]
    exact core_ssubset_core hij

lemma finiteFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal input (finiteFamily r j) :=
  legal_of_contains_squares _ (finiteFamily_contains_squares j)

lemma finiteFamily_globalFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (finiteFamily r) := by
  refine ⟨globalGen, fun stream _ => ⟨globalOutput stream, globalOutput_follows stream, ?_⟩⟩
  intro j
  exact globalOutput_novel stream (finiteFamily r j) (finiteFamily_contains_squares j)

lemma finiteFamily_zero_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (finiteFamily r) input := by
  intro Ω _ μ _ gen output _ _ _ hev
  let j0 : Fin r := ⟨0, by omega⟩
  let jl : Fin r := ⟨r - 1, Nat.sub_lt (by omega) (by omega)⟩
  have hj0 : finiteFamily r j0 = squares := by
    ext x
    simp [finiteFamily, j0, core]
    omega
  have hjl : finiteFamily r jl = Set.univ := by
    simp [finiteFamily, jl]
  have hnovel : ∀ᵐ ω ∂μ, GenLimit.NovelGeneratesInLimit input (output ω) squares := by
    simpa [hj0] using hev j0
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 :=
    hnovel.mono fun ω hω => generatorFirst_univ_density_zero_of_novel hω
  refine ⟨jl, ?_⟩
  rw [hjl]
  unfold Stage3Case024.expectedUpperDensity
  simpa using integral_congr_ae hzero

lemma finiteFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (finiteFamily r) input := by
  refine ⟨finiteFamily_strict hr, ?_, finiteFamily_globalFeasible, finiteFamily_zero_obstruction hr⟩
  exact fun j => finiteFamily_legal j

end Case024

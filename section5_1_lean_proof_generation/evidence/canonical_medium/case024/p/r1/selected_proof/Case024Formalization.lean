import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Case024

noncomputable section

local instance (p : ℕ → Prop) : DecidablePred p := Classical.decPred p

abbrev Squares : Set ℕ := {x | ∃ k, k * k = x}
abbrev inSquares (n : ℕ) : Prop := n ∈ Squares

lemma squares_infinite : Squares.Infinite := by
  apply Set.infinite_range_of_injective (f := fun k : ℕ => k * k)
  intro a b h
  exact Nat.mul_self_inj.mp h

lemma squares_compl_infinite : Squaresᶜ.Infinite := by
  let f : ℕ → ℕ := fun k => (k + 1) * (k + 1) + (k + 1)
  have hmono : StrictMono f := by
    intro a b hab
    dsimp [f]
    nlinarith
  apply (Set.infinite_range_of_injective hmono.injective).mono
  rintro x ⟨k, rfl⟩ ⟨m, hm⟩
  dsimp [f] at hm
  have hlow : (k + 1) * (k + 1) < m * m := by omega
  have hhigh : m * m < (k + 2) * (k + 2) := by nlinarith
  have hm1 : k + 1 < m := by
    by_contra h
    have : m ≤ k + 1 := by omega
    nlinarith
  have hm2 : m < k + 2 := by
    by_contra h
    have : k + 2 ≤ m := by omega
    nlinarith
  omega

lemma prefixCount_eq_count (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n = Nat.count (fun x => x ∈ S) n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range]

lemma square_prefix_bound (n : ℕ) :
    GenLimit.PatientScope.prefixCount Squares n ≤ Nat.sqrt n + 1 := by
  rw [prefixCount_eq_count, Nat.count_eq_card_filter_range]
  let s : Finset ℕ := (Finset.range n).filter (fun x => x ∈ Squares)
  have hinj : Set.InjOn Nat.sqrt (s : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ s := ha
    have hb' : b ∈ s := hb
    rw [Finset.mem_filter] at ha' hb'
    obtain ⟨ka, hka⟩ := ha'.2
    obtain ⟨kb, hkb⟩ := hb'.2
    have hsa : Nat.sqrt a * Nat.sqrt a = a := (Nat.exists_mul_self a).mp ⟨ka, hka⟩
    have hsb : Nat.sqrt b * Nat.sqrt b = b := (Nat.exists_mul_self b).mp ⟨kb, hkb⟩
    calc
      a = Nat.sqrt a * Nat.sqrt a := hsa.symm
      _ = Nat.sqrt b * Nat.sqrt b := by rw [hab]
      _ = b := hsb
  have hsub : Finset.image Nat.sqrt s ⊆ Finset.range (Nat.sqrt n + 1) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [s, Finset.mem_filter, Finset.mem_range] at ha
    simp only [Finset.mem_range]
    exact (Nat.sqrt_le_sqrt ha.1.le).trans_lt (Nat.lt_succ_self _)
  change s.card ≤ _
  calc
    s.card = (Finset.image Nat.sqrt s).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (Nat.sqrt n + 1)).card := Finset.card_le_card hsub
    _ = Nat.sqrt n + 1 := Finset.card_range _

lemma tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  exact ⟨b * b, fun a ha => Nat.le_sqrt.mpr ha⟩

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => (1 : ℝ) / Nat.sqrt n) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp tendsto_sqrt_atTop
  have hn : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  apply squeeze_zero' (g := fun n : ℕ => (1 : ℝ) / Nat.sqrt n + 1 / n)
  · filter_upwards with n
    positivity
  · filter_upwards [Filter.eventually_gt_atTop 1] with n hn1
    have hspos : 0 < (Nat.sqrt n : ℝ) := by
      exact_mod_cast (Nat.sqrt_pos.2 (by omega : 0 < n))
    have hnpos : 0 < (n : ℝ) := by positivity
    have hsq : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by
      exact_mod_cast Nat.sqrt_le n
    rw [Nat.cast_add, Nat.cast_one]
    have hmain : (Nat.sqrt n : ℝ) / n ≤ 1 / Nat.sqrt n := by
      rw [div_le_iff₀ hnpos]
      convert (le_div_iff₀ hspos).2 hsq using 1 <;> ring
    calc
      ((Nat.sqrt n : ℝ) + 1) / n = (Nat.sqrt n : ℝ) / n + 1 / n := by ring
      _ ≤ 1 / Nat.sqrt n + 1 / n := add_le_add_right hmain _
  · simpa using hs.add hn

lemma squares_density_zero :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount Squares n : ℝ) / n) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards with n
    have hbound : (GenLimit.PatientScope.prefixCount Squares n : ℝ) ≤ (Nat.sqrt n + 1 : ℕ) := by
      exact_mod_cast square_prefix_bound n
    exact div_le_div_of_nonneg_right hbound (by positivity)
  · exact tendsto_sqrt_add_one_div

noncomputable def shuffledInput (t : ℕ) : ℕ :=
  if h : inSquares t then
    Nat.nth (fun x => ¬ inSquares x) (Nat.count inSquares t)
  else
    Nat.nth inSquares (Nat.count (fun x => ¬ inSquares x) t)

lemma shuffled_mem_iff (t : ℕ) : shuffledInput t ∉ Squares ↔ t ∈ Squares := by
  unfold shuffledInput inSquares
  split_ifs with h
  · simp only [h, iff_true]
    exact Nat.nth_mem_of_infinite squares_compl_infinite _
  · simp only [h, iff_false, not_not]
    exact Nat.nth_mem_of_infinite squares_infinite _

lemma shuffled_injective : Function.Injective shuffledInput := by
  intro a b hab
  by_cases ha : a ∈ Squares <;> by_cases hb : b ∈ Squares
  · unfold shuffledInput at hab
    simp only [ha, hb, ↓reduceDIte] at hab
    have hc := Nat.nth_injective squares_compl_infinite hab
    exact Nat.count_injective ha hb hc
  · have hma := (shuffled_mem_iff a).2 ha
    have hmb : shuffledInput b ∈ Squares := by
      by_contra h
      exact hb ((shuffled_mem_iff b).1 h)
    exact False.elim (hma (hab ▸ hmb))
  · have hma : shuffledInput a ∈ Squares := by
      by_contra h
      exact ha ((shuffled_mem_iff a).1 h)
    have hmb := (shuffled_mem_iff b).2 hb
    exact False.elim (hmb (hab ▸ hma))
  · unfold shuffledInput at hab
    simp only [ha, hb, ↓reduceDIte] at hab
    have hc := Nat.nth_injective squares_infinite hab
    exact Nat.count_injective ha hb hc

lemma shuffled_surjective : Function.Surjective shuffledInput := by
  classical
  intro x
  by_cases hx : x ∈ Squares
  · have hx' : x ∈ Set.range (Nat.nth inSquares) := by
      have hr := Nat.range_nth_of_infinite squares_infinite
      change Set.range (Nat.nth inSquares) = Squares at hr
      rw [hr]
      exact hx
    obtain ⟨k, hk⟩ := hx'
    let t := Nat.nth (fun z => ¬ inSquares z) k
    have ht : ¬ inSquares t := Nat.nth_mem_of_infinite squares_compl_infinite k
    refine ⟨t, ?_⟩
    unfold shuffledInput
    simp only [ht, ↓reduceDIte]
    rw [Nat.count_nth_of_infinite squares_compl_infinite]
    exact hk
  · have hx' : x ∈ Set.range (Nat.nth (fun z => ¬ inSquares z)) := by
      have hr := Nat.range_nth_of_infinite squares_compl_infinite
      change Set.range (Nat.nth (fun z => ¬ inSquares z)) = Squaresᶜ at hr
      rw [hr]
      exact hx
    obtain ⟨k, hk⟩ := hx'
    let t := Nat.nth inSquares k
    have ht : inSquares t := Nat.nth_mem_of_infinite squares_infinite k
    refine ⟨t, ?_⟩
    unfold shuffledInput
    simp only [ht, ↓reduceDIte]
    letI : DecidablePred inSquares := Classical.decPred _
    have hc : Nat.count inSquares t = k := by
      dsimp [t]
      exact Nat.count_nth_of_infinite squares_infinite k
    rw [hc]
    exact hk

lemma shuffled_noise_count (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount shuffledInput Squares n =
      GenLimit.PatientScope.prefixCount Squares n := by
  unfold GenLimit.InfiniteContamination.noiseCount
    GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro ht
  exact shuffled_mem_iff t

lemma legal_squares : Stage3Case024.Legal shuffledInput Squares := by
  refine ⟨squares_infinite, shuffled_injective, ?_, ?_⟩
  · intro x hx
    exact shuffled_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squares_density_zero.congr'
    filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, shuffled_noise_count]


lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.limsup_le_of_le
    (hf := Filter.isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  filter_upwards with n
  have hcount := prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
  by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
  · have hz2 : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 :=
      Nat.eq_zero_of_le_zero (hz ▸ hcount)
    simp [hz, hz2]
  · apply (div_le_one (by positivity : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n)).2
    exact_mod_cast hcount

lemma generatorFirst_subset_range (input output : ℕ → ℕ) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, hbefore⟩
  exact ⟨t, ht⟩

lemma prefix_generatorFirst_bound {input output : ℕ → ℕ} {T : ℕ}
    (hvalid : ∀ t, T ≤ t → output t ∈ Squares) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n ≤
      GenLimit.PatientScope.prefixCount Squares n + T := by
  let early := (Finset.range T).image output
  have hsub : GenLimit.PatientScope.prefixFinset (GenLimit.GeneratorFirst input output) n ⊆
      GenLimit.PatientScope.prefixFinset Squares n ∪ early := by
    intro x hx
    have hx' : x < n ∧ x ∈ GenLimit.GeneratorFirst input output := by
      simpa [GenLimit.PatientScope.prefixFinset] using hx
    by_cases hs : x ∈ Squares
    · apply Finset.mem_union_left early
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx'.1, hs⟩
    · apply Finset.mem_union_right _
      obtain ⟨t, ht⟩ := generatorFirst_subset_range input output hx'.2
      have hlt : t < T := by
        by_contra hnot
        exact hs (ht ▸ hvalid t (by omega))
      simp only [early, Finset.mem_image, Finset.mem_range]
      exact ⟨t, hlt, ht⟩
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset (GenLimit.GeneratorFirst input output) n).card
        ≤ (GenLimit.PatientScope.prefixFinset Squares n ∪ early).card := Finset.card_le_card hsub
    _ ≤ (GenLimit.PatientScope.prefixFinset Squares n).card + early.card := Finset.card_union_le _ _
    _ ≤ (GenLimit.PatientScope.prefixFinset Squares n).card + T :=
      by
        simpa [early] using
          Nat.add_le_add_left (Finset.card_image_le (s := Finset.range T) (f := output))
            (GenLimit.PatientScope.prefixFinset Squares n).card

lemma relativeUpperDensity_univ_zero {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Squares) :
    Stage3Case024.relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hvalid
  have hbound (n : ℕ) :=
    prefix_generatorFirst_bound (input := input) (output := output)
      (fun t ht => (hT t ht).1) n
  unfold Stage3Case024.relativeUpperDensity
  have htend : Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n : ℝ) /
        GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n) atTop (𝓝 0) := by
    simp_rw [prefixCount_univ]
    apply squeeze_zero' (g := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount Squares n : ℝ) / n + (T : ℝ) / n)
    · filter_upwards with n
      positivity
    · filter_upwards with n
      have hb : (GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount Squares n + T := by exact_mod_cast hbound n
      calc
        (GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n : ℝ) / n
            ≤ ((GenLimit.PatientScope.prefixCount Squares n : ℝ) + T) / n :=
              div_le_div_of_nonneg_right hb (by positivity)
        _ = (GenLimit.PatientScope.prefixCount Squares n : ℝ) / n + (T : ℝ) / n := by ring
    · simpa using squares_density_zero.add (tendsto_const_div_atTop_nhds_zero_nat T)
  simpa only [Set.inter_univ] using htend.limsup_eq

lemma pair_obstruction : Stage3Case024.PairObstruction Squares Set.univ shuffledInput := by
  intro Ω _ μ _ gen output hfollows hmeas hint0 hint1 hvalid0 hvalid1
  have hzero : ∀ᵐ ω ∂μ, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst shuffledInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalid0] with ω hω
    exact relativeUpperDensity_univ_zero hω
  have eint1 : Stage3Case024.expectedUpperDensity μ Set.univ shuffledInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [MeasureTheory.integral_congr_ae hzero]
    simp
  have ele0 : Stage3Case024.expectedUpperDensity μ Squares shuffledInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    have hone : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    calc
      ∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst shuffledInput (output ω)) Squares ∂μ
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := MeasureTheory.integral_mono hint0 hone
            (fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · rw [eint1, add_zero]
    exact ele0
  · rw [eint1]
    intro h
    linarith [h.2]


lemma noiseCount_anti {A B : Set ℕ} (h : A ⊆ B) (input : ℕ → ℕ) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input B n ≤
      GenLimit.InfiniteContamination.noiseCount input A n := by
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun ha => ht.2 (h ha)⟩

lemma legal_of_squares_subset {K : Set ℕ} (hsub : Squares ⊆ K) :
    Stage3Case024.Legal shuffledInput K := by
  refine ⟨squares_infinite.mono hsub, shuffled_injective, ?_, ?_⟩
  · intro x hx
    exact shuffled_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero' (g := GenLimit.InfiniteContamination.empiricalNoiseRate shuffledInput Squares)
    · filter_upwards with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split_ifs <;> positivity
    · filter_upwards with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast noiseCount_anti hsub shuffledInput n
    · exact legal_squares.2.2.2

lemma legal_univ : Stage3Case024.Legal shuffledInput Set.univ :=
  legal_of_squares_subset (Set.subset_univ Squares)

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if j.val = r - 1 then Set.univ
  else {x | x ∈ Squares ∨
    (x ∉ Squares ∧ Nat.count (fun y => y ∉ Squares) x < j.val)}

lemma squares_subset_nestedFamily {r : ℕ} (j : Fin r) :
    Squares ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split_ifs
  · trivial
  · exact Or.inl hx

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hi : i.val ≠ r - 1 := by omega
  rw [nestedFamily, if_neg hi]
  by_cases hj : j.val = r - 1
  · rw [nestedFamily, if_pos hj]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hreverse
    let x := Nat.nth (fun y => y ∉ Squares) i.val
    have hxns : x ∉ Squares := Nat.nth_mem_of_infinite squares_compl_infinite i.val
    have hxc : Nat.count (fun y => y ∉ Squares) x = i.val := by
      dsimp [x]
      exact Nat.count_nth_of_infinite squares_compl_infinite i.val
    have hxnot : x ∉ {x | x ∈ Squares ∨
        (x ∉ Squares ∧ Nat.count (fun y => y ∉ Squares) x < i.val)} := by
      rintro (hxs | ⟨_, hlt⟩)
      · exact hxns hxs
      · omega
    exact hxnot (hreverse (Set.mem_univ x))
  · rw [nestedFamily, if_neg hj]
    constructor
    · rintro x (hx | ⟨hxns, hxc⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨hxns, hxc.trans hij⟩
    · intro hreverse
      let x := Nat.nth (fun y => y ∉ Squares) i.val
      have hxns : x ∉ Squares := Nat.nth_mem_of_infinite squares_compl_infinite i.val
      have hxc : Nat.count (fun y => y ∉ Squares) x = i.val := by
        dsimp [x]
        exact Nat.count_nth_of_infinite squares_compl_infinite i.val
      have hxj : x ∈ {x | x ∈ Squares ∨
          (x ∉ Squares ∧ Nat.count (fun y => y ∉ Squares) x < j.val)} :=
        Or.inr ⟨hxns, hxc.le.trans_lt hij⟩
      have hxi := hreverse hxj
      rcases hxi with hxs | ⟨_, hlt⟩
      · exact hxns hxs
      · omega

lemma nestedFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal shuffledInput (nestedFamily r j) :=
  legal_of_squares_subset (squares_subset_nestedFamily j)


noncomputable def squareGenerator : Stage3Case024.OnlineGenerator
  | 0, inputPrefix, _ =>
      let b := inputPrefix (Fin.last 0) + 1
      b * b
  | t + 1, inputPrefix, outputPrefix =>
      let b := outputPrefix (Fin.last t) + inputPrefix (Fin.last (t + 1)) + 1
      b * b

noncomputable def squareOutput (input : ℕ → ℕ) : ℕ → ℕ
  | 0 => let b := input 0 + 1; b * b
  | t + 1 =>
      let b := squareOutput input t + input (t + 1) + 1
      b * b

lemma squareOutput_follows (input : ℕ → ℕ) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  cases t <;> rfl

lemma squareOutput_step_lt (input : ℕ → ℕ) (t : ℕ) :
    squareOutput input t < squareOutput input (t + 1) := by
  rw [squareOutput]
  let b := squareOutput input t + input (t + 1) + 1
  have hb : squareOutput input t < b := by dsimp [b]; omega
  have hbpos : 0 < b := by dsimp [b]; omega
  have hble : b ≤ b * b := by nlinarith
  exact hb.trans_le hble

lemma squareOutput_strictMono (input : ℕ → ℕ) : StrictMono (squareOutput input) :=
  strictMono_nat_of_lt_succ (squareOutput_step_lt input)

lemma input_lt_squareOutput (input : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    input s < squareOutput input t := by
  induction t with
  | zero =>
      have hs : s = 0 := by omega
      subst s
      rw [squareOutput]
      let b := input 0 + 1
      have hb : input 0 < b := by dsimp [b]; omega
      have hble : b ≤ b * b := by dsimp [b]; nlinarith
      exact hb.trans_le hble
  | succ t ih =>
      rw [squareOutput]
      let b := squareOutput input t + input (t + 1) + 1
      have hbpos : 0 < b := by dsimp [b]; omega
      have hble : b ≤ b * b := by nlinarith
      by_cases hs : s = t + 1
      · subst s
        have : input (t + 1) < b := by dsimp [b]; omega
        exact this.trans_le hble
      · have hst' : s ≤ t := by omega
        have : input s < squareOutput input t := ih hst'
        have : input s < b := this.trans (by dsimp [b]; omega)
        exact this.trans_le hble

lemma squareOutput_novel (input : ℕ → ℕ) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) Squares := by
  refine ⟨0, fun t _ => ?_⟩
  constructor
  · cases t <;> simp [squareOutput, Squares]
  constructor
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    have hlt := input_lt_squareOutput input (Nat.le_of_lt_succ hs)
    omega
  · intro s hs
    exact ne_of_lt (squareOutput_strictMono input hs)

lemma nestedFamily_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, fun input _ => ⟨squareOutput input, squareOutput_follows input, ?_⟩⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, fun t ht => ?_⟩
  have hs := hT t ht
  exact ⟨squares_subset_nestedFamily j hs.1, hs.2⟩


lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = Squares := by
  ext x
  simp [nestedFamily]
  omega

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily]

lemma nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) shuffledInput := by
  intro Ω _ μ _ gen output hfollows hmeas hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidSquares : Stage3Case024.EventuallyFreshValid μ Squares shuffledInput output := by
    have h := hvalid first
    simpa [first, nestedFamily_zero hr] using h
  have hzero : ∀ᵐ ω ∂μ, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst shuffledInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalidSquares] with ω hω
    exact relativeUpperDensity_univ_zero hω
  refine ⟨last, ?_⟩
  have hlast : nestedFamily r last = Set.univ := by
    simpa [last] using nestedFamily_last hr
  rw [hlast]
  unfold Stage3Case024.expectedUpperDensity
  rw [MeasureTheory.integral_congr_ae hzero]
  simp

lemma squares_strict_univ : Squares ⊂ (Set.univ : Set ℕ) := by
  constructor
  · exact Set.subset_univ _
  · intro h
    let x := Nat.nth (fun y => y ∉ Squares) 0
    have hx : x ∉ Squares := Nat.nth_mem_of_infinite squares_compl_infinite 0
    exact hx (h (Set.mem_univ x))

end
end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨Case024.Squares, Set.univ, Case024.shuffledInput,
      Case024.squares_strict_univ, Case024.legal_squares, Case024.legal_univ,
      Case024.pair_obstruction⟩
  · intro r hr
    exact ⟨Case024.nestedFamily r, Case024.shuffledInput,
      Case024.nestedFamily_strict hr, Case024.nestedFamily_legal,
      Case024.nestedFamily_globallyFeasible, Case024.nestedFamily_obstruction hr⟩

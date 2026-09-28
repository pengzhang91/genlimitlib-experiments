import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

def squares : Language := {x | Nat.sqrt x ^ 2 = x}

noncomputable instance squaresMembershipDecidable (n : ℕ) : Decidable (n ∈ squares) :=
  Classical.propDecidable _

def gapEven (n : ℕ) : ℕ :=
  let m := n + 1
  m ^ 2 + m

def gapOdd (n : ℕ) : ℕ := gapEven n + 1

lemma squareMap_injective : Function.Injective (fun n : ℕ => n ^ 2) :=
  Nat.pow_left_injective (by decide)

lemma squares_infinite : squares.Infinite := by
  exact (Set.infinite_range_of_injective squareMap_injective).mono (by
    rintro x ⟨n, rfl⟩
    simp [squares])

lemma mem_squares_iff (x : ℕ) : x ∈ squares ↔ ∃ n : ℕ, x = n ^ 2 := by
  constructor
  · intro hx
    exact ⟨Nat.sqrt x, hx.symm⟩
  · rintro ⟨n, rfl⟩
    simp [squares]

lemma sqrt_sq (n : ℕ) : Nat.sqrt (n ^ 2) = n := Nat.sqrt_eq' n

lemma gapEven_sqrt (n : ℕ) : Nat.sqrt (gapEven n) = n + 1 := by
  unfold gapEven
  exact Nat.sqrt_add_eq' (n + 1) (by omega)

lemma gapOdd_sqrt (n : ℕ) : Nat.sqrt (gapOdd n) = n + 1 := by
  change Nat.sqrt ((n + 1) ^ 2 + (n + 2)) = n + 1
  apply Nat.sqrt_add_eq'
  omega

lemma gapEven_not_square (n : ℕ) : gapEven n ∉ squares := by
  rw [mem_squares_iff]
  rintro ⟨m, hm⟩
  have hs := congrArg Nat.sqrt hm
  rw [sqrt_sq, gapEven_sqrt] at hs
  subst m
  unfold gapEven at hm
  nlinarith

lemma gapOdd_not_square (n : ℕ) : gapOdd n ∉ squares := by
  rw [mem_squares_iff]
  rintro ⟨m, hm⟩
  have hs := congrArg Nat.sqrt hm
  rw [sqrt_sq, gapOdd_sqrt] at hs
  subst m
  unfold gapOdd gapEven at hm
  nlinarith

lemma gapEven_even (n : ℕ) : Even (gapEven n) := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd (n + 1)
  · refine ⟨2 * k ^ 2 + k, ?_⟩
    unfold gapEven
    rw [hk]
    ring
  · refine ⟨(2 * k + 1) * (k + 1), ?_⟩
    unfold gapEven
    rw [hk]
    ring

lemma gapOdd_odd (n : ℕ) : Odd (gapOdd n) := by
  obtain ⟨k, hk⟩ := gapEven_even n
  exact ⟨k, by simp [gapOdd, hk, Nat.two_mul]⟩

lemma gapEven_injective : Function.Injective gapEven := by
  intro m n h
  have := congrArg Nat.sqrt h
  simpa [gapEven_sqrt] using this

lemma gapOdd_injective : Function.Injective gapOdd := by
  intro m n h
  have := congrArg Nat.sqrt h
  simpa [gapOdd_sqrt] using this

lemma gapOdd_ne_gapEven (m n : ℕ) : gapOdd m ≠ gapEven n := by
  intro h
  have he : Even (gapOdd m) := h ▸ gapEven_even n
  obtain ⟨a, ha⟩ := gapOdd_odd m
  obtain ⟨b, hb⟩ := he
  omega

lemma nonsquares_infinite : (squaresᶜ : Set ℕ).Infinite := by
  exact (Set.infinite_range_of_injective gapEven_injective).mono (by
    rintro x ⟨n, rfl⟩
    exact gapEven_not_square n)

end Case024

namespace Case024

lemma prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  have h := Finset.card_le_card_of_injOn (s := (Finset.range n).filter (fun x => x ∈ squares))
    (t := Finset.range (Nat.sqrt n + 1)) Nat.sqrt (by
      intro x hx
      change x ∈ (Finset.range n).filter (fun x => x ∈ squares) at hx
      change Nat.sqrt x ∈ Finset.range (Nat.sqrt n + 1)
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_range]
      exact lt_of_le_of_lt (Nat.sqrt_le_sqrt hx.1.le) (Nat.lt_succ_self _)) (by
      intro x hx y hy hxy
      change x ∈ (Finset.range n).filter (fun x => x ∈ squares) at hx
      change y ∈ (Finset.range n).filter (fun x => x ∈ squares) at hy
      simp only [Finset.mem_filter, Finset.mem_range] at hx hy
      rw [mem_squares_iff] at hx hy
      obtain ⟨a, rfl⟩ := hx.2
      obtain ⟨b, rfl⟩ := hy.2
      simpa using hxy)
  simpa using h

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Real.sqrt_eq_rpow] using h
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
    hsqrt.inv_tendsto_atTop
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n : ℕ =>
      (Real.sqrt (n : ℝ) + 1) / (n : ℝ)) atTop (nhds 0) := by
    convert hinv.add hone using 1
    · funext n
      by_cases hn : n = 0
      · simp [hn]
      · rw [add_div, Real.sqrt_div_self]
    · norm_num
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hreal
  exact Filter.Eventually.of_forall (fun n => by
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
      simpa only [Nat.cast_add, Nat.cast_one] using
        add_le_add_right (Real.nat_sqrt_le_real_sqrt (a := n)) 1)

lemma tendsto_squareCount_div :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_
    tendsto_sqrt_add_one_div
  exact Filter.Eventually.of_forall (fun n => by
    by_cases hn : n = 0
    · simp [hn, GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
    · apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
      exact_mod_cast prefixCount_squares_le n)

end Case024

namespace Case024

noncomputable def sparseEnumeration : Stream := by
  classical
  exact fun t =>
    if ht : t ∈ squares then
      Nat.nth (fun x => x ∉ squares) (Nat.count (fun s => s ∈ squares) t)
    else
      Nat.nth (fun x => x ∈ squares) (Nat.count (fun s => s ∉ squares) t)

lemma sparseEnumeration_of_square {t : ℕ} (ht : t ∈ squares) :
    sparseEnumeration t =
      Nat.nth (fun x => x ∉ squares) (Nat.count (fun s => s ∈ squares) t) := by
  classical
  simp [sparseEnumeration, ht]

lemma sparseEnumeration_of_nonsquare {t : ℕ} (ht : t ∉ squares) :
    sparseEnumeration t =
      Nat.nth (fun x => x ∈ squares) (Nat.count (fun s => s ∉ squares) t) := by
  classical
  simp [sparseEnumeration, ht]

lemma sparseEnumeration_square_iff (t : ℕ) :
    sparseEnumeration t ∈ squares ↔ t ∉ squares := by
  classical
  by_cases ht : t ∈ squares
  · rw [sparseEnumeration_of_square ht]
    exact ⟨fun h => (Nat.nth_mem_of_infinite nonsquares_infinite _ h).elim,
      fun h => (h ht).elim⟩
  · rw [sparseEnumeration_of_nonsquare ht]
    exact ⟨fun _ => ht, fun _ => Nat.nth_mem_of_infinite squares_infinite _⟩

lemma sparseEnumeration_injective : Function.Injective sparseEnumeration := by
  classical
  intro s t hst
  by_cases hs : s ∈ squares <;> by_cases ht : t ∈ squares
  · rw [sparseEnumeration_of_square hs, sparseEnumeration_of_square ht] at hst
    have hc := (Nat.nth_injective nonsquares_infinite) hst
    exact Nat.count_injective hs ht hc
  · have ho : sparseEnumeration s ∉ squares :=
      (sparseEnumeration_square_iff s).not.mpr (not_not.mpr hs)
    have hi : sparseEnumeration t ∈ squares :=
      (sparseEnumeration_square_iff t).mpr ht
    exact (ho (hst ▸ hi)).elim
  · have hi : sparseEnumeration s ∈ squares :=
      (sparseEnumeration_square_iff s).mpr hs
    have ho : sparseEnumeration t ∉ squares :=
      (sparseEnumeration_square_iff t).not.mpr (not_not.mpr ht)
    exact (ho (hst ▸ hi)).elim
  · rw [sparseEnumeration_of_nonsquare hs, sparseEnumeration_of_nonsquare ht] at hst
    have hc := (Nat.nth_injective squares_infinite) hst
    exact Nat.count_injective hs ht hc

lemma sparseEnumeration_surjective : Function.Surjective sparseEnumeration := by
  classical
  intro x
  by_cases hx : x ∈ squares
  · let k := Nat.count (fun y => y ∈ squares) x
    let t := Nat.nth (fun s => s ∉ squares) k
    have ht : t ∉ squares := Nat.nth_mem_of_infinite nonsquares_infinite k
    refine ⟨t, ?_⟩
    rw [sparseEnumeration_of_nonsquare ht, Nat.count_nth_of_infinite (p := fun s => s ∉ squares) nonsquares_infinite]
    exact Nat.nth_count hx
  · let k := Nat.count (fun y => y ∉ squares) x
    let t := Nat.nth (fun s => s ∈ squares) k
    have ht : t ∈ squares := Nat.nth_mem_of_infinite squares_infinite k
    refine ⟨t, ?_⟩
    rw [sparseEnumeration_of_square ht, Nat.count_nth_of_infinite (p := fun s => s ∈ squares) squares_infinite]
    exact Nat.nth_count hx

lemma sparseEnumeration_range : Set.range sparseEnumeration = Set.univ := by
  exact Set.range_eq_univ.mpr sparseEnumeration_surjective

lemma noiseCount_sparseEnumeration_le (K : Language) (hK : squares ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount sparseEnumeration K n ≤
      GenLimit.PatientScope.prefixCount squares n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
    GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  refine ⟨ht.1, ?_⟩
  by_contra hts
  exact ht.2 (hK ((sparseEnumeration_square_iff t).mpr hts))

lemma sparseEnumeration_vanishingNoise (K : Language) (hK : squares ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise sparseEnumeration K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
    GenLimit.InfiniteContamination.empiricalNoiseRate
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => by
    split_ifs <;> positivity)) ?_ tendsto_squareCount_div
  exact Filter.Eventually.of_forall (fun n => by
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
      exact_mod_cast noiseCount_sparseEnumeration_le K hK n)

lemma sparseEnumeration_legal (K : Language) (hK : squares ⊆ K) :
    Stage3Case024.Legal sparseEnumeration K ↔ K.Infinite := by
  constructor
  · exact fun h => h.1
  · intro hInf
    refine ⟨hInf, sparseEnumeration_injective, ?_, sparseEnumeration_vanishingNoise K hK⟩
    intro x hx
    rw [sparseEnumeration_range]
    trivial

end Case024

namespace Case024

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Language) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall (fun n => by positivity)))
  exact Filter.Eventually.of_forall (fun n => by
      by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hz]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)]
        exact_mod_cast prefixCount_mono (Set.inter_subset_right) n)

lemma prefixCount_le_square_add_of_finite {A : Language}
    (hfinite : (A \ squares).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount squares n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  calc
    ((Finset.range n).filter fun x => x ∈ A).card ≤
        (((Finset.range n).filter fun x => x ∈ squares) ∪ hfinite.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range,
        Set.Finite.mem_toFinset]
      by_cases hs : x ∈ squares
      · exact Or.inl ⟨hx.1, hs⟩
      · exact Or.inr ⟨hx.2, hs⟩
    _ ≤ ((Finset.range n).filter fun x => x ∈ squares).card + hfinite.toFinset.card :=
      Finset.card_union_le _ _

lemma tendsto_prefixCount_div_of_finite {A : Language}
    (hfinite : (A \ squares).Finite) :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hc : Tendsto (fun n : ℕ => (hfinite.toFinset.card : ℝ) / (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum : Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ) +
        (hfinite.toFinset.card : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa using tendsto_squareCount_div.add hc
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hsum
  exact Filter.Eventually.of_forall (fun n => by
    by_cases hn : n = 0
    · simp [hn]
    · calc
        (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ) ≤
            ((GenLimit.PatientScope.prefixCount squares n : ℝ) +
              (hfinite.toFinset.card : ℝ)) / (n : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
          exact_mod_cast prefixCount_le_square_add_of_finite hfinite n
        _ = (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ) +
              (hfinite.toFinset.card : ℝ) / (n : ℝ) := by rw [add_div])

lemma relativeUpperDensity_univ_eq_zero_of_finite {A : Language}
    (hfinite : (A \ squares).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  have ht := tendsto_prefixCount_div_of_finite hfinite
  rw [show (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
        (GenLimit.PatientScope.prefixCount Set.univ n : ℝ)) =
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)) by
    funext n
    simp [prefixCount_univ]]
  exact ht.limsup_eq

lemma generatorFirst_diff_finite {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squares) :
    (GenLimit.GeneratorFirst input output \ squares).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  let exceptional : Finset ℕ := (Finset.range T).image output
  apply exceptional.finite_toSet.subset
  intro x hx
  rcases hx.1 with ⟨t, hout, _⟩
  have ht : t < T := by
    by_contra hnot
    exact hx.2 (hout ▸ (hT t (Nat.le_of_not_gt hnot)).1)
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, hout⟩

lemma path_univ_density_zero {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 :=
  relativeUpperDensity_univ_eq_zero_of_finite (generatorFirst_diff_finite hvalid)

end Case024

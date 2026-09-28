import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Case017

open Stage3Case017

noncomputable def inputSet {t : ℕ} (xs : Fin (t + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image xs

noncomputable def outputSet {t : ℕ} (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image ys

def currentCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def generator {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let used := inputSet xs ∪ outputSet ys
    let core := currentCore family xs
    if h : core.Infinite then
      Nat.find (h.exists_not_mem_finset used)
    else
      Nat.find (Set.infinite_univ.exists_not_mem_finset used)

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t
decreasing_by exact i.isLt

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run.eq_1 gen input t

theorem generator_fresh {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ inputSet xs ∪ outputSet ys := by
  classical
  simp only [generator]
  split_ifs with h
  · exact (Nat.find_spec (h.exists_not_mem_finset (inputSet xs ∪ outputSet ys))).2
  · exact (Nat.find_spec
      (Set.infinite_univ.exists_not_mem_finset (inputSet xs ∪ outputSet ys))).2

theorem generator_mem_core {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) :
    generator family t xs ys ∈ currentCore family xs := by
  classical
  simp only [generator, dif_pos h]
  exact (Nat.find_spec
    (h.exists_not_mem_finset (inputSet xs ∪ outputSet ys))).1

theorem run_ne_input {m : ℕ} (family : Fin m → Language) (input : Stream)
    (t s : ℕ) (hs : s ≤ t) :
    run (generator family) input t ≠ input s := by
  intro heq
  have hf := generator_fresh family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (generator family) input i)
  apply hf
  apply Finset.mem_union_left
  simp only [inputSet, Finset.mem_image]
  refine ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, Finset.mem_univ _, ?_⟩
  exact heq.symm.trans (run.eq_1 (generator family) input t)

theorem run_ne_output {m : ℕ} (family : Fin m → Language) (input : Stream)
    (t s : ℕ) (hs : s < t) :
    run (generator family) input s ≠ run (generator family) input t := by
  intro heq
  have hf := generator_fresh family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (generator family) input i)
  apply hf
  apply Finset.mem_union_right
  simp only [outputSet, Finset.mem_image]
  refine ⟨⟨s, hs⟩, Finset.mem_univ _, ?_⟩
  exact heq.trans (run.eq_1 (generator family) input t)


theorem streamIn_iff (input : Stream) (L : Language) :
    GenLimit.Generic.StreamIn input L ↔ ∀ t, input t ∈ L := by
  constructor
  · intro h t
    exact h ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩
    exact h t

noncomputable def badTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  by_cases h : GenLimit.Generic.StreamIn input (family j)
  · exact 0
  · exact Nat.find ((not_forall.mp (h ∘ (streamIn_iff input (family j)).mpr)))

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ := by
  classical
  exact Finset.univ.sup (badTime family input)

theorem badTime_not_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (badTime family input j) ∉ family j := by
  classical
  rw [badTime]
  simp only [dif_neg h]
  exact Nat.find_spec
    (not_forall.mp (h ∘ (streamIn_iff input (family j)).mpr))

theorem badTime_le_stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    badTime family input j ≤ stabilizationTime family input := by
  classical
  exact Finset.le_sup (f := badTime family input) (Finset.mem_univ j)

theorem currentCore_eq_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) (ht : stabilizationTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact (streamIn_iff input (family j)).mp hj i
  · intro hz j hj
    apply hz j
    rw [streamIn_iff]
    by_contra hnot
    have hnot' : ¬ GenLimit.Generic.StreamIn input (family j) := by
      exact fun h => hnot ((streamIn_iff input (family j)).mp h)
    have hb := badTime_not_mem family input j hnot'
    have hle : badTime family input j ≤ t :=
      (badTime_le_stabilizationTime family input j).trans ht
    exact hb (hj ⟨badTime family input j, Nat.lt_succ_iff.mpr hle⟩)


theorem run_mem_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (t : ℕ) (ht : stabilizationTime family input ≤ t) :
    run (generator family) input t ∈ informationCore family input := by
  rw [run.eq_1]
  have heq := currentCore_eq_informationCore family input t ht
  rw [← heq]
  apply generator_mem_core
  simpa [heq] using hcore

theorem informationCore_subset_target {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

theorem run_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run (generator family) input) (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  refine ⟨informationCore_subset_target family input j hj
      (run_mem_informationCore family input hcore t ht), ?_, ?_⟩
  · intro hmem
    rw [GenLimit.sample, Finset.mem_image] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact run_ne_input family input t s (Nat.lt_succ_iff.mp (by simpa using hs)) heq.symm
  · intro s hs
    exact run_ne_output family input t s hs


theorem run_injective {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Function.Injective (run (generator family) input) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact run_ne_output family input b a hlt hab
  · exact run_ne_output family input a b hgt hab.symm

theorem generator_le {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (currentCore family xs).Infinite)
    {z : ℕ} (hz : z ∈ currentCore family xs)
    (hfresh : z ∉ inputSet xs ∪ outputSet ys) :
    generator family t xs ys ≤ z := by
  classical
  simp only [generator, dif_pos hcore]
  exact Nat.find_min' _ ⟨hz, hfresh⟩

theorem run_le_unannounced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z t : ℕ} (hz : z ∈ informationCore family input)
    (ht : stabilizationTime family input ≤ t)
    (hin : z ∉ Set.range input)
    (hout : ∀ s < t, run (generator family) input s ≠ z) :
    run (generator family) input t ≤ z := by
  rw [run.eq_1]
  have heq := currentCore_eq_informationCore family input t ht
  apply generator_le family
  · simpa [heq] using hcore
  · simpa [heq] using hz
  · intro hmem
    rcases Finset.mem_union.mp hmem with hinput | houtput
    · simp only [inputSet, Finset.mem_image] at hinput
      obtain ⟨i, -, hi⟩ := hinput
      exact hin ⟨i, hi⟩
    · simp only [outputSet, Finset.mem_image] at houtput
      obtain ⟨i, -, hi⟩ := houtput
      exact hout i i.isLt hi

theorem core_eventually_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ informationCore family input) :
    z ∈ Set.range input ∨ z ∈ Set.range (run (generator family) input) := by
  classical
  by_contra h
  push_neg at h
  let T := stabilizationTime family input
  let vals : Finset ℕ := (Finset.range (z + 2)).image
    (fun k => run (generator family) input (T + k))
  have hinj : Set.InjOn (fun k => run (generator family) input (T + k))
      (Finset.range (z + 2) : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.add_left_cancel (run_injective family input hab)
  have hcard : vals.card = z + 2 := by
    simpa [vals] using Finset.card_image_iff.mpr hinj
  have hsub : vals ⊆ Finset.range (z + 1) := by
    intro y hy
    simp only [vals, Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (run_le_unannounced family input hcore hz
      (by simp [T]) h.1 (fun s hs heq => h.2 ⟨s, heq⟩))
  have hc := Finset.card_le_card hsub
  simp [hcard] at hc

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (generator family) input) := by
  intro z hz
  rcases core_eventually_announced family input hcore hz.1 with hin | hout
  · exact (hz.2 hin).elim
  · obtain ⟨t, ht⟩ := hout
    refine ⟨t, ht, ?_⟩
    intro s hs heq
    exact hz.2 ⟨s, heq⟩


theorem prefixFinset_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixFinset A n ⊆
      GenLimit.PatientScope.prefixFinset B n := by
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

theorem prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n :=
  Finset.card_le_card (prefixFinset_mono h n)

theorem relativeLowerDensity_mono {A B K : Set ℕ} (h : A ⊆ B) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply liminf_le_liminf
  filter_upwards [] with n
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast prefixCount_mono h n)
    (Nat.cast_nonneg _)


end Case017

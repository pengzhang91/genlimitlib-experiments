import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Case017

open Stage3Case017

noncomputable def used {t : ℕ} (xs : Fin (t+1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def versionCore {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t+1) → ℕ) : Set ℕ :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

lemma exists_not_mem_finset (s : Finset ℕ) : ∃ z, z ∉ s := by
  classical
  by_cases hs : s.Nonempty
  · exact ⟨s.max' hs + 1, by
      intro h
      have := Finset.le_max' s _ h
      omega⟩
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    exact ⟨0, by simp [he]⟩

noncomputable def chooseFresh (C : Set ℕ) (s : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ z, z ∈ C ∧ z ∉ s then Nat.find h else Nat.find (exists_not_mem_finset s)

lemma chooseFresh_not_mem (C : Set ℕ) (s : Finset ℕ) : chooseFresh C s ∉ s := by
  classical
  unfold chooseFresh
  split
  · exact (Nat.find_spec ‹∃ z, z ∈ C ∧ z ∉ s›).2
  · exact Nat.find_spec (exists_not_mem_finset s)

lemma chooseFresh_mem {C : Set ℕ} {s : Finset ℕ} (h : ∃ z, z ∈ C ∧ z ∉ s) :
    chooseFresh C s ∈ C := by
  classical
  simp only [chooseFresh, dif_pos h]
  exact (Nat.find_spec h).1

lemma chooseFresh_le {C : Set ℕ} {s : Finset ℕ} (h : ∃ z, z ∈ C ∧ z ∉ s)
    {z : ℕ} (hzC : z ∈ C) (hzs : z ∉ s) : chooseFresh C s ≤ z := by
  classical
  simp only [chooseFresh, dif_pos h]
  exact Nat.find_min' h ⟨hzC, hzs⟩

noncomputable def onlineGen {m : ℕ} (family : Fin m → Set ℕ) : OnlineGenerator :=
  fun t xs ys => chooseFresh (versionCore family xs) (used xs ys)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  Nat.strongRec (motive := fun _ => ℕ)
    (fun n ih => gen n (fun i => input i) (fun i => ih i (by omega))) t

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory, Nat.strongRec_eq]
  congr

lemma onlineGen_fresh {m : ℕ} (family : Fin m → Set ℕ) (input : Stream) (t : ℕ) :
    trajectory (onlineGen family) input t ∉
      used (fun i : Fin (t+1) => input i)
        (fun i : Fin t => trajectory (onlineGen family) input i) := by
  rw [trajectory_follows (onlineGen family) input t]
  exact chooseFresh_not_mem _ _

lemma onlineGen_not_input {m : ℕ} (family : Fin m → Set ℕ) (input : Stream) (t : ℕ) :
    trajectory (onlineGen family) input t ∉ GenLimit.sample input (t+1) := by
  intro h
  rw [GenLimit.sample] at h
  rcases Finset.mem_image.mp h with ⟨s, hs, heq⟩
  apply onlineGen_fresh family input t
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨⟨s, by simpa using hs⟩, Finset.mem_univ _, heq⟩

lemma onlineGen_ne_previous {m : ℕ} (family : Fin m → Set ℕ) (input : Stream)
    {s t : ℕ} (hst : s < t) :
    trajectory (onlineGen family) input s ≠ trajectory (onlineGen family) input t := by
  intro heq
  apply onlineGen_fresh family input t
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

end Case017

namespace Case017

noncomputable def witnessTime {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Nat.find (by
      rw [GenLimit.Generic.StreamIn, Set.range_subset_iff] at h
      simpa only [not_forall] using h)

lemma witnessTime_spec {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (witnessTime family input j) ∉ family j := by
  classical
  simp only [witnessTime, dif_neg h]
  exact Nat.find_spec (by
    rw [GenLimit.Generic.StreamIn, Set.range_subset_iff] at h
    simpa only [not_forall] using h)

noncomputable def stabilizationTime {m : ℕ} (hm : 0 < m)
    (family : Fin m → Set ℕ) (input : Stage3Case017.Stream) : ℕ :=
  (Finset.univ.image (witnessTime family input)).max'
    (by
      rw [Finset.image_nonempty]
      exact Finset.univ_nonempty_iff.mpr ⟨0, hm⟩)

lemma witnessTime_le_stabilizationTime {m : ℕ} (hm : 0 < m)
    (family : Fin m → Set ℕ) (input : Stage3Case017.Stream) (j : Fin m) :
    witnessTime family input j ≤ stabilizationTime hm family input := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

lemma prefix_compatible_iff {m : ℕ} (hm : 0 < m)
    (family : Fin m → Set ℕ) (input : Stage3Case017.Stream)
    {t : ℕ} (ht : stabilizationTime hm family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t+1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp
    by_contra h
    have hw := witnessTime_spec family input j h
    have hle : witnessTime family input j < t + 1 := by
      have := witnessTime_le_stabilizationTime hm family input j
      omega
    exact hw (hp ⟨witnessTime family input j, hle⟩)
  · intro hs i
    exact hs ⟨i, rfl⟩

lemma versionCore_eq_informationCore {m : ℕ} (hm : 0 < m)
    (family : Fin m → Set ℕ) (input : Stage3Case017.Stream)
    {t : ℕ} (ht : stabilizationTime hm family input ≤ t) :
    versionCore family (fun i : Fin (t+1) => input i) =
      Stage3Case017.informationCore family input := by
  ext z
  simp only [versionCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor <;> intro h j hj
  · exact h j ((prefix_compatible_iff hm family input ht j).mpr hj)
  · exact h j ((prefix_compatible_iff hm family input ht j).mp hj)

lemma core_available {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stabilizationTime hm family input ≤ t) :
    ∃ z, z ∈ versionCore family (fun i : Fin (t+1) => input i) ∧
      z ∉ used (fun i : Fin (t+1) => input i)
        (fun i : Fin t => trajectory (onlineGen family) input i) := by
  rw [versionCore_eq_informationCore hm family input ht]
  exact hInf.exists_not_mem_finset _

lemma onlineGen_mem_core {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stabilizationTime hm family input ≤ t) :
    trajectory (onlineGen family) input t ∈ Stage3Case017.informationCore family input := by
  rw [trajectory_follows (onlineGen family) input t]
  have ha := core_available hm family input hInf ht
  rw [← versionCore_eq_informationCore hm family input ht]
  exact chooseFresh_mem ha

lemma onlineGen_le_available_core {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {t z : ℕ} (ht : stabilizationTime hm family input ≤ t)
    (hz : z ∈ Stage3Case017.informationCore family input)
    (hzin : ∀ s, s ≤ t → input s ≠ z)
    (hzout : ∀ s, s < t → trajectory (onlineGen family) input s ≠ z) :
    trajectory (onlineGen family) input t ≤ z := by
  rw [trajectory_follows (onlineGen family) input t]
  have ha := core_available hm family input hInf ht
  apply chooseFresh_le ha
  · rwa [versionCore_eq_informationCore hm family input ht]
  · intro hused
    rcases Finset.mem_union.mp hused with hx | hy
    · rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
      exact hzin i (by omega) hi
    · rcases Finset.mem_image.mp hy with ⟨i, -, hi⟩
      exact hzout i (by omega) hi

end Case017

namespace Case017

lemma core_eventually_announced {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ Stage3Case017.informationCore family input) :
    (∃ t, input t = z) ∨ (∃ t, trajectory (onlineGen family) input t = z) := by
  by_contra h
  push_neg at h
  rcases h with ⟨hin, hout⟩
  let T := stabilizationTime hm family input
  let f : ℕ → ℕ := fun k => trajectory (onlineGen family) input (T + k)
  have hf_le : ∀ k, f k ≤ z := by
    intro k
    apply onlineGen_le_available_core hm family input hInf (by simp [T]) hz
    · intro s _
      exact hin s
    · intro s _
      exact hout s
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra habn
    by_cases hablt : a < b
    · exact (onlineGen_ne_previous family input (by omega)) hab
    · have hba : b < a := by omega
      exact (onlineGen_ne_previous family input (by omega)) hab.symm
  let s := (Finset.range (z+2)).image f
  have hcard : s.card = z + 2 := by
    rw [Finset.card_image_of_injective _ hf_inj]
    simp [s]
  have hsub : s ⊆ Finset.range (z+1) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, -, rfl⟩
    exact Finset.mem_range.mpr (by have := hf_le k; omega)
  have := Finset.card_le_card hsub
  simp [hcard, s] at this

lemma output_mem_generatorFirst {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (t : ℕ) :
    trajectory (onlineGen family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (onlineGen family) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  have hnot := onlineGen_not_input family input t
  apply hnot
  rw [GenLimit.sample]
  apply Finset.mem_image.mpr
  exact ⟨s, Finset.mem_range.mpr (by omega), heq⟩

lemma unpresented_core_subset_generatorFirst {m : ℕ} (hm : 0 < m)
    (family : Fin m → Set ℕ) (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (onlineGen family) input) := by
  intro z hz
  rcases core_eventually_announced hm family input hInf hz.1 with hin | hout
  · exact False.elim (hz.2 hin)
  · rcases hout with ⟨t, ht⟩
    refine ⟨t, ht, ?_⟩
    intro s _ hs
    exact hz.2 ⟨s, hs⟩

lemma prefixFinset_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixFinset A n ⊆
      GenLimit.PatientScope.prefixFinset B n := by
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  exact Finset.card_le_card (prefixFinset_mono hAB n)

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall (fun n => by
      gcongr
      exact prefixCount_mono hAB n)
  · apply Filter.isBoundedUnder_of_eventually_ge (a := 0)
    exact Filter.Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity))
  · apply Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := 1)
    exact Filter.Eventually.of_forall (fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · have hle := prefixCount_mono hBK n
        have hbzero : GenLimit.PatientScope.prefixCount B n = 0 := by
          omega
        simp [hzero, hbzero]
      · rw [div_le_one]
        · exact_mod_cast prefixCount_mono hBK n
        · positivity)

end Case017

namespace Case017

noncomputable def inputTime (input : Stage3Case017.Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

lemma inputTime_spec (input : Stage3Case017.Stream) {z : ℕ} (h : ∃ t, input t = z) :
    input (inputTime input z) = z := by
  classical
  simp only [inputTime, dif_pos h]
  exact Nat.find_spec h

lemma inputTime_min (input : Stage3Case017.Stream) {z : ℕ} (h : ∃ t, input t = z)
    {t : ℕ} (ht : input t = z) : inputTime input z ≤ t := by
  classical
  simp only [inputTime, dif_pos h]
  exact Nat.find_min' h ht

noncomputable def early {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) : Finset ℕ :=
  used (fun i : Fin (stabilizationTime hm family input + 1) => input i)
    (fun i : Fin (stabilizationTime hm family input) =>
      trajectory (onlineGen family) input i)

noncomputable def corePrefix {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (n : ℕ) : Finset ℕ :=
  GenLimit.PatientScope.prefixFinset (Stage3Case017.informationCore family input) n


lemma mem_corePrefix_iff {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) {n z : ℕ} :
    z ∈ corePrefix family input n ↔
      z < n ∧ z ∈ Stage3Case017.informationCore family input := by
  simp [corePrefix, GenLimit.PatientScope.prefixFinset]

noncomputable def generatorPrefix {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (n : ℕ) : Finset ℕ :=
  GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (onlineGen family) input) ∩
      Stage3Case017.informationCore family input) n

noncomputable def lateLosers {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact (corePrefix family input n).filter fun z =>
    z ∉ early hm family input ∧
    z ∉ GenLimit.GeneratorFirst input (trajectory (onlineGen family) input)

lemma lateLoser_input {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {n z : ℕ} (hz : z ∈ lateLosers hm family input n) : ∃ t, input t = z := by
  classical
  simp only [lateLosers, Finset.mem_filter] at hz
  rcases core_eventually_announced hm family input hInf (mem_corePrefix_iff family input |>.mp hz.1).2 with hin | hout
  · exact hin
  · rcases hout with ⟨t, ht⟩
    exfalso
    exact hz.2.2 (ht ▸ output_mem_generatorFirst family input t)

lemma lateLoser_time_gt {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {n z : ℕ} (hz : z ∈ lateLosers hm family input n) :
    stabilizationTime hm family input < inputTime input z := by
  classical
  have hin := lateLoser_input hm family input hInf hz
  by_contra hle
  have hmem : z ∈ early hm family input := by
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨⟨inputTime input z, by omega⟩, Finset.mem_univ _, ?_⟩
    exact inputTime_spec input hin
  exact (Finset.mem_filter.mp hz).2.1 hmem

lemma pair_lateLoser {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {n x x' : ℕ} (hx : x ∈ lateLosers hm family input n)
    (hx' : x' ∈ lateLosers hm family input n)
    (hlt : inputTime input x < inputTime input x') :
    trajectory (onlineGen family) input (inputTime input x) ∈ generatorPrefix family input n := by
  classical
  have hxin := lateLoser_input hm family input hInf hx
  have hx'in := lateLoser_input hm family input hInf hx'
  have hx'core : x' ∈ Stage3Case017.informationCore family input :=
    (mem_corePrefix_iff family input |>.mp (Finset.mem_filter.mp hx').1).2
  have houtle : trajectory (onlineGen family) input (inputTime input x) ≤ x' := by
    apply onlineGen_le_available_core hm family input hInf
      (le_of_lt (lateLoser_time_gt hm family input hInf hx)) hx'core
    · intro s hs heq
      have := inputTime_min input hx'in heq
      omega
    · intro s hs heq
      have hgf := output_mem_generatorFirst family input s
      rw [heq] at hgf
      exact (Finset.mem_filter.mp hx').2.2 hgf
  simp only [generatorPrefix, GenLimit.PatientScope.prefixFinset, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
  · have hx'n : x' < n := (mem_corePrefix_iff family input |>.mp (Finset.mem_filter.mp hx').1).1
    omega
  · exact output_mem_generatorFirst family input _
  · exact onlineGen_mem_core hm family input hInf
      (le_of_lt (lateLoser_time_gt hm family input hInf hx))

lemma lateLosers_card_le {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (hinj : Function.Injective input)
    (hInf : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    (lateLosers hm family input n).card ≤ (generatorPrefix family input n).card + 1 := by
  classical
  let A := lateLosers hm family input n
  let D := generatorPrefix family input n
  by_cases hA : A.Nonempty
  · obtain ⟨xmax, hxmax, hmax⟩ := Finset.exists_max_image A (inputTime input) hA
    have hmap : Set.MapsTo
        (fun x => trajectory (onlineGen family) input (inputTime input x))
        (↑(A.erase xmax) : Set ℕ) (↑D : Set ℕ) := by
      intro x hx
      have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
      have hne : x ≠ xmax := (Finset.mem_erase.mp hx).1
      have hle := hmax x hxA
      have hlt : inputTime input x < inputTime input xmax := by
        apply lt_of_le_of_ne hle
        intro heq
        apply hne
        calc
          x = input (inputTime input x) := (inputTime_spec input (lateLoser_input hm family input hInf hxA)).symm
          _ = input (inputTime input xmax) := congrArg input heq
          _ = xmax := inputTime_spec input (lateLoser_input hm family input hInf hxmax)
      exact pair_lateLoser hm family input hInf hxA hxmax hlt
    have hinjmap : Set.InjOn
        (fun x => trajectory (onlineGen family) input (inputTime input x))
        (↑(A.erase xmax) : Set ℕ) := by
      intro x hx y hy heq
      have htimes : inputTime input x = inputTime input y := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (onlineGen_ne_previous family input hlt) heq
        · exact (onlineGen_ne_previous family input hgt) heq.symm
      calc
        x = input (inputTime input x) :=
          (inputTime_spec input (lateLoser_input hm family input hInf (Finset.mem_erase.mp hx).2)).symm
        _ = input (inputTime input y) := congrArg input htimes
        _ = y := inputTime_spec input (lateLoser_input hm family input hInf (Finset.mem_erase.mp hy).2)
    have hcard : (A.erase xmax).card ≤ D.card :=
      Finset.card_le_card_of_injOn _ hmap hinjmap
    have herase : (A.erase xmax).card + 1 = A.card := Finset.card_erase_add_one hxmax
    have hresult : A.card ≤ D.card + 1 := by omega
    simpa [A, D] using hresult
  · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hresult : A.card ≤ D.card + 1 := by simp [hzero]
    simpa [A, D] using hresult

lemma corePrefix_card_bound {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) (hinj : Function.Injective input)
    (hInf : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    (corePrefix family input n).card ≤
      (early hm family input).card + 2 * (generatorPrefix family input n).card + 1 := by
  classical
  let P := corePrefix family input n
  let E := early hm family input
  let D := generatorPrefix family input n
  let A := lateLosers hm family input n
  have hsub : P ⊆ E ∪ D ∪ A := by
    intro z hz
    by_cases he : z ∈ E
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    by_cases hd : z ∈ GenLimit.GeneratorFirst input (trajectory (onlineGen family) input)
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      simp only [D, generatorPrefix, GenLimit.PatientScope.prefixFinset, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (mem_corePrefix_iff family input |>.mp hz).1, hd, (mem_corePrefix_iff family input |>.mp hz).2⟩
    · apply Finset.mem_union_right
      simp only [A, lateLosers, Finset.mem_filter]
      exact ⟨by simpa [P] using hz, by simpa [E] using he, hd⟩
  have hp : P.card ≤ (E ∪ D ∪ A).card := Finset.card_le_card hsub
  have hu1 : (E ∪ D).card ≤ E.card + D.card := Finset.card_union_le E D
  have hu2 : (E ∪ D ∪ A).card ≤ (E ∪ D).card + A.card := Finset.card_union_le (E ∪ D) A
  have ha0 := lateLosers_card_le hm family input hinj hInf n
  have ha : A.card ≤ D.card + 1 := by simpa [A, D] using ha0
  have hresult : P.card ≤ E.card + 2 * D.card + 1 := by omega
  simpa [P, E, D] using hresult

end Case017

namespace Case017

lemma informationCore_subset {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stage3Case017.Stream) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Filter.Tendsto (GenLimit.PatientScope.prefixCount K) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq b
  let N := s.sup id + 1
  refine ⟨N, ?_⟩
  intro n hn
  have hs : s ⊆ GenLimit.PatientScope.prefixFinset K n := by
    intro z hz
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, hsK hz⟩
    have hzle : z ≤ s.sup id := Finset.le_sup (f := id) hz
    omega
  have := Finset.card_le_card hs
  simpa [GenLimit.PatientScope.prefixCount, hscard] using this

lemma half_core_density {m : ℕ} (hm : 0 < m) (family : Fin m → Set ℕ)
    (hfamily : ∀ j, (family j).Infinite)
    (input : Stage3Case017.Stream) (hinj : Function.Injective input)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (onlineGen family) input) ∩ family j)
        (family j) := by
  let I := Stage3Case017.informationCore family input
  let D := GenLimit.GeneratorFirst input (trajectory (onlineGen family) input) ∩ family j
  let K := family j
  let c : ℝ := ((early hm family input).card + 1 : ℕ)
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount I n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let d : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (c / 2) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hIK : I ⊆ K := informationCore_subset family input hj
  have hDK : D ⊆ K := Set.inter_subset_right
  have ha0 : ∀ n, 0 ≤ a n := fun n => div_nonneg (by positivity) (by positivity)
  have ha1 : ∀ n, a n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hIz := Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono hIK n)
      simp [a, hzero, hIz]
    · change (GenLimit.PatientScope.prefixCount I n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one]
      · exact_mod_cast prefixCount_mono hIK n
      · positivity
  have hd0 : ∀ n, 0 ≤ d n := fun n => div_nonneg (by positivity) (by positivity)
  have hd1 : ∀ n, d n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hDz := Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono hDK n)
      simp [d, hzero, hDz]
    · change (GenLimit.PatientScope.prefixCount D n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one]
      · exact_mod_cast prefixCount_mono hDK n
      · positivity
  have he0 : ∀ n, 0 ≤ e n := by
    intro n
    apply div_nonneg
    · dsimp [c]
      positivity
    · positivity
  have hc : 0 ≤ c / 2 := by
    dsimp [c]
    positivity
  have hec : ∀ n, e n ≤ c / 2 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · dsimp [e]
      rw [hzero]
      simp
      dsimp [c]
      positivity
    · change (c / 2) / (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ c / 2
      rw [div_le_iff₀ (by positivity)]
      have hden : (1 : ℝ) ≤ (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      nlinarith
  have he_tendsto : Filter.Tendsto e Filter.atTop (nhds 0) := by
    have hk := prefixCount_tendsto_atTop (hfamily j)
    have hbase := tendsto_const_div_atTop_nhds_zero_nat (c / 2)
    exact hbase.comp hk
  have hpoint : ∀ n, (1 / 2 : ℝ) * a n + (-e n) ≤ d n := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hIz := Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono hIK n)
      have hDz := Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono hDK n)
      simp [a, d, e, hzero, hIz, hDz]
    · have hb := corePrefix_card_bound hm family input hinj hInf n
      have hDI : generatorPrefix family input n ⊆
          GenLimit.PatientScope.prefixFinset D n := by
        intro z hz
        simp only [generatorPrefix, GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, hz.2.1, hIK hz.2.2⟩
      have hdc0 := Finset.card_le_card hDI
      have hdc : (generatorPrefix family input n).card ≤
          GenLimit.PatientScope.prefixCount D n := by
        simpa [GenLimit.PatientScope.prefixCount] using hdc0
      have hnat : GenLimit.PatientScope.prefixCount I n ≤
          2 * GenLimit.PatientScope.prefixCount D n + ((early hm family input).card + 1) := by
        change (corePrefix family input n).card ≤ _
        change (corePrefix family input n).card ≤
          2 * (GenLimit.PatientScope.prefixCount D n) + ((early hm family input).card + 1)
        omega
      have hden : (0 : ℝ) < (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity
      have hr : (GenLimit.PatientScope.prefixCount I n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount D n : ℝ) +
            ((early hm family input).card + 1 : ℕ) := by
        exact_mod_cast hnat
      dsimp [a, d, e, c]
      calc
        (1 / 2 : ℝ) *
              ((GenLimit.PatientScope.prefixCount I n : ℝ) /
                (GenLimit.PatientScope.prefixCount K n : ℝ)) +
            -(((early hm family input).card + 1 : ℕ) / 2 /
                (GenLimit.PatientScope.prefixCount K n : ℝ)) =
            (((GenLimit.PatientScope.prefixCount I n : ℝ) / 2) -
              (((early hm family input).card + 1 : ℕ) / 2)) /
                (GenLimit.PatientScope.prefixCount K n : ℝ) := by ring
        _ ≤ (GenLimit.PatientScope.prefixCount D n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
          apply (div_le_div_iff_of_pos_right hden).2
          nlinarith
  have ha_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop a :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall ha0)
  have ha_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop a :=
    Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall ha1)
  have ha_cob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop a :=
    Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := 1)
      (Filter.Eventually.of_forall ha1)
  have hu_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => (1/2:ℝ) * a n) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => mul_nonneg (by norm_num) (ha0 n))
  have hu_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => (1/2:ℝ) * a n) :=
    Filter.isBoundedUnder_of_eventually_le (a := (1/2:ℝ))
      (Filter.Eventually.of_forall fun n => by nlinarith [ha0 n, ha1 n])
  have hv_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => -e n) :=
    Filter.isBoundedUnder_of_eventually_ge (a := -(c/2))
      (Filter.Eventually.of_forall fun n => by have := hec n; linarith)
  have hv_above : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (fun n => -e n) :=
    Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := 0)
      (Filter.Eventually.of_forall fun n => by have := he0 n; linarith)
  have hd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop d :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hd0)
  have hd_cob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop d :=
    Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop
      (Filter.Eventually.of_forall hd1)
  have hscale : (1 / 2 : ℝ) * Filter.liminf a Filter.atTop =
      Filter.liminf (fun n => (1 / 2 : ℝ) * a n) Filter.atTop := by
    have hmapping := Monotone.map_liminf_of_continuousAt
      (F := Filter.atTop) (f := fun x : ℝ => (1/2:ℝ) * x)
      (fun _ _ h => by nlinarith) a
      (continuousAt_const.mul continuousAt_id) ha_cob ha_below
    simpa [Function.comp_def] using hmapping
  have hneg : Filter.liminf (fun n => -e n) Filter.atTop = 0 := by
    simpa using he_tendsto.neg.liminf_eq
  have hadd : Filter.liminf (fun n => (1/2:ℝ) * a n) Filter.atTop +
      Filter.liminf (fun n => -e n) Filter.atTop ≤
      Filter.liminf (fun n => (1/2:ℝ) * a n + (-e n)) Filter.atTop := by
    exact le_liminf_add hu_below hu_above hv_below hv_above
  have hmono : Filter.liminf (fun n => (1/2:ℝ) * a n + (-e n)) Filter.atTop ≤
      Filter.liminf d Filter.atTop := by
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hpoint)
      (Filter.isBoundedUnder_of_eventually_ge (a := -(c/2))
        (Filter.Eventually.of_forall fun n => by
          have h1 := ha0 n
          have h2 := hec n
          linarith)) hd_cob
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * Filter.liminf a Filter.atTop ≤ Filter.liminf d Filter.atTop
  rw [hscale]
  simpa [hneg] using hadd.trans hmono

end Case017

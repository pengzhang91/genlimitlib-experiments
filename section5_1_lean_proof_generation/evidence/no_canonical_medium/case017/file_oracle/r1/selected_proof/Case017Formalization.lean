import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
import Mathlib.Data.Nat.Find

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable section

variable {m : ℕ} (family : Fin m → Stage3Case017.Language)

/-- The intersection of candidates consistent with a finite input prefix. -/
def active (xs : Finset ℕ) : Set ℕ :=
  {z | ∀ j, (↑xs : Set ℕ) ⊆ family j → z ∈ family j}

def available (xs ys : Finset ℕ) : Set ℕ :=
  active family xs \ (↑(xs ∪ ys) : Set ℕ)

/-- Least currently available value, with an irrelevant fallback off valid runs. -/
def pick (xs ys : Finset ℕ) : ℕ := by
  classical
  exact if h : (available family xs ys).Nonempty then Nat.find h else 0

lemma pick_mem {xs ys : Finset ℕ} (h : (available family xs ys).Nonempty) :
    pick (family := family) xs ys ∈ available family xs ys := by
  classical
  rw [pick, dif_pos h]
  exact Nat.find_spec h

lemma pick_le {xs ys : Finset ℕ} (h : (available family xs ys).Nonempty)
    {z : ℕ} (hz : z ∈ available family xs ys) : pick (family := family) xs ys ≤ z := by
  classical
  simp only [pick, dif_pos h]
  exact Nat.find_min' h hz

/-- The causal recursion producing the unique trace of the greedy rule. -/
def run (input : Stage3Case017.Stream) : Stage3Case017.Stream :=
  WellFounded.fix (measure id).wf (fun t rec =>
    pick (family := family)
      (GenLimit.Generic.sample input (t + 1))
      (Finset.image (fun s : Fin t => rec s (by exact s.isLt)) Finset.univ))

lemma run_eq (input : Stage3Case017.Stream) (t : ℕ) :
    run (family := family) input t =
      pick (family := family)
        (GenLimit.Generic.sample input (t + 1))
        (Finset.image (fun s : Fin t => run (family := family) input s) Finset.univ) := by
  rw [run, WellFounded.fix_eq]

/-- The actual online rule; on a genuine trace its second finite argument is
exactly the finite set used by `run`. -/
def generator : Stage3Case017.OnlineGenerator := fun _ xs ys =>
  pick (family := family)
    (GenLimit.Generic.sequenceSample xs)
    (GenLimit.Generic.sequenceSample ys)

lemma follows (input : Stage3Case017.Stream) :
    Stage3Case017.Follows (generator (family := family)) input (run (family := family) input) := by
  intro t
  rw [run_eq]
  unfold generator
  rw [GenLimit.Generic.sequenceSample_prefix]
  have hout : GenLimit.Generic.sequenceSample (fun i : Fin t => run (family := family) input i) =
      Finset.image (fun s : Fin t => run (family := family) input s) Finset.univ := by
    ext z
    simp [GenLimit.Generic.sequenceSample]
  rw [hout]


lemma active_eventually_core (input : Stage3Case017.Stream) :
    ∃ T, ∀ t, T ≤ t →
      active family (GenLimit.Generic.sample input (t + 1)) =
        Stage3Case017.informationCore family input := by
  classical
  let bad : Finset (Fin m) := Finset.univ.filter fun j =>
    ¬ GenLimit.Generic.StreamIn input (family j)
  let witness : Fin m → ℕ := fun j =>
    if h : ∃ s, input s ∉ family j then Classical.choose h else 0
  have hwitness : ∀ j ∈ bad, input (witness j) ∉ family j := by
    intro j hj
    have hn := (Finset.mem_filter.mp hj).2
    have he : ∃ s, input s ∉ family j := by
      simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using hn
    simp [witness, he, Classical.choose_spec he]
  let T := bad.sup (fun j => witness j + 1)
  refine ⟨T, ?_⟩
  intro t ht
  apply Set.Subset.antisymm
  · intro z hz j hj
    apply hz j
    intro x hx
    change x ∈ GenLimit.Generic.sample input (t + 1) at hx
    rw [GenLimit.Generic.mem_sample_iff] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact hj ⟨s, rfl⟩
  · intro z hz j hsample
    by_contra hzj
    have jbad : j ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      intro hstream
      exact hzj (hz j hstream)⟩
    have hle : witness j + 1 ≤ T := by
      exact Finset.le_sup (f := fun j => witness j + 1) jbad
    have hwt : witness j < t + 1 := by omega
    exact (hwitness j jbad) (hsample (GenLimit.Generic.value_mem_sample hwt))

lemma available_nonempty (input : Stage3Case017.Stream) (t : ℕ)
    (hactive : (active family (GenLimit.Generic.sample input (t + 1))).Infinite) :
    (available family (GenLimit.Generic.sample input (t + 1))
      (Finset.image (fun s : Fin t => run (family := family) input s) Finset.univ)).Nonempty := by
  let forbidden : Set ℕ :=
    ↑(GenLimit.Generic.sample input (t + 1) ∪
      Finset.image (fun s : Fin t => run (family := family) input s) Finset.univ)
  obtain ⟨z, hzactive, hznot⟩ := hactive.exists_notMem_finite forbidden.toFinite
  exact ⟨z, hzactive, hznot⟩

lemma run_properties (input : Stage3Case017.Stream) (t : ℕ)
    (hactive : (active family (GenLimit.Generic.sample input (t + 1))).Infinite) :
    run (family := family) input t ∈ active family (GenLimit.Generic.sample input (t + 1)) ∧
    run (family := family) input t ∉ GenLimit.Generic.sample input (t + 1) ∧
    ∀ s, s < t → run (family := family) input s ≠ run (family := family) input t := by
  rw [run_eq]
  have hne := available_nonempty (family := family) input t hactive
  have hp := pick_mem (family := family) hne
  refine ⟨hp.1, ?_, ?_⟩
  · exact fun hmem => hp.2 (Finset.mem_union_left _ hmem)
  · intro s hs heq
    apply hp.2
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩

lemma novel (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run (family := family) input) (family j) := by
  obtain ⟨T, hT⟩ := active_eventually_core (family := family) input
  refine ⟨T, ?_⟩
  intro t ht
  have hactive := hT t ht
  have hp := run_properties (family := family) input t (hactive.symm ▸ hcore)
  refine ⟨?_, ?_, hp.2.2⟩
  · rw [hactive] at hp
    exact hp.1 j hj
  · intro hs
    apply hp.2.1
    rw [GenLimit.Generic.mem_sample_iff]
    rw [GenLimit.mem_sample_iff] at hs
    exact hs


lemma tail_injective (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hT : ∀ t, T ≤ t →
      active family (GenLimit.Generic.sample input (t + 1)) =
        Stage3Case017.informationCore family input) :
    Function.Injective (fun n => run (family := family) input (T + n)) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbal
  · have hactive := hT (T + b) (Nat.le_add_right T b)
    have hp := run_properties (family := family) input (T + b) (hactive.symm ▸ hcore)
    exact hp.2.2 (T + a) (by omega) hab
  · have hactive := hT (T + a) (Nat.le_add_right T a)
    have hp := run_properties (family := family) input (T + a) (hactive.symm ▸ hcore)
    exact hp.2.2 (T + b) (by omega) hab.symm

lemma tail_generatorFirst (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hT : ∀ t, T ≤ t →
      active family (GenLimit.Generic.sample input (t + 1)) =
        Stage3Case017.informationCore family input) (n : ℕ) :
    run (family := family) input (T + n) ∈
      GenLimit.GeneratorFirst input (run (family := family) input) := by
  refine ⟨T + n, rfl, ?_⟩
  intro s hs heq
  have hactive := hT (T + n) (Nat.le_add_right T n)
  have hp := run_properties (family := family) input (T + n) (hactive.symm ▸ hcore)
  apply hp.2.1
  rw [GenLimit.Generic.mem_sample_iff]
  exact ⟨s, Nat.lt_succ_of_le hs, heq⟩

lemma generatorFirst_infinite (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    (GenLimit.GeneratorFirst input (run (family := family) input)).Infinite := by
  obtain ⟨T, hT⟩ := active_eventually_core (family := family) input
  exact Set.infinite_of_injective_forall_mem
    (tail_injective (family := family) input hcore hT)
    (tail_generatorFirst (family := family) input hcore hT)

lemma missing_core_subset_generatorFirst (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (family := family) input) := by
  obtain ⟨T, hT⟩ := active_eventually_core (family := family) input
  intro z hz
  by_contra hnot
  have hout_ne : ∀ t, run (family := family) input t ≠ z := by
    intro t heq
    apply hnot
    refine ⟨t, heq, ?_⟩
    intro s hs hin
    exact hz.2 ⟨s, hin⟩
  have hle : ∀ n, run (family := family) input (T + n) ≤ z := by
    intro n
    rw [run_eq]
    have hactive := hT (T + n) (Nat.le_add_right T n)
    have hne := available_nonempty (family := family) input (T + n) (hactive.symm ▸ hcore)
    apply pick_le (family := family) hne
    refine ⟨?_, ?_⟩
    · rw [hactive]
      exact hz.1
    · intro hmem
      rcases Finset.mem_union.mp hmem with hin | hout
      · rw [GenLimit.Generic.mem_sample_iff] at hin
        obtain ⟨s, hs, heq⟩ := hin
        exact hz.2 ⟨s, heq⟩
      · obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hout
        exact hout_ne s (by simpa using heq)
  let f : Fin (z + 2) → Fin (z + 1) := fun n =>
    ⟨run (family := family) input (T + n), Nat.lt_succ_of_le (hle n)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply (tail_injective (family := family) input hcore hT)
    exact congrArg (fun x : Fin (z + 1) => x.val) hab
  have hc := Fintype.card_le_of_injective f hf
  simp at hc


def firstInput (input : Stage3Case017.Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range input then Nat.find h else 0

lemma firstInput_spec {input : Stage3Case017.Stream} {x : ℕ}
    (hx : x ∈ Set.range input) : input (firstInput input x) = x := by
  classical
  rw [firstInput, dif_pos hx]
  exact Nat.find_spec hx

lemma firstInput_min {input : Stage3Case017.Stream} {x : ℕ}
    (hx : x ∈ Set.range input) {s : ℕ} (hs : input s = x) :
    firstInput input x ≤ s := by
  classical
  rw [firstInput, dif_pos hx]
  exact Nat.find_min' hx hs

lemma firstInput_injective (input : Stage3Case017.Stream)
    (hinj : Function.Injective input) :
    Set.InjOn (firstInput input) (Set.range input) := by
  intro x hx y hy hxy
  rw [← firstInput_spec hx, ← firstInput_spec hy]
  exact congrArg input hxy

lemma late_partner_data (input : Stage3Case017.Stream)
    (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j))
    {T : ℕ} (hT : ∀ t, T ≤ t →
      active family (GenLimit.Generic.sample input (t + 1)) =
        Stage3Case017.informationCore family input)
    {x : ℕ}
    (hxcore : x ∈ Stage3Case017.informationCore family input)
    (hxnotD : x ∉ GenLimit.GeneratorFirst input (run (family := family) input))
    (hxlate : x ∉ GenLimit.Generic.sample input (T + 1)) :
    let tx := firstInput input x
    let partner := run (family := family) input (tx - 1)
    partner ∈ GenLimit.GeneratorFirst input (run (family := family) input) ∩ family j ∧
      partner < x := by
  have hxrange : x ∈ Set.range input := by
    by_contra hnr
    exact hxnotD (missing_core_subset_generatorFirst (family := family) input hcore ⟨hxcore, hnr⟩)
  let tx := firstInput input x
  have htx : input tx = x := firstInput_spec hxrange
  have htxgt : T < tx := by
    by_contra hnot
    apply hxlate
    rw [GenLimit.Generic.mem_sample_iff]
    exact ⟨tx, by omega, htx⟩
  have hnoOut : ∀ s, s < tx → run (family := family) input s ≠ x := by
    intro s hs heq
    apply hxnotD
    refine ⟨s, heq, ?_⟩
    intro q hqs hqin
    have hmin := firstInput_min hxrange hqin
    omega
  have hactive := hT (tx - 1) (by omega)
  have hp := run_properties (family := family) input (tx - 1) (hactive.symm ▸ hcore)
  have hxavail : x ∈ available family
      (GenLimit.Generic.sample input tx)
      (Finset.image (fun s : Fin (tx - 1) => run (family := family) input s) Finset.univ) := by
    refine ⟨?_, ?_⟩
    · rw [show tx = (tx - 1) + 1 by omega, hactive]
      exact hxcore
    · intro hmem
      rcases Finset.mem_union.mp hmem with hin | hout
      · rw [GenLimit.Generic.mem_sample_iff] at hin
        obtain ⟨s, hs, heq⟩ := hin
        have hmin := firstInput_min hxrange heq
        omega
      · obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hout
        exact hnoOut s (by omega) (by simpa using heq)
  have hle : run (family := family) input (tx - 1) ≤ x := by
    rw [run_eq]
    have hne := available_nonempty (family := family) input (tx - 1) (hactive.symm ▸ hcore)
    exact pick_le (family := family) hne (by simpa [show tx - 1 + 1 = tx by omega] using hxavail)
  have hlt : run (family := family) input (tx - 1) < x :=
    lt_of_le_of_ne hle (hnoOut (tx - 1) (by omega))
  refine ⟨?_, hlt⟩
  refine ⟨?_, ?_⟩
  · refine ⟨tx - 1, rfl, ?_⟩
    intro q hq heq
    apply hp.2.1
    rw [GenLimit.Generic.mem_sample_iff]
    exact ⟨q, by omega, heq⟩
  · rw [hactive] at hp
    exact hp.1 j hj



lemma core_count_le (input : Stage3Case017.Stream)
    (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j))
    {T : ℕ} (hT : ∀ t, T ≤ t →
      active family (GenLimit.Generic.sample input (t + 1)) =
        Stage3Case017.informationCore family input) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (family := family) input) ∩ family j) n +
      (GenLimit.Generic.sample input (T + 1)).card := by
  classical
  let core := Stage3Case017.informationCore family input
  let defender := GenLimit.GeneratorFirst input (run (family := family) input) ∩ family j
  let E := GenLimit.PatientScope.prefixFinset core n
  let D := GenLimit.PatientScope.prefixFinset defender n
  let A := E \ D
  let early := GenLimit.Generic.sample input (T + 1)
  let late := A \ early
  let partner : ℕ → ℕ := fun x =>
    run (family := family) input (firstInput input x - 1)
  have hcoreK : core ⊆ family j := fun x hx => hx j hj
  have hlate_map : Set.MapsTo partner (↑late : Set ℕ) (↑D : Set ℕ) := by
    intro x hx
    have hxlatefin : x ∈ late := hx
    have hxA : x ∈ A := (Finset.mem_sdiff.mp hxlatefin).1
    have hxearly : x ∉ early := (Finset.mem_sdiff.mp hxlatefin).2
    have hxE : x ∈ E := (Finset.mem_sdiff.mp hxA).1
    have hxnotDfin : x ∉ D := (Finset.mem_sdiff.mp hxA).2
    have hxprefix := GenLimit.PatientScope.mem_prefixFinset.mp hxE
    have hxcore : x ∈ core := hxprefix.2
    have hxnotGF : x ∉ GenLimit.GeneratorFirst input (run (family := family) input) := by
      intro hxGF
      apply hxnotDfin
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      exact ⟨hxprefix.1, hxGF, hcoreK hxcore⟩
    have hp := late_partner_data (family := family) input hinj hcore hj hT hxcore hxnotGF hxearly
    apply GenLimit.PatientScope.mem_prefixFinset.mpr
    exact ⟨lt_trans hp.2 hxprefix.1, hp.1⟩
  have hlate_inj : Set.InjOn partner (↑late : Set ℕ) := by
    intro x hx y hy hxy
    have hxlatefin : x ∈ late := hx
    have hylatefin : y ∈ late := hy
    have hxA : x ∈ A := (Finset.mem_sdiff.mp hxlatefin).1
    have hyA : y ∈ A := (Finset.mem_sdiff.mp hylatefin).1
    have hxE : x ∈ E := (Finset.mem_sdiff.mp hxA).1
    have hyE : y ∈ E := (Finset.mem_sdiff.mp hyA).1
    have hxcore : x ∈ core := (GenLimit.PatientScope.mem_prefixFinset.mp hxE).2
    have hycore : y ∈ core := (GenLimit.PatientScope.mem_prefixFinset.mp hyE).2
    have hxrange : x ∈ Set.range input := by
      by_contra hnr
      have hxGF := missing_core_subset_generatorFirst (family := family) input hcore ⟨hxcore, hnr⟩
      exact (Finset.mem_sdiff.mp hxA).2 (GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hxE).1, hxGF, hcoreK hxcore⟩)
    have hyrange : y ∈ Set.range input := by
      by_contra hnr
      have hyGF := missing_core_subset_generatorFirst (family := family) input hcore ⟨hycore, hnr⟩
      exact (Finset.mem_sdiff.mp hyA).2 (GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hyE).1, hyGF, hcoreK hycore⟩)
    have hxt : T < firstInput input x := by
      by_contra hnle
      exact (Finset.mem_sdiff.mp hxlatefin).2 (by
        rw [GenLimit.Generic.mem_sample_iff]
        exact ⟨firstInput input x, by omega, firstInput_spec hxrange⟩)
    have hyt : T < firstInput input y := by
      by_contra hnle
      exact (Finset.mem_sdiff.mp hylatefin).2 (by
        rw [GenLimit.Generic.mem_sample_iff]
        exact ⟨firstInput input y, by omega, firstInput_spec hyrange⟩)
    have htimes : firstInput input x - 1 = firstInput input y - 1 := by
      let tx := firstInput input x - 1
      let ty := firstInput input y - 1
      have hxrepr : tx = T + (tx - T) := by omega
      have hyrepr : ty = T + (ty - T) := by omega
      have hxy' : run (family := family) input tx = run (family := family) input ty := by
        exact hxy
      rw [hxrepr, hyrepr] at hxy'
      have hsuffix := (tail_injective (family := family) input hcore hT) hxy'
      omega
    have hfirst : firstInput input x = firstInput input y := by omega
    rw [← firstInput_spec hxrange, ← firstInput_spec hyrange, hfirst]
  have hlate_card : late.card ≤ D.card :=
    Finset.card_le_card_of_injOn partner hlate_map hlate_inj
  have hA_cover : A ⊆ late ∪ early := by
    intro x hx
    by_cases he : x ∈ early
    · exact Finset.mem_union_right _ he
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, he⟩)
  have hA_card : A.card ≤ late.card + early.card := by
    calc
      A.card ≤ (late ∪ early).card := Finset.card_le_card hA_cover
      _ ≤ late.card + early.card := Finset.card_union_le _ _
  have hE_cover : E ⊆ D ∪ A := by
    intro x hx
    by_cases hd : x ∈ D
    · exact Finset.mem_union_left _ hd
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hd⟩)
  have hE_card : E.card ≤ D.card + A.card := by
    calc
      E.card ≤ (D ∪ A).card := Finset.card_le_card hE_cover
      _ ≤ D.card + A.card := Finset.card_union_le _ _
  change E.card ≤ 2 * D.card + early.card
  omega

lemma half_core_density (input : Stage3Case017.Stream)
    (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (family := family) input) ∩ family j) (family j) := by
  obtain ⟨T, hT⟩ := active_eventually_core (family := family) input
  apply GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount (family j) n)
    (fun n => GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n)
    (fun n => GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (run (family := family) input) ∩ family j) n)
    (GenLimit.Generic.sample input (T + 1)).card
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono (fun x (hx : x ∈ Stage3Case017.informationCore family input) => hx j hj) n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hc := core_count_le (family := family) input hinj hcore hj hT n
    omega


lemma relativeLowerDensity_mono_left {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      have hc := GenLimit.PatientScope.prefixCount_mono hAB n
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
  · exact isBoundedUnder_of_eventually_ge <| Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · have hb0 : GenLimit.PatientScope.prefixCount B n = 0 :=
          Nat.eq_zero_of_le_zero (hn ▸ GenLimit.PatientScope.prefixCount_mono hBK n)
        simp [hn, hb0]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

end

end Stage3Case017Proof

open Stage3Case017Proof

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  classical
  refine ⟨generator (family := family), ?_⟩
  intro input hinj hexists hcore
  refine ⟨run (family := family) input, follows (family := family) input, ?_⟩
  intro j hj
  refine ⟨novel (family := family) input hcore hj, ?_⟩
  apply max_le
  · exact half_core_density (family := family) input hinj hcore hj (hinfinite j)
  · apply relativeLowerDensity_mono_left
    · intro z hz
      exact ⟨missing_core_subset_generatorFirst (family := family) input hcore hz,
        hz.1 j hj⟩
    · exact Set.inter_subset_right

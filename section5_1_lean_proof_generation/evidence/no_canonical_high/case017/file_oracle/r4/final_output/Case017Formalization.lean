import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

def activeCore {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

def available {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) : Language :=
  activeCore family input \ (Set.range input ∪ Set.range previous)

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator :=
  fun _ input previous => sInf (available family input previous)

theorem available_nonempty {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {previous : Fin t → ℕ}
    (hcore : (activeCore family input).Infinite) :
    (available family input previous).Nonempty := by
  have hfinite : (Set.range input ∪ Set.range previous).Finite :=
    (Set.finite_range input).union (Set.finite_range previous)
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_not_mem_finite hfinite
  exact ⟨z, hzcore, hzused⟩

theorem greedy_mem_available {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {previous : Fin t → ℕ}
    (hcore : (activeCore family input).Infinite) :
    greedyGenerator family t input previous ∈ available family input previous := by
  exact Nat.sInf_mem (available_nonempty hcore)

noncomputable def trajectory (gen : OnlineGenerator)
    (input : Stream) : Stream :=
  WellFounded.fix Nat.lt_wfRel.wf fun t rec =>
    gen t (fun i => input i) (fun i => rec i i.isLt)

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]
  rw [WellFounded.fix_eq]

theorem activeCore_stabilizes {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      activeCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have badTimeExists (j : Fin m)
      (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
      ∃ s, input s ∉ family j := by
    obtain ⟨z, ⟨s, rfl⟩, hz⟩ := Set.not_subset.mp h
    exact ⟨s, hz⟩
  let witnessTime : Fin m → ℕ := fun j =>
    if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Classical.choose (badTimeExists j h)
  let T := (Finset.univ.image witnessTime).max'
    (Finset.image_nonempty.mpr ⟨⟨0, hm⟩, Finset.mem_univ _⟩)
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hj
    apply hz j
    intro z' hz'
    obtain ⟨s, rfl⟩ := hz'
    by_contra hmem
    have hnot : ¬ GenLimit.Generic.StreamIn input (family j) := by
      intro hall
      exact hmem (hall ⟨s, rfl⟩)
    have hwitness : input (witnessTime j) ∉ family j := by
      dsimp [witnessTime]
      rw [dif_neg hnot]
      exact Classical.choose_spec (badTimeExists j hnot)
    have htime_le_T : witnessTime j ≤ T := by
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have htime_le_t : witnessTime j ≤ t := le_trans htime_le_T ht
    let i : Fin (t + 1) := ⟨witnessTime j, Nat.lt_succ_of_le htime_le_t⟩
    exact hwitness (hj i)

theorem activeCore_infinite_after {m : ℕ} (hm : 0 < m)
    {family : Fin m → Language} {input : Stream} (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      (activeCore family (fun i : Fin (t + 1) => input i)).Infinite := by
  obtain ⟨T, hT⟩ := activeCore_stabilizes hm family input
  exact ⟨T, fun t ht => by rw [hT t ht]; exact hcore⟩


theorem stable_output_spec {m t : ℕ} {family : Fin m → Language}
    {input output : Stream}
    (hfollows : Follows (greedyGenerator family) input output)
    (hstable : activeCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input)
    (hcore : (informationCore family input).Infinite) :
    output t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ output t) ∧
      ∀ s, s < t → output s ≠ output t := by
  have hactive :
      (activeCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hstable]
    exact hcore
  have hmem := greedy_mem_available
    (family := family) (input := fun i : Fin (t + 1) => input i)
    (previous := fun i : Fin t => output i) hactive
  rw [← hfollows t] at hmem
  rcases hmem with ⟨hmem, hnot⟩
  refine ⟨hstable ▸ hmem, ?_, ?_⟩
  · intro s hs heq
    apply hnot
    apply Set.mem_union_left
    exact ⟨⟨s, Nat.lt_succ_of_le hs⟩, heq⟩
  · intro s hs heq
    apply hnot
    apply Set.mem_union_right
    exact ⟨⟨s, hs⟩, heq⟩

theorem stable_output_le {m t z : ℕ} {family : Fin m → Language}
    {input output : Stream}
    (hfollows : Follows (greedyGenerator family) input output)
    (hstable : activeCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input)
    (hcore : (informationCore family input).Infinite)
    (hzcore : z ∈ informationCore family input)
    (hzinput : ∀ s, s ≤ t → input s ≠ z)
    (hzoutput : ∀ s, s < t → output s ≠ z) :
    output t ≤ z := by
  have hactive :
      (activeCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hstable]
    exact hcore
  have hzavailable : z ∈ available family
      (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i) := by
    refine ⟨hstable.symm ▸ hzcore, ?_⟩
    intro hz
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := hz
      exact hzinput i (Nat.le_of_lt_succ i.isLt) hi
    · obtain ⟨i, hi⟩ := hz
      exact hzoutput i i.isLt hi
  rw [hfollows t]
  exact Nat.sInf_le hzavailable

theorem missing_core_generatorFirst {m : ℕ} {family : Fin m → Language}
    {input output : Stream} {T : ℕ}
    (hfollows : Follows (greedyGenerator family) input output)
    (hstable : ∀ t, T ≤ t →
      activeCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output := by
  classical
  intro z hz
  rcases hz with ⟨hzcore, hzinput⟩
  have hzinput' : ∀ s, input s ≠ z := by
    intro s hs
    exact hzinput ⟨s, hs⟩
  have hout : z ∈ Set.range output := by
    by_contra hzoutput
    have hzoutput' : ∀ s, output s ≠ z := by
      intro s hs
      exact hzoutput ⟨s, hs⟩
    let f : Fin (z + 2) → Fin (z + 1) := fun i =>
      ⟨output (T + i), Nat.lt_succ_iff.mpr <|
        stable_output_le hfollows (hstable _ (Nat.le_add_right T i)) hcore hzcore
          (fun s _ => hzinput' s) (fun s _ => hzoutput' s)⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      by_contra hijval
      rcases lt_or_gt_of_ne hijval with hijlt | hijgt
      · have hneq := (stable_output_spec hfollows
          (hstable (T + j) (Nat.le_add_right T j)) hcore).2.2
          (T + i) (Nat.add_lt_add_left hijlt T)
        exact hneq (congrArg Fin.val hij)
      · have hneq := (stable_output_spec hfollows
          (hstable (T + i) (Nat.le_add_right T i)) hcore).2.2
          (T + j) (Nat.add_lt_add_left hijgt T)
        exact hneq (congrArg Fin.val hij).symm
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨t, ht⟩ := hout
  refine ⟨t, ht, ?_⟩
  intro s hs
  exact hzinput' s

noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ :=
  sInf {t | input t = z}

theorem firstInput_spec {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  exact Nat.sInf_mem hz

theorem firstInput_min {input : Stream} {z t : ℕ} (ht : input t = z) :
    firstInput input z ≤ t := by
  exact Nat.sInf_le ht

theorem core_prefix_count_le {m : ℕ} {family : Fin m → Language}
    {input output : Stream} {T : ℕ}
    (hinj : Function.Injective input)
    (hfollows : Follows (greedyGenerator family) input output)
    (hstable : ∀ t, T ≤ t →
      activeCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {K : Language} (hcompat : GenLimit.Generic.StreamIn input K)
    (hcoreK : informationCore family input ⊆ K) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ K) n + (T + 1) := by
  classical
  let E := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ K) n
  let early := (Finset.range (T + 1)).image input
  let A := E \ D
  let late := A \ early
  have hmissing := missing_core_generatorFirst hfollows hstable hcore
  have hxrange : ∀ x ∈ A, x ∈ Set.range input := by
    intro x hx
    have hxE := GenLimit.PatientScope.mem_prefixFinset.mp (Finset.mem_sdiff.mp hx).1
    by_contra hxr
    have hxG := hmissing ⟨hxE.2, hxr⟩
    have hxD : x ∈ D := GenLimit.PatientScope.mem_prefixFinset.mpr
      ⟨hxE.1, hxG, hcoreK hxE.2⟩
    exact (Finset.mem_sdiff.mp hx).2 hxD
  let partner : ℕ → ℕ := fun x => output (firstInput input x - 1)
  have hpartner : ∀ x ∈ late, partner x ∈ D := by
    intro x hx
    have hxA := (Finset.mem_sdiff.mp hx).1
    have hxearly := (Finset.mem_sdiff.mp hx).2
    have hxE := GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_sdiff.mp hxA).1
    have hxr := hxrange x hxA
    have hfirst : input (firstInput input x) = x := firstInput_spec hxr
    have hTlt : T < firstInput input x := by
      by_contra hle
      have hmemEarly : x ∈ early := by
        apply Finset.mem_image.mpr
        exact ⟨firstInput input x, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt hle)), hfirst⟩
      exact hxearly hmemEarly
    have hpred : T ≤ firstInput input x - 1 := by omega
    have hnotG : x ∉ GenLimit.GeneratorFirst input output := by
      intro hxG
      have hxD : x ∈ D := GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hxE.1, hxG, hcoreK hxE.2⟩
      exact (Finset.mem_sdiff.mp hxA).2 hxD
    have hnoInput : ∀ s, s ≤ firstInput input x - 1 → input s ≠ x := by
      intro s hs hsi
      have hmin := firstInput_min hsi
      omega
    have hnoOutput : ∀ s, s < firstInput input x - 1 → output s ≠ x := by
      intro s hs hso
      apply hnotG
      refine ⟨s, hso, ?_⟩
      intro q hqs hqi
      have hmin := firstInput_min hqi
      omega
    have hle : partner x ≤ x := by
      exact stable_output_le (output := output) (t := firstInput input x - 1) (z := x)
        hfollows (hstable _ hpred) hcore hxE.2 hnoInput hnoOutput
    have hspec := stable_output_spec hfollows (hstable _ hpred) hcore
    apply GenLimit.PatientScope.mem_prefixFinset.mpr
    refine ⟨lt_of_le_of_lt hle hxE.1, ?_, hcoreK hspec.1⟩
    refine ⟨firstInput input x - 1, rfl, ?_⟩
    intro q hq
    exact hspec.2.1 q hq
  have hpartner_inj : Set.InjOn partner (↑late : Set ℕ) := by
    intro x hx y hy hxy
    have hxlate : x ∈ late := hx
    have hylate : y ∈ late := hy
    have hxA := (Finset.mem_sdiff.mp hxlate).1
    have hyA := (Finset.mem_sdiff.mp hylate).1
    have hxearly := (Finset.mem_sdiff.mp hxlate).2
    have hyearly := (Finset.mem_sdiff.mp hylate).2
    have hxfirst := firstInput_spec (hxrange x hxA)
    have hyfirst := firstInput_spec (hxrange y hyA)
    have hxT : T < firstInput input x := by
      by_contra hle
      apply hxearly
      exact Finset.mem_image.mpr
        ⟨firstInput input x, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt hle)), hxfirst⟩
    have hyT : T < firstInput input y := by
      by_contra hle
      apply hyearly
      exact Finset.mem_image.mpr
        ⟨firstInput input y, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt hle)), hyfirst⟩
    have hpredEq : firstInput input x - 1 = firstInput input y - 1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hspec := (stable_output_spec hfollows
          (hstable (firstInput input y - 1) (by omega)) hcore).2.2
          (firstInput input x - 1) hlt
        exact hspec hxy
      · have hspec := (stable_output_spec hfollows
          (hstable (firstInput input x - 1) (by omega)) hcore).2.2
          (firstInput input y - 1) hgt
        exact hspec hxy.symm
    have hfirstEq : firstInput input x = firstInput input y := by omega
    rw [← hxfirst, ← hyfirst, hfirstEq]
  have hlateCard : late.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn partner
    · exact hpartner
    · exact hpartner_inj
  have hearlyCard : early.card ≤ T + 1 := by
    calc
      early.card ≤ (Finset.range (T + 1)).card := Finset.card_image_le
      _ = T + 1 := Finset.card_range _
  have hAcard : A.card ≤ D.card + (T + 1) := by
    have hcover : A ⊆ early ∪ late := by
      intro x hx
      by_cases he : x ∈ early
      · exact Finset.mem_union_left _ he
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, he⟩)
    calc
      A.card ≤ (early ∪ late).card := Finset.card_le_card hcover
      _ ≤ early.card + late.card := Finset.card_union_le _ _
      _ ≤ (T + 1) + D.card := Nat.add_le_add hearlyCard hlateCard
      _ = D.card + (T + 1) := Nat.add_comm _ _
  have hEcover : E ⊆ D ∪ A := by
    intro x hx
    by_cases hd : x ∈ D
    · exact Finset.mem_union_left _ hd
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hd⟩)
  calc
    GenLimit.PatientScope.prefixCount (informationCore family input) n = E.card := rfl
    _ ≤ (D ∪ A).card := Finset.card_le_card hEcover
    _ ≤ D.card + A.card := Finset.card_union_le _ _
    _ ≤ D.card + (D.card + (T + 1)) := Nat.add_le_add_left hAcard _
    _ = 2 * D.card + (T + 1) := by omega
    _ = 2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ K) n + (T + 1) := rfl

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · apply isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hratio : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact isCoboundedUnder_ge_of_le atTop hratio

theorem half_core_density {m : ℕ} {family : Fin m → Language}
    {input output : Stream} {T : ℕ}
    (hinj : Function.Injective input)
    (hfollows : Follows (greedyGenerator family) input output)
    (hstable : ∀ t, T ≤ t →
      activeCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {K : Language} (hK : K.Infinite)
    (hcompat : GenLimit.Generic.StreamIn input K)
    (hcoreK : informationCore family input ⊆ K) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ K) K := by
  apply GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount K n)
    (fun n => GenLimit.PatientScope.prefixCount (informationCore family input) n)
    (fun n => GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input output ∩ K) n)
    (T + 1)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono hcoreK n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hcount := core_prefix_count_le hinj hfollows hstable hcore
      hcompat hcoreK n
    omega
end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  classical
  intro m hm family hfamily
  let gen := Stage3Case017Proof.greedyGenerator family
  refine ⟨gen, ?_⟩
  intro input hinj hpresentation hcore
  let output := Stage3Case017Proof.trajectory gen input
  have hfollows : Stage3Case017.Follows gen input output :=
    Stage3Case017Proof.trajectory_follows gen input
  obtain ⟨T, hstable⟩ :=
    Stage3Case017Proof.activeCore_stabilizes hm family input
  refine ⟨output, hfollows, ?_⟩
  intro j hcompat
  have hcoreK : Stage3Case017.informationCore family input ⊆ family j :=
    fun z hz => hz j hcompat
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    have hspec := Stage3Case017Proof.stable_output_spec hfollows
      (hstable t ht) hcore
    refine ⟨hcoreK hspec.1, ?_, hspec.2.2⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hspec.2.1 s (Nat.le_of_lt_succ hs) heq
  · apply max_le
    · exact Stage3Case017Proof.half_core_density hinj hfollows hstable hcore
        (hfamily j) hcompat hcoreK
    · apply Stage3Case017Proof.relativeLowerDensity_mono
      · intro z hz
        exact ⟨Stage3Case017Proof.missing_core_generatorFirst hfollows hstable hcore hz,
          hcoreK hz.1⟩
      · exact Set.inter_subset_right


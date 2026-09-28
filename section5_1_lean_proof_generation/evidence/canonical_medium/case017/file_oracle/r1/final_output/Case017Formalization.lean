import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable def finiteRange {n : ℕ} (f : Fin n → ℕ) : Finset ℕ :=
  Finset.univ.image f

def currentCore {m t : ℕ} (family : Fin m → Stage3Case017.Language)
    (xs : Fin (t + 1) → ℕ) : Stage3Case017.Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def freshChoice {n k : ℕ} (S : Set ℕ)
    (xs : Fin n → ℕ) (ys : Fin k → ℕ) : ℕ := by
  classical
  let used := finiteRange xs ∪ finiteRange ys
  by_cases hS : S.Infinite
  · exact Nat.find (hS.exists_notMem_finset used)
  · exact Nat.find (Set.infinite_univ.exists_notMem_finset used)

theorem freshChoice_spec {n k : ℕ} (S : Set ℕ)
    (xs : Fin n → ℕ) (ys : Fin k → ℕ) :
    let used := finiteRange xs ∪ finiteRange ys
    freshChoice S xs ys ∉ used ∧
      (S.Infinite → freshChoice S xs ys ∈ S) := by
  classical
  dsimp only
  unfold freshChoice
  dsimp only
  split <;> rename_i h
  · exact ⟨(Nat.find_spec (h.exists_notMem_finset _)).2,
      fun _ => (Nat.find_spec (h.exists_notMem_finset _)).1⟩
  · exact ⟨(Nat.find_spec (Set.infinite_univ.exists_notMem_finset _)).2,
      fun h' => False.elim (h h')⟩

theorem freshChoice_not_input {n k : ℕ} (S : Set ℕ)
    (xs : Fin n → ℕ) (ys : Fin k → ℕ) (i : Fin n) :
    freshChoice S xs ys ≠ xs i := by
  intro heq
  exact (freshChoice_spec S xs ys).1 <| Finset.mem_union_left _ <|
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩

theorem freshChoice_not_output {n k : ℕ} (S : Set ℕ)
    (xs : Fin n → ℕ) (ys : Fin k → ℕ) (i : Fin k) :
    freshChoice S xs ys ≠ ys i := by
  intro heq
  exact (freshChoice_spec S xs ys).1 <| Finset.mem_union_right _ <|
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩

theorem freshChoice_mem {n k : ℕ} {S : Set ℕ} (hS : S.Infinite)
    (xs : Fin n → ℕ) (ys : Fin k → ℕ) : freshChoice S xs ys ∈ S :=
  (freshChoice_spec S xs ys).2 hS

theorem freshChoice_le {n k : ℕ} {S : Set ℕ} (hS : S.Infinite)
    (xs : Fin n → ℕ) (ys : Fin k → ℕ) {z : ℕ}
    (hzS : z ∈ S) (hzx : ∀ i, xs i ≠ z) (hzy : ∀ i, ys i ≠ z) :
    freshChoice S xs ys ≤ z := by
  classical
  unfold freshChoice
  dsimp only
  rw [dif_pos hS]
  apply Nat.find_min'
  exact ⟨hzS, by
    intro hz
    rcases Finset.mem_union.mp hz with hx | hy
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
      exact hzx i hi
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
      exact hzy i hi⟩

noncomputable def generator {m : ℕ}
    (family : Fin m → Stage3Case017.Language) : Stage3Case017.OnlineGenerator :=
  fun t xs ys => freshChoice (currentCore family xs) xs ys

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) : Stage3Case017.Stream
  | t => gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t => t

theorem trajectory_follows (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory.eq_1 gen input t

theorem eventually_currentCore_eq {m : ℕ}
    (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases h : GenLimit.Generic.StreamIn input (family j)
    · exact ⟨0, fun _ _ => ⟨fun _ => h, fun _ i => h ⟨i, rfl⟩⟩⟩
    · obtain ⟨z, ⟨s, rfl⟩, hz⟩ := Set.not_subset.mp h
      refine ⟨s, ?_⟩
      intro t hst
      constructor
      · intro hall
        exact False.elim (hz (hall ⟨s, Nat.lt_succ_of_le hst⟩))
      · exact fun hs => False.elim (h hs)
  choose T hT using hj
  let T0 := Finset.univ.sup T
  refine ⟨T0, ?_⟩
  intro t ht
  ext z
  simp only [currentCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor <;> intro hz j hjc
  · exact hz j ((hT j t (le_trans (Finset.le_sup (Finset.mem_univ j)) ht)).2 hjc)
  · exact hz j ((hT j t (le_trans (Finset.le_sup (Finset.mem_univ j)) ht)).1 hjc)


theorem trajectory_not_input_le {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {s t : ℕ} (hst : s ≤ t) :
    trajectory (generator family) input t ≠ input s := by
  rw [trajectory.eq_1]
  exact freshChoice_not_input _ _ _ ⟨s, Nat.lt_succ_of_le hst⟩

theorem trajectory_not_output_lt {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {s t : ℕ} (hst : s < t) :
    trajectory (generator family) input t ≠
      trajectory (generator family) input s := by
  rw [trajectory.eq_1]
  exact freshChoice_not_output _ _ _ ⟨s, hst⟩

theorem trajectory_injective {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) :
    Function.Injective (trajectory (generator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact trajectory_not_output_lt family input hlt hst.symm
  · exact trajectory_not_output_lt family input hgt hst

theorem core_subset_family {m : ℕ} {family : Fin m → Stage3Case017.Language}
    {input : Stage3Case017.Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

theorem eventual_trace {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      trajectory (generator family) input t ∈
          Stage3Case017.informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  refine ⟨T, ?_⟩
  intro t ht
  rw [trajectory.eq_1]
  change freshChoice (currentCore family fun i : Fin (t + 1) => input i)
      (fun i => input i) (fun i => trajectory (generator family) input i) ∈
    Stage3Case017.informationCore family input
  rw [← hT t ht]
  apply freshChoice_mem
  simpa only [hT t ht] using hInf

theorem novel_for_compatible {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory (generator family) input)
      (family j) := by
  obtain ⟨T, hT⟩ := eventual_trace family input hInf
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨core_subset_family hj (hT t ht), ?_, ?_⟩
  · intro hsamp
    rw [GenLimit.mem_sample_iff] at hsamp
    obtain ⟨s, hst, hs⟩ := hsamp
    exact trajectory_not_input_le family input (Nat.le_of_lt_succ hst) hs.symm
  · intro s hst
    exact (trajectory_not_output_lt family input hst).symm

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro z hz
  have hzI := hz.1
  have hzNotInput := hz.2
  by_contra hzNotGF
  have hzNotOutput : z ∉ Set.range (trajectory (generator family) input) := by
    intro hzOut
    obtain ⟨t, ht⟩ := hzOut
    apply hzNotGF
    refine ⟨t, ht, ?_⟩
    intro s _ hs
    exact hzNotInput ⟨s, hs⟩
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨trajectory (generator family) input (T + i), by
      apply Nat.lt_succ_iff.mpr
      rw [trajectory.eq_1]
      apply freshChoice_le
      · simpa only [hT (T + i) (Nat.le_add_right T i)] using hInf
      · simpa only [hT (T + i) (Nat.le_add_right T i)] using hzI
      · intro q hq
        exact hzNotInput ⟨q, hq⟩
      · intro q hq
        exact hzNotOutput ⟨q, hq⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have habv : T + a = T + b :=
      trajectory_injective family input (congrArg Fin.val hab)
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      gcongr
      exact GenLimit.PatientScope.prefixCount_mono hAB n
  · apply Filter.isBoundedUnder_of_eventually_ge
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
    exact Filter.isCoboundedUnder_ge_of_le Filter.atTop hratio


noncomputable def firstInput (input : Stage3Case017.Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem firstInput_spec {input : Stage3Case017.Stream} {z : ℕ}
    (hz : z ∈ Set.range input) : input (firstInput input z) = z := by
  unfold firstInput
  rw [dif_pos hz]
  exact Nat.find_spec hz

theorem firstInput_min {input : Stage3Case017.Stream} {z q : ℕ}
    (hz : z ∈ Set.range input) (hq : input q = z) : firstInput input z ≤ q := by
  unfold firstInput
  rw [dif_pos hz]
  exact Nat.find_min' hz hq

theorem core_prefix_count_bound {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hinj : Function.Injective input)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    ∃ r, ∀ n,
      GenLimit.PatientScope.prefixCount
          (Stage3Case017.informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
            family j) n + r := by
  classical
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  refine ⟨2 * T + 1, ?_⟩
  intro n
  let I := Stage3Case017.informationCore family input
  let output := trajectory (generator family) input
  let P := GenLimit.PatientScope.prefixFinset I n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ family j) n
  let early := (Finset.range T).image input ∪ (Finset.range T).image output
  let A := P \ (early ∪ D)
  have hP : P ⊆ early ∪ D ∪ A := by
    intro x hx
    by_cases hxe : x ∈ early ∪ D
    · exact Finset.mem_union_left _ hxe
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxe⟩)
  have hPcard : P.card ≤ early.card + D.card + A.card := by
    calc
      P.card ≤ (early ∪ D ∪ A).card := Finset.card_le_card hP
      _ ≤ (early ∪ D).card + A.card := Finset.card_union_le _ _
      _ ≤ (early.card + D.card) + A.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hearly : early.card ≤ 2 * T := by
    calc
      early.card ≤ ((Finset.range T).image input).card +
          ((Finset.range T).image output).card := Finset.card_union_le _ _
      _ ≤ T + T := by
        apply Nat.add_le_add
        · simpa using (Finset.card_image_le : ((Finset.range T).image input).card ≤ (Finset.range T).card)
        · simpa using (Finset.card_image_le : ((Finset.range T).image output).card ≤ (Finset.range T).card)
      _ = 2 * T := by omega
  have hA_range : ∀ x ∈ A, x ∈ Set.range input := by
    intro x hxA
    have hxP := (Finset.mem_sdiff.mp hxA).1
    have hxI := (GenLimit.PatientScope.mem_prefixFinset.mp hxP).2
    by_contra hxrange
    have hxGF := core_diff_range_subset_generatorFirst family input hInf
      ⟨hxI, hxrange⟩
    have hxD : x ∈ D := GenLimit.PatientScope.mem_prefixFinset.mpr
      ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hxP).1,
        hxGF, core_subset_family hj hxI⟩
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_union_right _ hxD)
  have hA_time : ∀ x ∈ A, T ≤ firstInput input x := by
    intro x hxA
    by_contra hbad
    have hxrange := hA_range x hxA
    have hxearly : x ∈ early := Finset.mem_union_left _ <|
      Finset.mem_image.mpr ⟨firstInput input x, Finset.mem_range.mpr (Nat.lt_of_not_ge hbad),
        firstInput_spec hxrange⟩
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_union_left _ hxearly)
  have hA_no_output_before : ∀ x ∈ A, ∀ q, q < firstInput input x → output q ≠ x := by
    intro x hxA q hq hout
    have hxrange := hA_range x hxA
    have hxGF : x ∈ GenLimit.GeneratorFirst input output := by
      refine ⟨q, hout, ?_⟩
      intro s hs hin
      have hmin := firstInput_min hxrange hin
      omega
    have hxP := (Finset.mem_sdiff.mp hxA).1
    have hxD : x ∈ D := GenLimit.PatientScope.mem_prefixFinset.mpr
      ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hxP).1,
        hxGF, core_subset_family hj (GenLimit.PatientScope.mem_prefixFinset.mp hxP).2⟩
    exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_union_right _ hxD)
  let partner : ℕ → ℕ := fun x =>
    if output (firstInput input x) < n then output (firstInput input x) else n
  have hpartner_mem : ∀ x ∈ A, partner x ∈ insert n D := by
    intro x hxA
    dsimp only [partner]
    split <;> rename_i hout
    · apply Finset.mem_insert_of_mem
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨hout, ?_, ?_⟩
      · refine ⟨firstInput input x, rfl, ?_⟩
        intro s _ hs
        exact trajectory_not_input_le family input (show s ≤ firstInput input x by assumption) hs.symm
      · have ht := hA_time x hxA
        apply core_subset_family hj
        dsimp only [output]
        rw [trajectory.eq_1]
        change freshChoice (currentCore family
            (fun i : Fin (firstInput input x + 1) => input i))
          (fun i => input i)
          (fun i => trajectory (generator family) input i) ∈
            Stage3Case017.informationCore family input
        rw [← hT _ ht]
        apply freshChoice_mem
        simpa only [hT _ ht] using hInf
    · exact Finset.mem_insert_self _ _
  have hpartner_inj : Set.InjOn partner (↑A : Set ℕ) := by
    intro x hxA y hyA hxy
    have hxAf : x ∈ A := hxA
    have hyAf : y ∈ A := hyA
    have hxr := hA_range x hxAf
    have hyr := hA_range y hyAf
    let tx := firstInput input x
    let ty := firstInput input y
    by_cases hxgood : output tx < n
    · by_cases hygood : output ty < n
      · have hout : output tx = output ty := by simpa [partner, tx, ty, hxgood, hygood] using hxy
        have htt : tx = ty := trajectory_injective family input hout
        calc
          x = input tx := (firstInput_spec hxr).symm
          _ = input ty := by rw [htt]
          _ = y := firstInput_spec hyr
      · have : output tx = n := by simpa [partner, tx, ty, hxgood, hygood] using hxy
        omega
    · by_cases hygood : output ty < n
      · have : n = output ty := by simpa [partner, tx, ty, hxgood, hygood] using hxy
        omega
      · by_contra hne
        have htt : tx ≠ ty := by
          intro heq
          apply hne
          calc
            x = input tx := (firstInput_spec hxr).symm
            _ = input ty := congrArg input heq
            _ = y := firstInput_spec hyr
        rcases lt_or_gt_of_ne htt with hlt | hgt
        · have hylt : y < n := (GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_sdiff.mp hyAf).1).1
          have hle : output tx ≤ y := by
            dsimp only [output, tx]
            rw [trajectory.eq_1]
            apply freshChoice_le
            · simpa only [hT _ (hA_time x hxAf)] using hInf
            · simpa only [hT _ (hA_time x hxAf)] using
                (GenLimit.PatientScope.mem_prefixFinset.mp
                  (Finset.mem_sdiff.mp hyAf).1).2
            · intro q hq
              have hmin := firstInput_min hyr hq
              omega
            · intro q hq
              exact hA_no_output_before y hyAf q
                (by simpa [tx, ty] using lt_trans q.isLt hlt) hq
          exact hxgood (lt_of_le_of_lt hle hylt)
        · have hxlt : x < n := (GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_sdiff.mp hxAf).1).1
          have hle : output ty ≤ x := by
            dsimp only [output, ty]
            rw [trajectory.eq_1]
            apply freshChoice_le
            · simpa only [hT _ (hA_time y hyAf)] using hInf
            · simpa only [hT _ (hA_time y hyAf)] using
                (GenLimit.PatientScope.mem_prefixFinset.mp
                  (Finset.mem_sdiff.mp hxAf).1).2
            · intro q hq
              have hmin := firstInput_min hxr hq
              omega
            · intro q hq
              exact hA_no_output_before x hxAf q
                (by simpa [tx, ty] using lt_trans q.isLt hgt) hq
          exact hygood (lt_of_le_of_lt hle hxlt)
  have hAcard : A.card ≤ D.card + 1 := by
    have hle := Finset.card_le_card_of_injOn partner hpartner_mem hpartner_inj
    exact le_trans hle (Finset.card_insert_le n D)
  change P.card ≤ 2 * D.card + (2 * T + 1)
  omega

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  intro input hinj hexists hInf
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.generator family) input
  refine ⟨output, Stage3Case017Proof.trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨Stage3Case017Proof.novel_for_compatible family input hInf j hj, ?_⟩
  let I := Stage3Case017.informationCore family input
  let D := GenLimit.GeneratorFirst input output ∩ family j
  obtain ⟨r, hcount0⟩ :=
    Stage3Case017Proof.core_prefix_count_bound family input hinj hInf j hj
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity I (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity D (family j) := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (GenLimit.PatientScope.prefixCount I)
      (GenLimit.PatientScope.prefixCount D) r
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono
        (Stage3Case017Proof.core_subset_family hj) n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
    · intro n
      have hcount := hcount0 n
      change GenLimit.PatientScope.prefixCount I n ≤
        2 * GenLimit.PatientScope.prefixCount D n + r at hcount
      omega
  have hmissing :
      GenLimit.PatientScope.relativeLowerDensity
          (I \ Set.range input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity D (family j) := by
    apply Stage3Case017Proof.relativeLowerDensity_mono
    · intro z hz
      refine ⟨?_, Stage3Case017Proof.core_subset_family hj hz.1⟩
      exact Stage3Case017Proof.core_diff_range_subset_generatorFirst
        family input hInf hz
    · exact Set.inter_subset_right
  exact max_le hhalf hmissing

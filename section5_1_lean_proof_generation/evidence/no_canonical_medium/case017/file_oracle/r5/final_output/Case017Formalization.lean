import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def currentCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t input output =>
    if h : ∃ z, z ∈ currentCore family input ∧
        (∀ i, input i ≠ z) ∧ (∀ i, output i ≠ z) then
      Nat.find h
    else 0

def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]

private theorem eventually_candidate_correct {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) :
    ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
  classical
  by_cases h : GenLimit.Generic.StreamIn input (family j)
  · exact ⟨0, fun _ _ => ⟨fun _ => h, fun _ i => h ⟨i, rfl⟩⟩⟩
  · obtain ⟨_, ⟨s, rfl⟩, hs⟩ := Set.not_subset.mp h
    refine ⟨s, ?_⟩
    intro t ht
    constructor
    · intro hall
      exact False.elim (hs (hall ⟨s, Nat.lt_succ_of_le ht⟩))
    · intro hstream
      exact False.elim (hs (hstream ⟨s, rfl⟩))

private theorem currentCore_eventually_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  choose bound hbound using fun j => eventually_candidate_correct family input j
  let T := Finset.univ.sup bound
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    apply hz j
    exact (hbound j t (le_trans (Finset.le_sup (f := bound) (by simp : j ∈ Finset.univ)) ht)).2 hj
  · intro hz j hj
    apply hz j
    exact (hbound j t (le_trans (Finset.le_sup (f := bound) (by simp : j ∈ Finset.univ)) ht)).1 hj



private theorem greedyGenerator_spec {m t : ℕ}
    (family : Fin m → Language) (input : Fin (t + 1) → ℕ)
    (output : Fin t → ℕ) (hInfinite : (currentCore family input).Infinite) :
    let z := greedyGenerator family t input output
    z ∈ currentCore family input ∧
      (∀ i, input i ≠ z) ∧ (∀ i, output i ≠ z) ∧
      ∀ w, w ∈ currentCore family input →
        (∀ i, input i ≠ w) → (∀ i, output i ≠ w) → z ≤ w := by
  classical
  let used := Finset.univ.image input ∪ Finset.univ.image output
  obtain ⟨z, hzcore, hzused⟩ := hInfinite.exists_not_mem_finset used
  have hzinput : ∀ i, input i ≠ z := by
    intro i hi
    apply hzused
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hzoutput : ∀ i, output i ≠ z := by
    intro i hi
    apply hzused
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hex : ∃ z, z ∈ currentCore family input ∧
      (∀ i, input i ≠ z) ∧ (∀ i, output i ≠ z) :=
    ⟨z, hzcore, hzinput, hzoutput⟩
  dsimp only
  unfold greedyGenerator
  split
  next h =>
    have hspec := Nat.find_spec h
    refine ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩
    intro w hw hwi hwo
    exact Nat.find_min' h ⟨hw, hwi, hwo⟩
  next h => exact False.elim (h hex)

private theorem run_eventual_greedy {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hInfinite : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      run (greedyGenerator family) input t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ run (greedyGenerator family) input t) ∧
      (∀ s, s < t → run (greedyGenerator family) input s ≠
        run (greedyGenerator family) input t) ∧
      ∀ w, w ∈ informationCore family input →
        (∀ s, s ≤ t → input s ≠ w) →
        (∀ s, s < t → run (greedyGenerator family) input s ≠ w) →
          run (greedyGenerator family) input t ≤ w := by
  obtain ⟨T, hT⟩ := currentCore_eventually_eq_informationCore family input
  refine ⟨T, ?_⟩
  intro t ht
  have hEq := hT t ht
  have hspec := greedyGenerator_spec family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (greedyGenerator family) input i)
    (hEq ▸ hInfinite)
  rw [run]
  rw [hEq] at hspec
  dsimp only at hspec
  refine ⟨hspec.1, ?_, ?_, ?_⟩
  · intro s hs
    exact hspec.2.1 ⟨s, Nat.lt_succ_iff.mpr hs⟩
  · intro s hs
    exact hspec.2.2.1 ⟨s, hs⟩
  · intro w hw hwi hwo
    apply hspec.2.2.2 w hw
    · intro i
      exact hwi i (Nat.le_of_lt_succ i.isLt)
    · intro i
      exact hwo i i.isLt

private theorem run_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hInfinite : (informationCore family input).Infinite) :
    GenLimit.NovelGeneratesInLimit input
      (run (greedyGenerator family) input) (informationCore family input) := by
  obtain ⟨T, hT⟩ := run_eventual_greedy family input hInfinite
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel, _⟩ := hT t ht
  refine ⟨hmem, ?_, hnovel⟩
  intro hsamp
  rw [GenLimit.mem_sample_iff] at hsamp
  obtain ⟨s, hs, heq⟩ := hsamp
  exact hfresh s (Nat.le_of_lt_succ hs) heq



noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

private theorem firstInputTime_spec (input : Stream) {z : ℕ}
    (hz : z ∈ Set.range input) : input (firstInputTime input z) = z := by
  classical
  simp only [firstInputTime, dif_pos hz]
  exact Nat.find_spec hz

private theorem firstInputTime_injective (input : Stream)
    (hinj : Function.Injective input) :
    Set.InjOn (firstInputTime input) (Set.range input) := by
  intro x hx y hy hxy
  have hx' := firstInputTime_spec input hx
  have hy' := firstInputTime_spec input hy
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

private theorem adversaryFirst_no_output_before_first (input output : Stream)
    (hinj : Function.Injective input) {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) :
    ∀ s, s < firstInputTime input z → output s ≠ z := by
  obtain ⟨t, ht, hno⟩ := hz
  have hrange : z ∈ Set.range input := ⟨t, ht⟩
  have hfirst := firstInputTime_spec input hrange
  have heq : firstInputTime input z = t := hinj (hfirst.trans ht.symm)
  simpa [heq] using hno

private theorem core_covered_by_ranges {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hInfinite : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run (greedyGenerator family) input) := by
  classical
  obtain ⟨T, hT⟩ := run_eventual_greedy family input hInfinite
  intro z hz
  by_contra hnot
  have hzInput : ∀ s, input s ≠ z := by
    intro s hs
    apply hnot
    exact Set.mem_union_left _ ⟨s, hs⟩
  have hzOutput : ∀ s, run (greedyGenerator family) input s ≠ z := by
    intro s hs
    apply hnot
    exact Set.mem_union_right _ ⟨s, hs⟩
  have hbound : ∀ q : Fin (z + 2),
      run (greedyGenerator family) input (T + q) < z + 1 := by
    intro q
    apply Nat.lt_succ_iff.mpr
    exact (hT (T + q) (Nat.le_add_right T q)).2.2.2 z hz
      (fun s _ => hzInput s) (fun s _ => hzOutput s)
  let f : Fin (z + 2) → Fin (z + 1) := fun q =>
    ⟨run (greedyGenerator family) input (T + q), hbound q⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    have htime : T + a ≠ T + b := by omega
    rcases lt_or_gt_of_ne htime with hlt | hgt
    · exact (hT (T + b) (by omega)).2.2.1 (T + a) hlt (Fin.ext_iff.mp hab)
    · exact (hT (T + a) (by omega)).2.2.1 (T + b) hgt (Fin.ext_iff.mp hab).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard

private theorem core_partition {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hInfinite : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (run (greedyGenerator family) input) ∪
        GenLimit.GeneratorFirst input (run (greedyGenerator family) input) := by
  intro z hz
  rcases core_covered_by_ranges family input hInfinite hz with hin | hout
  · exact GenLimit.range_subset_first_announcements input
      (run (greedyGenerator family) input) hin
  · obtain ⟨t, ht⟩ := hout
    by_cases hearlier : ∃ s, s ≤ t ∧ input s = z
    · obtain ⟨s, hst, hs⟩ := hearlier
      exact GenLimit.range_subset_first_announcements input
        (run (greedyGenerator family) input) ⟨s, hs⟩
    · apply Set.mem_union_right
      exact ⟨t, ht, fun s hs hsz => hearlier ⟨s, hs, hsz⟩⟩


private theorem attacker_prefix_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hInfinite : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (GenLimit.AdversaryFirst input (run (greedyGenerator family) input) ∩
          informationCore family input) n ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (greedyGenerator family) input) ∩
          informationCore family input) n +
        (Classical.choose (run_eventual_greedy family input hInfinite)) + 1 := by
  classical
  let output := run (greedyGenerator family) input
  let core := informationCore family input
  let T := Classical.choose (run_eventual_greedy family input hInfinite)
  have hT := Classical.choose_spec (run_eventual_greedy family input hInfinite)
  let attackers := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ core) n
  let defenders := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ core) n
  let early := attackers.filter (fun z => firstInputTime input z < T)
  let late := attackers.filter (fun z => ¬ firstInputTime input z < T)
  have hsplit : early.card + late.card = attackers.card := by
    simpa [early, late] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := attackers) (fun z => firstInputTime input z < T))
  have hearly : early.card ≤ T := by
    rw [← Finset.card_range T]
    apply Finset.card_le_card_of_injOn (firstInputTime input)
    · intro z hz
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
    · intro x hx y hy hxy
      apply firstInputTime_injective input hinj
      · obtain ⟨_, hxA, _⟩ := GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hx).1
        obtain ⟨t, ht, _⟩ := hxA
        exact ⟨t, ht⟩
      · obtain ⟨_, hyA, _⟩ := GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hy).1
        obtain ⟨t, ht, _⟩ := hyA
        exact ⟨t, ht⟩
      · exact hxy
  have hlate : late.card ≤ defenders.card + 1 := by
    by_cases hempty : late.Nonempty
    · obtain ⟨last, hlast, hmax⟩ := Finset.exists_max_image late
          (firstInputTime input) hempty
      have herase : (late.erase last).card + 1 = late.card :=
        Finset.card_erase_add_one hlast
      have hmap : (late.erase last).card ≤ defenders.card := by
        apply Finset.card_le_card_of_injOn
          (fun z => output (firstInputTime input z))
        · intro z hz
          have hzlate : z ∈ late := (Finset.mem_erase.mp hz).2
          have hzneq : z ≠ last := (Finset.mem_erase.mp hz).1
          have hztime_le := hmax z hzlate
          have hzrange : z ∈ Set.range input := by
            obtain ⟨_, hzA, _⟩ := GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp hzlate).1
            obtain ⟨t, ht, _⟩ := hzA
            exact ⟨t, ht⟩
          have hlastrange : last ∈ Set.range input := by
            obtain ⟨_, hlastA, _⟩ := GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp hlast).1
            obtain ⟨t, ht, _⟩ := hlastA
            exact ⟨t, ht⟩
          have hztime_ne : firstInputTime input z ≠ firstInputTime input last := by
            intro heq
            exact hzneq (firstInputTime_injective input hinj hzrange hlastrange heq)
          have hztime_lt : firstInputTime input z < firstInputTime input last :=
            lt_of_le_of_ne hztime_le hztime_ne
          have hzT : T ≤ firstInputTime input z := by
            exact Nat.le_of_not_gt (Finset.mem_filter.mp hzlate).2
          have hlastData := GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp hlast).1
          have hlastCore : last ∈ core := hlastData.2.2
          have hlastN : last < n := hlastData.1
          have hlastInput : ∀ s, s ≤ firstInputTime input z → input s ≠ last := by
            intro s hs hslast
            have hspec := firstInputTime_spec input hlastrange
            have : s = firstInputTime input last := hinj (hslast.trans hspec.symm)
            omega
          have hlastOutput : ∀ s, s < firstInputTime input z → output s ≠ last := by
            intro s hs
            apply adversaryFirst_no_output_before_first input output hinj hlastData.2.1
            omega
          have hgreedy := hT (firstInputTime input z) hzT
          have hout_lt : output (firstInputTime input z) < n :=
            lt_of_le_of_lt (hgreedy.2.2.2 last hlastCore hlastInput hlastOutput) hlastN
          apply GenLimit.PatientScope.mem_prefixFinset.mpr
          refine ⟨hout_lt, ?_, hgreedy.1⟩
          exact ⟨firstInputTime input z, rfl, hgreedy.2.1⟩
        · intro x hx y hy hxy
          have hxlate := (Finset.mem_erase.mp hx).2
          have hylate := (Finset.mem_erase.mp hy).2
          have hxT : T ≤ firstInputTime input x :=
            Nat.le_of_not_gt (Finset.mem_filter.mp hxlate).2
          have hyT : T ≤ firstInputTime input y :=
            Nat.le_of_not_gt (Finset.mem_filter.mp hylate).2
          have htx : firstInputTime input x = firstInputTime input y := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact (hT (firstInputTime input y) hyT).2.2.1
                (firstInputTime input x) hlt hxy
            · exact (hT (firstInputTime input x) hxT).2.2.1
                (firstInputTime input y) hgt hxy.symm
          have hxrange : x ∈ Set.range input := by
            obtain ⟨_, hxA, _⟩ := GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp hxlate).1
            obtain ⟨t, ht, _⟩ := hxA
            exact ⟨t, ht⟩
          have hyrange : y ∈ Set.range input := by
            obtain ⟨_, hyA, _⟩ := GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp hylate).1
            obtain ⟨t, ht, _⟩ := hyA
            exact ⟨t, ht⟩
          exact firstInputTime_injective input hinj hxrange hyrange htx
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hempty
      simp [hempty]
  change attackers.card ≤ defenders.card + T + 1
  omega


private theorem core_prefix_le_ownership {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hInfinite : (informationCore family input).Infinite)
    (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.AdversaryFirst input (run (greedyGenerator family) input) ∩
          informationCore family input) n +
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (greedyGenerator family) input) ∩
          informationCore family input) n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  let coreFin := GenLimit.PatientScope.prefixFinset
    (informationCore family input) n
  let attackerFin := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input (run (greedyGenerator family) input) ∩
      informationCore family input) n
  let defenderFin := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (run (greedyGenerator family) input) ∩
      informationCore family input) n
  calc
    coreFin.card ≤ (attackerFin ∪ defenderFin).card := by
      apply Finset.card_le_card
      intro z hz
      have hzData := GenLimit.PatientScope.mem_prefixFinset.mp hz
      rcases core_partition family input hInfinite hzData.2 with hzA | hzD
      · exact Finset.mem_union_left _ <|
          GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hzData.1, hzA, hzData.2⟩
      · exact Finset.mem_union_right _ <|
          GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hzData.1, hzD, hzData.2⟩
    _ ≤ attackerFin.card + defenderFin.card := Finset.card_union_le _ _

private theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hInfinite : (informationCore family input).Infinite) (j : Fin m)
    (hstream : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (greedyGenerator family) input) ∩
          family j) (family j) := by
  let core := informationCore family input
  let output := run (greedyGenerator family) input
  let T := Classical.choose (run_eventual_greedy family input hInfinite)
  have hcoreK : core ⊆ family j := fun z hz => hz j hstream
  apply GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount (family j) n)
    (fun n => GenLimit.PatientScope.prefixCount core n)
    (fun n => GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input output ∩ family j) n)
    (T + 1)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (by
      exact Set.Infinite.mono hcoreK hInfinite)
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono hcoreK n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hcover := core_prefix_le_ownership family input hInfinite n
    have hattacker := attacker_prefix_le family input hinj hInfinite n
    have hdefmono :
        GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ core) n ≤
        GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ family j) n := by
      apply GenLimit.PatientScope.prefixCount_mono
      intro z hz
      exact ⟨hz.1, hcoreK hz.2⟩
    dsimp only [core, output, T] at hcover hattacker hdefmono ⊢
    omega

private theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · apply Filter.Eventually.of_forall
    intro n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
    · positivity
  · apply Filter.isBoundedUnder_of
    refine ⟨0, ?_⟩
    intro n
    positivity
  · apply Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) Filter.atTop
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hnum : GenLimit.PatientScope.prefixCount B n = 0 := by
        have hle := GenLimit.PatientScope.prefixCount_mono hBK n
        omega
      simp [hzero, hnum]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

private theorem missing_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hInfinite : (informationCore family input).Infinite)
    (j : Fin m) (hstream : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (greedyGenerator family) input) ∩
          family j) (family j) := by
  apply relativeLowerDensity_mono_left
  · intro z hz
    have hcover := core_partition family input hInfinite hz.1
    have hzGen : z ∈ GenLimit.GeneratorFirst input
        (run (greedyGenerator family) input) := by
      rcases hcover with hzAdv | hzGen
      · obtain ⟨t, ht, _⟩ := hzAdv
        exact False.elim (hz.2 ⟨t, ht⟩)
      · exact hzGen
    exact ⟨hzGen, hz.1 j hstream⟩
  · exact Set.inter_subset_right

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.greedyGenerator family, ?_⟩
  intro input hinj hpresentation hInfinite
  let output := Stage3Case017Proof.run
    (Stage3Case017Proof.greedyGenerator family) input
  refine ⟨output, Stage3Case017Proof.run_follows _ _, ?_⟩
  intro j hstream
  constructor
  · obtain ⟨T, hT⟩ := Stage3Case017Proof.run_novel family input hInfinite
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
    exact ⟨hcore j hstream, hfresh, hnovel⟩
  · apply max_le
    · exact Stage3Case017Proof.half_core_density
        family input hinj hInfinite j hstream
    · exact Stage3Case017Proof.missing_core_density
        family input hInfinite j hstream

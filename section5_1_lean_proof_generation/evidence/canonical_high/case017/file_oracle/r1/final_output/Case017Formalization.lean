import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017

noncomputable def currentCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def caseGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : (currentCore family xs).Infinite then
      Nat.find (h.exists_notMem_finset
        (Finset.univ.image xs ∪ Finset.univ.image ys))
    else
      Nat.find (Set.infinite_univ.exists_notMem_finset
        (Finset.univ.image xs ∪ Finset.univ.image ys))

private theorem caseGenerator_fresh {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    caseGenerator family t xs ys ∉ Finset.univ.image xs ∪ Finset.univ.image ys := by
  classical
  rw [caseGenerator]
  split_ifs with h
  · exact (Nat.find_spec (h.exists_notMem_finset
      (Finset.univ.image xs ∪ Finset.univ.image ys))).2
  · exact (Nat.find_spec (Set.infinite_univ.exists_notMem_finset
      (Finset.univ.image xs ∪ Finset.univ.image ys))).2

private theorem caseGenerator_mem {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) :
    caseGenerator family t xs ys ∈ currentCore family xs := by
  classical
  rw [caseGenerator, dif_pos h]
  exact (Nat.find_spec (h.exists_notMem_finset
    (Finset.univ.image xs ∪ Finset.univ.image ys))).1

private theorem caseGenerator_le {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) {z : ℕ}
    (hzcore : z ∈ currentCore family xs)
    (hzfresh : z ∉ Finset.univ.image xs ∪ Finset.univ.image ys) :
    caseGenerator family t xs ys ≤ z := by
  classical
  rw [caseGenerator, dif_pos h]
  exact Nat.find_min' _ ⟨hzcore, hzfresh⟩

noncomputable def run (gen : OnlineGenerator) (input : Stream) : Stream :=
  Nat.lt_wfRel.wf.fix fun t previous =>
    gen t (fun i => input i) (fun i => previous i i.isLt)

private theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run, WellFounded.fix_eq]

private theorem streamIn_iff_prefixes
    (input : Stream) (L : Language) :
    GenLimit.Generic.StreamIn input L ↔ ∀ i, input i ∈ L := by
  constructor
  · intro h i
    exact h ⟨i, rfl⟩
  · rintro h z ⟨i, rfl⟩
    exact h i

private theorem eventually_currentCore_eq {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases h : GenLimit.Generic.StreamIn input (family j)
    · exact ⟨0, fun t ht => ⟨fun _ => h, fun _ i => h ⟨i, rfl⟩⟩⟩
    · have hex : ∃ n, input n ∉ family j := by
        rw [streamIn_iff_prefixes] at h
        push_neg at h
        exact h
      obtain ⟨n, hn⟩ := hex
      refine ⟨n, fun t ht => ⟨?_, fun hs => (h hs).elim⟩⟩
      intro hp
      exact (hn (hp ⟨n, Nat.lt_succ_of_le ht⟩)).elim
  choose bound hbound using hj
  let T := Finset.univ.sup bound
  refine ⟨T, fun t ht => ?_⟩
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hjstream
    apply hz j
    exact (hbound j t (le_trans (Finset.le_sup (s := Finset.univ)
      (by simp : j ∈ (Finset.univ : Finset (Fin m)))) ht)).2 hjstream
  · intro hz j hjprefix
    apply hz j
    exact (hbound j t (le_trans (Finset.le_sup (s := Finset.univ)
      (by simp : j ∈ (Finset.univ : Finset (Fin m)))) ht)).1 hjprefix


private theorem run_fresh {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    run (caseGenerator family) input t ∉ GenLimit.sample input (t + 1) ∧
      ∀ s, s < t →
        run (caseGenerator family) input s ≠
          run (caseGenerator family) input t := by
  classical
  have h := caseGenerator_fresh family t
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (caseGenerator family) input i)
  rw [← run_follows (caseGenerator family) input t] at h
  constructor
  · rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    apply h
    apply Finset.mem_union_left
    rw [Finset.mem_image]
    exact ⟨⟨s, hs⟩, by simp, heq⟩
  · intro s hs heq
    apply h
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    exact ⟨⟨s, hs⟩, by simp, heq⟩

private theorem run_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (run (caseGenerator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (run_fresh family input t).2 s hlt hst
  · exact (run_fresh family input s).2 t hgt hst.symm

private theorem run_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (run (caseGenerator family) input) ⊆
      GenLimit.GeneratorFirst input (run (caseGenerator family) input) := by
  rintro z ⟨t, rfl⟩
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  exact (run_fresh family input t).1
    (GenLimit.mem_sample_iff.mpr ⟨s, Nat.lt_succ_iff.mpr hs, heq⟩)

private theorem informationCore_subset {m : ℕ}
    {family : Fin m → Language} {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

private theorem eventual_run_mem_core {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      run (caseGenerator family) input t ∈ informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  refine ⟨T, fun t ht => ?_⟩
  rw [run_follows]
  have hm := caseGenerator_mem family t
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (caseGenerator family) input i)
    (by rw [hT t ht]; exact hcore)
  rw [hT t ht] at hm
  exact hm

private noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

private theorem input_inputTime {input : Stream} {z : ℕ}
    (hz : z ∈ Set.range input) : input (inputTime input z) = z := by
  rw [inputTime, dif_pos hz]
  exact Nat.find_spec hz

private theorem inputTime_injective (input : Stream) (hinj : Function.Injective input) :
    Set.InjOn (inputTime input) (Set.range input) := by
  intro x hx y hy hxy
  rw [← input_inputTime hx, ← input_inputTime hy, hxy]

private theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run (caseGenerator family) input) := by
  classical
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  intro z hz
  by_cases hin : z ∈ Set.range input
  · exact Or.inl hin
  by_cases hout : z ∈ Set.range (run (caseGenerator family) input)
  · exact Or.inr hout
  exfalso
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨run (caseGenerator family) input (T + i), by
      rw [Nat.lt_succ_iff]
      rw [run_follows]
      apply caseGenerator_le family
        (h := by simpa [hT (T + i) (Nat.le_add_right T i)] using hcore)
        (hzcore := by simpa [hT (T + i) (Nat.le_add_right T i)] using hz)
      intro hmem
      rcases Finset.mem_union.mp hmem with hxs | hys
      · rw [Finset.mem_image] at hxs
        obtain ⟨k, -, hk⟩ := hxs
        exact hin ⟨k, hk⟩
      · rw [Finset.mem_image] at hys
        obtain ⟨k, -, hk⟩ := hys
        exact hout ⟨k, hk⟩⟩
  have hf : Function.Injective f := by
    intro i k hik
    apply Fin.ext
    apply Nat.add_left_cancel
    apply run_injective family input
    exact congrArg Fin.val hik
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard


private theorem core_counting {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    ∃ r, ∀ n,
      GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (Set.range (run (caseGenerator family) input) ∩
            informationCore family input) n + r := by
  classical
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  refine ⟨T + 1, fun n => ?_⟩
  let core := informationCore family input
  let output := run (caseGenerator family) input
  let P := GenLimit.PatientScope.prefixFinset core n
  let O := P.filter fun z => z ∈ Set.range output
  let A := P.filter fun z => z ∉ Set.range output
  let early := A.filter fun z => inputTime input z < T
  let late := A.filter fun z => T ≤ inputTime input z
  have hA_input : ∀ z ∈ A, z ∈ Set.range input := by
    intro z hz
    have hzP : z ∈ P := (Finset.mem_filter.mp hz).1
    have hzcore : z ∈ informationCore family input :=
      (GenLimit.PatientScope.mem_prefixFinset.mp hzP).2
    rcases core_covered family input hcore hzcore with hzin | hzout
    · exact hzin
    · exact ((Finset.mem_filter.mp hz).2 hzout).elim
  have hearly : early.card ≤ T := by
    have hmap : Set.MapsTo (inputTime input) (↑early : Set ℕ)
        (↑(Finset.range T) : Set ℕ) := by
      intro z hz
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
    have hinjTime : Set.InjOn (inputTime input) (↑early : Set ℕ) := by
      intro x hx y hy hxy
      exact inputTime_injective input hinj
        (hA_input x (Finset.mem_filter.mp hx).1)
        (hA_input y (Finset.mem_filter.mp hy).1) hxy
    simpa using Finset.card_le_card_of_injOn (inputTime input) hmap hinjTime
  have hlate : late.card ≤ O.card + 1 := by
    by_cases hempty : late.Nonempty
    · obtain ⟨last, hlast, hmax⟩ := Finset.exists_max_image late
        (inputTime input) hempty
      have herase : (late.erase last).card ≤ O.card := by
        let f : ℕ → ℕ := fun z => output (inputTime input z)
        apply Finset.card_le_card_of_injOn f
        · intro z hz
          have hzlate : z ∈ late := Finset.mem_of_mem_erase hz
          have hzA : z ∈ A := (Finset.mem_filter.mp hzlate).1
          have hzP : z ∈ P := (Finset.mem_filter.mp hzA).1
          have hzT : T ≤ inputTime input z := (Finset.mem_filter.mp hzlate).2
          have hlastA : last ∈ A := (Finset.mem_filter.mp hlast).1
          have hlastP : last ∈ P := (Finset.mem_filter.mp hlastA).1
          have hlastcore : last ∈ informationCore family input :=
            (GenLimit.PatientScope.mem_prefixFinset.mp hlastP).2
          have hneq : z ≠ last := (Finset.mem_erase.mp hz).1
          have htimes_ne : inputTime input z ≠ inputTime input last := by
            intro heq
            exact hneq (inputTime_injective input hinj
              (hA_input z hzA) (hA_input last hlastA) heq)
          have htime_lt : inputTime input z < inputTime input last :=
            lt_of_le_of_ne (hmax z hzlate) htimes_ne
          have hlast_fresh : last ∉
              Finset.univ.image
                  (fun i : Fin (inputTime input z + 1) => input i) ∪
                Finset.univ.image
                  (fun i : Fin (inputTime input z) => output i) := by
            intro hmem
            rcases Finset.mem_union.mp hmem with hxin | hxout
            · rw [Finset.mem_image] at hxin
              obtain ⟨i, -, hi⟩ := hxin
              have hmin : inputTime input last ≤ i := by
                rw [inputTime, dif_pos (hA_input last hlastA)]
                exact Nat.find_min' _ hi
              exact (Nat.not_le_of_gt htime_lt)
                (le_trans hmin (Nat.le_of_lt_succ i.isLt))
            · rw [Finset.mem_image] at hxout
              obtain ⟨i, -, hi⟩ := hxout
              exact (Finset.mem_filter.mp hlastA).2 ⟨i, hi⟩
          have hle : output (inputTime input z) ≤ last := by
            change run (caseGenerator family) input (inputTime input z) ≤ last
            rw [run_follows]
            apply caseGenerator_le family
              (h := by rw [hT _ hzT]; exact hcore)
              (hzcore := by rw [hT _ hzT]; exact hlastcore)
              (hzfresh := hlast_fresh)
          apply Finset.mem_filter.mpr
          refine ⟨?_, ⟨inputTime input z, rfl⟩⟩
          apply GenLimit.PatientScope.mem_prefixFinset.mpr
          refine ⟨?_, ?_⟩
          · exact lt_of_le_of_lt hle
              (GenLimit.PatientScope.mem_prefixFinset.mp hlastP).1
          · change run (caseGenerator family) input (inputTime input z) ∈
              informationCore family input
            rw [run_follows]
            have hm := caseGenerator_mem family (inputTime input z)
              (fun i : Fin (inputTime input z + 1) => input i)
              (fun i : Fin (inputTime input z) => output i)
              (by rw [hT _ hzT]; exact hcore)
            rw [hT _ hzT] at hm
            exact hm
        · intro x hx y hy hxy
          have htx : x ∈ late := Finset.mem_of_mem_erase hx
          have hty : y ∈ late := Finset.mem_of_mem_erase hy
          apply inputTime_injective input hinj
            (hA_input x (Finset.mem_filter.mp htx).1)
            (hA_input y (Finset.mem_filter.mp hty).1)
          apply run_injective family input
          exact hxy
      have hcard := Finset.card_erase_add_one hlast
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hempty
      simp [hempty]
  have hpartitionP : O.card + A.card = P.card := by
    simpa [O, A] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := P) (fun z => z ∈ Set.range output))
  have hpartitionA : early.card + late.card = A.card := by
    simpa [early, late, Nat.not_lt] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := A) (fun z => inputTime input z < T))
  have hOcount : O.card = GenLimit.PatientScope.prefixCount
      (Set.range output ∩ core) n := by
    unfold O P GenLimit.PatientScope.prefixCount
    congr 1
    ext z
    simp [core, and_assoc, and_left_comm, and_comm]
  change P.card ≤ 2 * GenLimit.PatientScope.prefixCount
    (Set.range output ∩ core) n + (T + 1)
  rw [← hOcount]
  omega


private theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hzero := GenLimit.PatientScope.prefixCount_mono hBK n
      have hB : GenLimit.PatientScope.prefixCount B n = 0 := by omega
      simp [hn, hB]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

end Stage3Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  classical
  intro m hm family hfamily
  refine ⟨Stage3Case017.caseGenerator family, ?_⟩
  intro input hinj hpresentation hcore
  let output := Stage3Case017.run (Stage3Case017.caseGenerator family) input
  refine ⟨output, Stage3Case017.run_follows _ _, ?_⟩
  intro j hj
  have hcoreK : Stage3Case017.informationCore family input ⊆ family j :=
    Stage3Case017.informationCore_subset hj
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    obtain ⟨T, hT⟩ := Stage3Case017.eventual_run_mem_core family input hcore
    refine ⟨T, fun t ht => ⟨hcoreK (hT t ht), ?_, ?_⟩⟩
    · exact (Stage3Case017.run_fresh family input t).1
    · exact (Stage3Case017.run_fresh family input t).2
  refine ⟨hnovel, ?_⟩
  have hKinf : (family j).Infinite := hfamily j
  have hgenSubset : Set.range output ⊆ GenLimit.GeneratorFirst input output := by
    exact Stage3Case017.run_generatorFirst family input
  have hmissingSubset :
      Stage3Case017.informationCore family input \ Set.range input ⊆
        GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    have hzcover := Stage3Case017.core_covered family input hcore hz.1
    rcases hzcover with hzin | hzout
    · exact (hz.2 hzin).elim
    · exact ⟨hgenSubset hzout, hcoreK hz.1⟩
  have hmissing :
      GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input \ Set.range input)
          (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply Stage3Case017.relativeLowerDensity_mono hmissingSubset
    exact Set.inter_subset_right
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    obtain ⟨r, hcount⟩ := Stage3Case017.core_counting family input hinj hcore
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (GenLimit.PatientScope.prefixCount
        (Stage3Case017.informationCore family input))
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j)) r
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop hKinf
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono hcoreK n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
    · intro n
      have hrange : Set.range output ∩
          Stage3Case017.informationCore family input ⊆
          GenLimit.GeneratorFirst input output ∩ family j := by
        intro z hz
        exact ⟨hgenSubset hz.1, hcoreK hz.2⟩
      have hD := GenLimit.PatientScope.prefixCount_mono hrange n
      have hc : GenLimit.PatientScope.prefixCount
          (Stage3Case017.informationCore family input) n ≤
          2 * GenLimit.PatientScope.prefixCount
            (Set.range output ∩ Stage3Case017.informationCore family input) n + r := by
        simpa [output] using hcount n
      omega
  exact max_le hhalf hmissing

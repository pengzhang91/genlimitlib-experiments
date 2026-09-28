import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable def currentCore {m : ℕ} (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) : Stage3Case017.Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

noncomputable def available {m : ℕ} (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : Set ℕ :=
  currentCore family input \ (Set.range input ∪ Set.range output)

noncomputable def generator {m : ℕ} (family : Fin m → Stage3Case017.Language) : Stage3Case017.OnlineGenerator := by
  classical
  exact fun _ input output =>
    if h : (available family input output).Nonempty then Nat.find h else 0

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator) (input : Stage3Case017.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

@[simp] theorem trajectory_eq (gen : Stage3Case017.OnlineGenerator) (input : Stage3Case017.Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory]

 theorem follows_trajectory (gen : Stage3Case017.OnlineGenerator) (input : Stage3Case017.Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

 theorem currentCore_eq_informationCore {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (T : ℕ)
    (hstable : ∀ j, (∀ i : Fin (T + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j)) :
    currentCore family (fun i : Fin (T + 1) => input i) =
      Stage3Case017.informationCore family input := by
  ext z
  simp only [currentCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((hstable j).2 hj)
  · intro hz j hj
    exact hz j ((hstable j).1 hj)

 theorem finite_family_stabilizes {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases h : GenLimit.Generic.StreamIn input (family j)
    · exact ⟨0, fun _ _ => ⟨fun _ => h, fun _ i => h ⟨i, rfl⟩⟩⟩
    · obtain ⟨_, ⟨s, rfl⟩, hs⟩ := Set.not_subset.mp h
      refine ⟨s, ?_⟩
      intro t ht
      constructor
      · intro hall
        exact False.elim (hs (hall ⟨s, Nat.lt_succ_of_le ht⟩))
      · intro hfull
        exact False.elim (hs (hfull ⟨s, rfl⟩))
  choose bound hbound using hj
  refine ⟨Finset.univ.sup bound, ?_⟩
  intro t ht j
  apply hbound j t
  exact le_trans (Finset.le_sup (s := Finset.univ) (f := bound) (Finset.mem_univ j)) ht

 theorem infinite_diff_finite_nonempty {S : Set ℕ} (hS : S.Infinite)
    (F : Set ℕ) (hF : F.Finite) : (S \ F).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h
  exact hS (hF.subset h)

 theorem generator_spec_of_available {m : ℕ} (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (h : (available family input output).Nonempty) :
    generator family t input output ∈ available family input output := by
  classical
  rw [generator, dif_pos h]
  exact Nat.find_spec h

 theorem generator_le_of_available {m : ℕ}
    (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (h : (available family input output).Nonempty)
    {z : ℕ} (hz : z ∈ available family input output) :
    generator family t input output ≤ z := by
  classical
  rw [generator, dif_pos h]
  exact Nat.find_min' h hz


 theorem eventual_rule {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (hInf : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      let output := trajectory (generator family) input
      let fresh := Stage3Case017.informationCore family input \
        (Set.range (fun i : Fin (t + 1) => input i) ∪
          Set.range (fun i : Fin t => output i))
      output t ∈ fresh ∧ ∀ z, z ∈ fresh → output t ≤ z := by
  classical
  obtain ⟨T, hT⟩ := finite_family_stabilizes family input
  refine ⟨T, ?_⟩
  intro t ht
  dsimp only
  have hcore : currentCore family (fun i : Fin (t + 1) => input i) =
      Stage3Case017.informationCore family input :=
    currentCore_eq_informationCore family input t (hT t ht)
  have hfinite :
      (Set.range (fun i : Fin (t + 1) => input i) ∪
        Set.range (fun i : Fin t => trajectory (generator family) input i)).Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  have havail :
      (available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (generator family) input i)).Nonempty := by
    rw [available, hcore]
    exact infinite_diff_finite_nonempty hInf _ hfinite
  rw [trajectory_eq]
  have hs := generator_spec_of_available family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (generator family) input i) havail
  rw [available, hcore] at hs
  refine ⟨hs, ?_⟩
  intro z hz
  exact generator_le_of_available family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (generator family) input i) havail (by
      rw [available, hcore]
      exact hz)

 theorem eventual_novel {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (hInf : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory (generator family) input)
      (family j) := by
  obtain ⟨T, hT⟩ := eventual_rule family input hInf
  refine ⟨T, ?_⟩
  intro t ht
  have h := (hT t ht).1
  refine ⟨?_, ?_, ?_⟩
  · exact h.1 j hj
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    exact h.2 (Or.inl ⟨⟨s, hst⟩, hs⟩)
  · intro s hst heq
    exact h.2 (Or.inr ⟨⟨s, hst⟩, heq⟩)

 theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  classical
  intro z hz
  let output := trajectory (generator family) input
  obtain ⟨T, hT⟩ := eventual_rule family input hInf
  by_contra hnot
  have hnever : ∀ t, output t ≠ z := by
    intro t hout
    apply hnot
    refine ⟨t, hout, ?_⟩
    intro q hqt hin
    exact hz.2 ⟨q, hin⟩
  have hbound : ∀ k, output (T + k) ≤ z := by
    intro k
    apply (hT (T + k) (Nat.le_add_right T k)).2 z
    refine ⟨hz.1, ?_⟩
    intro hu
    rcases hu with hu | hu
    · obtain ⟨i, hi⟩ := hu
      exact hz.2 ⟨i, hi⟩
    · obtain ⟨i, hi⟩ := hu
      exact hnever i hi
  have hinj : Function.Injective (fun k => output (T + k)) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab' | hba'
    · have hfresh := (hT (T + b) (Nat.le_add_right T b)).1.2
      exact hfresh (Or.inr ⟨⟨T + a, Nat.add_lt_add_left hab' T⟩, hab⟩)
    · have hfresh := (hT (T + a) (Nat.le_add_right T a)).1.2
      exact hfresh (Or.inr ⟨⟨T + b, Nat.add_lt_add_left hba' T⟩, hab.symm⟩)
  have hrangeInf : (Set.range (fun k => output (T + k))).Infinite :=
    Set.infinite_range_of_injective hinj
  have hrangeSub : Set.range (fun k => output (T + k)) ⊆ Set.Iic z := by
    rintro _ ⟨k, rfl⟩
    exact hbound k
  exact hrangeInf (Set.finite_Iic z |>.subset hrangeSub)


noncomputable def inputTime (input : Stage3Case017.Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range input then Nat.find h else 0

 theorem input_inputTime {input : Stage3Case017.Stream} {x : ℕ}
    (hx : x ∈ Set.range input) : input (inputTime input x) = x := by
  classical
  rw [inputTime, dif_pos hx]
  exact Nat.find_spec hx

 theorem inputTime_injective {input : Stage3Case017.Stream}
    (hinj : Function.Injective input) {x y : ℕ}
    (hx : x ∈ Set.range input) (hy : y ∈ Set.range input)
    (hxy : inputTime input x = inputTime input y) : x = y := by
  rw [← input_inputTime hx, ← input_inputTime hy, hxy]

 theorem inputTime_no_prior_output {input output : Stage3Case017.Stream} {x : ℕ}
    (hinj : Function.Injective input)
    (hx : x ∈ GenLimit.AdversaryFirst input output) :
    ∀ s, s < inputTime input x → output s ≠ x := by
  obtain ⟨t, htx, ht⟩ := hx
  have hrange : x ∈ Set.range input := ⟨t, htx⟩
  have heq : inputTime input x = t := hinj (by
    rw [input_inputTime hrange, htx])
  simpa [heq] using ht

 theorem inputTime_range {input output : Stage3Case017.Stream} {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) : x ∈ Set.range input := by
  obtain ⟨t, htx, _⟩ := hx
  exact ⟨t, htx⟩

 theorem core_prefix_counting {m : ℕ}
    (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (hinj : Function.Injective input)
    (hInf : (Stage3Case017.informationCore family input).Infinite) :
    ∃ r, ∀ n,
      GenLimit.PatientScope.prefixCount
          (Stage3Case017.informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
            Stage3Case017.informationCore family input) n + r := by
  classical
  let output := trajectory (generator family) input
  let core := Stage3Case017.informationCore family input
  obtain ⟨T, hT⟩ := eventual_rule family input hInf
  refine ⟨T + 1, ?_⟩
  intro n
  let all := GenLimit.PatientScope.prefixFinset core n
  let attackers := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ core) n
  let defenders := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ core) n
  let early := attackers.filter (fun x => inputTime input x < T)
  let late := attackers.filter (fun x => T ≤ inputTime input x)
  have hall : all ⊆ attackers ∪ defenders := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hr : x ∈ Set.range input
    · rcases GenLimit.range_subset_first_announcements input output hr with ha | hd
      · exact Finset.mem_union_left _ <|
          GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, ha, hx'.2⟩
      · exact Finset.mem_union_right _ <|
          GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hd, hx'.2⟩
    · exact Finset.mem_union_right _ <|
        GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1,
          core_diff_range_subset_generatorFirst family input hInf ⟨hx'.2, hr⟩,
          hx'.2⟩
  have hAllCard : all.card ≤ attackers.card + defenders.card := by
    exact le_trans (Finset.card_le_card hall) (Finset.card_union_le _ _)
  have hsplit : attackers ⊆ early ∪ late := by
    intro x hx
    by_cases hxt : inputTime input x < T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxt⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx, Nat.le_of_not_gt hxt⟩)
  have hAttackCard : attackers.card ≤ early.card + late.card := by
    exact le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  have hEarly : early.card ≤ T := by
    have hcard : early.card ≤ (Finset.range T).card := by
      apply Finset.card_le_card_of_injOn (inputTime input)
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro x hx y hy hxy
        have hxA : x ∈ GenLimit.AdversaryFirst input output :=
          (GenLimit.PatientScope.mem_prefixFinset.mp (Finset.mem_filter.mp hx).1).2.1
        have hyA : y ∈ GenLimit.AdversaryFirst input output :=
          (GenLimit.PatientScope.mem_prefixFinset.mp (Finset.mem_filter.mp hy).1).2.1
        exact inputTime_injective hinj (inputTime_range hxA) (inputTime_range hyA) hxy
    simpa using hcard
  have hLate : late.card ≤ defenders.card + 1 := by
    by_cases hempty : late = ∅
    · simp [hempty]
    · have hne : late.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨last, hlast, hmax⟩ :=
        Finset.exists_max_image late (inputTime input) hne
      have herase : (late.erase last).card + 1 = late.card := by
        have hpos : 0 < late.card := Finset.card_pos.mpr hne
        rw [Finset.card_erase_of_mem hlast]
        omega
      have hmap : ∀ x ∈ late.erase last,
          output (inputTime input x) ∈ defenders := by
        intro x hx
        have hxlate := (Finset.mem_erase.mp hx).2
        have hxne := (Finset.mem_erase.mp hx).1
        have hxatt := (Finset.mem_filter.mp hxlate).1
        have hxT := (Finset.mem_filter.mp hxlate).2
        have hxdata := GenLimit.PatientScope.mem_prefixFinset.mp hxatt
        have hxA := hxdata.2.1
        have hxrange := inputTime_range hxA
        have hlastLate := Finset.mem_filter.mp hlast
        have hlastData := GenLimit.PatientScope.mem_prefixFinset.mp hlastLate.1
        have hlastA := hlastData.2.1
        have hlastRange := inputTime_range hlastA
        have hle := hmax x hxlate
        have hlt : inputTime input x < inputTime input last := by
          exact lt_of_le_of_ne hle fun heq => hxne <|
            inputTime_injective hinj hxrange hlastRange heq
        have hlastFresh : last ∈ core \
            (Set.range (fun i : Fin (inputTime input x + 1) => input i) ∪
              Set.range (fun i : Fin (inputTime input x) => output i)) := by
          refine ⟨hlastData.2.2, ?_⟩
          intro hu
          rcases hu with hu | hu
          · obtain ⟨i, hi⟩ := hu
            have hitime : i = inputTime input last := by
              apply hinj
              exact hi.trans (input_inputTime hlastRange).symm
            omega
          · obtain ⟨i, hi⟩ := hu
            exact inputTime_no_prior_output hinj hlastA i
              (lt_trans i.isLt hlt) hi
        have hrule := hT (inputTime input x) hxT
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨lt_of_le_of_lt (hrule.2 last hlastFresh) hlastData.1, ?_, hrule.1.1⟩
        refine ⟨inputTime input x, rfl, ?_⟩
        intro q hq hin
        exact hrule.1.2 (Or.inl ⟨⟨q, Nat.lt_succ_iff.mpr hq⟩, hin⟩)
      have hinjMap : Set.InjOn (fun x => output (inputTime input x))
          (late.erase last : Set ℕ) := by
        intro x hx y hy hout
        have hxlate := (Finset.mem_erase.mp hx).2
        have hylate := (Finset.mem_erase.mp hy).2
        have hxT := (Finset.mem_filter.mp hxlate).2
        have hyT := (Finset.mem_filter.mp hylate).2
        have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hxlate).1).2.1
        have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hylate).1).2.1
        have hxrange := inputTime_range hxA
        have hyrange := inputTime_range hyA
        by_cases htimes : inputTime input x = inputTime input y
        · exact inputTime_injective hinj hxrange hyrange htimes
        · rcases lt_or_gt_of_ne htimes with hxy | hyx
          · exact False.elim <| (hT (inputTime input y) hyT).1.2
              (Or.inr ⟨⟨inputTime input x, hxy⟩, hout⟩)
          · exact False.elim <| (hT (inputTime input x) hxT).1.2
              (Or.inr ⟨⟨inputTime input y, hyx⟩, hout.symm⟩)
      have heraseLe : (late.erase last).card ≤ defenders.card := by
        exact Finset.card_le_card_of_injOn
          (fun x => output (inputTime input x)) hmap hinjMap
      omega
  change all.card ≤ 2 * defenders.card + (T + 1)
  omega

 theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · apply div_le_div_of_nonneg_right
        · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
        · exact_mod_cast Nat.zero_le (GenLimit.PatientScope.prefixCount K n)
  · apply isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hzero : GenLimit.PatientScope.prefixCount B n = 0 := by
        have := GenLimit.PatientScope.prefixCount_mono hBK n
        omega
      simp [hn, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n


 theorem half_core_density {m : ℕ}
    (family : Fin m → Stage3Case017.Language)
    (hfamily : ∀ j, (family j).Infinite)
    (input : Stage3Case017.Stream) (hinj : Function.Injective input)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
          family j) (family j) := by
  let core := Stage3Case017.informationCore family input
  let wonCore := GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ core
  have hcoreTarget : core ⊆ family j := fun _ hz => hz j hj
  obtain ⟨r, hcount⟩ := core_prefix_counting family input hinj hInf
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity core (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity wonCore (family j) := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (GenLimit.PatientScope.prefixCount core)
      (GenLimit.PatientScope.prefixCount wonCore) r
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono hcoreTarget n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono
        (Set.Subset.trans Set.inter_subset_right hcoreTarget) n
    · intro n
      have hc := hcount n
      dsimp only [core, wonCore] at hc ⊢
      omega
  exact hhalf.trans <| relativeLowerDensity_mono
    (fun _ hz => ⟨hz.1, hcoreTarget hz.2⟩) Set.inter_subset_right
 theorem missing_core_density {m : ℕ}
    (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hInf : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j)
        (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    exact ⟨core_diff_range_subset_generatorFirst family input hInf hz,
      hz.1 j hj⟩
  · exact Set.inter_subset_right

end Stage3Case017Proof

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  intro input hinj hp hInf
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.generator family) input
  refine ⟨output, Stage3Case017Proof.follows_trajectory _ _, ?_⟩
  intro j hj
  refine ⟨Stage3Case017Proof.eventual_novel family input hInf j hj, ?_⟩
  apply max_le
  · exact Stage3Case017Proof.half_core_density
      family hfamily input hinj hInf j hj
  · exact Stage3Case017Proof.missing_core_density family input hInf j hj

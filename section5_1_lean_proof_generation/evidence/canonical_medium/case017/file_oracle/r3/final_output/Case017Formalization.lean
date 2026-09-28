import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable def freshFallback {t : ℕ} (xs : Fin (t+1) → ℕ) (ys : Fin t → ℕ) : ℕ :=
  max (Finset.univ.sup xs) (Finset.univ.sup ys) + 1

lemma lt_freshFallback_input {t : ℕ} (xs : Fin (t+1) → ℕ) (ys : Fin t → ℕ)
    (i : Fin (t+1)) : xs i < freshFallback xs ys := by
  unfold freshFallback
  have h : xs i ≤ Finset.univ.sup xs := Finset.le_sup (Finset.mem_univ i)
  omega

lemma lt_freshFallback_output {t : ℕ} (xs : Fin (t+1) → ℕ) (ys : Fin t → ℕ)
    (i : Fin t) : ys i < freshFallback xs ys := by
  unfold freshFallback
  have h : ys i ≤ Finset.univ.sup ys := Finset.le_sup (Finset.mem_univ i)
  omega

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Stage3Case017.Language) : Stage3Case017.OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z : ℕ,
        (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧
        (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)
    then Nat.find h
    else freshFallback xs ys

lemma familyGenerator_spec_of_exists {m : ℕ} (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (xs : Fin (t+1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z : ℕ,
        (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧
        (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)) :
    (∀ j, (∀ i, xs i ∈ family j) → familyGenerator family t xs ys ∈ family j) ∧
    (∀ i, xs i ≠ familyGenerator family t xs ys) ∧
    (∀ i, ys i ≠ familyGenerator family t xs ys) := by
  classical
  rw [familyGenerator, dif_pos h]
  exact Nat.find_spec h

lemma familyGenerator_fresh {m : ℕ} (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (xs : Fin (t+1) → ℕ) (ys : Fin t → ℕ) :
    (∀ i, xs i ≠ familyGenerator family t xs ys) ∧
    (∀ i, ys i ≠ familyGenerator family t xs ys) := by
  classical
  by_cases h : ∃ z : ℕ,
      (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧
      (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)
  · exact (familyGenerator_spec_of_exists family xs ys h).2
  · rw [familyGenerator, dif_neg h]
    constructor
    · intro i hi
      exact (Nat.ne_of_lt (lt_freshFallback_input xs ys i)) hi
    · intro i hi
      exact (Nat.ne_of_lt (lt_freshFallback_output xs ys i)) hi

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by exact i.isLt

lemma trajectory_follows (gen : Stage3Case017.OnlineGenerator) (input : Stage3Case017.Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory.eq_def gen input t

lemma trajectory_fresh {m : ℕ} (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) (t : ℕ) :
    (∀ s, s ≤ t → input s ≠ trajectory (familyGenerator family) input t) ∧
    (∀ s, s < t → trajectory (familyGenerator family) input s ≠
      trajectory (familyGenerator family) input t) := by
  rw [trajectory.eq_def]
  have h := familyGenerator_fresh family
    (fun i : Fin (t+1) => input i) (fun i : Fin t => trajectory (familyGenerator family) input i)
  constructor
  · intro s hs
    exact h.1 ⟨s, Nat.lt_succ_iff.mpr hs⟩
  · intro s hs
    exact h.2 ⟨s, hs⟩

lemma trajectory_injective {m : ℕ} (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) :
    Function.Injective (trajectory (familyGenerator family) input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact False.elim ((trajectory_fresh family input t).2 s hlt hst)
  · rfl
  · exact False.elim ((trajectory_fresh family input s).2 t hgt hst.symm)

lemma generatorFirst_of_output {m : ℕ} (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (t : ℕ) : trajectory (familyGenerator family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  exact ⟨t, rfl, (trajectory_fresh family input t).1⟩


def currentGood {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (t : ℕ) (j : Fin m) : Prop :=
  ∀ i : Fin (t+1), input i ∈ family j

lemma currentGood_eventually_iff {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (j : Fin m) :
    ∃ T, ∀ t, T ≤ t →
      (currentGood family input t j ↔ GenLimit.Generic.StreamIn input (family j)) := by
  classical
  by_cases hj : GenLimit.Generic.StreamIn input (family j)
  · exact ⟨0, fun t _ => ⟨fun _ => hj, fun _ i => hj ⟨i, rfl⟩⟩⟩
  · obtain ⟨z, ⟨s, rfl⟩, hnot⟩ := Set.not_subset.mp hj
    refine ⟨s, ?_⟩
    intro t hst
    constructor
    · intro hgood
      exact False.elim (hnot (hgood ⟨s, Nat.lt_succ_iff.mpr hst⟩))
    · intro hstream
      exact False.elim (hj hstream)

noncomputable def stabilizationTime {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) : ℕ :=
  Finset.univ.sup (fun j => Classical.choose (currentGood_eventually_iff family input j))

lemma currentGood_iff_after_stabilization {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (t : ℕ) (ht : stabilizationTime family input ≤ t) (j : Fin m) :
    currentGood family input t j ↔ GenLimit.Generic.StreamIn input (family j) := by
  apply (Classical.choose_spec (currentGood_eventually_iff family input j)) t
  have hjT : Classical.choose (currentGood_eventually_iff family input j) ≤
      stabilizationTime family input := by
    unfold stabilizationTime
    exact Finset.le_sup (f := fun k =>
      Classical.choose (currentGood_eventually_iff family input k)) (Finset.mem_univ j)
  exact le_trans hjT ht

lemma core_candidate_exists_after_stabilization {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (t : ℕ) (ht : stabilizationTime family input ≤ t) :
    ∃ z : ℕ,
      (∀ j, currentGood family input t j → z ∈ family j) ∧
      (∀ i : Fin (t+1), input i ≠ z) ∧
      (∀ i : Fin t, trajectory (familyGenerator family) input i ≠ z) := by
  classical
  let used : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t+1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => trajectory (familyGenerator family) input i))
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_not_mem_finset used
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hgood
    exact hzcore j ((currentGood_iff_after_stabilization family input t ht j).mp hgood)
  · intro i hi
    apply hzused
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  · intro i hi
    apply hzused
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

lemma output_spec_after_stabilization {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (t : ℕ) (ht : stabilizationTime family input ≤ t) :
    trajectory (familyGenerator family) input t ∈
        Stage3Case017.informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ trajectory (familyGenerator family) input t) ∧
      (∀ s, s < t → trajectory (familyGenerator family) input s ≠
        trajectory (familyGenerator family) input t) := by
  rw [trajectory.eq_def]
  have hex := core_candidate_exists_after_stabilization family input hcore t ht
  have hs := familyGenerator_spec_of_exists family
    (fun i : Fin (t+1) => input i)
    (fun i : Fin t => trajectory (familyGenerator family) input i) hex
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact hs.1 j ((currentGood_iff_after_stabilization family input t ht j).mpr hj)
  · intro s hst
    exact hs.2.1 ⟨s, Nat.lt_succ_iff.mpr hst⟩
  · intro s hst
    exact hs.2.2 ⟨s, hst⟩

lemma output_le_available_after_stabilization {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (t : ℕ) (ht : stabilizationTime family input ≤ t) (z : ℕ)
    (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hzin : ∀ s, s ≤ t → input s ≠ z)
    (hzout : ∀ s, s < t → trajectory (familyGenerator family) input s ≠ z) :
    trajectory (familyGenerator family) input t ≤ z := by
  classical
  rw [trajectory.eq_def, familyGenerator]
  have hex0 := core_candidate_exists_after_stabilization family input hcore t ht
  have hex : ∃ z : ℕ,
      (∀ j, (∀ i : Fin (t+1), input i ∈ family j) → z ∈ family j) ∧
      (∀ i : Fin (t+1), input i ≠ z) ∧
      (∀ i : Fin t, trajectory (familyGenerator family) input i ≠ z) := by
    simpa [currentGood] using hex0
  rw [dif_pos hex]
  apply Nat.find_min'
  refine ⟨?_, ?_, ?_⟩
  · intro j hgood
    exact hzcore j ((currentGood_iff_after_stabilization family input t ht j).mp hgood)
  · intro i
    exact hzin i (Nat.le_of_lt_succ i.isLt)
  · intro i
    exact hzout i i.isLt


lemma core_covered {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input ⊆
      Set.range input ∪ Set.range (trajectory (familyGenerator family) input) := by
  classical
  intro z hzcore
  induction z using Nat.strong_induction_on with
  | h z ih =>
      by_contra hznot
      have hzinput : z ∉ Set.range input := fun h => hznot (Set.mem_union_left _ h)
      have hzoutput : z ∉ Set.range (trajectory (familyGenerator family) input) :=
        fun h => hznot (Set.mem_union_right _ h)
      let P : Finset ℕ := (Finset.range z).filter
        (fun w => w ∈ Stage3Case017.informationCore family input)
      have hann : ∀ w ∈ P, ∃ q,
          input q = w ∨ trajectory (familyGenerator family) input q = w := by
        intro w hw
        have hw' := Finset.mem_filter.mp hw
        rcases ih w (Finset.mem_range.mp hw'.1) hw'.2 with hin | hout
        · obtain ⟨q, hq⟩ := hin
          exact ⟨q, Or.inl hq⟩
        · obtain ⟨q, hq⟩ := hout
          exact ⟨q, Or.inr hq⟩
      let announceTime : ℕ → ℕ := fun w =>
        if hw : w ∈ P then Classical.choose (hann w hw) else 0
      let B := P.sup announceTime
      let t := max (stabilizationTime family input) (B + 1)
      have htstab : stabilizationTime family input ≤ t := Nat.le_max_left _ _
      have hzIn : ∀ s, s ≤ t → input s ≠ z := by
        intro s _ hsz
        exact hzinput ⟨s, hsz⟩
      have hzOut : ∀ s, s < t → trajectory (familyGenerator family) input s ≠ z := by
        intro s _ hsz
        exact hzoutput ⟨s, hsz⟩
      have houtle := output_le_available_after_stabilization family input hcore t htstab z
        hzcore hzIn hzOut
      have houtcore := (output_spec_after_stabilization family input hcore t htstab).1
      have houtnotseen := (output_spec_after_stabilization family input hcore t htstab).2
      have houtge : z ≤ trajectory (familyGenerator family) input t := by
        by_contra hlt
        have hwlt : trajectory (familyGenerator family) input t < z := Nat.lt_of_not_ge hlt
        have hwP : trajectory (familyGenerator family) input t ∈ P :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, houtcore⟩
        have htime : announceTime (trajectory (familyGenerator family) input t) ≤ B := by
          exact Finset.le_sup (f := announceTime) hwP
        have htime_lt : announceTime (trajectory (familyGenerator family) input t) < t := by
          exact lt_of_le_of_lt htime (lt_of_lt_of_le (Nat.lt_succ_self B) (Nat.le_max_right _ _))
        have hspec := Classical.choose_spec (hann _ hwP)
        rw [show announceTime (trajectory (familyGenerator family) input t) =
          Classical.choose (hann _ hwP) by simp [announceTime, hwP]] at htime_lt
        rcases hspec with hin | hout
        · exact houtnotseen.1 _ (Nat.le_of_lt htime_lt) hin
        · exact houtnotseen.2 _ htime_lt hout
      have heq : trajectory (familyGenerator family) input t = z := Nat.le_antisymm houtle houtge
      exact hzoutput ⟨t, heq⟩

lemma core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  intro z hz
  rcases core_covered family input hcore hz.1 with hin | hout
  · exact False.elim (hz.2 hin)
  · obtain ⟨t, ht⟩ := hout
    refine ⟨t, ht, ?_⟩
    intro s _ hs
    exact hz.2 ⟨s, hs⟩

lemma relativeLowerDensity_mono_left {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
  · filter_upwards [] with n
    by_cases hK : GenLimit.PatientScope.prefixCount K n = 0
    · norm_num [hK]
    · apply div_le_div_of_nonneg_right
      · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
      · positivity
  · exact isBoundedUnder_of_eventually_ge <| Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply isCoboundedUnder_ge_of_le Filter.atTop
    intro n
    show (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ (1 : ℝ)
    by_cases hK : GenLimit.PatientScope.prefixCount K n = 0
    · norm_num [hK]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hK
      rw [div_le_one hpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n


noncomputable def inputTime (input : Stage3Case017.Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

lemma input_at_inputTime {input : Stage3Case017.Stream} {z : ℕ}
    (hz : z ∈ Set.range input) : input (inputTime input z) = z := by
  classical
  rw [inputTime, dif_pos hz]
  exact Nat.find_spec hz

lemma inputTime_le {input : Stage3Case017.Stream} {z : ℕ}
    (hz : z ∈ Set.range input) {q : ℕ} (hq : input q = z) :
    inputTime input z ≤ q := by
  classical
  rw [inputTime, dif_pos hz]
  exact Nat.find_min' hz hq

lemma inputTime_injective (input : Stage3Case017.Stream) (hinj : Function.Injective input) :
    Set.InjOn (inputTime input) (Set.range input) := by
  intro x hx y hy hxy
  calc
    x = input (inputTime input x) := (input_at_inputTime hx).symm
    _ = input (inputTime input y) := congrArg input hxy
    _ = y := input_at_inputTime hy

lemma adversaryFirst_range {input output : Stage3Case017.Stream} {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) : z ∈ Set.range input := by
  obtain ⟨t, ht, -⟩ := hz
  exact ⟨t, ht⟩

lemma no_output_before_inputTime_of_adversaryFirst
    {input output : Stage3Case017.Stream} {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) :
    ∀ s, s < inputTime input z → output s ≠ z := by
  obtain ⟨q, hq, hno⟩ := hz
  have hzrange : z ∈ Set.range input := ⟨q, hq⟩
  intro s hs
  exact hno s (lt_of_lt_of_le hs (inputTime_le hzrange hq))

lemma core_subset_first {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∪
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  intro z hz
  by_cases hin : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input
      (trajectory (familyGenerator family) input) hin
  · have hout : z ∈ Set.range (trajectory (familyGenerator family) input) := by
      rcases core_covered family input hcore hz with h | h
      · exact False.elim (hin h)
      · exact h
    obtain ⟨t, ht⟩ := hout
    exact Set.mem_union_right _ ⟨t, ht, fun s _ hs => hin ⟨s, hs⟩⟩

noncomputable def coreCount {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) (n : ℕ) : ℕ :=
  GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n

noncomputable def adversaryCoreCount {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) (n : ℕ) : ℕ :=
  GenLimit.PatientScope.prefixCount
    (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n

noncomputable def generatorCoreCount {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) (n : ℕ) : ℕ :=
  GenLimit.PatientScope.prefixCount
    (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n

lemma coreCount_le_ownership {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    coreCount family input n ≤
      adversaryCoreCount family input n + generatorCoreCount family input n := by
  classical
  unfold coreCount adversaryCoreCount generatorCoreCount GenLimit.PatientScope.prefixCount
  let E := GenLimit.PatientScope.prefixFinset (Stage3Case017.informationCore family input) n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  calc
    E.card ≤ (A ∪ D).card := Finset.card_le_card (by
      intro z hz
      have hz' := GenLimit.PatientScope.mem_prefixFinset.mp hz
      rcases core_subset_first family input hcore hz'.2 with ha | hd
      · exact Finset.mem_union_left _ <| GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨hz'.1, ha, hz'.2⟩
      · exact Finset.mem_union_right _ <| GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨hz'.1, hd, hz'.2⟩)
    _ ≤ A.card + D.card := Finset.card_union_le _ _

lemma adversaryCoreCount_le {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    adversaryCoreCount family input n ≤ generatorCoreCount family input n +
      stabilizationTime family input + 1 := by
  classical
  let output := trajectory (familyGenerator family) input
  let T := stabilizationTime family input
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ Stage3Case017.informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ Stage3Case017.informationCore family input) n
  let early := A.filter (fun z => inputTime input z < T)
  let late := A.filter (fun z => T ≤ inputTime input z)
  have hsplit : A ⊆ early ∪ late := by
    intro z hz
    by_cases hzt : inputTime input z < T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, Nat.le_of_not_gt hzt⟩)
  have hearly : early.card ≤ T := by
    have hc := Finset.card_le_card_of_injOn (s := early) (t := Finset.range T)
      (inputTime input) (by
        intro z hz
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2) (by
        intro x hx y hy hxy
        apply inputTime_injective input hinj
        · exact adversaryFirst_range (GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp hx).1).2.1
        · exact adversaryFirst_range (GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp hy).1).2.1
        · exact hxy)
    simpa using hc
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hne : late.Nonempty
    · obtain ⟨zmax, hzmax, hmax⟩ := Finset.exists_max_image late (inputTime input) hne
      have hmap : Set.MapsTo
          (fun z => output (inputTime input z)) (↑(late.erase zmax) : Set ℕ) (↑D : Set ℕ) := by
        intro z hz
        have hzlate : z ∈ late := (Finset.mem_erase.mp hz).2
        have hzA := (Finset.mem_filter.mp hzlate).1
        have hzprefix := GenLimit.PatientScope.mem_prefixFinset.mp hzA
        have hzadv := hzprefix.2.1
        have hzcore := hzprefix.2.2
        have hzT := (Finset.mem_filter.mp hzlate).2
        have hstrict : inputTime input z < inputTime input zmax := by
          have hle := hmax z hzlate
          exact lt_of_le_of_ne hle (fun heq => (Finset.mem_erase.mp hz).1 <|
            inputTime_injective input hinj
              (adversaryFirst_range hzadv)
              (adversaryFirst_range (GenLimit.PatientScope.mem_prefixFinset.mp
                ((Finset.mem_filter.mp hzmax).1)).2.1) heq)
        have hwA := (Finset.mem_filter.mp hzmax).1
        have hwpre := GenLimit.PatientScope.mem_prefixFinset.mp hwA
        have hwadv := hwpre.2.1
        have hwcore := hwpre.2.2
        have hwinput : ∀ s, s ≤ inputTime input z → input s ≠ zmax := by
          intro s hs hsz
          have hmin := inputTime_le (adversaryFirst_range hwadv) hsz
          omega
        have hwoutput : ∀ s, s < inputTime input z → output s ≠ zmax := by
          intro s hs
          exact no_output_before_inputTime_of_adversaryFirst hwadv s (lt_trans hs hstrict)
        have houtle := output_le_available_after_stabilization family input hcore
          (inputTime input z) hzT zmax hwcore hwinput hwoutput
        have houtcore := (output_spec_after_stabilization family input hcore
          (inputTime input z) hzT).1
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨lt_of_le_of_lt houtle hwpre.1, generatorFirst_of_output family input _, houtcore⟩
      have hinjmap : Set.InjOn (fun z => output (inputTime input z))
          (↑(late.erase zmax) : Set ℕ) := by
        intro x hx y hy hxy
        apply inputTime_injective input hinj
        · exact adversaryFirst_range (GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).1).2.1
        · exact adversaryFirst_range (GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).1).2.1
        · exact trajectory_injective family input hxy
      have hc := Finset.card_le_card_of_injOn _ hmap hinjmap
      rw [Finset.card_erase_of_mem hzmax] at hc
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  change A.card ≤ D.card + T + 1
  have hA : A.card ≤ early.card + late.card :=
    le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  omega

lemma core_counting_bound {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    coreCount family input n ≤ 2 * generatorCoreCount family input n +
      stabilizationTime family input + 1 := by
  have hown := coreCount_le_ownership family input hcore n
  have hadv := adversaryCoreCount_le family input hinj hcore n
  omega

end Stage3Case017Proof

open Stage3Case017Proof

 theorem stage3_result : Stage3Case017.MainClaim := by
  classical
  intro m hm family hInfinite
  refine ⟨familyGenerator family, ?_⟩
  intro input hinput hpartial hcore
  let output := trajectory (familyGenerator family) input
  refine ⟨output, trajectory_follows _ _, ?_⟩
  intro j hj
  have hcoreK : Stage3Case017.informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hj
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    refine ⟨stabilizationTime family input, ?_⟩
    intro t ht
    have hs := output_spec_after_stabilization family input hcore t ht
    refine ⟨hcoreK hs.1, ?_, hs.2.2⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hslt, hseq⟩ := hsample
    exact hs.2.1 s (Nat.le_of_lt_succ hslt) hseq
  refine ⟨hnovel, ?_⟩
  let I := Stage3Case017.informationCore family input
  let G := GenLimit.GeneratorFirst input output ∩ family j
  let DC := GenLimit.GeneratorFirst input output ∩ I
  have hhalfCore :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity I (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity DC (family j) := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (coreCount family input) (generatorCoreCount family input)
      (stabilizationTime family input + 1)
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hInfinite j)
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono hcoreK n
    · intro n
      apply GenLimit.PatientScope.prefixCount_mono
      intro z hz
      exact hcoreK hz.2
    · intro n
      have hc := core_counting_bound family input hinput hcore n
      omega
  have hDCG : DC ⊆ G := by
    intro z hz
    exact ⟨hz.1, hcoreK hz.2⟩
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity I (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity G (family j) :=
    le_trans hhalfCore
      (relativeLowerDensity_mono_left hDCG (Set.inter_subset_right))
  have hmissingSubset : I \ Set.range input ⊆ G := by
    intro z hz
    exact ⟨core_diff_range_subset_generatorFirst family input hcore hz, hcoreK hz.1⟩
  have hmissing :
      GenLimit.PatientScope.relativeLowerDensity (I \ Set.range input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity G (family j) :=
    relativeLowerDensity_mono_left hmissingSubset Set.inter_subset_right
  exact max_le hhalf hmissing

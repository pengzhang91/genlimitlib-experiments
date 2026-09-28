import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
import GenLimit.Paper39_DenseGeneration.Partial.Trace
import GenLimit.Support.Fresh

open Filter

namespace Case017Proof

open GenLimit
open GenLimit.Generic

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream

noncomputable def versionCore {m : ℕ} (family : Fin m → Language)
    (seen : Finset ℕ) : Language :=
  {z | ∀ j, (↑seen : Set ℕ) ⊆ family j → z ∈ family j}

def Available (C : Language) (seen : Finset ℕ) (z : ℕ) : Prop :=
  z ∈ C ∧ z ∉ seen

noncomputable def leastFresh (C : Language) (hC : C.Infinite)
    (seen : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ z, Available C seen z from
    ⟨GenLimit.Support.freshFromInfinite C hC seen,
      GenLimit.Support.freshFromInfinite_mem C hC seen,
      GenLimit.Support.freshFromInfinite_not_mem C hC seen⟩)

theorem leastFresh_spec (C : Language) (hC : C.Infinite)
    (seen : Finset ℕ) : Available C seen (leastFresh C hC seen) := by
  classical
  exact Nat.find_spec (show ∃ z, Available C seen z from
    ⟨GenLimit.Support.freshFromInfinite C hC seen,
      GenLimit.Support.freshFromInfinite_mem C hC seen,
      GenLimit.Support.freshFromInfinite_not_mem C hC seen⟩)

theorem leastFresh_minimal (C : Language) (hC : C.Infinite)
    (seen : Finset ℕ) {z : ℕ} (hz : Available C seen z) :
    leastFresh C hC seen ≤ z := by
  classical
  exact Nat.find_min' (show ∃ z, Available C seen z from
    ⟨GenLimit.Support.freshFromInfinite C hC seen,
      GenLimit.Support.freshFromInfinite_mem C hC seen,
      GenLimit.Support.freshFromInfinite_not_mem C hC seen⟩) hz

noncomputable def select {m : ℕ} (family : Fin m → Language)
    (seenInput seenOutput : Finset ℕ) : ℕ := by
  classical
  let C := versionCore family seenInput
  let seen := seenInput ∪ seenOutput
  exact if hC : C.Infinite then leastFresh C hC seen
    else leastFresh Set.univ Set.infinite_univ seen

theorem select_not_input {m : ℕ} (family : Fin m → Language)
    (seenInput seenOutput : Finset ℕ) :
    select family seenInput seenOutput ∉ seenInput := by
  classical
  by_cases hcore : (versionCore family seenInput).Infinite
  · simp only [select, dif_pos hcore]
    exact fun hmem => (leastFresh_spec _ _ _).2 (Finset.mem_union_left _ hmem)
  · simp only [select, dif_neg hcore]
    exact fun hmem => (leastFresh_spec _ _ _).2 (Finset.mem_union_left _ hmem)

theorem select_not_output {m : ℕ} (family : Fin m → Language)
    (seenInput seenOutput : Finset ℕ) :
    select family seenInput seenOutput ∉ seenOutput := by
  classical
  by_cases hcore : (versionCore family seenInput).Infinite
  · simp only [select, dif_pos hcore]
    exact fun hmem => (leastFresh_spec _ _ _).2 (Finset.mem_union_right _ hmem)
  · simp only [select, dif_neg hcore]
    exact fun hmem => (leastFresh_spec _ _ _).2 (Finset.mem_union_right _ hmem)

theorem select_mem_core {m : ℕ} (family : Fin m → Language)
    (seenInput seenOutput : Finset ℕ)
    (hcore : (versionCore family seenInput).Infinite) :
    select family seenInput seenOutput ∈ versionCore family seenInput := by
  classical
  simp only [select, dif_pos hcore]
  exact (leastFresh_spec _ _ _).1

theorem select_minimal {m : ℕ} (family : Fin m → Language)
    (seenInput seenOutput : Finset ℕ)
    (hcore : (versionCore family seenInput).Infinite)
    {z : ℕ} (hzCore : z ∈ versionCore family seenInput)
    (hzInput : z ∉ seenInput) (hzOutput : z ∉ seenOutput) :
    select family seenInput seenOutput ≤ z := by
  classical
  simp only [select, dif_pos hcore]
  apply leastFresh_minimal
  exact ⟨hzCore, by simpa using ⟨hzInput, hzOutput⟩⟩

structure State where
  used : Finset ℕ
  lastOutput : ℕ

noncomputable def initialState : State := ⟨∅, 0⟩

noncomputable def process {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) (old : State) : State :=
  let z := select family (GenLimit.sample input (t + 1)) old.used
  ⟨insert z old.used, z⟩

noncomputable def run {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ → State
  | 0 => initialState
  | t + 1 => process family input t (run family input t)

noncomputable def output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) : ℕ :=
  (run family input (t + 1)).lastOutput

@[simp] theorem run_zero {m : ℕ} (family : Fin m → Language)
    (input : Stream) : run family input 0 = initialState := rfl

@[simp] theorem run_succ {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    run family input (t + 1) = process family input t (run family input t) := rfl

@[simp] theorem output_eq_select {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    output family input t =
      select family (GenLimit.sample input (t + 1))
        (run family input t).used := by
  simp [output, process]

@[simp] theorem run_succ_used {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    (run family input (t + 1)).used =
      insert (output family input t) (run family input t).used := by
  simp [process, output]

theorem sample_succ (stream : Stream) (t : ℕ) :
    GenLimit.sample stream (t + 1) =
      insert (stream t) (GenLimit.sample stream t) := by
  classical
  simp [GenLimit.sample, Finset.range_succ, Finset.image_insert]

theorem run_used {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    (run family input t).used = GenLimit.sample (output family input) t := by
  induction t with
  | zero => simp [initialState, GenLimit.sample]
  | succ t ih =>
      rw [run_succ_used, sample_succ, ih]

noncomputable def onlineGenerator {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.OnlineGenerator :=
  fun _ xs ys =>
    select family (GenLimit.Generic.sequenceSample xs)
      (GenLimit.Generic.sequenceSample ys)

theorem follows {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Stage3Case017.Follows (onlineGenerator family) input (output family input) := by
  intro t
  rw [output_eq_select, run_used]
  simp only [onlineGenerator, GenLimit.Generic.sequenceSample_prefix,
    GenLimit.Generic.sample, GenLimit.sample]
  congr 1 <;> ext z <;> simp

 theorem output_not_input_sample {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    output family input t ∉ GenLimit.sample input (t + 1) := by
  rw [output_eq_select]
  exact select_not_input _ _ _

theorem output_not_output_sample {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    output family input t ∉ GenLimit.sample (output family input) t := by
  rw [output_eq_select, ← run_used]
  exact select_not_output _ _ _

theorem output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (output family input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact output_not_output_sample family input t
      (by rw [GenLimit.mem_sample_iff]; exact ⟨s, hlt, hst⟩)
  · exact output_not_output_sample family input s
      (by rw [GenLimit.mem_sample_iff]; exact ⟨t, hgt, hst.symm⟩)

theorem range_subset_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range input ⊆ Stage3Case017.informationCore family input := by
  rintro z ⟨t, rfl⟩ j hj
  exact hj ⟨t, rfl⟩

theorem eventually_versionCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      versionCore family (GenLimit.sample input (t + 1)) =
        Stage3Case017.informationCore family input := by
  classical
  have hj : ∀ j : Fin m, ∃ T : ℕ, ∀ t, T ≤ t →
      ((↑(GenLimit.sample input (t + 1)) : Set ℕ) ⊆ family j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hgood : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, ?_⟩
      intro t _
      constructor
      · intro _
        exact hgood
      · intro _ z hz
        have hz' : z ∈ GenLimit.sample input (t + 1) := hz
        rw [GenLimit.mem_sample_iff] at hz'
        obtain ⟨s, -, rfl⟩ := hz'
        exact hgood ⟨s, rfl⟩
    · obtain ⟨z, ⟨s, rfl⟩, hbad⟩ := Set.not_subset.mp hgood
      refine ⟨s, ?_⟩
      intro t hst
      constructor
      · intro hsub
        exfalso
        apply hbad
        apply hsub
        have hsamp : input s ∈ GenLimit.sample input (t + 1) := by
          rw [GenLimit.mem_sample_iff]
          exact ⟨s, by omega, rfl⟩
        exact hsamp
      · exact fun h => False.elim (hgood h)
  choose threshold hthreshold using hj
  let T := Finset.univ.sup threshold
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [versionCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hjStream
    apply hz j
    exact (hthreshold j t ((Finset.le_sup (s := Finset.univ)
      (f := threshold) (Finset.mem_univ j)).trans ht)).2 hjStream
  · intro hz j hjSample
    apply hz j
    exact (hthreshold j t ((Finset.le_sup (s := Finset.univ)
      (f := threshold) (Finset.mem_univ j)).trans ht)).1 hjSample

theorem eventual_output_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      output family input t ∈ Stage3Case017.informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_versionCore_eq_informationCore family input
  refine ⟨T, ?_⟩
  intro t ht
  rw [output_eq_select]
  have heq := hT t ht
  have hinf : (versionCore family (GenLimit.sample input (t + 1))).Infinite := by
    rw [heq]
    exact hcore
  rw [← heq]
  exact select_mem_core _ _ _ hinf

theorem novel_generates {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (output family input) (family j) := by
  obtain ⟨T, hT⟩ := eventual_output_core family input hcore
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨?_, output_not_input_sample family input t, ?_⟩
  · exact hT t ht j hj
  · intro s hst
    exact fun heq => output_not_output_sample family input t
      (by rw [GenLimit.mem_sample_iff]; exact ⟨s, hst, heq⟩)

theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input ⊆
      GenLimit.AdversaryFirst input (output family input) ∪
        GenLimit.GeneratorFirst input (output family input) := by
  classical
  obtain ⟨T, hstable⟩ := eventually_versionCore_eq_informationCore family input
  have houtInj := output_injective family input
  intro z hz
  by_cases hzInput : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input (output family input) hzInput
  by_cases hzOutput : z ∈ Set.range (output family input)
  · apply Set.mem_union_right
    obtain ⟨t, ht⟩ := hzOutput
    refine ⟨t, ht, ?_⟩
    intro s hst hs
    apply hzInput
    exact ⟨s, hs⟩
  exfalso
  let f : Fin (z + 2) → Fin z := fun i =>
    ⟨output family input (T + i), by
      have heq := hstable (T + i) (Nat.le_add_right T i)
      have hinf :
          (versionCore family
            (GenLimit.sample input (T + i + 1))).Infinite := by
        rw [heq]
        exact hcore
      have hzCore : z ∈ versionCore family
          (GenLimit.sample input (T + i + 1)) := by
        rw [heq]
        exact hz
      have hzNotInput : z ∉ GenLimit.sample input (T + i + 1) := by
        intro hmem
        rw [GenLimit.mem_sample_iff] at hmem
        exact hzInput ⟨hmem.choose, hmem.choose_spec.2⟩
      have hzNotOutput : z ∉ (run family input (T + i)).used := by
        rw [run_used]
        intro hmem
        rw [GenLimit.mem_sample_iff] at hmem
        exact hzOutput ⟨hmem.choose, hmem.choose_spec.2⟩
      have hle : output family input (T + i) ≤ z := by
        rw [output_eq_select]
        exact select_minimal family _ _ hinf hzCore hzNotInput hzNotOutput
      have hne : output family input (T + i) ≠ z := by
        intro heqOut
        exact hzOutput ⟨T + i, heqOut⟩
      omega⟩
  have hf : Function.Injective f := by
    intro i k hik
    exact Fin.ext (Nat.add_left_cancel (houtInj (congrArg Fin.val hik)))
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard

theorem has_predecessor_comparison {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    (T : ℕ)
    (hstable : ∀ t, T ≤ t →
      versionCore family (GenLimit.sample input (t + 1)) =
        Stage3Case017.informationCore family input)
    (K : Language) (hIK : Stage3Case017.informationCore family input ⊆ K) :
    let G : GenLimit.PartialEnumeration.PartialGameTrace :=
      { target := K
        enumerated := Set.range input
        enumerated_subset_target := fun z hz => hIK (range_subset_informationCore family input hz)
        adversary := input
        generator := output family input
        presents := rfl
        fresh_adversary := fun t s hst hs =>
          output_not_input_sample family input t
            (by rw [GenLimit.mem_sample_iff]; exact ⟨s, Nat.lt_succ_of_le hst, hs⟩)
        fresh_generator := fun t s hst hs =>
          output_not_output_sample family input t
            (by rw [GenLimit.mem_sample_iff]; exact ⟨s, hst, hs⟩)
        validFrom := T
        eventual_target := fun t ht => hIK (by
          have heq := hstable t ht
          rw [output_eq_select]
          have hinf : (versionCore family
              (GenLimit.sample input (t + 1))).Infinite := by
            rw [heq]
            exact hcore
          rw [← heq]
          exact select_mem_core _ _ _ hinf) }
    G.HasPredecessorComparison ∅ := by
  dsimp
  intro t ht hattacker hfresh _
  change T < t at ht
  change GenLimit.AdversaryFirst input (output family input) (input t) at hattacker
  obtain ⟨q, hqt, hno⟩ := hattacker
  have htq : t ≤ q := by
    by_contra hqtlt
    apply hfresh
    rw [GenLimit.mem_sample_iff]
    exact ⟨q, Nat.lt_of_not_ge hqtlt, hqt⟩
  have htprev : T ≤ t - 1 := by omega
  have heq := hstable (t - 1) htprev
  have hinf : (versionCore family
      (GenLimit.sample input (t - 1 + 1))).Infinite := by
    rw [heq]
    exact hcore
  have hxI : input t ∈ Stage3Case017.informationCore family input :=
    range_subset_informationCore family input ⟨t, rfl⟩
  have hxCore : input t ∈ versionCore family
      (GenLimit.sample input (t - 1 + 1)) := by
    rw [heq]
    exact hxI
  have hxNotSample : input t ∉ GenLimit.sample input (t - 1 + 1) := by
    change input t ∉ GenLimit.sample input t at hfresh
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hfresh
  have hxNotUsed : input t ∉ (run family input (t - 1)).used := by
    rw [run_used]
    intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, hout⟩ := hmem
    have hst : s < t := by omega
    exact hno s (lt_of_lt_of_le hst htq) hout
  have hle : output family input (t - 1) ≤ input t := by
    rw [output_eq_select]
    exact select_minimal family _ _ hinf hxCore hxNotSample hxNotUsed
  have hne : output family input (t - 1) ≠ input t := by
    intro heqOut
    exact hno (t - 1) (lt_of_lt_of_le (by omega) htq) heqOut
  change output family input (t - 1) < input t
  omega

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (by positivity)
  · exact isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n => div_nonneg (by positivity) (by positivity)
  · apply isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hB : GenLimit.PatientScope.prefixCount B n = 0 := by
        have hle := GenLimit.PatientScope.prefixCount_mono hBK n
        omega
      norm_num [hn, hB]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (output family input) ∩ family j) (family j) := by
  classical
  let I := Stage3Case017.informationCore family input
  have hIK : I ⊆ family j := fun z hz => hz j hj
  obtain ⟨T, hstable⟩ := eventually_versionCore_eq_informationCore family input
  let G : GenLimit.PartialEnumeration.PartialGameTrace :=
    { target := family j
      enumerated := Set.range input
      enumerated_subset_target := fun z hz => hj hz
      adversary := input
      generator := output family input
      presents := rfl
      fresh_adversary := fun t s hst hs =>
        output_not_input_sample family input t
          (by rw [GenLimit.mem_sample_iff]; exact ⟨s, Nat.lt_succ_of_le hst, hs⟩)
      fresh_generator := fun t s hst hs =>
        output_not_output_sample family input t
          (by rw [GenLimit.mem_sample_iff]; exact ⟨s, hst, hs⟩)
      validFrom := T
      eventual_target := fun t ht => hIK (by
        have heq := hstable t ht
        rw [output_eq_select]
        have hinf : (versionCore family
            (GenLimit.sample input (t + 1))).Infinite := by
          rw [heq]
          exact hcore
        change select family (GenLimit.sample input (t + 1))
          (run family input t).used ∈
            Stage3Case017.informationCore family input
        rw [← heq]
        exact select_mem_core _ _ _ hinf) }
  have hcompare : G.HasPredecessorComparison ∅ := by
    exact has_predecessor_comparison family input hcore T hstable (family j) hIK
  let P0 := G.toCertificate ∅ (by simp) hcompare (fun _ => 0) (by
    intro n
    simp [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset])
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { P0 with
      enumerated := I
      enumerated_subset_target := hIK
      enumerated_covered := by
        simpa [P0, G, GenLimit.PartialEnumeration.PartialGameTrace.attacker,
          GenLimit.PartialEnumeration.PartialGameTrace.defender] using
          core_covered family input hcore }
  have hhalf : (1 / 2 : ℝ) *
      GenLimit.PatientScope.relativeLowerDensity I (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (output family input) ∩ family j) (family j) := by
    have hswitch : P.switchLoss = ∅ := by rfl
    have hlog : ∀ n, GenLimit.PatientScope.prefixCount P.switchLoss n ≤
        Nat.log2 (P.targetCount n) := by
      intro n
      rw [hswitch]
      simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset]
    have h := GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
      P (hcore.mono hIK) hlog
    simpa [GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity,
      P, P0, G, GenLimit.PartialEnumeration.PartialGameTrace.defender] using h
  have hmissingSubset : I \ Set.range input ⊆
      GenLimit.GeneratorFirst input (output family input) ∩ family j := by
    intro z hz
    have hcover := core_covered family input hcore hz.1
    refine ⟨?_, hIK hz.1⟩
    rcases hcover with hA | hD
    · obtain ⟨t, ht, -⟩ := hA
      exact False.elim (hz.2 ⟨t, ht⟩)
    · exact hD
  have hmissing := relativeLowerDensity_mono hmissingSubset Set.inter_subset_right
  exact max_le hhalf hmissing

theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hInfinite : ∀ j, (family j).Infinite) :
    Stage3Case017.SucceedsFor family (onlineGenerator family) := by
  intro input hinjective hpresentation hcore
  refine ⟨output family input, follows family input, ?_⟩
  intro j hj
  exact ⟨novel_generates family input hcore j hj,
    density_bounds family input hcore j hj⟩

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hInfinite
  exact ⟨Case017Proof.onlineGenerator family,
    Case017Proof.succeeds family hInfinite⟩

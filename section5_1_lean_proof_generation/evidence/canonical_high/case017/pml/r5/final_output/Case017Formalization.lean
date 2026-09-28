import Stage3Model
import GenLimit.Paper39_DenseGeneration.Partial.Trace
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def currentCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

noncomputable def leastFresh (S : Set ℕ) (hS : S.Infinite)
    (F : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset F)

theorem leastFresh_spec (S : Set ℕ) (hS : S.Infinite) (F : Finset ℕ) :
    leastFresh S hS F ∈ S ∧ leastFresh S hS F ∉ F := by
  classical
  exact Nat.find_spec (hS.exists_notMem_finset F)

theorem leastFresh_le (S : Set ℕ) (hS : S.Infinite) (F : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hzF : z ∉ F) :
    leastFresh S hS F ≤ z := by
  classical
  exact Nat.find_min' (hS.exists_notMem_finset F) ⟨hzS, hzF⟩

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun _ xs ys =>
    if h : (currentCore family xs).Infinite then
      leastFresh (currentCore family xs) h (forbidden xs ys)
    else
      leastFresh Set.univ Set.infinite_univ (forbidden xs ys)

theorem familyGenerator_fresh {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∉ forbidden xs ys := by
  classical
  simp only [familyGenerator]
  split
  · exact (leastFresh_spec _ _ _).2
  · exact (leastFresh_spec _ _ _).2

theorem familyGenerator_mem {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) :
    familyGenerator family t xs ys ∈ currentCore family xs := by
  classical
  simp [familyGenerator, h, leastFresh_spec]

theorem familyGenerator_le {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) {z : ℕ}
    (hz : z ∈ currentCore family xs) (hzfresh : z ∉ forbidden xs ys) :
    familyGenerator family t xs ys ≤ z := by
  classical
  simp only [familyGenerator, dif_pos h]
  exact leastFresh_le _ _ _ hz hzfresh

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t
decreasing_by exact i.isLt

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]

noncomputable def firstBad {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (by
    rw [GenLimit.Generic.StreamIn] at h
    obtain ⟨z, ⟨t, rfl⟩, hz⟩ := Set.not_subset.mp h
    exact ⟨t, hz⟩)

theorem firstBad_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (firstBad family input j) ∉ family j := by
  classical
  simp only [firstBad, dif_neg h]
  exact Nat.find_spec (by
    rw [GenLimit.Generic.StreamIn] at h
    obtain ⟨z, ⟨t, rfl⟩, hz⟩ := Set.not_subset.mp h
    exact ⟨t, hz⟩)

noncomputable def stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (firstBad family input)

theorem firstBad_le_stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    firstBad family input j ≤ stableTime family input := by
  classical
  exact Finset.le_sup (f := firstBad family input) (Finset.mem_univ j)

theorem prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t)
    (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hpref
    by_contra hnot
    have hbad := firstBad_spec family input j hnot
    have hle : firstBad family input j ≤ t :=
      (firstBad_le_stableTime family input j).trans ht
    exact hbad (hpref ⟨firstBad family input j, Nat.lt_succ_of_le hle⟩)
  · intro hin i
    exact hin ⟨i, rfl⟩

theorem currentCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t : ℕ}
    (ht : stableTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input ht j).2 hj)
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input ht j).1 hj)

theorem informationCore_subset {m : ℕ} (family : Fin m → Language)
    (input : Stream) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j :=
  fun _ hz => hz j hj

theorem range_subset_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    Set.range input ⊆ informationCore family input := by
  rintro z ⟨t, rfl⟩ j hj
  exact hj ⟨t, rfl⟩

section RunFacts

variable {m : ℕ} (family : Fin m → Language) (input : Stream)

local notation "gen" => familyGenerator family
local notation "output" => run gen input

theorem output_fresh_input (t s : ℕ) (hs : s ≤ t) :
    input s ≠ output t := by
  intro heq
  have hfresh := familyGenerator_fresh family t
    (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i)
  apply hfresh
  apply Finset.mem_union_left
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  refine ⟨⟨s, Nat.lt_succ_of_le hs⟩, ?_⟩
  exact heq.trans (run_follows gen input t)

theorem output_fresh_output (t s : ℕ) (hs : s < t) :
    output s ≠ output t := by
  intro heq
  have hfresh := familyGenerator_fresh family t
    (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i)
  apply hfresh
  apply Finset.mem_union_right
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  refine ⟨⟨s, hs⟩, ?_⟩
  exact heq.trans (run_follows gen input t)

theorem output_injective : Function.Injective output := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact output_fresh_output family input b a hlt hab
  · exact output_fresh_output family input a b hgt hab.symm

theorem output_mem_core {t : ℕ}
    (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t) :
    output t ∈ informationCore family input := by
  rw [run]
  have heq := currentCore_eq_informationCore family input ht
  have hinf :
      (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    simpa [heq] using hcore
  have hmem := familyGenerator_mem family t
    (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i) hinf
  simpa [heq] using hmem

theorem output_le_available {t z : ℕ}
    (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzinput : ∀ s, s ≤ t → input s ≠ z)
    (hzoutput : ∀ s, s < t → output s ≠ z) :
    output t ≤ z := by
  rw [run]
  have heq := currentCore_eq_informationCore family input ht
  have hinf :
      (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    simpa [heq] using hcore
  apply familyGenerator_le family t
    (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i) hinf
  · simpa [heq] using hzcore
  · intro hz
    unfold forbidden at hz
    rw [Finset.mem_union, GenLimit.Generic.mem_sequenceSample_iff,
      GenLimit.Generic.mem_sequenceSample_iff] at hz
    rcases hz with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hzinput i (Nat.le_of_lt_succ i.isLt) hi
    · exact hzoutput i i.isLt hi

theorem core_subset_announcements
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input output ∪
        GenLimit.GeneratorFirst input output := by
  intro z hzcore
  by_cases hzrange : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input output hzrange
  · apply Set.mem_union_right
    by_contra hzgen
    have hzout : z ∉ Set.range output := by
      intro hrange
      obtain ⟨t, ht⟩ := hrange
      apply hzgen
      refine ⟨t, ht, ?_⟩
      intro s hs hsz
      exact hzrange ⟨s, hsz⟩
    let tail : ℕ → ℕ := fun k => output (stableTime family input + k)
    have htailinj : Function.Injective tail := by
      intro a b hab
      apply Nat.add_left_cancel
      exact output_injective family input hab
    have htailInfinite : (Set.range tail).Infinite :=
      Set.infinite_range_of_injective htailinj
    have htailSubset : Set.range tail ⊆ Set.Iic z := by
      rintro y ⟨k, rfl⟩
      apply output_le_available family input hcore (Nat.le_add_right _ _)
      · exact hzcore
      · intro s hs hsz
        exact hzrange ⟨s, hsz⟩
      · intro s hs hsz
        exact hzout ⟨s, hsz⟩
    exact (Set.finite_Iic z).not_infinite (htailInfinite.mono htailSubset)

end RunFacts

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · apply Eventually.of_forall
    intro n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  · exact isBoundedUnder_of ⟨0, fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · exact isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop (fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp only [hn, Nat.cast_zero, div_zero]
        exact (zero_le_one : (0 : ℝ) ≤ 1)
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n)

theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite) :
    SucceedsFor family (familyGenerator family) := by
  intro input hinj hexists hcore
  let output := run (familyGenerator family) input
  refine ⟨output, run_follows _ _, ?_⟩
  intro j hj
  have hKinf : (family j).Infinite := hfamily j
  let T := stableTime family input
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    refine ⟨T, ?_⟩
    intro t ht
    refine ⟨informationCore_subset family input hj
        (output_mem_core family input hcore ht), ?_, ?_⟩
    · intro hmem
      rw [GenLimit.mem_sample_iff] at hmem
      obtain ⟨s, hs, heq⟩ := hmem
      exact output_fresh_input family input t s (Nat.le_of_lt_succ hs) heq
    · intro s hs
      exact output_fresh_output family input t s hs
  refine ⟨hnovel, ?_⟩
  have hcoreSubK : informationCore family input ⊆ family j :=
    informationCore_subset family input hj
  have hpresentedSubCore : Set.range input ⊆ informationCore family input :=
    range_subset_informationCore family input
  let G : GenLimit.PartialEnumeration.PartialGameTrace :=
    { target := family j
      enumerated := Set.range input
      enumerated_subset_target := hpresentedSubCore.trans hcoreSubK
      adversary := input
      generator := output
      presents := rfl
      fresh_adversary := fun t s hst => output_fresh_input family input t s hst
      fresh_generator := fun t s hst => output_fresh_output family input t s hst
      validFrom := T
      eventual_target := fun t ht =>
        hcoreSubK (output_mem_core family input hcore ht) }
  have hcompare : G.HasPredecessorComparison (∅ : Set ℕ) := by
    intro t ht hattacker _ _
    change T < t at ht
    change input t ∈ GenLimit.AdversaryFirst input output at hattacker
    have htstable : T ≤ t - 1 := by omega
    have hxcore : input t ∈ informationCore family input :=
      hpresentedSubCore ⟨t, rfl⟩
    have hxinput : ∀ s, s ≤ t - 1 → input s ≠ input t := by
      intro s hs heq
      have hst : s = t := hinj heq
      omega
    have hprior : ∀ s, s < t → output s ≠ input t := by
      intro s hs
      obtain ⟨q, hqt, hno⟩ := hattacker
      have hqtEq : q = t := hinj hqt
      subst q
      exact hno s hs
    have hxoutput : ∀ s, s < t - 1 → output s ≠ input t := by
      intro s hs
      exact hprior s (by omega)
    have hle := output_le_available family input hcore htstable hxcore
      hxinput hxoutput
    have hne : output (t - 1) ≠ input t := hprior (t - 1) (by omega)
    change output (t - 1) < input t
    exact Nat.lt_of_le_of_ne hle hne
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { target := family j
      enumerated := informationCore family input
      enumerated_subset_target := hcoreSubK
      attacker := G.attacker
      defender := G.defender
      output := output
      output_range := G.output_range
      output_injective := G.generator_injective
      validFrom := T
      eventual_target := G.eventual_target
      enumerated_covered := core_subset_announcements family input hcore
      attacker_subset_target := G.attacker_subset_target
      ownership_disjoint := G.ownership_disjoint
      earlyAttacker := G.earlyAttacker
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := G.predecessorPartner
      partner_mem := fun _ hx => G.predecessorPartner_mem hx
      partner_lt := fun _ hx => G.predecessorPartner_lt hcompare hx
      partner_injective := G.predecessorPartner_injective
      switchBudget := fun _ => 0
      switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset] }
  have hhalf := P.theorem_3_17 hKinf (by
    intro n
    simp [P, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset])
  have hhalf' :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    simpa [P, G, GenLimit.PartialEnumeration.PartialGameTrace.defender] using hhalf
  have hmissingSub :
      informationCore family input \ Set.range input ⊆
        GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    have hann := core_subset_announcements family input hcore hz.1
    rcases hann with hzA | hzD
    · obtain ⟨t, hit, -⟩ := hzA
      exact False.elim (hz.2 ⟨t, hit⟩)
    · exact ⟨hzD, hcoreSubK hz.1⟩
  have hmissing := relativeLowerDensity_mono hmissingSub Set.inter_subset_right
  exact max_le hhalf' hmissing

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  exact ⟨Case017Proof.familyGenerator family,
    Case017Proof.succeeds family hfamily⟩

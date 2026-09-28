import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

noncomputable section

def compatibleCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

def eligible {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Set ℕ := by
  classical
  let core := compatibleCore family xs
  let base := if core.Infinite then core else Set.univ
  exact base \ (Set.range xs ∪ Set.range ys)

theorem eligible_nonempty {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    (eligible family xs ys).Nonempty := by
  classical
  let core := compatibleCore family xs
  let base : Set ℕ := if core.Infinite then core else Set.univ
  have hbase : base.Infinite := by
    dsimp [base]
    split_ifs with h
    · exact h
    · exact Set.infinite_univ
  have hfinite : (Set.range xs ∪ Set.range ys).Finite :=
    (Set.finite_range xs).union (Set.finite_range ys)
  simpa [eligible, core, base] using (hbase.diff hfinite).nonempty

def familyGenerator {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys => Nat.find (eligible_nonempty family xs ys)

theorem familyGenerator_mem_eligible {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∈ eligible family xs ys := by
  classical
  exact Nat.find_spec (eligible_nonempty family xs ys)

theorem familyGenerator_le {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hz : z ∈ eligible family xs ys) :
    familyGenerator family t xs ys ≤ z := by
  classical
  exact Nat.find_min' (eligible_nonempty family xs ys) hz

def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t
decreasing_by exact i.isLt

@[simp] theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run]

theorem follows_run (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

theorem exists_bad_time {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ q, input q ∉ family j := by
  obtain ⟨z, ⟨q, hq⟩, hz⟩ := Set.not_subset.mp h
  exact ⟨q, hq ▸ hz⟩

def witnessTime {m : ℕ} (family : Fin m → Language) (input : Stream)
    (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Classical.choose (exists_bad_time family input j h)

theorem witnessTime_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (witnessTime family input j) ∉ family j := by
  rw [witnessTime, dif_neg h]
  exact Classical.choose_spec (exists_bad_time family input j h)

def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  ∑ j, witnessTime family input j

theorem witnessTime_le_stabilizationTime {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) :
    witnessTime family input j ≤ stabilizationTime family input := by
  classical
  unfold stabilizationTime
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem compatible_at_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t)
    (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hprefix z hz
    obtain ⟨q, rfl⟩ := hz
    by_contra hbad
    have hstream : ¬ GenLimit.Generic.StreamIn input (family j) := by
      intro hall
      exact hbad (hall ⟨q, rfl⟩)
    have hq : witnessTime family input j ≤ t :=
      le_trans (witnessTime_le_stabilizationTime family input j) ht
    exact witnessTime_spec family input j hstream
      (hprefix ⟨witnessTime family input j, Nat.lt_succ_of_le hq⟩)
  · intro hall i
    exact hall ⟨i, rfl⟩

theorem compatibleCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t : ℕ}
    (ht : stabilizationTime family input ≤ t) :
    compatibleCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [compatibleCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((compatible_at_iff family input ht j).2 hj)
  · intro hz j hj
    exact hz j ((compatible_at_iff family input ht j).1 hj)


def outputFor {m : ℕ} (family : Fin m → Language) (input : Stream) : Stream :=
  run (familyGenerator family) input

theorem output_mem_eligible {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    outputFor family input t ∈
      eligible family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => outputFor family input i) := by
  rw [outputFor, run_eq]
  exact familyGenerator_mem_eligible family _ _

theorem output_avoids_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    outputFor family input t ∉ Set.range (fun i : Fin (t + 1) => input i) := by
  have h := (output_mem_eligible family input t).2
  exact fun hmem => h (Set.mem_union_left _ hmem)

theorem output_avoids_previous {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    outputFor family input t ∉ Set.range (fun i : Fin t => outputFor family input i) := by
  have h := (output_mem_eligible family input t).2
  exact fun hmem => h (Set.mem_union_right _ hmem)

theorem output_ne_input_of_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) {s t : ℕ} (hst : s ≤ t) :
    input s ≠ outputFor family input t := by
  intro heq
  exact output_avoids_input family input t
    ⟨⟨s, Nat.lt_succ_of_le hst⟩, heq⟩

theorem output_ne_previous {m : ℕ} (family : Fin m → Language)
    (input : Stream) {s t : ℕ} (hst : s < t) :
    outputFor family input s ≠ outputFor family input t := by
  intro heq
  exact output_avoids_previous family input t ⟨⟨s, hst⟩, heq⟩

theorem output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (outputFor family input) := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hts
  · exact False.elim (output_ne_previous family input hst heq)
  · exact hst
  · exact False.elim (output_ne_previous family input hts heq.symm)

theorem stable_output_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    outputFor family input t ∈ informationCore family input := by
  have hmem := (output_mem_eligible family input t).1
  rw [compatibleCore_eq_informationCore family input ht] at hmem
  simpa [eligible, hcore] using hmem

theorem stable_output_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t z : ℕ} (ht : stabilizationTime family input ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzinput : z ∉ Set.range (fun i : Fin (t + 1) => input i))
    (hzoutput : z ∉ Set.range (fun i : Fin t => outputFor family input i)) :
    outputFor family input t ≤ z := by
  rw [outputFor, run_eq]
  apply familyGenerator_le family
  change z ∈ eligible family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => outputFor family input i)
  simp only [eligible, compatibleCore_eq_informationCore family input ht,
    hcore, if_pos, Set.mem_diff, Set.mem_union]
  exact ⟨hzcore, fun h => h.elim hzinput hzoutput⟩

theorem stable_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (outputFor family input) (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  have hmemCore := stable_output_mem_core family input hcore ht
  refine ⟨hmemCore j hj, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact output_ne_input_of_le family input (Nat.le_of_lt_succ hs) heq
  · intro s hst
    exact output_ne_previous family input hst


theorem output_range_eq_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    Set.range (outputFor family input) =
      GenLimit.GeneratorFirst input (outputFor family input) := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    refine ⟨t, rfl, ?_⟩
    intro s hs
    exact output_ne_input_of_le family input hs
  · rintro z ⟨t, htz, -⟩
    exact ⟨t, htz⟩

theorem core_point_in_output_of_not_input {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hzinput : z ∉ Set.range input) :
    z ∈ Set.range (outputFor family input) := by
  by_contra hzoutput
  let tail : ℕ → ℕ := fun n =>
    outputFor family input (stabilizationTime family input + n)
  have htailinj : Function.Injective tail :=
    (output_injective family input).comp (fun _ _ h => Nat.add_left_cancel h)
  have hinfinite : (Set.range tail).Infinite :=
    Set.infinite_range_of_injective htailinj
  have hsubset : Set.range tail ⊆ Set.Iic z := by
    rintro y ⟨n, rfl⟩
    apply stable_output_le family input hcore
    · exact Nat.le_add_right _ _
    · exact hzcore
    · intro hmem
      obtain ⟨i, hi⟩ := hmem
      exact hzinput ⟨i, hi⟩
    · intro hmem
      obtain ⟨i, hi⟩ := hmem
      exact hzoutput ⟨i, hi⟩
  exact hinfinite ((Set.finite_Iic z).subset hsubset)

theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (outputFor family input) ∪
        GenLimit.GeneratorFirst input (outputFor family input) := by
  intro z hz
  by_cases hzinput : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input
      (outputFor family input) hzinput
  · apply Set.mem_union_right
    rw [← output_range_eq_generatorFirst family input]
    exact core_point_in_output_of_not_input family input hcore hz hzinput

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  let aRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let bRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have haNonneg : ∀ n, 0 ≤ aRatio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbLeOne : ∀ n, bRatio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [bRatio, hn]
    · dsimp [bRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  change liminf aRatio atTop ≤ liminf bRatio atTop
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      dsimp [aRatio, bRatio]
      gcongr
      exact GenLimit.PatientScope.prefixCount_mono hAB n
  · exact isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall haNonneg)
  · exact isCoboundedUnder_ge_of_le atTop hbLeOne

def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem firstInputTime_spec (input : Stream) {z : ℕ}
    (hz : z ∈ Set.range input) :
    input (firstInputTime input z) = z := by
  rw [firstInputTime, dif_pos hz]
  exact Nat.find_spec hz

theorem firstInputTime_eq_of_input_injective (input : Stream)
    (hinj : Function.Injective input) {z t : ℕ} (ht : input t = z) :
    firstInputTime input z = t := by
  apply hinj
  rw [firstInputTime_spec input ⟨t, ht⟩, ht]

def earlyAnnouncements {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Finset ℕ :=
  (Finset.range (stabilizationTime family input)).image input ∪
    (Finset.range (stabilizationTime family input)).image (outputFor family input)

theorem earlyAnnouncements_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    (earlyAnnouncements family input).card ≤
      2 * stabilizationTime family input := by
  classical
  unfold earlyAnnouncements
  calc
    ((Finset.range _).image input ∪
        (Finset.range _).image (outputFor family input)).card
        ≤ ((Finset.range _).image input).card +
          ((Finset.range _).image (outputFor family input)).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.range _).card + (Finset.range _).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2 * stabilizationTime family input := by simp [two_mul]

def lateAttackerPrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ :=
  (GenLimit.PatientScope.prefixFinset
      (GenLimit.AdversaryFirst input (outputFor family input) ∩
        informationCore family input) n) \
    earlyAnnouncements family input

def defenderTargetPrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (K : Language) (n : ℕ) : Finset ℕ :=
  GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (outputFor family input) ∩ K) n

def charge {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n x : ℕ) : ℕ :=
  if outputFor family input (firstInputTime input x) < n then
    outputFor family input (firstInputTime input x)
  else n

theorem lateAttacker_time_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    {n x : ℕ} (hx : x ∈ lateAttackerPrefix family input n) :
    stabilizationTime family input ≤ firstInputTime input x := by
  classical
  have hxpre := (GenLimit.PatientScope.mem_prefixFinset.mp
    (Finset.mem_sdiff.mp hx).1).2.1
  obtain ⟨t, htx, -⟩ := hxpre
  have htime : firstInputTime input x = t :=
    firstInputTime_eq_of_input_injective input hinj htx
  by_contra hlt
  have ht : t < stabilizationTime family input := by omega
  have : x ∈ earlyAnnouncements family input := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, htx⟩
  exact (Finset.mem_sdiff.mp hx).2 this

theorem later_attacker_forces_small_output {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {n x y : ℕ} (hx : x ∈ lateAttackerPrefix family input n)
    (hy : y ∈ lateAttackerPrefix family input n)
    (hxy : firstInputTime input x < firstInputTime input y) :
    outputFor family input (firstInputTime input x) < n := by
  classical
  have hydata := GenLimit.PatientScope.mem_prefixFinset.mp
    (Finset.mem_sdiff.mp hy).1
  have hyA := hydata.2.1
  have hycore := hydata.2.2
  have hylt : y < n := hydata.1
  have hle : outputFor family input (firstInputTime input x) ≤ y :=
    stable_output_le family input hcore
      (lateAttacker_time_stable family input hinj hx) hycore (by
        intro hmem
        obtain ⟨i, hi⟩ := hmem
        have hitime := firstInputTime_spec input
          (z := y) ⟨Classical.choose hyA, (Classical.choose_spec hyA).1⟩
        have : (i : ℕ) = firstInputTime input y := hinj (hi.trans hitime.symm)
        omega) (by
        intro hmem
        obtain ⟨i, hi⟩ := hmem
        obtain ⟨ty, hity, hbefore⟩ := hyA
        have hty : ty = firstInputTime input y := by
          symm
          exact firstInputTime_eq_of_input_injective input hinj hity
        exact hbefore i (by omega) hi)
  exact lt_of_le_of_lt hle hylt

theorem charge_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (K : Language) (hIK : informationCore family input ⊆ K)
    {n x : ℕ} (hx : x ∈ lateAttackerPrefix family input n) :
    charge family input n x ∈
      insert n (defenderTargetPrefix family input K n) := by
  classical
  unfold charge
  split_ifs with hsmall
  · apply Finset.mem_insert_of_mem
    apply GenLimit.PatientScope.mem_prefixFinset.mpr
    refine ⟨hsmall, ?_, hIK (stable_output_mem_core family input hcore
      (lateAttacker_time_stable family input hinj hx))⟩
    rw [← output_range_eq_generatorFirst family input]
    exact ⟨firstInputTime input x, rfl⟩
  · exact Finset.mem_insert_self _ _

theorem charge_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    Set.InjOn (charge family input n) (lateAttackerPrefix family input n) := by
  classical
  intro x hx y hy hcharge
  have hxrange : x ∈ Set.range input := by
    have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_sdiff.mp hx).1).2.1
    obtain ⟨t, htx, -⟩ := hxA
    exact ⟨t, htx⟩
  have hyrange : y ∈ Set.range input := by
    have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_sdiff.mp hy).1).2.1
    obtain ⟨t, hty, -⟩ := hyA
    exact ⟨t, hty⟩
  let tx := firstInputTime input x
  let ty := firstInputTime input y
  have hxin : input tx = x := firstInputTime_spec input hxrange
  have hyin : input ty = y := firstInputTime_spec input hyrange
  by_cases hxsmall : outputFor family input tx < n
  · by_cases hysmall : outputFor family input ty < n
    · have hout : outputFor family input tx = outputFor family input ty := by
        simpa [charge, tx, ty, hxsmall, hysmall] using hcharge
      have ht : tx = ty := output_injective family input hout
      calc
        x = input tx := hxin.symm
        _ = input ty := congrArg input ht
        _ = y := hyin
    · have : outputFor family input tx = n := by
        simpa [charge, tx, ty, hxsmall, hysmall] using hcharge
      omega
  · by_cases hysmall : outputFor family input ty < n
    · have : n = outputFor family input ty := by
        simpa [charge, tx, ty, hxsmall, hysmall] using hcharge
      omega
    · by_contra hxy
      have htne : tx ≠ ty := by
        intro ht
        apply hxy
        rw [← hxin, ← hyin, ht]
      rcases lt_or_gt_of_ne htne with hlt | hgt
      · exact hxsmall (later_attacker_forces_small_output family input hinj hcore hx hy hlt)
      · exact hysmall (later_attacker_forces_small_output family input hinj hcore hy hx hgt)

theorem lateAttacker_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (K : Language) (hIK : informationCore family input ⊆ K) (n : ℕ) :
    (lateAttackerPrefix family input n).card ≤
      (defenderTargetPrefix family input K n).card + 1 := by
  classical
  calc
    (lateAttackerPrefix family input n).card
        ≤ (insert n (defenderTargetPrefix family input K n)).card := by
      apply Finset.card_le_card_of_injOn (charge family input n)
      · intro x hx
        exact charge_mem family input hinj hcore K hIK hx
      · exact charge_injective family input hinj hcore n
    _ ≤ (defenderTargetPrefix family input K n).card + 1 := by
      exact Finset.card_insert_le _ _

theorem core_prefix_counting {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (K : Language) (hIK : informationCore family input ⊆ K) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (outputFor family input) ∩ K) n +
      (2 * stabilizationTime family input + 1) := by
  classical
  let P := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let E := earlyAnnouncements family input
  let L := lateAttackerPrefix family input n
  let D := defenderTargetPrefix family input K n
  have hsubset : P ⊆ (E ∪ L) ∪ D := by
    intro z hz
    have hzdata := GenLimit.PatientScope.mem_prefixFinset.mp hz
    rcases core_covered family input hcore hzdata.2 with hzA | hzD
    · by_cases hzE : z ∈ E
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzE)
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_sdiff.mpr ⟨
          GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨hzdata.1, hzA, hzdata.2⟩, hzE⟩
    · apply Finset.mem_union_right
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hzdata.1, hzD, hIK hzdata.2⟩
  have hcards : P.card ≤ E.card + L.card + D.card := by
    calc
      P.card ≤ ((E ∪ L) ∪ D).card := Finset.card_le_card hsubset
      _ ≤ (E ∪ L).card + D.card := Finset.card_union_le _ _
      _ ≤ (E.card + L.card) + D.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hE := earlyAnnouncements_card_le family input
  change E.card ≤ 2 * stabilizationTime family input at hE
  have hL := lateAttacker_card_le family input hinj hcore K hIK n
  change L.card ≤ D.card + 1 at hL
  change P.card ≤ 2 * D.card + (2 * stabilizationTime family input + 1)
  omega


theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (K : Language) (hK : K.Infinite)
    (hIK : informationCore family input ⊆ K) :
    (1 / 2 : ℝ) *
        GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (outputFor family input) ∩ K) K := by
  apply GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount K n)
    (fun n => GenLimit.PatientScope.prefixCount (informationCore family input) n)
    (fun n => GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (outputFor family input) ∩ K) n)
    (2 * stabilizationTime family input + 1)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono hIK n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hcount := core_prefix_counting family input hinj hcore K hIK n
    omega

theorem missing_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hIK : informationCore family input ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (outputFor family input) ∩ K) K := by
  apply relativeLowerDensity_mono
  · intro z hz
    refine ⟨?_, hIK hz.1⟩
    rw [← output_range_eq_generatorFirst family input]
    exact core_point_in_output_of_not_input family input hcore hz.1 hz.2
  · exact Set.inter_subset_right


end

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.familyGenerator family, ?_⟩
  intro input hinj hpresentation hcore
  let output := Stage3Case017Proof.outputFor family input
  refine ⟨output, Stage3Case017Proof.follows_run _ _, ?_⟩
  intro j hj
  have hIK : Stage3Case017.informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hj
  refine ⟨Stage3Case017Proof.stable_novel family input hcore j hj, ?_⟩
  apply max_le
  · exact Stage3Case017Proof.half_core_density family input hinj hcore
      (family j) (hfamily j) hIK
  · exact Stage3Case017Proof.missing_core_density family input hcore
      (family j) hIK

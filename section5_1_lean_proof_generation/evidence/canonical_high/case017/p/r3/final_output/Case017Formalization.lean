import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable section

local instance instPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream

 def historySet {n : ℕ} (xs : Fin n → ℕ) : Set ℕ := Set.range xs

 def currentCore {m n : ℕ} (family : Fin m → Language) (xs : Fin n → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

 def available {m a b : ℕ} (family : Fin m → Language)
    (xs : Fin a → ℕ) (ys : Fin b → ℕ) : Set ℕ :=
  currentCore family xs \ (historySet xs ∪ historySet ys)

 noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.OnlineGenerator :=
  fun _ xs ys => if h : (available family xs ys).Nonempty then Nat.find h else 0

 theorem familyGenerator_mem {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (available family xs ys).Nonempty) :
    familyGenerator family t xs ys ∈ available family xs ys := by
  simp only [familyGenerator, dif_pos h]
  exact Nat.find_spec h

 theorem familyGenerator_min {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (available family xs ys).Nonempty) {z : ℕ}
    (hz : z ∈ available family xs ys) :
    familyGenerator family t xs ys ≤ z := by
  simp only [familyGenerator, dif_pos h]
  exact Nat.find_min' h hz

 noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator) (input : Stream) : Stream :=
  Nat.lt_wfRel.wf.fix fun t rec =>
    gen t (fun i => input i) (fun i => rec i i.isLt)

 theorem trajectory_eq (gen : Stage3Case017.OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory, WellFounded.fix_eq]

 theorem trajectory_follows (gen : Stage3Case017.OnlineGenerator) (input : Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

 theorem historySet_finite {n : ℕ} (xs : Fin n → ℕ) : (historySet xs).Finite := by
  exact Set.finite_range xs

 theorem available_nonempty_of_infinite {m a b : ℕ} (family : Fin m → Language)
    (xs : Fin a → ℕ) (ys : Fin b → ℕ)
    (hcore : (currentCore family xs).Infinite) :
    (available family xs ys).Nonempty := by
  apply (hcore.diff ((historySet_finite xs).union (historySet_finite ys))).nonempty

 def failureTime {m : ℕ} (family : Fin m → Language) (input : Stream) (j : Fin m) : ℕ :=
  if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (show ∃ t, input t ∉ family j by
    simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

 def stabilizationTime {m : ℕ} (family : Fin m → Language) (input : Stream) : ℕ :=
  ∑ j, failureTime family input j

 theorem failureTime_spec {m : ℕ} (family : Fin m → Language) (input : Stream)
    (j : Fin m) (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (failureTime family input j) ∉ family j := by
  simp only [failureTime, dif_neg h]
  exact Nat.find_spec (show ∃ t, input t ∉ family j by
    simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

 theorem failureTime_le_stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    failureTime family input j ≤ stabilizationTime family input := by
  classical
  unfold stabilizationTime
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

 theorem currentCore_eq_informationCore {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      Stage3Case017.informationCore family input := by
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hj
    apply hz j
    intro z' hz'
    rcases hz' with ⟨s, rfl⟩
    by_contra hnot
    have hstream : ¬ GenLimit.Generic.StreamIn input (family j) := by
      intro hs
      exact hnot (hs ⟨s, rfl⟩)
    have hbad := failureTime_spec family input j hstream
    have hle : failureTime family input j ≤ t :=
      (failureTime_le_stabilizationTime family input j).trans ht
    exact hbad (hj ⟨failureTime family input j, Nat.lt_succ_of_le hle⟩)

 theorem eventual_generator_properties {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∀ t, stabilizationTime family input ≤ t →
      output t ∈ Stage3Case017.informationCore family input ∧
      output t ∉ Set.range (fun i : Fin (t + 1) => input i) ∧
      output t ∉ Set.range (fun i : Fin t => output i) := by
  intro t ht
  have heq := currentCore_eq_informationCore family input ht
  have hinf : (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [heq]
    exact hcore
  have havail : (available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i)).Nonempty :=
    available_nonempty_of_infinite family _ _ hinf
  rw [hfollows t]
  have hmem := familyGenerator_mem family _ _ havail
  change _ ∈ currentCore family (fun i : Fin (t + 1) => input i) ∧
    _ ∉ (historySet (fun i : Fin (t + 1) => input i) ∪
      historySet (fun i : Fin t => output i)) at hmem
  rw [heq] at hmem
  refine ⟨hmem.1, ?_, ?_⟩
  · intro hx
    exact hmem.2 (Or.inl hx)
  · intro hy
    exact hmem.2 (Or.inr hy)

 theorem eventual_novel {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input output (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  have hp := eventual_generator_properties family input output hfollows hcore t ht
  refine ⟨?_, ?_, ?_⟩
  · exact (hp.1 j hj)
  · intro hmem
    rw [GenLimit.sample, Finset.mem_image] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact hp.2.1 ⟨⟨s, by simpa using hs⟩, heq⟩
  · intro s hs heq
    exact hp.2.2 ⟨⟨s, hs⟩, heq⟩


 theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ Stage3Case017.informationCore family input) :
    z ∈ Set.range input ∪ Set.range output := by
  by_contra hnot
  have hnot_input : z ∉ Set.range input := fun h => hnot (Or.inl h)
  have hnot_output : z ∉ Set.range output := fun h => hnot (Or.inr h)
  let T := stabilizationTime family input
  have hout_le : ∀ i : Fin (z + 2), output (T + i) ≤ z := by
    intro i
    have ht : stabilizationTime family input ≤ T + i := by simp [T]
    have heq := currentCore_eq_informationCore family input ht
    have havail : z ∈ available family (fun k : Fin (T + i + 1) => input k)
        (fun k : Fin (T + i) => output k) := by
      refine ⟨?_, ?_⟩
      · rw [heq]
        exact hz
      · intro hu
        rcases hu with hu | hu
        · rcases hu with ⟨k, hk⟩
          exact hnot_input ⟨k, hk⟩
        · rcases hu with ⟨k, hk⟩
          exact hnot_output ⟨k, hk⟩
    have hnonempty : (available family (fun k : Fin (T + i + 1) => input k)
        (fun k : Fin (T + i) => output k)).Nonempty := ⟨z, havail⟩
    rw [hfollows (T + i)]
    exact familyGenerator_min family _ _ hnonempty havail
  let f : Fin (z + 2) → Fin (z + 1) := fun i => ⟨output (T + i), Nat.lt_succ_of_le (hout_le i)⟩
  have hf_inj : Function.Injective f := by
    intro i k hik
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hprops := eventual_generator_properties family input output hfollows hcore (T + k) (by simp [T])
      have hprev : output (T + i) ≠ output (T + k) := by
        intro heqout
        exact hprops.2.2 ⟨⟨T + i, Nat.add_lt_add_left hlt T⟩, heqout⟩
      exact hprev (Fin.ext_iff.mp hik)
    · have hprops := eventual_generator_properties family input output hfollows hcore (T + i) (by simp [T])
      have hprev : output (T + k) ≠ output (T + i) := by
        intro heqout
        exact hprops.2.2 ⟨⟨T + k, Nat.add_lt_add_left hgt T⟩, heqout⟩
      exact hprev (Fin.ext_iff.mp hik).symm
  have hcard := Fintype.card_le_of_injective f hf_inj
  simp at hcard

 theorem core_diff_range_subset_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output := by
  intro z hz
  have hcovered := core_covered family input output hfollows hcore hz.1
  have hout : z ∈ Set.range output := hcovered.resolve_left hz.2
  rcases hout with ⟨t, ht⟩
  refine ⟨t, ht, ?_⟩
  intro s hs hin
  exact hz.2 ⟨s, hin⟩

 def inputTime (input : Stream) (z : ℕ) : ℕ :=
  if h : z ∈ Set.range input then Nat.find h else 0

 theorem inputTime_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  simp only [inputTime, dif_pos hz]
  exact Nat.find_spec hz

 theorem not_generatorFirst_has_input {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input output) :
    z ∈ Set.range input := by
  have hcovered := core_covered family input output hfollows hcore hzcore
  rcases hcovered with hin | hout
  · exact hin
  · by_contra hninput
    rcases hout with ⟨t, ht⟩
    apply hznot
    refine ⟨t, ht, ?_⟩
    intro s hs hin
    exact hninput ⟨s, hin⟩

 theorem output_before_input_ne {input output : Stream} (hinj : Function.Injective input)
    {z : ℕ} (hzrange : z ∈ Set.range input)
    (hznot : z ∉ GenLimit.GeneratorFirst input output)
    {s : ℕ} (hs : s < inputTime input z) : output s ≠ z := by
  intro hout
  apply hznot
  refine ⟨s, hout, ?_⟩
  intro r hrs hin
  have hir : r = inputTime input z := hinj (hin.trans (inputTime_spec input hzrange).symm)
  omega

 theorem inputTime_injective_on_range {input : Stream} (hinj : Function.Injective input) :
    Set.InjOn (inputTime input) (Set.range input) := by
  intro x hx y hy htime
  have hxspec := inputTime_spec input hx
  have hyspec := inputTime_spec input hy
  rw [htime] at hxspec
  exact hxspec.symm.trans hyspec

 theorem half_prefix_bound {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ Stage3Case017.informationCore family input) n +
        stabilizationTime family input + 1 := by
  let core := Stage3Case017.informationCore family input
  let wins := GenLimit.GeneratorFirst input output
  let T := stabilizationTime family input
  let P := GenLimit.PatientScope.prefixFinset core n
  let D := P.filter (fun z => z ∈ wins)
  let N := P.filter (fun z => z ∉ wins)
  let E := N.filter (fun z => inputTime input z < T)
  let A := N.filter (fun z => T ≤ inputTime input z)
  have unpackN {z : ℕ} (hz : z ∈ N) :
      z < n ∧ z ∈ core ∧ z ∉ wins := by
    have hzfilter := Finset.mem_filter.mp hz
    have hzprefix : z < n ∧ z ∈ core := by
      simpa [P, GenLimit.PatientScope.prefixFinset] using hzfilter.1
    exact ⟨hzprefix.1, hzprefix.2, hzfilter.2⟩
  have rangeN {z : ℕ} (hz : z ∈ N) : z ∈ Set.range input := by
    have hu := unpackN hz
    exact not_generatorFirst_has_input family input output hfollows hcore hu.2.1 hu.2.2
  have hE : E.card ≤ T := by
    have hmaps : Set.MapsTo (inputTime input) (↑E : Set ℕ) (↑(Finset.range T) : Set ℕ) := by
      intro z hz
      have hzE : z ∈ E := hz
      simpa [E] using (Finset.mem_filter.mp hzE).2
    have hinjtime : Set.InjOn (inputTime input) (↑E : Set ℕ) := by
      intro x hx y hy hxy
      have hxE : x ∈ E := hx
      have hyE : y ∈ E := hy
      exact inputTime_injective_on_range hinj
        (rangeN (Finset.mem_filter.mp hxE).1)
        (rangeN (Finset.mem_filter.mp hyE).1) hxy
    have hc := Finset.card_le_card_of_injOn (inputTime input) hmaps hinjtime
    simpa using hc
  have hA : A.card ≤ D.card + 1 := by
    by_cases hempty : A.Nonempty
    · obtain ⟨last, hlast, hmax⟩ := A.exists_max_image (inputTime input) hempty
      have unpackA {z : ℕ} (hz : z ∈ A) :
          z < n ∧ z ∈ core ∧ z ∉ wins ∧ T ≤ inputTime input z := by
        have hn : z ∈ N := (Finset.mem_filter.mp hz).1
        have hu := unpackN hn
        exact ⟨hu.1, hu.2.1, hu.2.2, (Finset.mem_filter.mp hz).2⟩
      have hlastU := unpackA hlast
      have hlastRange : last ∈ Set.range input := rangeN (Finset.mem_filter.mp hlast).1
      let partner : ℕ → ℕ := fun z => output (inputTime input z)
      have hmaps : Set.MapsTo partner (↑(A.erase last) : Set ℕ) (↑D : Set ℕ) := by
        intro z hz
        have hzA : z ∈ A := (Finset.mem_erase.mp hz).2
        have hzne : z ≠ last := (Finset.mem_erase.mp hz).1
        have hzU := unpackA hzA
        have hzRange : z ∈ Set.range input := rangeN (Finset.mem_filter.mp hzA).1
        have htimele := hmax z hzA
        have htimelt : inputTime input z < inputTime input last := by
          apply lt_of_le_of_ne htimele
          intro heq
          apply hzne
          exact inputTime_injective_on_range hinj hzRange hlastRange heq
        have htprops := eventual_generator_properties family input output hfollows hcore
          (inputTime input z) hzU.2.2.2
        have heqcore := currentCore_eq_informationCore family input hzU.2.2.2
        have hlastAvail : last ∈ available family
            (fun k : Fin (inputTime input z + 1) => input k)
            (fun k : Fin (inputTime input z) => output k) := by
          refine ⟨?_, ?_⟩
          · rw [heqcore]
            exact hlastU.2.1
          · intro hu
            rcases hu with hu | hu
            · rcases hu with ⟨k, hk⟩
              have hkt : (k : ℕ) = inputTime input last :=
                hinj (hk.trans (inputTime_spec input hlastRange).symm)
              have hkz : (k : ℕ) ≤ inputTime input z := Nat.lt_succ_iff.mp k.isLt
              omega
            · rcases hu with ⟨k, hk⟩
              exact output_before_input_ne hinj hlastRange hlastU.2.2.1
                (lt_trans k.isLt htimelt) hk
        have hnonempty : (available family
            (fun k : Fin (inputTime input z + 1) => input k)
            (fun k : Fin (inputTime input z) => output k)).Nonempty := ⟨last, hlastAvail⟩
        have houtle : output (inputTime input z) ≤ last := by
          rw [hfollows (inputTime input z)]
          exact familyGenerator_min family _ _ hnonempty hlastAvail
        have houtlt : output (inputTime input z) < n := lt_of_le_of_lt houtle hlastU.1
        have houtwin : output (inputTime input z) ∈ wins := by
          refine ⟨inputTime input z, rfl, ?_⟩
          intro s hs hin
          have hslt : s < inputTime input z + 1 := Nat.lt_succ_of_le hs
          exact htprops.2.1 ⟨⟨s, hslt⟩, hin⟩
        have houtP : output (inputTime input z) ∈ P := by
          simp only [P, GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
          exact ⟨houtlt, htprops.1⟩
        exact Finset.mem_filter.mpr ⟨houtP, houtwin⟩
      have hpartnerinj : Set.InjOn partner (↑(A.erase last) : Set ℕ) := by
        intro x hx y hy hxy
        have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
        have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
        have hxU := unpackA hxA
        have hyU := unpackA hyA
        have hxRange : x ∈ Set.range input := rangeN (Finset.mem_filter.mp hxA).1
        have hyRange : y ∈ Set.range input := rangeN (Finset.mem_filter.mp hyA).1
        by_contra hne
        have htimene : inputTime input x ≠ inputTime input y := by
          intro ht
          exact hne (inputTime_injective_on_range hinj hxRange hyRange ht)
        rcases lt_or_gt_of_ne htimene with hlt | hgt
        · have hp := eventual_generator_properties family input output hfollows hcore
            (inputTime input y) hyU.2.2.2
          exact hp.2.2 ⟨⟨inputTime input x, hlt⟩, hxy⟩
        · have hp := eventual_generator_properties family input output hfollows hcore
            (inputTime input x) hxU.2.2.2
          exact hp.2.2 ⟨⟨inputTime input y, hgt⟩, hxy.symm⟩
      have hcard := Finset.card_le_card_of_injOn partner hmaps hpartnerinj
      have herase := Finset.card_erase_add_one hlast
      omega
    · have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simp [this]
  have hDN : D.card + N.card = P.card := by
    simpa [D, N] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := P)
        (p := fun z => z ∈ wins))
  have hEA : E.card + A.card = N.card := by
    simpa [E, A, Nat.not_lt] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := N)
        (p := fun z => inputTime input z < T))
  have hDcount : D.card = GenLimit.PatientScope.prefixCount (wins ∩ core) n := by
    congr 1
    ext z
    simp [D, P, GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
      wins, core, and_comm, and_left_comm, and_assoc]
  change P.card ≤ 2 * GenLimit.PatientScope.prefixCount (wins ∩ core) n + T + 1
  rw [← hDcount]
  omega

 theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Filter.Tendsto (GenLimit.PatientScope.prefixCount K) Filter.atTop Filter.atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (r := (1 : ℕ)) (by omega)] at hK
  convert hK using 1
  funext n
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hmem : k ∈ K <;> simp [hmem, Set.indicator]

 theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩


 theorem half_relativeLowerDensity {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollows : Stage3Case017.Follows (familyGenerator family) input output)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {K : Set ℕ} (hKinf : K.Infinite)
    (hcoreK : Stage3Case017.informationCore family input ⊆ K) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ K) K := by
  let core := Stage3Case017.informationCore family input
  let wins := GenLimit.GeneratorFirst input output
  let T := stabilizationTime family input
  let countK : ℕ → ℕ := GenLimit.PatientScope.prefixCount K
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount core n : ℝ) / (countK n : ℝ)
  let b : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (wins ∩ K) n : ℝ) / (countK n : ℝ)
  let err : ℕ → ℝ := fun n => ((T + 1 : ℕ) : ℝ) / 2 / (countK n : ℝ)
  have haBound : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) Filter.atTop a := by
    apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    filter_upwards with n
    dsimp [a]
    positivity
  have hbBound : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) Filter.atTop b := by
    apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    filter_upwards with n
    dsimp [b]
    positivity
  have hbCob : Filter.IsCoboundedUnder (fun x y : ℝ => x ≥ y) Filter.atTop b := by
    apply IsBoundedUnder.isCoboundedUnder_ge
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    filter_upwards with n
    have hc := prefixCount_mono (show wins ∩ K ⊆ K by intro z hz; exact hz.2) n
    dsimp [b, countK]
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hw : GenLimit.PatientScope.prefixCount (wins ∩ K) n = 0 :=
        Nat.eq_zero_of_le_zero (hk ▸ hc)
      simp [hk, hw]
    · rw [div_le_one₀ (by positivity)]
      exact_mod_cast hc
  have hcount : Filter.Tendsto countK Filter.atTop Filter.atTop := by
    exact prefixCount_tendsto_atTop hKinf
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    have hcast : Filter.Tendsto (fun n => (countK n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hcount
    simpa [err] using hcast.const_div_atTop (((T + 1 : ℕ) : ℝ) / 2)
  change (1 / 2 : ℝ) * Filter.liminf a Filter.atTop ≤ Filter.liminf b Filter.atTop
  apply (Filter.le_liminf_iff hbCob hbBound).2
  intro y hy
  let L := Filter.liminf a Filter.atTop
  let gap := (1 / 2 : ℝ) * L - y
  have hgap : 0 < gap := by
    dsimp [gap, L]
    linarith
  have haevent : ∀ᶠ n in Filter.atTop, L - gap < a n := by
    apply Filter.eventually_lt_of_lt_liminf (hu := haBound)
    exact sub_lt_self L hgap
  have herrevent : ∀ᶠ n in Filter.atTop, err n < gap / 2 :=
    herr.eventually_lt_const (half_pos hgap)
  have hkpos : ∀ᶠ n in Filter.atTop, 0 < countK n :=
    hcount.eventually_gt_atTop 0
  filter_upwards [haevent, herrevent, hkpos] with n han herrn hkn
  have hdc : GenLimit.PatientScope.prefixCount (wins ∩ core) n ≤
      GenLimit.PatientScope.prefixCount (wins ∩ K) n := by
    apply prefixCount_mono
    intro z hz
    exact ⟨hz.1, hcoreK hz.2⟩
  have hnat : GenLimit.PatientScope.prefixCount core n ≤
      2 * GenLimit.PatientScope.prefixCount (wins ∩ K) n + T + 1 := by
    exact (half_prefix_bound family input output hinj hfollows hcore n).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hdc) (T + 1))
  have hpoint : (1 / 2 : ℝ) * a n - err n ≤ b n := by
    have hkreal : 0 < (countK n : ℝ) := by exact_mod_cast hkn
    have hreal : (GenLimit.PatientScope.prefixCount core n : ℝ) ≤
        2 * (GenLimit.PatientScope.prefixCount (wins ∩ K) n : ℝ) + (T + 1 : ℕ) := by
      exact_mod_cast hnat
    dsimp [a, b, err]
    calc
      (1 / 2 : ℝ) *
            ((GenLimit.PatientScope.prefixCount core n : ℝ) / (countK n : ℝ)) -
          ((T + 1 : ℕ) : ℝ) / 2 / (countK n : ℝ) =
          (((1 / 2 : ℝ) * GenLimit.PatientScope.prefixCount core n -
              ((T + 1 : ℕ) : ℝ) / 2) / (countK n : ℝ)) := by ring
      _ ≤ (GenLimit.PatientScope.prefixCount (wins ∩ K) n : ℝ) / (countK n : ℝ) := by
          apply div_le_div_of_nonneg_right _ hkreal.le
          linarith
  calc
    y = (1 / 2 : ℝ) * L - gap := by dsimp [gap]; ring
    _ < (1 / 2 : ℝ) * a n - gap / 2 := by linarith
    _ < (1 / 2 : ℝ) * a n - err n := by linarith
    _ ≤ b n := hpoint
 theorem relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
  · filter_upwards with n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_mono hAB n
    · positivity
  · apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    filter_upwards with n
    positivity
  · apply IsBoundedUnder.isCoboundedUnder_ge
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    filter_upwards with n
    have hc : GenLimit.PatientScope.prefixCount B n ≤
        GenLimit.PatientScope.prefixCount K n := prefixCount_mono hBK n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hb : GenLimit.PatientScope.prefixCount B n = 0 := Nat.eq_zero_of_le_zero (hk ▸ hc)
      simp [hk, hb]
    · rw [div_le_one₀ (by positivity)]
      exact_mod_cast hc

end

end Stage3Case017Proof

open Stage3Case017Proof

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨familyGenerator family, ?_⟩
  intro input hinj hexists hcore
  let output := trajectory (familyGenerator family) input
  refine ⟨output, trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨eventual_novel family input output (trajectory_follows _ _) hcore j hj, ?_⟩
  have hcoreTarget : Stage3Case017.informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hj
  have hhalf := half_relativeLowerDensity family input output hinj
    (trajectory_follows _ _) hcore (hinfinite j) hcoreTarget
  have hmissing : GenLimit.PatientScope.relativeLowerDensity
      (Stage3Case017.informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply relativeLowerDensity_mono
    · intro z hz
      exact ⟨core_diff_range_subset_generatorFirst family input output
        (trajectory_follows _ _) hcore hz, hcoreTarget hz.1⟩
    · intro z hz
      exact hz.2
  exact max_le hhalf hmissing

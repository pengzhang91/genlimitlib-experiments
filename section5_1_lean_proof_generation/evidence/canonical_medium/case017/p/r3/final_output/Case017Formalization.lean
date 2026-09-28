import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Case017

open Stage3Case017

noncomputable def prefixSet (input : Stream) (t : ℕ) : Set ℕ :=
  Set.range (fun i : Fin (t + 1) => input i)

noncomputable def oldOutputSet (output : Fin t → ℕ) : Set ℕ := Set.range output

noncomputable def currentCore {m : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

noncomputable def available {m : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : Set ℕ :=
  currentCore family input \ (Set.range input ∪ Set.range output)

noncomputable def fallback (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : Set ℕ :=
  (Set.range input ∪ Set.range output)ᶜ

noncomputable def online {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun _ input output =>
    if h : (available family input output).Nonempty then sInf (available family input output)
    else sInf (fallback input output)

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  Nat.strongRec (motive := fun _ => ℕ)
    (fun n rec => gen n (fun i => input i) (fun i => rec i i.isLt)) t

@[simp] theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run, Nat.strongRec_eq]
  apply congrArg (gen t (fun i => input i))
  funext i
  rfl

 theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

 theorem fallback_nonempty (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    (fallback input output).Nonempty := by
  have hf : (Set.range input ∪ Set.range output).Finite :=
    (Set.finite_range input).union (Set.finite_range output)
  obtain ⟨z, hz⟩ := hf.exists_not_mem
  exact ⟨z, hz⟩

 theorem online_fresh {m : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    online family t input output ∉ Set.range input ∪ Set.range output := by
  classical
  simp only [online]
  split_ifs with h
  · exact (Nat.sInf_mem h).2
  · exact Nat.sInf_mem (fallback_nonempty input output)

 theorem run_fresh {m : ℕ} (family : Fin m → Language) (input : Stream) (t : ℕ) :
    run (online family) input t ∉
      Set.range (fun i : Fin (t + 1) => input i) ∪
      Set.range (fun i : Fin t => run (online family) input i) := by
  rw [run_eq]
  exact online_fresh family _ _

 theorem run_not_input {m : ℕ} (family : Fin m → Language) (input : Stream)
    {s t : ℕ} (hs : s ≤ t) : run (online family) input t ≠ input s := by
  intro h
  apply run_fresh family input t
  exact Or.inl ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, h.symm⟩

 theorem run_injective {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Function.Injective (run (online family) input) := by
  intro s t h
  rcases lt_trichotomy s t with hst | hst | hst
  · exfalso
    apply run_fresh family input t
    exact Or.inr ⟨⟨s, hst⟩, h⟩
  · exact hst
  · exfalso
    apply run_fresh family input s
    exact Or.inr ⟨⟨t, hst⟩, h.symm⟩


noncomputable def witnessTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Classical.choose (by
      obtain ⟨z, ⟨n, rfl⟩, hz⟩ := Set.not_subset.mp h
      exact ⟨n, hz⟩)

noncomputable def stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (witnessTime family input)

 theorem witness_spec {m : ℕ} (family : Fin m → Language) (input : Stream)
    (j : Fin m) (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (witnessTime family input j) ∉ family j := by
  rw [witnessTime, dif_neg h]
  exact Classical.choose_spec (by
    obtain ⟨z, ⟨n, rfl⟩, hz⟩ := Set.not_subset.mp h
    exact ⟨n, hz⟩)

 theorem witness_le_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    witnessTime family input j ≤ stableTime family input := by
  exact Finset.le_sup (Finset.mem_univ j)

 theorem prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) {t : ℕ} (ht : stableTime family input ≤ t) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp
    by_contra hstream
    have hw := witness_spec family input j hstream
    have hle : witnessTime family input j ≤ t :=
      (witness_le_stable family input j).trans ht
    exact hw (hp ⟨witnessTime family input j, Nat.lt_succ_iff.mpr hle⟩)
  · intro hs i
    exact hs ⟨i, rfl⟩

 theorem currentCore_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input j ht).2 hj)
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input j ht).1 hj)

 theorem available_nonempty {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    (available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (online family) input i)).Nonempty := by
  rw [available, currentCore_eq family input ht]
  have hfin :
      (Set.range (fun i : Fin (t + 1) => input i) ∪
        Set.range (fun i : Fin t => run (online family) input i)).Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  have hd : (informationCore family input \
      (Set.range (fun i : Fin (t + 1) => input i) ∪
        Set.range (fun i : Fin t => run (online family) input i))).Infinite :=
    hcore.diff hfin
  exact hd.nonempty

 theorem run_in_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    run (online family) input t ∈ informationCore family input := by
  rw [run_eq]
  have hav := available_nonempty family input hcore ht
  simp only [online, dif_pos hav]
  have hm := Nat.sInf_mem hav
  rw [← currentCore_eq family input ht]
  exact (Nat.sInf_mem hav).1

 theorem run_le_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t z : ℕ} (ht : stableTime family input ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzin : z ∉ Set.range (fun i : Fin (t + 1) => input i))
    (hzout : z ∉ Set.range (fun i : Fin t => run (online family) input i)) :
    run (online family) input t ≤ z := by
  rw [run_eq]
  have hav := available_nonempty family input hcore ht
  simp only [online, dif_pos hav]
  apply Nat.sInf_le
  rw [available, currentCore_eq family input ht]
  exact ⟨hzcore, fun h => h.elim hzin hzout⟩

 theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run (online family) input) := by
  intro z hz
  by_contra h
  have hzin : z ∉ Set.range input := fun hz' => h (Or.inl hz')
  have hzout : z ∉ Set.range (run (online family) input) := fun hz' => h (Or.inr hz')
  let T := stableTime family input
  let f : Fin (z + 2) → Fin (z + 1) := fun k =>
    ⟨run (online family) input (T + k), Nat.lt_succ_iff.mpr (by
      apply run_le_available family input hcore
      · omega
      · exact hz
      · intro hr
        obtain ⟨i, hi⟩ := hr
        exact hzin ⟨i, hi⟩
      · intro hr
        obtain ⟨i, hi⟩ := hr
        exact hzout ⟨i, hi⟩)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hout : run (online family) input (T + a) =
        run (online family) input (T + b) := congrArg Fin.val hab
    have htime := run_injective family input hout
    omega
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

 theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (online family) input) := by
  intro z hz
  obtain ⟨t, ht⟩ := (core_covered family input hcore hz.1).resolve_left hz.2
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩

 theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

 theorem relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf (hu := ?_) (hv := ?_)
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_mono hAB n
    · positivity
  · apply Filter.isBoundedUnder_of_eventually_ge
    filter_upwards [] with n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hle := prefixCount_mono hBK n
      have hbzero : GenLimit.PatientScope.prefixCount B n = 0 := by omega
      simp [hzero, hbzero]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono hBK n

 theorem novel_generation {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run (online family) input) (family j) := by
  refine ⟨stableTime family input, fun t ht => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (run_in_core family input hcore ht) j hj
  · intro hin
    rw [GenLimit.sample] at hin
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hin
    apply run_fresh family input t
    exact Or.inl ⟨⟨s, by simpa using hs⟩, heq⟩
  · intro s hs heq
    exact (Nat.ne_of_lt hs) (run_injective family input heq)


noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

 theorem input_inputTime (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  rw [inputTime, dif_pos hz]
  exact Nat.find_spec hz

 theorem inputTime_injective (input : Stream) (hinj : Function.Injective input) :
    Set.InjOn (inputTime input) (Set.range input) := by
  intro z hz w hw heq
  rw [← input_inputTime input hz, ← input_inputTime input hw, heq]

noncomputable def badPrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun z =>
    z ∈ informationCore family input ∧
      z ∉ GenLimit.GeneratorFirst input (run (online family) input))

 theorem mem_badPrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) {z n : ℕ} :
    z ∈ badPrefix family input n ↔ z < n ∧
      z ∈ informationCore family input ∧
      z ∉ GenLimit.GeneratorFirst input (run (online family) input) := by
  classical
  simp [badPrefix]

noncomputable def lateBad {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ :=
  (badPrefix family input n).filter
    (fun z => stableTime family input ≤ inputTime input z)

noncomputable def exceptional {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : ℕ := by
  classical
  exact if h : (lateBad family input n).Nonempty then
    Classical.choose (Finset.exists_max_image (lateBad family input n)
      (inputTime input) h)
  else 0

 theorem exceptional_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) (h : (lateBad family input n).Nonempty) :
    exceptional family input n ∈ lateBad family input n := by
  rw [exceptional, dif_pos h]
  exact (Classical.choose_spec
    (Finset.exists_max_image (lateBad family input n) (inputTime input) h)).1

 theorem inputTime_le_exceptional {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) (h : (lateBad family input n).Nonempty)
    {z : ℕ} (hz : z ∈ lateBad family input n) :
    inputTime input z ≤ inputTime input (exceptional family input n) := by
  rw [exceptional, dif_pos h]
  exact (Classical.choose_spec
    (Finset.exists_max_image (lateBad family input n) (inputTime input) h)).2 z hz

 theorem bad_mem_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z n : ℕ} (hz : z ∈ badPrefix family input n) : z ∈ Set.range input := by
  classical
  have hz := (mem_badPrefix family input).1 hz
  by_contra hzin
  exact hz.2.2 (core_diff_range_subset_generatorFirst family input hcore ⟨hz.2.1, hzin⟩)

 theorem paired_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z n : ℕ} (hz : z ∈ lateBad family input n) :
    run (online family) input (inputTime input z) ∈
      GenLimit.GeneratorFirst input (run (online family) input) := by
  have hzbad : z ∈ badPrefix family input n := (Finset.mem_filter.mp hz).1
  have hzin := bad_mem_input family input hcore hzbad
  let q := inputTime input z
  refine ⟨q, rfl, ?_⟩
  intro s hs heq
  have hfresh := run_fresh family input q
  apply hfresh
  exact Or.inl ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, heq⟩

 theorem paired_lt_prefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {z w n : ℕ} (hz : z ∈ lateBad family input n)
    (hw : w ∈ lateBad family input n)
    (htime : inputTime input z < inputTime input w) :
    run (online family) input (inputTime input z) < n := by
  classical
  have hzbad : z ∈ badPrefix family input n := (Finset.mem_filter.mp hz).1
  have hwbad : w ∈ badPrefix family input n := (Finset.mem_filter.mp hw).1
  have hwdata := (mem_badPrefix family input).1 hwbad
  have hwcore : w ∈ informationCore family input := hwdata.2.1
  have hwlt : w < n := by simpa [GenLimit.PatientScope.prefixFinset] using hwdata.1
  have hwin := bad_mem_input family input hcore hwbad
  have hwprefix : w ∉ Set.range (fun i : Fin (inputTime input z + 1) => input i) := by
    rintro ⟨i, hi⟩
    have hiq : inputTime input w = i := by
      apply hinj
      rw [input_inputTime input hwin]
      exact hi.symm
    omega
  have hwout : w ∉ Set.range
      (fun i : Fin (inputTime input z) => run (online family) input i) := by
    rintro ⟨i, hi⟩
    have hwgf : w ∈ GenLimit.GeneratorFirst input (run (online family) input) := by
      refine ⟨i, hi, ?_⟩
      intro s hs heq
      have hslt : s < inputTime input w := lt_of_le_of_lt hs (by omega)
      have := hinj (show input s = input (inputTime input w) by
        rw [input_inputTime input hwin]
        exact heq)
      omega
    exact hwdata.2.2 hwgf
  have hle := run_le_available family input hcore
    (Finset.mem_filter.mp hz).2 hwcore hwprefix hwout
  omega


noncomputable def goodPrefix (input output : Stream) (K : Language) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun z => z ∈ GenLimit.GeneratorFirst input output ∩ K)

 theorem mem_goodPrefix (input output : Stream) (K : Language) {z n : ℕ} :
    z ∈ goodPrefix input output K n ↔
      z < n ∧ z ∈ GenLimit.GeneratorFirst input output ∧ z ∈ K := by
  classical
  simp [goodPrefix]

 theorem lateBad_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    (lateBad family input n).card ≤
      (goodPrefix input (run (online family) input) (family j) n).card + 1 := by
  classical
  by_cases hempty : (lateBad family input n).Nonempty
  · let e := exceptional family input n
    let f : ℕ → ℕ := fun z => run (online family) input (inputTime input z)
    have he : e ∈ lateBad family input n := exceptional_mem family input n hempty
    have hmap : Set.MapsTo f ↑((lateBad family input n).erase e)
        ↑(goodPrefix input (run (online family) input) (family j) n) := by
      intro z hz
      have hzlate : z ∈ lateBad family input n := (Finset.mem_erase.mp hz).2
      have hzne : z ≠ e := (Finset.mem_erase.mp hz).1
      have hzbad : z ∈ badPrefix family input n := (Finset.mem_filter.mp hzlate).1
      have hebad : e ∈ badPrefix family input n := (Finset.mem_filter.mp he).1
      have hzin := bad_mem_input family input hcore hzbad
      have hein := bad_mem_input family input hcore hebad
      have hle := inputTime_le_exceptional family input n hempty hzlate
      have hneq : inputTime input z ≠ inputTime input e := by
        intro hq
        exact hzne (inputTime_injective input hinj hzin hein hq)
      have hlt : inputTime input z < inputTime input e := lt_of_le_of_ne hle hneq
      have hfn : f z < n := paired_lt_prefix family input hinj hcore hzlate he hlt
      have hgf := paired_generatorFirst family input hcore hzlate
      have hK : f z ∈ family j :=
        (run_in_core family input hcore (Finset.mem_filter.mp hzlate).2) j hj
      exact (mem_goodPrefix input (run (online family) input) (family j)).2
        ⟨hfn, hgf, hK⟩
    have hinjf : Set.InjOn f ↑((lateBad family input n).erase e) := by
      intro z hz w hw heq
      have htime := run_injective family input heq
      have hzlate := (Finset.mem_erase.mp hz).2
      have hwlate := (Finset.mem_erase.mp hw).2
      have hzin := bad_mem_input family input hcore (Finset.mem_filter.mp hzlate).1
      have hwin := bad_mem_input family input hcore (Finset.mem_filter.mp hwlate).1
      exact inputTime_injective input hinj hzin hwin htime
    have hc := Finset.card_le_card_of_injOn f hmap hinjf
    have herase := Finset.card_erase_add_one he
    omega
  · have hzero : (lateBad family input n).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hempty)
    omega

 theorem earlyBad_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    ((badPrefix family input n).filter
      (fun z => inputTime input z < stableTime family input)).card ≤
      stableTime family input := by
  classical
  let early := (badPrefix family input n).filter
    (fun z => inputTime input z < stableTime family input)
  have hmap : Set.MapsTo (inputTime input) (↑early : Set ℕ)
      (↑(Finset.range (stableTime family input)) : Set ℕ) := by
    intro z hz
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
  have hinjtime : Set.InjOn (inputTime input) (↑early : Set ℕ) := by
    intro z hz w hw heq
    have hzin := bad_mem_input family input hcore (Finset.mem_filter.mp hz).1
    have hwin := bad_mem_input family input hcore (Finset.mem_filter.mp hw).1
    exact inputTime_injective input hinj hzin hwin heq
  have hc := Finset.card_le_card_of_injOn (inputTime input) hmap hinjtime
  simpa [early] using hc

 theorem badPrefix_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    (badPrefix family input n).card ≤
      (goodPrefix input (run (online family) input) (family j) n).card +
        stableTime family input + 1 := by
  classical
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := badPrefix family input n)
    (fun z => stableTime family input ≤ inputTime input z)
  have heq : {z ∈ badPrefix family input n |
      ¬stableTime family input ≤ inputTime input z} =
      (badPrefix family input n).filter
        (fun z => inputTime input z < stableTime family input) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hnot⟩
      exact ⟨hz, Nat.lt_of_not_ge hnot⟩
    · rintro ⟨hz, hlt⟩
      exact ⟨hz, Nat.not_le_of_lt hlt⟩
  have hearly := earlyBad_card_le family input hinj hcore n
  have hlate := lateBad_card_le family input hinj hcore j hj n
  change (lateBad family input n).card + _ = _ at hpart
  rw [heq] at hpart
  omega

 theorem core_prefix_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j) n +
      stableTime family input + 1 := by
  classical
  let coreFin := (Finset.range n).filter (fun z => z ∈ informationCore family input)
  let goodFin := goodPrefix input (run (online family) input) (family j) n
  let badFin := badPrefix family input n
  have hcover : coreFin ⊆ goodFin ∪ badFin := by
    intro z hz
    have hz' : z < n ∧ z ∈ informationCore family input := by
      simpa [coreFin] using hz
    by_cases hgf : z ∈ GenLimit.GeneratorFirst input (run (online family) input)
    · apply Finset.mem_union_left
      exact (mem_goodPrefix input (run (online family) input) (family j)).2
        ⟨hz'.1, hgf, hz'.2 j hj⟩
    · apply Finset.mem_union_right
      exact (mem_badPrefix family input).2 ⟨hz'.1, hz'.2, hgf⟩
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le goodFin badFin
  have hb := badPrefix_card_le family input hinj hcore j hj n
  change coreFin.card ≤ _ at hc
  change badFin.card ≤ goodFin.card + stableTime family input + 1 at hb
  have hcoreeq : coreFin.card = GenLimit.PatientScope.prefixCount
      (informationCore family input) n := by rfl
  have hgoodeq : goodFin.card = GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j) n := by
    apply congrArg Finset.card
    ext z
    simp [goodFin, mem_goodPrefix, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  omega


 theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq b
  obtain ⟨M, hM⟩ := s.bddAbove
  apply eventually_atTop.2
  refine ⟨M + 1, fun n hn => ?_⟩
  have hsub : s ⊆ GenLimit.PatientScope.prefixFinset K n := by
    intro z hz
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (hM hz) (Nat.lt_of_succ_le hn), hsK hz⟩
  have hc := Finset.card_le_card hsub
  simpa [GenLimit.PatientScope.prefixCount, hscard] using hc

 theorem ratio_lower_bounded (A K : Set ℕ) :
    IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop
      (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) := by
  apply Filter.isBoundedUnder_of_eventually_ge
  filter_upwards [] with n
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

 theorem ratio_upper_bounded {A K : Set ℕ} (hAK : A ⊆ K) :
    IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) atTop
      (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) := by
  apply Filter.isBoundedUnder_of_eventually_le (a := (1 : ℝ))
  filter_upwards [] with n
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have hle := prefixCount_mono hAK n
    have hazero : GenLimit.PatientScope.prefixCount A n = 0 := by omega
    simp [hzero, hazero]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono hAK n

set_option maxHeartbeats 800000 in
 theorem half_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j)
        (family j) := by
  let C : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let D : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let E : ℕ → ℝ := fun n =>
    ((stableTime family input + 1 : ℕ) : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  have hpoint : ∀ n, (1 / 2 : ℝ) * C n ≤ E n + D n := by
    intro n
    have hc := core_prefix_count_le family input hinj hcore j hj n
    by_cases hzero : GenLimit.PatientScope.prefixCount (family j) n = 0
    · have hcoreK : informationCore family input ⊆ family j := fun z hz => hz j hj
      have hCK := prefixCount_mono hcoreK n
      have hDK := prefixCount_mono
        (A := GenLimit.GeneratorFirst input (run (online family) input) ∩ family j)
        (B := family j) Set.inter_subset_right n
      have hczero : GenLimit.PatientScope.prefixCount (informationCore family input) n = 0 := by omega
      have hdzero : GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j) n = 0 := by omega
      simp [C, D, E, hzero, hczero, hdzero]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount (family j) n := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      have hcr : (GenLimit.PatientScope.prefixCount
          (informationCore family input) n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j) n : ℝ) +
          ((stableTime family input + 1 : ℕ) : ℝ) := by
        exact_mod_cast hc
      dsimp [C, D, E]
      field_simp [ne_of_gt hpos]
      linarith
  have hEtend : Tendsto E atTop (𝓝 0) := by
    exact (prefixCount_tendsto_atTop hK).const_div_atTop
      (((stableTime family input + 1 : ℕ) : ℝ))
  have hEupper : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) atTop E := by
    apply Filter.isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    exact hEtend.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  have hElower : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop E := by
    apply Filter.isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    filter_upwards [] with n
    dsimp [E]
    positivity
  have hDlower : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop D := by
    exact ratio_lower_bounded
      (GenLimit.GeneratorFirst input (run (online family) input) ∩ family j) (family j)
  have hmono : liminf (fun n => (1 / 2 : ℝ) * C n) atTop ≤
      liminf (fun n => E n + D n) atTop := by
    apply Filter.liminf_le_liminf
    · exact Filter.Eventually.of_forall hpoint
    · apply Filter.isBoundedUnder_of_eventually_ge
      filter_upwards [] with n
      exact mul_nonneg (by norm_num) (by dsimp [C]; positivity)
    · exact Filter.isCoboundedUnder_ge_add hEupper
        ((ratio_upper_bounded (A :=
          GenLimit.GeneratorFirst input (run (online family) input) ∩ family j)
          (K := family j) Set.inter_subset_right).isCoboundedUnder_ge)
  have hscale : (1 / 2 : ℝ) * liminf C atTop ≤
      liminf (fun n => (1 / 2 : ℝ) * C n) atTop := by
    have h := le_liminf_mul (f := atTop)
      (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := C)
      (Filter.Eventually.of_forall fun _ => by norm_num)
      (Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun _ => le_rfl))
      (Filter.Eventually.of_forall fun n => by dsimp [C]; positivity)
      ((ratio_upper_bounded (A := informationCore family input) (K := family j)
        (fun z hz => hz j hj)).isCoboundedUnder_ge)
    simpa [liminf_const, Pi.mul_apply] using h
  have hadd : liminf (fun n => E n + D n) atTop ≤ liminf D atTop := by
    have h := liminf_add_le (f := atTop) (u := E) (v := D)
      hElower hEupper hDlower
      ((ratio_upper_bounded (A :=
        GenLimit.GeneratorFirst input (run (online family) input) ∩ family j)
        (K := family j) Set.inter_subset_right).isCoboundedUnder_ge)
    rw [hEtend.limsup_eq] at h
    simpa using h
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * liminf C atTop ≤ liminf D atTop
  exact hscale.trans (hmono.trans hadd)


end Case017

open Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinf
  classical
  refine ⟨online family, ?_⟩
  intro input hinj hpartial hcore
  refine ⟨run (online family) input, run_follows _ _, ?_⟩
  intro j hj
  refine ⟨novel_generation family input hcore j hj, ?_⟩
  apply max_le
  · exact half_density family input hinj hcore j hj (hinf j)
  · apply relativeLowerDensity_mono
    · intro z hz
      exact ⟨core_diff_range_subset_generatorFirst family input hcore hz,
        hz.1 j hj⟩
    · exact Set.inter_subset_right

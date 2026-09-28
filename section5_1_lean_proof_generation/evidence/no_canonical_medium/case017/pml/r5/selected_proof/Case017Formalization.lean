import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

/-- The family members consistent with the observations through round `t`. -/
def compatibleAt {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

/-- Points lying in every currently compatible family member. -/
def currentCore {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, compatibleAt family t xs j → z ∈ family j}

/-- A point is available if it is in the current core and has not occurred in
    either finite history. -/
def available {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ currentCore family t xs ∧
    (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)

noncomputable def leastFresh {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys => if h : ∃ z, available family t xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by exact i.isLt

@[simp] theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

 theorem leastFresh_spec {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family t xs ys z) :
    available family t xs ys (leastFresh family t xs ys) := by
  classical
  simp only [leastFresh, dif_pos h]
  exact Nat.find_spec h

 theorem compatibleAt_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      compatibleAt family t (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      (compatibleAt family t (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases h : GenLimit.Generic.StreamIn input (family j)
    · exact ⟨0, fun t _ => ⟨fun _ => h, fun _ i => h ⟨i, rfl⟩⟩⟩
    · simp only [GenLimit.Generic.StreamIn, Set.range_subset_iff] at h
      push_neg at h
      obtain ⟨n, hn⟩ := h
      refine ⟨n, fun t hnt => ⟨?_, fun hfull => False.elim (hn (hfull ⟨n, rfl⟩))⟩⟩
      intro hcomp
      exact False.elim (hn (hcomp ⟨n, Nat.lt_succ_iff.mpr hnt⟩))
  choose bound hbound using hj
  let T := Finset.univ.sup bound
  refine ⟨T, ?_⟩
  intro t ht j
  apply hbound j t
  exact le_trans (Finset.le_sup (s := Finset.univ) (f := bound) (Finset.mem_univ j)) ht

 theorem currentCore_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ} (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) :
    currentCore family t (fun i => input i) = informationCore family input := by
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor <;> intro hz j hj
  · exact hz j ((hstabilizes t ht j).2 hj)
  · exact hz j ((hstabilizes t ht j).1 hj)

 theorem exists_available {m : ℕ} (family : Fin m → Language)
    (input output : Stream) {T t : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) (hcore : (informationCore family input).Infinite) :
    ∃ z, available family t (fun i => input i) (fun i => output i) z := by
  let forbidden : Set ℕ := Set.range (fun i : Fin (t + 1) => input i) ∪
    Set.range (fun i : Fin t => output i)
  have hfinite : forbidden.Finite := Set.Finite.union (Set.finite_range _) (Set.finite_range _)
  obtain ⟨z, hzcore, hznot⟩ := Set.Infinite.exists_not_mem_finset hcore hfinite.toFinset
  refine ⟨z, ?_⟩
  have hzforbidden : z ∉ forbidden := by simpa using hznot
  refine ⟨?_, ?_, ?_⟩
  · rw [currentCore_eq family input hstabilizes ht]
    exact hzcore
  · intro i hi
    exact hzforbidden (Or.inl ⟨i, hi⟩)
  · intro i hi
    exact hzforbidden (Or.inr ⟨i, hi⟩)


theorem trajectory_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) (hcore : (informationCore family input).Infinite) :
    available family t (fun i => input i)
      (fun i => trajectory (leastFresh family) input i)
      (trajectory (leastFresh family) input t) := by
  rw [trajectory]
  apply leastFresh_spec
  exact exists_available family input (trajectory (leastFresh family) input)
    hstabilizes ht hcore

 theorem trajectory_minimal {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t z : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) (hcore : (informationCore family input).Infinite)
    (hz : available family t (fun i => input i)
      (fun i => trajectory (leastFresh family) input i) z) :
    trajectory (leastFresh family) input t ≤ z := by
  rw [trajectory]
  classical
  let hex := exists_available family input
    (trajectory (leastFresh family) input) hstabilizes ht hcore
  change (if h : ∃ z, available family t (fun i => input i)
    (fun i => trajectory (leastFresh family) input i) z then Nat.find h else 0) ≤ z
  rw [dif_pos hex]
  exact Nat.find_min' hex hz

 theorem core_eventually_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    ∀ z ∈ informationCore family input,
      ∃ t, input t = z ∨ trajectory (leastFresh family) input t = z := by
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
      intro hzcore
      classical
      have hsmall : ∀ q, q < z → q ∈ informationCore family input →
          ∃ t, input t = q ∨ trajectory (leastFresh family) input t = q := by
        intro q hq hzq
        exact ih q hq hzq
      let announceTime : ℕ → ℕ := fun q =>
        if hq : q < z ∧ q ∈ informationCore family input then
          Nat.find (hsmall q hq.1 hq.2)
        else 0
      let base := max T ((Finset.range z).sup announceTime)
      let r := base + 1
      by_cases hinput : ∃ s, s ≤ r ∧ input s = z
      · obtain ⟨s, -, hs⟩ := hinput
        exact ⟨s, Or.inl hs⟩
      by_cases houtput : ∃ s, s < r ∧
          trajectory (leastFresh family) input s = z
      · obtain ⟨s, -, hs⟩ := houtput
        exact ⟨s, Or.inr hs⟩
      have hTr : T ≤ r := by
        exact le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
      have hzavailable : available family r (fun i => input i)
          (fun i => trajectory (leastFresh family) input i) z := by
        refine ⟨?_, ?_, ?_⟩
        · rw [currentCore_eq family input hstabilizes hTr]
          exact hzcore
        · intro i hi
          exact hinput ⟨i, Nat.le_of_lt_succ i.isLt, hi⟩
        · intro i hi
          exact houtput ⟨i, i.isLt, hi⟩
      have hout_le : trajectory (leastFresh family) input r ≤ z :=
        trajectory_minimal family input hstabilizes hTr hcore hzavailable
      have hz_le : z ≤ trajectory (leastFresh family) input r := by
        by_contra hnot
        have hlt : trajectory (leastFresh family) input r < z :=
          Nat.lt_of_not_ge hnot
        let q := trajectory (leastFresh family) input r
        have hqcore : q ∈ informationCore family input := by
          have hs := trajectory_available family input hstabilizes hTr hcore
          unfold available at hs
          rw [currentCore_eq family input hstabilizes hTr] at hs
          exact hs.1
        have hqcond : q < z ∧ q ∈ informationCore family input :=
          ⟨hlt, hqcore⟩
        have htime_mem : announceTime q ≤ (Finset.range z).sup announceTime := by
          exact Finset.le_sup (Finset.mem_range.mpr hlt)
        have htime_lt : announceTime q < r := by
          exact lt_of_le_of_lt
            (le_trans htime_mem (Nat.le_max_right _ _)) (Nat.lt_succ_self _)
        have hannounce : input (announceTime q) = q ∨
            trajectory (leastFresh family) input (announceTime q) = q := by
          simpa [announceTime, hqcond] using
            Nat.find_spec (hsmall q hlt hqcore)
        have hs := trajectory_available family input hstabilizes hTr hcore
        rcases hannounce with ha | hg
        · exact hs.2.1 ⟨announceTime q, lt_trans htime_lt (Nat.lt_succ_self r)⟩ ha
        · exact hs.2.2 ⟨announceTime q, htime_lt⟩ hg
      exact ⟨r, Or.inr (Nat.le_antisymm hout_le hz_le)⟩


noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

 theorem firstInput_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  simp [firstInput, hz, Nat.find_spec hz]

 theorem firstInput_min (input : Stream) {z s : ℕ} (hz : z ∈ Set.range input)
    (hs : input s = z) : firstInput input z ≤ s := by
  classical
  simp only [firstInput, dif_pos hz]
  exact Nat.find_min' hz hs

 theorem core_not_generatorFirst_in_range {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T z : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite)
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (trajectory (leastFresh family) input)) :
    z ∈ Set.range input := by
  obtain ⟨t, hit | hout⟩ :=
    core_eventually_announced family input hstabilizes hcore z hzcore
  · exact ⟨t, hit⟩
  · by_contra hnrange
    apply hznot
    refine ⟨t, hout, ?_⟩
    intro s hs hinput
    exact hnrange ⟨s, hinput⟩

 theorem predecessor_charge {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T z : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite)
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (trajectory (leastFresh family) input))
    (hlate : T < firstInput input z) :
    let q := firstInput input z - 1
    trajectory (leastFresh family) input q ≤ z ∧
    trajectory (leastFresh family) input q ∈ informationCore family input ∧
    trajectory (leastFresh family) input q ∈
      GenLimit.GeneratorFirst input (trajectory (leastFresh family) input) := by
  classical
  have hzrange := core_not_generatorFirst_in_range family input
    hstabilizes hcore hzcore hznot
  let q := firstInput input z - 1
  have hqT : T ≤ q := by omega
  have hq_lt : q < firstInput input z := by omega
  have hzavailable : available family q (fun i => input i)
      (fun i => trajectory (leastFresh family) input i) z := by
    refine ⟨?_, ?_, ?_⟩
    · rw [currentCore_eq family input hstabilizes hqT]
      exact hzcore
    · intro i hi
      have hmin := firstInput_min input hzrange hi
      omega
    · intro i hi
      apply hznot
      refine ⟨i, hi, ?_⟩
      intro s hs his
      have hmin := firstInput_min input hzrange his
      omega
  have hspec := trajectory_available family input hstabilizes hqT hcore
  refine ⟨trajectory_minimal family input hstabilizes hqT hcore hzavailable,
    ?_, ?_⟩
  · unfold available at hspec
    rw [currentCore_eq family input hstabilizes hqT] at hspec
    exact hspec.1
  · refine ⟨q, rfl, ?_⟩
    intro s hs
    exact hspec.2.1 ⟨s, Nat.lt_succ_iff.mpr hs⟩

 theorem tail_output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    Set.InjOn (trajectory (leastFresh family) input) {t | T ≤ t} := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hs := trajectory_available family input hstabilizes hb hcore
    exact False.elim (hs.2.2 ⟨a, hlt⟩ hab)
  · exact heq
  · have hs := trajectory_available family input hstabilizes ha hcore
    exact False.elim (hs.2.2 ⟨b, hgt⟩ hab.symm)

 theorem core_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) (K : Language)
    (hcoreK : informationCore family input ⊆ K) {T : ℕ}
    (hstabilizes : ∀ q, T ≤ q → ∀ j,
      compatibleAt family q (fun i => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (leastFresh family) input) ∩ K) n +
      (T + 1) := by
  classical
  let C := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (leastFresh family) input) ∩ K) n
  let A := C.filter fun z => z ∉ GenLimit.GeneratorFirst input
    (trajectory (leastFresh family) input)
  let early := A.filter fun z => firstInput input z ≤ T
  let late := A.filter fun z => T < firstInput input z
  have hpartition : early.card + late.card = A.card := by
    simpa [early, late] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := A) (p := fun z => firstInput input z ≤ T))
  have hEarly : early.card ≤ T + 1 := by
    have hcard : early.card ≤ (Finset.range (T + 1)).card := by
      apply Finset.card_le_card_of_injOn (s := early) (t := Finset.range (T + 1)) (firstInput input)
      · intro z hz
        have hz' : z ∈ early := hz
        exact Finset.mem_range.mpr (by
          have := (Finset.mem_filter.mp hz').2
          omega)
      · intro x hx y hy heq
        have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
        have hyA : y ∈ A := (Finset.mem_filter.mp hy).1
        have hxC := (Finset.mem_filter.mp hxA).1
        have hyC := (Finset.mem_filter.mp hyA).1
        have hxcore := (GenLimit.PatientScope.mem_prefixFinset.mp hxC).2
        have hycore := (GenLimit.PatientScope.mem_prefixFinset.mp hyC).2
        have hxnot := (Finset.mem_filter.mp hxA).2
        have hynot := (Finset.mem_filter.mp hyA).2
        have hxrange := core_not_generatorFirst_in_range family input
          hstabilizes hcore hxcore hxnot
        have hyrange := core_not_generatorFirst_in_range family input
          hstabilizes hcore hycore hynot
        calc
          x = input (firstInput input x) := (firstInput_spec input hxrange).symm
          _ = input (firstInput input y) := congrArg input heq
          _ = y := firstInput_spec input hyrange
    simpa using hcard
  let charge : ℕ → ℕ := fun z =>
    trajectory (leastFresh family) input (firstInput input z - 1)
  have hLate : late.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn charge
    · intro z hz
      have hzA : z ∈ A := (Finset.mem_filter.mp hz).1
      have hzlate : T < firstInput input z := (Finset.mem_filter.mp hz).2
      have hzC : z ∈ C := (Finset.mem_filter.mp hzA).1
      have hznot := (Finset.mem_filter.mp hzA).2
      have hzparts := GenLimit.PatientScope.mem_prefixFinset.mp hzC
      have hc := predecessor_charge family input hstabilizes hcore hzparts.2 hznot hzlate
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      exact ⟨lt_of_le_of_lt hc.1 hzparts.1, hc.2.2, hcoreK hc.2.1⟩
    · intro x hx y hy hxy
      have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
      have hyA : y ∈ A := (Finset.mem_filter.mp hy).1
      have hxlate : T < firstInput input x := (Finset.mem_filter.mp hx).2
      have hylate : T < firstInput input y := (Finset.mem_filter.mp hy).2
      have hxC : x ∈ C := (Finset.mem_filter.mp hxA).1
      have hyC : y ∈ C := (Finset.mem_filter.mp hyA).1
      have hxcore := (GenLimit.PatientScope.mem_prefixFinset.mp hxC).2
      have hycore := (GenLimit.PatientScope.mem_prefixFinset.mp hyC).2
      have hxnot := (Finset.mem_filter.mp hxA).2
      have hynot := (Finset.mem_filter.mp hyA).2
      have htimes : firstInput input x - 1 = firstInput input y - 1 :=
        tail_output_injective family input hstabilizes hcore
          (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) hxy
      have hfirst : firstInput input x = firstInput input y := by omega
      have hxrange := core_not_generatorFirst_in_range family input
        hstabilizes hcore hxcore hxnot
      have hyrange := core_not_generatorFirst_in_range family input
        hstabilizes hcore hycore hynot
      calc
        x = input (firstInput input x) := (firstInput_spec input hxrange).symm
        _ = input (firstInput input y) := congrArg input hfirst
        _ = y := firstInput_spec input hyrange
  have hA : A.card ≤ D.card + (T + 1) := by omega
  have hCsplit : C.card ≤ D.card + A.card := by
    have hsub : C ⊆ D ∪ A := by
      intro z hz
      by_cases hzD : z ∈ GenLimit.GeneratorFirst input
          (trajectory (leastFresh family) input)
      · exact Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hz).1, hzD,
              hcoreK (GenLimit.PatientScope.mem_prefixFinset.mp hz).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hzD⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le D A)
  change C.card ≤ 2 * D.card + (T + 1)
  omega


 theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Eventually.of_forall fun n => by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
      · exact Nat.cast_nonneg _
  · exact isBoundedUnder_of ⟨0, fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · apply Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hb : GenLimit.PatientScope.prefixCount B n = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa [hn] using GenLimit.PatientScope.prefixCount_mono hBK n
      simp [hn, hb]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

end Stage3Case017Proof

open Stage3Case017
open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  let gen := leastFresh family
  refine ⟨gen, ?_⟩
  intro input hinj hpartial hcore
  let output := trajectory gen input
  refine ⟨output, trajectory_follows gen input, ?_⟩
  obtain ⟨T, hT⟩ := compatibleAt_iff family input
  intro j hj
  have hcoreTarget : informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hj
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    refine ⟨T, ?_⟩
    intro t ht
    have hs := trajectory_available family input hT ht hcore
    have hscore : output t ∈ informationCore family input := by
      unfold available at hs
      rw [currentCore_eq family input hT ht] at hs
      simpa [output, gen] using hs.1
    refine ⟨hcoreTarget hscore, ?_, ?_⟩
    · rw [GenLimit.mem_sample_iff]
      rintro ⟨s, hslt, heq⟩
      exact hs.2.1 ⟨s, hslt⟩ (by simpa [output, gen] using heq)
    · intro s hslt
      exact hs.2.2 ⟨s, hslt⟩
  refine ⟨hnovel, ?_⟩
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (GenLimit.PatientScope.prefixCount (informationCore family input))
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j))
      (T + 1)
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hinfinite j)
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono hcoreTarget n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
    · intro n
      have hc := core_count_le family input hinj (family j) hcoreTarget hT hcore n
      have hc' : GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
          2 * GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input output ∩ family j) n + (T + 1) := by
        simpa [output, gen] using hc
      omega
  have hmissingSubset : informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    obtain ⟨t, hit | hout⟩ :=
      core_eventually_announced family input hT hcore z hz.1
    · exact False.elim (hz.2 ⟨t, hit⟩)
    · refine ⟨⟨t, by simpa [output, gen] using hout, ?_⟩,
        hcoreTarget hz.1⟩
      intro s hs heq
      exact hz.2 ⟨s, heq⟩
  have hmissing :
      GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) :=
    relativeLowerDensity_mono hmissingSubset Set.inter_subset_right
  exact max_le hhalf hmissing

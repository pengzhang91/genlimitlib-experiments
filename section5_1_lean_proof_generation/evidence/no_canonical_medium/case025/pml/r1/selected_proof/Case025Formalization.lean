import Stage3Model
import GenLimit.Paper39_DenseGeneration
import Mathlib.Logic.Equiv.Finset

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

def finiteAdditionFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family n.unpair.1 ∪ (Denumerable.eqv (Finset ℕ)).symm n.unpair.2

noncomputable def finiteAdditionOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact {
    language := finiteAdditionFamily family
    infinite' := by
      intro n
      rw [finiteAdditionFamily, Set.infinite_union]
      exact Or.inl (hInfinite n.unpair.1)
    query := fun n x => decide (x ∈ finiteAdditionFamily family n)
    query_spec := by simp }

def completedPrefix {n : ℕ} (xs : Fin n → ℕ) : Stream :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

theorem completedPrefix_apply {n : ℕ} (xs : Fin n → ℕ) {k : ℕ} (hk : k < n) :
    completedPrefix xs k = xs ⟨k, hk⟩ := by
  simp [completedPrefix, hk]

theorem sample_eq_of_eq_below
    {a b : Stream} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

theorem consistent_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.Consistent C a n = GenLimit.Consistent C b n := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eq_below h]

theorem recursiveCritical_eq_of_consistent_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {n : ℕ}
    (h : GenLimit.Consistent C a n = GenLimit.Consistent C b n) :
    GenLimit.RecursiveCritical C a n = GenLimit.RecursiveCritical C b n := by
  funext i
  apply propext
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using Iff.of_eq (congrFun h 0)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨(congrFun h (i + 1)).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨(congrFun h (i + 1)).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

theorem patient_processRound_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {n : ℕ}
    (h : ∀ k, k < n + 1 → a k = b k)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.processRound O a n old =
      GenLimit.PatientMachine.processRound O b n old := by
  have hprior : ∀ k, k < n → a k = b k :=
    fun k hk => h k (hk.trans (Nat.lt_succ_self n))
  have hsampleN := sample_eq_of_eq_below hprior
  have hsampleS := sample_eq_of_eq_below h
  have hconsN := consistent_eq_of_eq_below (C := O.language) hprior
  have hconsS := consistent_eq_of_eq_below (C := O.language) h
  have hcritN := recursiveCritical_eq_of_consistent_eq hconsN
  have hcritS := recursiveCritical_eq_of_consistent_eq hconsS
  have hconsN' : ∀ i, GenLimit.Consistent O.language a n i ↔
      GenLimit.Consistent O.language b n i :=
    fun i => Iff.of_eq (congrFun hconsN i)
  have hconsS' : ∀ i, GenLimit.Consistent O.language a (n + 1) i ↔
      GenLimit.Consistent O.language b (n + 1) i :=
    fun i => Iff.of_eq (congrFun hconsS i)
  have hcritN' : ∀ i, GenLimit.RecursiveCritical O.language a n i ↔
      GenLimit.RecursiveCritical O.language b n i :=
    fun i => Iff.of_eq (congrFun hcritN i)
  have hcritS' : ∀ i, GenLimit.RecursiveCritical O.language a (n + 1) i ↔
      GenLimit.RecursiveCritical O.language b (n + 1) i :=
    fun i => Iff.of_eq (congrFun hcritS i)
  have hdecide :
      GenLimit.PatientMachine.decide O.language a n old =
        GenLimit.PatientMachine.decide O.language b n old := by
    unfold GenLimit.PatientMachine.decide
      GenLimit.PatientMachine.stableDecision
      GenLimit.PatientMachine.backtrackDecision
      GenLimit.PatientMachine.highestCritical
      GenLimit.PatientMachine.highestSurvivor
      GenLimit.PatientMachine.lowestConsistentInScope
      GenLimit.PatientMachine.lowestConsistent
      GenLimit.PatientMachine.consistentIndices
      GenLimit.PatientMachine.criticalIndices
      GenLimit.PatientMachine.survivingCriticalIndices
    rw [hconsS, hcritN, hcritS]
  have havailable :
      GenLimit.PatientMachine.Available O.language a (n + 1) old.used
          (GenLimit.PatientMachine.decide O.language a n old).focus =
        GenLimit.PatientMachine.Available O.language b (n + 1) old.used
          (GenLimit.PatientMachine.decide O.language b n old).focus := by
    rw [hdecide]
    funext x
    apply propext
    simp only [GenLimit.PatientMachine.Available, hsampleS]
  have hleast :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (n + 1) old.used
          (GenLimit.PatientMachine.decide O.language b n old).focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (n + 1) old.used
          (GenLimit.PatientMachine.decide O.language b n old).focus := by
    rw [hdecide] at havailable
    classical
    unfold GenLimit.PatientMachine.leastAvailable
    apply Nat.find_congr'
    intro x
    exact Iff.of_eq (congrFun havailable x)
  unfold GenLimit.PatientMachine.processRound
  simp only [hdecide]
  rw [hleast]

theorem patient_run_congr
    (O : GenLimit.OracleFamily) {a b : Stream} :
    ∀ n, (∀ k, k < n → a k = b k) →
      GenLimit.PatientMachine.run O a n = GenLimit.PatientMachine.run O b n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      have hprior : ∀ k, k < n → a k = b k :=
        fun k hk => h k (hk.trans (Nat.lt_succ_self n))
      simp only [GenLimit.PatientMachine.run_succ]
      rw [ih hprior]
      exact patient_processRound_congr O h _

theorem patient_output_completedPrefix
    (O : GenLimit.OracleFamily) (input : Stream) (t : ℕ) :
    GenLimit.PatientMachine.output O (completedPrefix (fun i : Fin (t + 1) => input i)) t =
      GenLimit.PatientMachine.output O input t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_congr O (n := t + 1)]
  intro k hk
  exact completedPrefix_apply _ hk

def patientOnlineGenerator (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t inputPrefix _ =>
    GenLimit.PatientMachine.output O (completedPrefix inputPrefix) t

theorem patient_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  exact (patient_output_completedPrefix O input t).symm

def badValues (input : Stream) (K : Language) : Set ℕ :=
  Set.range input \ K

theorem badValues_finite
    {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (badValues input K).Finite := by
  rw [badValues, GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact hbad.image input

theorem range_eq_union_badValues
    {input : Stream} {K : Language} (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ badValues input K := by
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hx | hx)
    · exact hcover hx
    · exact hx.1

theorem exists_finiteAddition_index
    (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    ∃ z, finiteAdditionFamily family z = family i ∪ (F : Set ℕ) := by
  refine ⟨Nat.pair i (Denumerable.eqv (Finset ℕ) F), ?_⟩
  simp [finiteAdditionFamily]

theorem eventually_mem_of_finite_range
    {output : Stream} {F : Set ℕ} (hF : F.Finite)
    (hinj : Function.Injective output) :
    ∃ T, ∀ t, T ≤ t → output t ∉ F := by
  have hpre : (output ⁻¹' F).Finite := hF.preimage hinj.injOn
  have hbdd := hpre.bddAbove
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨B + 1, ?_⟩
  intro t ht htF
  have htpre : t ∈ output ⁻¹' F := htF
  have hle : t ≤ B := hB htpre
  omega

theorem novel_of_union_finite
    {input output : Stream} {K F : Language}
    (hEventualMem : ∃ T, ∀ t, T ≤ t → output t ∈ K ∪ F)
    (hF : F.Finite) (hinj : Function.Injective output)
    (hfresh : ∀ t, output t ∉ GenLimit.sample input (t + 1)) :
    GenLimit.NovelGeneratesInLimit input output K := by
  obtain ⟨T, hT⟩ := hEventualMem
  obtain ⟨U, hU⟩ := eventually_mem_of_finite_range hF hinj
  refine ⟨max T U, ?_⟩
  intro t ht
  have htT : T ≤ t := (le_max_left T U).trans ht
  have htU : U ≤ t := (le_max_right T U).trans ht
  refine ⟨(hT t htT).resolve_right (hU t htU), hfresh t, ?_⟩
  intro s hs
  exact hinj.ne hs.ne

theorem prefixCount_union_le (A B : Language) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset (A ∪ B) n).card ≤
        (GenLimit.PatientScope.prefixFinset A n ∪
          GenLimit.PatientScope.prefixFinset B n).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
      apply Finset.mem_union.mpr
      rcases hx'.2 with hxA | hxB
      · exact Or.inl (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxA⟩)
      · exact Or.inr (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    _ ≤ (GenLimit.PatientScope.prefixFinset A n).card +
        (GenLimit.PatientScope.prefixFinset B n).card :=
      Finset.card_union_le _ _

theorem prefixCount_le_card_finite
    {F : Language} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2
    (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

theorem prefixCount_finite_union_bound
    {A K F : Language} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∩ (K ∪ F)) n ≤
      GenLimit.PatientScope.prefixCount (A ∩ K) n + hF.toFinset.card := by
  calc
    GenLimit.PatientScope.prefixCount (A ∩ (K ∪ F)) n ≤
        GenLimit.PatientScope.prefixCount ((A ∩ K) ∪ F) n :=
      GenLimit.PatientScope.prefixCount_mono (by
        intro x hx
        rcases hx.2 with hxK | hxF
        · exact Or.inl ⟨hx.1, hxK⟩
        · exact Or.inr hxF) n
    _ ≤ GenLimit.PatientScope.prefixCount (A ∩ K) n +
        GenLimit.PatientScope.prefixCount F n := prefixCount_union_le _ _ _
    _ ≤ GenLimit.PatientScope.prefixCount (A ∩ K) n + hF.toFinset.card :=
      Nat.add_le_add_left (prefixCount_le_card_finite hF n) _

theorem relativeLowerDensity_finite_union_transfer
    {A K F : Language} (hK : K.Infinite) (hF : F.Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ (K ∪ F)) (K ∪ F) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ F)) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (K ∪ F) n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hF.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hcount)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcount.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop,
      source n ≤ target n + error n := by
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hnum :
        (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ F)) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n + hF.toFinset.card := by
      exact_mod_cast prefixCount_finite_union_bound hF n
    have hden :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (K ∪ F) n := by
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.subset_union_left) n
    have hratio := div_le_div₀
      (show (0 : ℝ) ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + hF.toFinset.card by positivity)
      hnum hnR hden
    simpa [source, target, error, add_div] using hratio
  have hsource_nonneg : ∀ n, 0 ≤ source n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have htarget_nonneg : ∀ n, 0 ≤ target n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [target, hn]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [target]
      rw [div_le_one hnR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrSource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr he hp
  linarith
theorem stage3_result : MainClaim := by
  intro family hInfinite
  let O := finiteAdditionOracle family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hPresentation
  let F : Finset ℕ := (badValues_finite hPresentation.2).toFinset
  obtain ⟨z, hz⟩ := exists_finiteAddition_index family i F
  have hRange : Set.range input = family i ∪ (F : Set ℕ) := by
    rw [range_eq_union_badValues hPresentation.1]
    simp [F]
  have hOz : O.language z = family i ∪ (F : Set ℕ) := by
    simpa [O] using hz
  have hP : GenLimit.Presents input (O.language z) := by
    rw [hOz]
    exact hRange
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patient_follows O input, ?_, ?_⟩
  · apply novel_of_union_finite
      (F := (F : Set ℕ)) (K := family i)
    · obtain ⟨T, hT⟩ := GenLimit.PatientMachine.patient_validity O input hP
      exact ⟨T, fun t ht => by rw [← hOz]; exact hT t ht⟩
    · exact Set.toFinite _
    · exact GenLimit.PatientMachine.output_injective O input
    · exact GenLimit.PatientMachine.output_not_mem_sample O input
  · have hhalf :=
      (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP).2
    have htransfer := relativeLowerDensity_finite_union_transfer
      (A := GenLimit.GeneratorFirst input output)
      (K := family i) (F := (F : Set ℕ)) (hInfinite i) (Set.toFinite _)
    rw [GenLimit.PatientMachine.patientLowerDensity, hOz] at hhalf
    exact hhalf.trans (by simpa [output] using htransfer)

end

end Stage3Case025

/-- Primary endpoint. -/
theorem stage3_result : Stage3Case025.MainClaim :=
  Stage3Case025.stage3_result

import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter

namespace Stage3Case017Proof

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Stage3Case017

noncomputable def prefixCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

theorem exists_available_of_infinite {S : Set ℕ} (hS : S.Infinite)
    (F : Finset ℕ) : ∃ z, z ∈ S ∧ z ∉ F := by
  have hdiff : (S \ (F : Set ℕ)).Infinite := hS.diff F.finite_toSet
  obtain ⟨z, hz⟩ := hdiff.nonempty
  exact ⟨z, hz.1, hz.2⟩

noncomputable def leastAvailable {S : Set ℕ} (hS : S.Infinite)
    (F : Finset ℕ) : ℕ := Nat.find (exists_available_of_infinite hS F)

theorem leastAvailable_spec {S : Set ℕ} (hS : S.Infinite) (F : Finset ℕ) :
    leastAvailable hS F ∈ S ∧ leastAvailable hS F ∉ F :=
  Nat.find_spec (exists_available_of_infinite hS F)

theorem leastAvailable_le {S : Set ℕ} (hS : S.Infinite) (F : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hzF : z ∉ F) : leastAvailable hS F ≤ z := by
  exact Nat.find_min' (exists_available_of_infinite hS F) ⟨hzS, hzF⟩

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := fun t xs ys =>
  if h : (prefixCore family xs).Infinite then
    leastAvailable h (forbidden xs ys)
  else leastAvailable Set.infinite_univ (forbidden xs ys)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

@[simp] theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem mem_forbidden_input {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (i : Fin (t + 1)) : xs i ∈ forbidden xs ys := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem mem_forbidden_output {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (i : Fin t) : ys i ∈ forbidden xs ys := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem generator_not_input {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (i : Fin (t + 1)) :
    generator family t xs ys ≠ xs i := by
  classical
  unfold generator
  split <;> intro hEq
  · exact (leastAvailable_spec ‹(prefixCore family xs).Infinite›
      (forbidden xs ys)).2 (hEq ▸ mem_forbidden_input xs ys i)
  · exact (leastAvailable_spec Set.infinite_univ
      (forbidden xs ys)).2 (hEq ▸ mem_forbidden_input xs ys i)

theorem generator_not_output {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (i : Fin t) :
    generator family t xs ys ≠ ys i := by
  classical
  unfold generator
  split <;> intro hEq
  · exact (leastAvailable_spec ‹(prefixCore family xs).Infinite›
      (forbidden xs ys)).2 (hEq ▸ mem_forbidden_output xs ys i)
  · exact (leastAvailable_spec Set.infinite_univ
      (forbidden xs ys)).2 (hEq ▸ mem_forbidden_output xs ys i)

theorem generator_mem_core {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (prefixCore family xs).Infinite) :
    generator family t xs ys ∈ prefixCore family xs := by
  simp only [generator, dif_pos hcore]
  exact (leastAvailable_spec hcore (forbidden xs ys)).1

theorem generator_le_available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (prefixCore family xs).Infinite) {z : ℕ}
    (hzcore : z ∈ prefixCore family xs) (hzfree : z ∉ forbidden xs ys) :
    generator family t xs ys ≤ z := by
  simp only [generator, dif_pos hcore]
  exact leastAvailable_le hcore (forbidden xs ys) hzcore hzfree

theorem trajectory_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s ≤ t) :
    trajectory (generator family) input t ≠ input s := by
  rw [trajectory_follows (generator family) input t]
  exact generator_not_input family _ _ ⟨s, Nat.lt_succ_iff.mpr hs⟩

theorem trajectory_fresh_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s < t) :
    trajectory (generator family) input t ≠ trajectory (generator family) input s := by
  rw [trajectory_follows (generator family) input t]
  exact generator_not_output family _ _ ⟨s, hs⟩

theorem trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (trajectory (generator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact trajectory_fresh_output family input t s hlt hst.symm
  · exact trajectory_fresh_output family input s t hgt hst

theorem exists_bad_index {L : Language} {input : Stream}
    (h : ¬ GenLimit.Generic.StreamIn input L) : ∃ q, input q ∉ L := by
  obtain ⟨z, ⟨q, rfl⟩, hz⟩ := Set.not_subset.mp h
  exact ⟨q, hz⟩

noncomputable def exclusionTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ :=
  if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (exists_bad_index h) + 1

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ := Finset.univ.sup (exclusionTime family input)

theorem streamIn_of_prefix {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) (hT : stabilizationTime family input ≤ t)
    (hpref : ∀ i : Fin (t + 1), input i ∈ family j) :
    GenLimit.Generic.StreamIn input (family j) := by
  classical
  by_contra hnot
  have hw := Nat.find_spec (exists_bad_index hnot)
  have hle : exclusionTime family input j ≤ stabilizationTime family input :=
    Finset.le_sup (s := Finset.univ) (Finset.mem_univ j)
  have hq : Nat.find (exists_bad_index hnot) < t + 1 := by
    have hq1 : Nat.find (exists_bad_index hnot) + 1 ≤ t := by
      simpa [exclusionTime, hnot] using le_trans hle hT
    omega
  exact hw (hpref ⟨_, hq⟩)

theorem prefixCore_eq_informationCore {m t : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hT : stabilizationTime family input ≤ t) :
    prefixCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  constructor
  · intro hz j hj
    exact hz j (fun i => hj ⟨i, rfl⟩)
  · intro hz j hpref
    exact hz j (streamIn_of_prefix family input j hT hpref)

theorem prefixCore_subset_of_streamIn {m t : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    prefixCore family (fun i : Fin (t + 1) => input i) ⊆ family j := by
  intro z hz
  exact hz j (fun i => hj ⟨i, rfl⟩)

theorem eventual_target_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    trajectory (generator family) input t ∈ family j := by
  rw [trajectory_follows (generator family) input t]
  have heq := prefixCore_eq_informationCore family input ht
  have hinf : (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    simpa [heq] using hI
  exact prefixCore_subset_of_streamIn family input j hj
    (generator_mem_core family _ _ hinf)

theorem core_point_eventually_announced {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hI : (informationCore family input).Infinite) {z : ℕ}
    (hz : z ∈ informationCore family input) :
    z ∈ Set.range input ∨ z ∈ Set.range (trajectory (generator family) input) := by
  classical
  by_contra hnot
  push_neg at hnot
  have hbound : ∀ n, trajectory (generator family) input
      (stabilizationTime family input + n) ≤ z := by
    intro n
    let t := stabilizationTime family input + n
    rw [trajectory_follows (generator family) input t]
    have ht : stabilizationTime family input ≤ t := Nat.le_add_right _ _
    have heq := prefixCore_eq_informationCore family input ht
    have hinf : (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
      simpa [heq] using hI
    apply generator_le_available family _ _ hinf
    · simpa [heq] using hz
    · intro hzforbidden
      rcases Finset.mem_union.mp hzforbidden with hx | hy
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
        exact hnot.1 ⟨i, hi⟩
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
        exact hnot.2 ⟨i, hi⟩
  let f : ℕ → Fin (z + 1) := fun n =>
    ⟨trajectory (generator family) input (stabilizationTime family input + n),
      Nat.lt_succ_iff.mpr (hbound n)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hout : trajectory (generator family) input
        (stabilizationTime family input + a) =
        trajectory (generator family) input
          (stabilizationTime family input + b) := Fin.ext_iff.mp hab
    exact Nat.add_left_cancel (trajectory_injective family input hout)
  exact Set.not_infinite.mpr (Set.toFinite (Set.range f))
    (Set.infinite_range_of_injective hf)

theorem output_range_eq_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    Set.range (trajectory (generator family) input) =
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, fun s hs => (trajectory_fresh_input family input t s hs).symm⟩
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩

theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite) :
    informationCore family input ⊆
      (GenLimit.AdversaryFirst input (trajectory (generator family) input) ∩
          informationCore family input) ∪
        GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro z hz
  rcases core_point_eventually_announced family input hI hz with hin | hout
  · rcases GenLimit.range_subset_first_announcements input
      (trajectory (generator family) input) hin with ha | hd
    · exact Or.inl ⟨ha, hz⟩
    · exact Or.inr hd
  · exact Or.inr (by rw [← output_range_eq_generatorFirst family input]; exact hout)

noncomputable def firstInputTime (input : Stream) (x : ℕ) : ℕ :=
  if h : ∃ t, input t = x then Nat.find h else 0

noncomputable def earlyCoreAttacker {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Finset ℕ :=
  (GenLimit.sample input (stabilizationTime family input + 1)).filter
    (fun x => x ∈ GenLimit.AdversaryFirst input
      (trajectory (generator family) input) ∩ informationCore family input)

noncomputable def predecessor {m : ℕ} (family : Fin m → Language)
    (input : Stream) (x : ℕ) : ℕ :=
  trajectory (generator family) input (firstInputTime input x - 1)

theorem firstInputTime_spec {input output : Stream} {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) :
    input (firstInputTime input x) = x := by
  rcases hx with ⟨t, ht, -⟩
  have hex : ∃ q, input q = x := ⟨t, ht⟩
  simp only [firstInputTime, dif_pos hex]
  exact Nat.find_spec hex

theorem firstInputTime_min {input output : Stream} {x t : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) (ht : input t = x) :
    firstInputTime input x ≤ t := by
  rcases hx with ⟨w, hw, -⟩
  have hex : ∃ q, input q = x := ⟨w, hw⟩
  simp only [firstInputTime, dif_pos hex]
  exact Nat.find_min' hex ht

theorem predecessor_mem_and_lt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) {x : ℕ}
    (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker (family j)
      (GenLimit.AdversaryFirst input (trajectory (generator family) input) ∩
        informationCore family input) ∅ (earlyCoreAttacker family input)) :
    predecessor family input x ∈
        GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j ∧
      predecessor family input x < x := by
  have hxA := hx.1.1.1
  have hxI := hx.1.1.2
  obtain ⟨qx, hqx, hxNo⟩ := hxA
  have hxA' : x ∈ GenLimit.AdversaryFirst input
      (trajectory (generator family) input) := ⟨qx, hqx, hxNo⟩
  have hlate : stabilizationTime family input < firstInputTime input x := by
    have hnotEarly : x ∉ earlyCoreAttacker family input := by
      intro he
      exact hx.2 (Set.mem_union_left _ he)
    by_contra hle
    apply hnotEarly
    simp only [earlyCoreAttacker, Finset.mem_filter]
    refine ⟨?_, hx.1.1⟩
    rw [GenLimit.mem_sample_iff]
    exact ⟨firstInputTime input x, Nat.lt_succ_of_le (Nat.le_of_not_gt hle),
      firstInputTime_spec hxA'⟩
  have htime : stabilizationTime family input ≤ firstInputTime input x - 1 := by omega
  have hmemK := eventual_target_output family input hI j hj htime
  have hmemD : predecessor family input x ∈
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
    rw [← output_range_eq_generatorFirst family input]
    exact ⟨firstInputTime input x - 1, rfl⟩
  refine ⟨⟨hmemD, hmemK⟩, ?_⟩
  have hle : predecessor family input x ≤ x := by
    unfold predecessor
    let t := firstInputTime input x - 1
    rw [trajectory_follows (generator family) input t]
    have heq := prefixCore_eq_informationCore family input htime
    have hinf : (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
      rw [heq]
      exact hI
    apply generator_le_available family _ _ hinf
    · rw [heq]
      exact hxI
    · intro hzforbidden
      rcases Finset.mem_union.mp hzforbidden with hin | hout
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hin
        have hmin := firstInputTime_min hxA' hi
        omega
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hout
        exact hxNo i.1 (by
          have hfirst := firstInputTime_min hxA' hqx
          omega) hi
  exact lt_of_le_of_ne hle (by
    intro heq
    exact hxNo (firstInputTime input x - 1) (by
      have hfirst := firstInputTime_min hxA' hqx
      omega) heq)

theorem predecessor_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    Set.InjOn (predecessor family input)
      (GenLimit.PatientScope.ordinaryAttacker (family j)
        (GenLimit.AdversaryFirst input (trajectory (generator family) input) ∩
          informationCore family input) ∅ (earlyCoreAttacker family input)) := by
  intro x hx y hy hxy
  have htimes : firstInputTime input x - 1 = firstInputTime input y - 1 := by
    apply trajectory_injective family input
    exact hxy
  have hlateX : stabilizationTime family input < firstInputTime input x := by
    by_contra h
    have hxin : x ∈ earlyCoreAttacker family input := by
      simp only [earlyCoreAttacker, Finset.mem_filter]
      refine ⟨?_, hx.1.1⟩
      rw [GenLimit.mem_sample_iff]
      exact ⟨firstInputTime input x, Nat.lt_succ_of_le (Nat.le_of_not_gt h),
        firstInputTime_spec hx.1.1.1⟩
    exact hx.2 (Set.mem_union_left _ hxin)
  have hlateY : stabilizationTime family input < firstInputTime input y := by
    by_contra h
    have hyin : y ∈ earlyCoreAttacker family input := by
      simp only [earlyCoreAttacker, Finset.mem_filter]
      refine ⟨?_, hy.1.1⟩
      rw [GenLimit.mem_sample_iff]
      exact ⟨firstInputTime input y, Nat.lt_succ_of_le (Nat.le_of_not_gt h),
        firstInputTime_spec hy.1.1.1⟩
    exact hy.2 (Set.mem_union_left _ hyin)
  have htime : firstInputTime input x = firstInputTime input y := by omega
  calc
    x = input (firstInputTime input x) := (firstInputTime_spec hx.1.1.1).symm
    _ = input (firstInputTime input y) := by rw [htime]
    _ = y := firstInputTime_spec hy.1.1.1

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · refine Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := (1 : ℝ)) ?_
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · rw [hn]
      norm_num
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite) (input : Stream)
    (hI : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
            family j) (family j) := by
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { target := family j
      enumerated := informationCore family input
      enumerated_subset_target := fun z hz => hz j hj
      attacker := GenLimit.AdversaryFirst input (trajectory (generator family) input) ∩
        informationCore family input
      defender := GenLimit.GeneratorFirst input (trajectory (generator family) input)
      output := trajectory (generator family) input
      output_range := output_range_eq_generatorFirst family input
      output_injective := trajectory_injective family input
      validFrom := stabilizationTime family input
      eventual_target := fun _ ht => eventual_target_output family input hI j hj ht
      enumerated_covered := core_covered family input hI
      attacker_subset_target := fun z hz => hz.2 j hj
      ownership_disjoint := by
        rw [Set.disjoint_left]
        intro z hzA hzD
        exact Set.disjoint_left.1
          (GenLimit.adversaryFirst_disjoint_generatorFirst input
            (trajectory (generator family) input)) hzA.1 hzD
      earlyAttacker := earlyCoreAttacker family input
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := predecessor family input
      partner_mem := fun _ hx => (predecessor_mem_and_lt family input hI j hj hx).1
      partner_lt := fun _ hx => (predecessor_mem_and_lt family input hI j hj hx).2
      partner_injective := predecessor_injective family input hI j hj
      switchBudget := fun _ => 0
      switch_prefix_le := by
        intro n
        change (GenLimit.PatientScope.prefixFinset ∅ n).card ≤ 0
        have hempty : GenLimit.PatientScope.prefixFinset ∅ n = ∅ := by
          ext x
          simp
        simp [hempty] }
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
            family j) (family j) := by
    have hlog : ∀ n, GenLimit.PatientScope.prefixCount P.switchLoss n ≤
        Nat.log2 (P.targetCount n) := by
      intro n
      have hempty : GenLimit.PatientScope.prefixCount (∅ : Set ℕ) n = 0 := by
        unfold GenLimit.PatientScope.prefixCount
        have hfin : GenLimit.PatientScope.prefixFinset ∅ n = ∅ := by
          ext x
          simp
        simp [hfin]
      simpa [P, hempty]
    simpa [P, GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity]
      using GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
        P (hfamily j) hlog
  have hmissingSub : informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j := by
    intro z hz
    have hout : z ∈ Set.range (trajectory (generator family) input) := by
      rcases core_point_eventually_announced family input hI hz.1 with hin | hout
      · exact False.elim (hz.2 hin)
      · exact hout
    refine ⟨?_, hz.1 j hj⟩
    rw [← output_range_eq_generatorFirst family input]
    exact hout
  have hmissing := relativeLowerDensity_mono hmissingSub Set.inter_subset_right
  exact max_le hhalf hmissing

end
end Stage3Case017Proof

open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨generator family, ?_⟩
  intro input hInjective hpartial hI
  let output := trajectory (generator family) input
  refine ⟨output, trajectory_follows (generator family) input, ?_⟩
  intro j hj
  refine ⟨?_, density_bounds family hfamily input hI j hj⟩
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  refine ⟨eventual_target_output family input hI j hj ht, ?_, ?_⟩
  · intro hin
    rw [GenLimit.mem_sample_iff] at hin
    obtain ⟨s, hs, heq⟩ := hin
    exact trajectory_fresh_input family input t s (by omega) heq.symm
  · intro s hs
    exact (trajectory_fresh_output family input t s hs).symm

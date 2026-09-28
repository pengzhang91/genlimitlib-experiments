import Stage3Model

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable def compatible {m : ℕ}
    (family : Fin m → Stage3Case017.Language) {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

noncomputable def available {m : ℕ}
    (family : Fin m → Stage3Case017.Language) {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  (∀ j, compatible family xs j → z ∈ family j) ∧
    (∀ i, z ≠ xs i) ∧ (∀ i, z ≠ ys i)

noncomputable def learner {m : ℕ}
    (family : Fin m → Stage3Case017.Language) : Stage3Case017.OnlineGenerator := by
  classical
  exact fun _ xs ys =>
    if h : ∃ z, available family xs ys z then Nat.find h else 0

noncomputable def history (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) : (t : ℕ) → Fin t → ℕ
  | 0 => fun i => Fin.elim0 i
  | t + 1 => Fin.lastCases
      (gen t (fun i => input i) (history gen input t))
      (history gen input t)

noncomputable def run (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) : Stage3Case017.Stream :=
  fun t => history gen input (t + 1) (Fin.last t)

lemma history_castSucc (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) {t : ℕ} (i : Fin t) :
    history gen input (t + 1) i.castSucc = history gen input t i := by
  simp [history]

lemma run_eq_history (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) {t : ℕ} (i : Fin t) :
    run gen input i = history gen input t i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [run, history]
      · rw [history_castSucc]
        exact ih k

noncomputable def badTime {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (j : Fin m) : ℕ := by
  classical
  exact if h : ∃ t, input t ∉ family j then Nat.find h else 0

noncomputable def threshold {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) : ℕ :=
  Finset.univ.sup (badTime family input)

lemma badTime_le_threshold {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (j : Fin m) : badTime family input j ≤ threshold family input := by
  exact Finset.le_sup (Finset.mem_univ j)

lemma compatible_iff_streamIn {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {t : ℕ} (ht : threshold family input ≤ t) (j : Fin m) :
    compatible family (fun i : Fin (t + 1) => input i) j ↔
      GenLimit.Generic.StreamIn input (family j) := by
  classical
  constructor
  · intro hc z hz
    rcases hz with ⟨s, rfl⟩
    by_contra hs
    have hex : ∃ q, input q ∉ family j := ⟨s, hs⟩
    have hbad : input (badTime family input j) ∉ family j := by
      simp only [badTime, dif_pos hex]
      exact Nat.find_spec hex
    have hle : badTime family input j ≤ t :=
      (badTime_le_threshold family input j).trans ht
    exact hbad (hc ⟨badTime family input j, Nat.lt_succ_iff.mpr hle⟩)
  · intro hs i
    exact hs ⟨i, rfl⟩

lemma exists_available {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : threshold family input ≤ t) (ys : Fin t → ℕ) :
    ∃ z, available family (fun i : Fin (t + 1) => input i) ys z := by
  classical
  let used : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image ys)
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_not_mem_finset used
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hj
    exact hzcore j ((compatible_iff_streamIn family input ht j).mp hj)
  · intro i hzi
    apply hzused
    simp [used, hzi]
  · intro i hzi
    apply hzused
    simp [used, hzi]

lemma learner_spec {m : ℕ}
    (family : Fin m → Stage3Case017.Language) {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hex : ∃ z, available family xs ys z) :
    available family xs ys (learner family t xs ys) := by
  classical
  simp only [learner, dif_pos hex]
  exact Nat.find_spec hex

lemma run_follows (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) :
    Stage3Case017.Follows gen input (run gen input) := by
  intro t
  rw [run]
  simp only [history, Fin.lastCases_last]
  congr 1
  funext i
  exact (run_eq_history gen input i).symm

lemma output_spec {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : threshold family input ≤ t) :
    available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (learner family) input i)
      (run (learner family) input t) := by
  rw [run_follows (learner family) input t]
  exact learner_spec family _ _ (exists_available family input hcore ht _)

lemma learner_le {m : ℕ}
    (family : Fin m → Stage3Case017.Language) {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hz : available family xs ys z) : learner family t xs ys ≤ z := by
  classical
  let hex : ∃ q, available family xs ys q := ⟨z, hz⟩
  simp only [learner, dif_pos hex]
  exact Nat.find_min' hex hz

lemma output_le_available {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {t z : ℕ}
    (hz : available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (learner family) input i) z) :
    run (learner family) input t ≤ z := by
  rw [run_follows (learner family) input t]
  exact learner_le family _ _ hz

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

lemma ratio_bounded_below (A K : Set ℕ) :
    IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop
      (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) := by
  refine ⟨0, ?_⟩
  rw [eventually_map]
  exact Eventually.of_forall (ratio_nonneg A K)

lemma ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  have hc : GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount K n :=
    Finset.card_le_card (by
      intro z hz
      simp only [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
        Finset.mem_range] at hz ⊢
      exact ⟨hz.1, hAK hz.2⟩)
  by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
  · have ha : GenLimit.PatientScope.prefixCount A n = 0 := Nat.eq_zero_of_le_zero (hk ▸ hc)
    simp [ha, hk]
  · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hk))).mpr
    exact_mod_cast hc

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
      (hu := ratio_bounded_below A K)
      (hv := Filter.isCoboundedUnder_ge_of_le atTop (ratio_le_one hBK))
  filter_upwards with n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro z hz
    simp only [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range] at hz ⊢
    exact ⟨hz.1, hAB hz.2⟩)

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq b
  obtain ⟨N, hsN⟩ := s.exists_nat_subset_range
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← hscard]
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hsK hz⟩
  have hzN : z < N := by simpa only [Finset.mem_range] using hsN hz
  exact hzN.trans_le hn

lemma half_density_of_count {A D K : Set ℕ} (hK : K.Infinite)
    (hAK : A ⊆ K) (hDK : D ⊆ K) (c : ℕ)
    (hcount : ∀ n,
      GenLimit.PatientScope.prefixCount A n ≤
        2 * GenLimit.PatientScope.prefixCount D n + c) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity D K := by
  let ar : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let dr : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have harLower : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop ar :=
    ratio_bounded_below A K
  have hdrLower : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop dr :=
    ratio_bounded_below D K
  have hdrUpper : IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop dr :=
    Filter.isCoboundedUnder_ge_of_le atTop (ratio_le_one hDK)
  change (1 / 2 : ℝ) * liminf ar atTop ≤ liminf dr atTop
  rw [Filter.le_liminf_iff' hdrUpper hdrLower]
  intro b hb
  let δ : ℝ := (liminf ar atTop - 2 * b) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hbelow : 2 * b + δ < liminf ar atTop := by
    dsimp [δ]
    linarith
  have har : ∀ᶠ n in atTop, 2 * b + δ < ar n :=
    Filter.eventually_lt_of_lt_liminf hbelow harLower
  have hkNat := prefixCount_tendsto_atTop hK
  have hkReal : Tendsto (fun n =>
      (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkNat
  have herr0 : Tendsto (fun n => (c : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hkReal
  have herr : ∀ᶠ n in atTop, (c : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) < δ := by
    filter_upwards [herr0.eventually (Iio_mem_nhds hδ)] with n hn
    exact hn
  have hkpos : ∀ᶠ n in atTop,
      0 < GenLimit.PatientScope.prefixCount K n := by
    filter_upwards [hkNat.eventually (eventually_gt_atTop 0)] with n hn
    exact hn
  filter_upwards [har, herr, hkpos] with n han hen hkn
  have hc : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
      2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + c := by
    exact_mod_cast hcount n
  have hkreal : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hkn
  have hcdiv := div_le_div_of_nonneg_right hc hkreal.le
  have hsplit :
      (2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + c) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) =
        2 * ((GenLimit.PatientScope.prefixCount D n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ)) +
        (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) := by
    field_simp
  rw [hsplit] at hcdiv
  change b ≤ dr n
  dsimp [ar] at han
  dsimp [dr]
  linarith

noncomputable def firstTime (input : Stage3Case017.Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

lemma firstTime_spec (input : Stage3Case017.Stream) {z : ℕ}
    (hz : z ∈ Set.range input) : input (firstTime input z) = z := by
  classical
  rcases hz with ⟨t, rfl⟩
  let h : ∃ q, input q = input t := ⟨t, rfl⟩
  simp only [firstTime, dif_pos h]
  exact Nat.find_spec h

lemma firstTime_min (input : Stage3Case017.Stream) {z : ℕ}
    (hz : z ∈ Set.range input) {s : ℕ} (hs : input s = z) :
    firstTime input z ≤ s := by
  classical
  rcases hz with ⟨t, rfl⟩
  let h : ∃ q, input q = input t := ⟨t, rfl⟩
  simp only [firstTime, dif_pos h]
  exact Nat.find_min' h hs

lemma core_not_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (learner family) input) := by
  classical
  intro z hz
  rcases hz with ⟨hzcore, hzinput⟩
  by_contra hzGF
  have hzoutput : z ∉ Set.range (run (learner family) input) := by
    intro hr
    rcases hr with ⟨q, hq⟩
    apply hzGF
    refine ⟨q, hq, ?_⟩
    intro s hs his
    apply hzinput
    exact ⟨s, his⟩
  let T := threshold family input
  let f : Fin (z + 2) → Fin (z + 1) := fun k =>
    ⟨run (learner family) input (T + k), by
      have ht : threshold family input ≤ T + (k : ℕ) := by
        simp [T]
      have hav : available family
          (fun i : Fin (T + (k : ℕ) + 1) => input i)
          (fun i : Fin (T + (k : ℕ)) => run (learner family) input i) z := by
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          exact hzcore j ((compatible_iff_streamIn family input ht j).mp hj)
        · intro i hzi
          apply hzinput
          exact ⟨i, hzi.symm⟩
        · intro i hzi
          apply hzoutput
          exact ⟨i, hzi.symm⟩
      exact Nat.lt_succ_iff.mpr (output_le_available family input hav)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    by_contra habv
    have hlt : T + (a : ℕ) < T + (b : ℕ) ∨ T + (b : ℕ) < T + (a : ℕ) :=
      lt_or_gt_of_ne (by omega)
    rcases hlt with hlt | hlt
    · have hs := (output_spec family input hcore (show threshold family input ≤ T + (b : ℕ) by simp [T])).2.2
      have hout : run (learner family) input (T + (a : ℕ)) =
          run (learner family) input (T + (b : ℕ)) := by
        simpa [f] using congrArg Fin.val hab
      exact (hs ⟨T + (a : ℕ), hlt⟩) hout.symm
    · have hs := (output_spec family input hcore (show threshold family input ≤ T + (a : ℕ) by simp [T])).2.2
      have hout : run (learner family) input (T + (a : ℕ)) =
          run (learner family) input (T + (b : ℕ)) := by
        simpa [f] using congrArg Fin.val hab
      exact (hs ⟨T + (b : ℕ), hlt⟩) hout
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

noncomputable def early {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) : Set ℕ :=
  ↑(GenLimit.sample input (threshold family input + 1))

noncomputable def defense {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) : Set ℕ :=
  GenLimit.GeneratorFirst input (run (learner family) input) ∩
    Stage3Case017.informationCore family input

noncomputable def regular {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream) : Set ℕ :=
  Stage3Case017.informationCore family input \ (defense family input ∪ early family input)

noncomputable def partner {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (z : ℕ) : ℕ :=
  run (learner family) input (firstTime input z - 1)

lemma regular_firstTime {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ regular family input) :
    threshold family input < firstTime input z := by
  have hzcore : z ∈ Stage3Case017.informationCore family input := hz.1
  have hzD : z ∉ defense family input := fun h => hz.2 (Or.inl h)
  have hzrange : z ∈ Set.range input := by
    by_contra hzr
    exact hzD ⟨core_not_range_subset_generatorFirst family input hcore ⟨hzcore, hzr⟩, hzcore⟩
  by_contra hle
  have hq : firstTime input z ≤ threshold family input := Nat.le_of_not_gt hle
  apply hz.2
  right
  simp only [early, GenLimit.sample, Finset.mem_coe, Finset.mem_image,
    Finset.mem_range]
  exact ⟨firstTime input z, Nat.lt_succ_iff.mpr hq, firstTime_spec input hzrange⟩

lemma regular_partner_lt_mem {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ regular family input) :
    partner family input z < z ∧
      partner family input z ∈ defense family input := by
  classical
  have hzcore := hz.1
  have hzD : z ∉ defense family input := fun h => hz.2 (Or.inl h)
  have hzrange : z ∈ Set.range input := by
    by_contra hzr
    exact hzD ⟨core_not_range_subset_generatorFirst family input hcore ⟨hzcore, hzr⟩, hzcore⟩
  let q := firstTime input z
  have hTq : threshold family input < q := regular_firstTime family input hcore hz
  have hqpos : 0 < q := by omega
  have hTpred : threshold family input ≤ q - 1 := by omega
  have hinput : ∀ i : Fin q, z ≠ input i := by
    intro i hiz
    have hmin := firstTime_min input hzrange hiz.symm
    change q ≤ (i : ℕ) at hmin
    omega
  have houtput : ∀ i : Fin (q - 1), z ≠ run (learner family) input i := by
    intro i hiz
    apply hzD
    refine ⟨⟨i, hiz.symm, ?_⟩, hzcore⟩
    intro s hs his
    exact hinput ⟨s, by omega⟩ his.symm
  have hav : available family (fun i : Fin ((q - 1) + 1) => input i)
      (fun i : Fin (q - 1) => run (learner family) input i) z := by
    refine ⟨?_, ?_, houtput⟩
    · intro j hj
      exact hzcore j ((compatible_iff_streamIn family input hTpred j).mp (by
        simpa [Nat.sub_add_cancel hqpos] using hj))
    · intro i
      have hiq : (i : ℕ) < q := by omega
      exact hinput ⟨i, hiq⟩
  have hle : partner family input z ≤ z := by
    exact output_le_available family input (by
      simpa [partner, q, Nat.sub_add_cancel hqpos] using hav)
  have hpD : partner family input z ∈ defense family input := by
    have hos := output_spec family input hcore hTpred
    refine ⟨⟨q - 1, rfl, ?_⟩, ?_⟩
    · intro s hs his
      exact hos.2.1 ⟨s, by omega⟩ his.symm
    · intro j hj
      exact hos.1 j ((compatible_iff_streamIn family input hTpred j).mpr hj)
  exact ⟨lt_of_le_of_ne hle (fun he => hzD (he ▸ hpD)), hpD⟩

lemma partner_injOn {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (input_inj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Set.InjOn (partner family input) (regular family input) := by
  intro a ha b hb hp
  let qa := firstTime input a
  let qb := firstTime input b
  have hTa : threshold family input < qa := regular_firstTime family input hcore ha
  have hTb : threshold family input < qb := regular_firstTime family input hcore hb
  have hpa : partner family input a = run (learner family) input (qa - 1) := rfl
  have hpb : partner family input b = run (learner family) input (qb - 1) := rfl
  have hqpred : qa - 1 = qb - 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hs := (output_spec family input hcore
          (show threshold family input ≤ qb - 1 by omega)).2.2
      exact (hs ⟨qa - 1, hlt⟩) (by simpa [hpa, hpb] using hp.symm)
    · have hs := (output_spec family input hcore
          (show threshold family input ≤ qa - 1 by omega)).2.2
      exact (hs ⟨qb - 1, hlt⟩) (by simpa [hpa, hpb] using hp)
  have hq : qa = qb := by omega
  have harange : a ∈ Set.range input := by
    by_contra hzr
    exact ha.2 (Or.inl ⟨core_not_range_subset_generatorFirst family input hcore ⟨ha.1, hzr⟩, ha.1⟩)
  have hbrange : b ∈ Set.range input := by
    by_contra hzr
    exact hb.2 (Or.inl ⟨core_not_range_subset_generatorFirst family input hcore ⟨hb.1, hzr⟩, hb.1⟩)
  calc
    a = input qa := (firstTime_spec input harange).symm
    _ = input qb := congrArg input hq
    _ = b := firstTime_spec input hbrange

lemma core_count_le {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (input_inj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount (defense family input) n +
        (GenLimit.sample input (threshold family input + 1)).card := by
  classical
  let C := GenLimit.PatientScope.prefixFinset
      (Stage3Case017.informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset (defense family input) n
  let E := GenLimit.sample input (threshold family input + 1)
  let R := GenLimit.PatientScope.prefixFinset (regular family input) n
  have hRleD : R.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (partner family input)
    · intro z hz
      change z ∈ GenLimit.PatientScope.prefixFinset (regular family input) n at hz
      have hzparts := Finset.mem_filter.mp hz
      have hzR : z ∈ regular family input := hzparts.2
      have hp := regular_partner_lt_mem family input hcore hzR
      have hzlt : z < n := by simpa only [Finset.mem_range] using hzparts.1
      change partner family input z ∈
        GenLimit.PatientScope.prefixFinset (defense family input) n
      exact Finset.mem_filter.mpr ⟨by simpa using hp.1.trans hzlt, hp.2⟩
    · exact (partner_injOn family input input_inj hcore).mono (by
        intro z hz
        change z ∈ GenLimit.PatientScope.prefixFinset (regular family input) n at hz
        exact (Finset.mem_filter.mp hz).2)
  have hCsub : C ⊆ D ∪ E ∪ R := by
    intro z hz
    change z ∈ GenLimit.PatientScope.prefixFinset
      (Stage3Case017.informationCore family input) n at hz
    have hzparts := Finset.mem_filter.mp hz
    have hzC : z ∈ Stage3Case017.informationCore family input := hzparts.2
    by_cases hzD : z ∈ defense family input
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      change z ∈ GenLimit.PatientScope.prefixFinset (defense family input) n
      exact Finset.mem_filter.mpr ⟨hzparts.1, hzD⟩
    by_cases hzE : z ∈ early family input
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      change z ∈ GenLimit.sample input (threshold family input + 1)
      simpa [early] using hzE
    · apply Finset.mem_union_right
      change z ∈ GenLimit.PatientScope.prefixFinset (regular family input) n
      exact Finset.mem_filter.mpr ⟨hzparts.1, ⟨hzC, by simp [hzD, hzE]⟩⟩
  have hc := Finset.card_le_card hCsub
  have hu := Finset.card_union_le (D ∪ E) R
  have hde := Finset.card_union_le D E
  change C.card ≤ 2 * D.card + E.card
  omega

end Stage3Case017Proof

open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinf
  refine ⟨learner family, ?_⟩
  intro input input_inj hex hcore
  refine ⟨run (learner family) input, run_follows _ _, ?_⟩
  intro j hj
  constructor
  · refine ⟨threshold family input, ?_⟩
    intro t ht
    have hs := output_spec family input hcore ht
    refine ⟨?_, ?_, ?_⟩
    · exact hs.1 j ((compatible_iff_streamIn family input ht j).mpr hj)
    · intro hmem
      simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
      rcases hmem with ⟨s, hslt, heq⟩
      exact hs.2.1 ⟨s, hslt⟩ heq.symm
    · intro s hslt heq
      exact hs.2.2 ⟨s, hslt⟩ heq.symm
  · let C := Stage3Case017.informationCore family input
    let G := GenLimit.GeneratorFirst input (run (learner family) input)
    let K := family j
    have hCK : C ⊆ K := by
      intro z hz
      exact hz j hj
    have hDK : defense family input ⊆ K := by
      intro z hz
      exact hCK hz.2
    have hDG : defense family input ⊆ G ∩ K := by
      intro z hz
      exact ⟨hz.1, hCK hz.2⟩
    have hGK : G ∩ K ⊆ K := Set.inter_subset_right
    have hhalfD :
        (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity C K ≤
          GenLimit.PatientScope.relativeLowerDensity (defense family input) K := by
      apply half_density_of_count (hinf j) hCK hDK
        (GenLimit.sample input (threshold family input + 1)).card
      intro n
      exact core_count_le family input input_inj hcore n
    have hhalf :
        (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity C K ≤
          GenLimit.PatientScope.relativeLowerDensity (G ∩ K) K :=
      hhalfD.trans (relativeLowerDensity_mono hDG hGK)
    have hneverSub : C \ Set.range input ⊆ G ∩ K := by
      intro z hz
      exact ⟨core_not_range_subset_generatorFirst family input hcore hz, hCK hz.1⟩
    have hnever :
        GenLimit.PatientScope.relativeLowerDensity (C \ Set.range input) K ≤
          GenLimit.PatientScope.relativeLowerDensity (G ∩ K) K :=
      relativeLowerDensity_mono hneverSub hGK
    exact max_le hhalf hnever

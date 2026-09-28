import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Case017

open Stage3Case017

noncomputable def historyFinset {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  Finset.univ.image xs

def currentCore {m n : ℕ} (family : Fin m → Language) (xs : Fin n → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def leastFresh (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset used)

lemma leastFresh_mem (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ) :
    leastFresh S hS used ∈ S :=
  by
    classical
    exact (Nat.find_spec (hS.exists_notMem_finset used)).1

lemma leastFresh_not_mem (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ) :
    leastFresh S hS used ∉ used :=
  by
    classical
    exact (Nat.find_spec (hS.exists_notMem_finset used)).2

lemma leastFresh_le (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hzused : z ∉ used) :
    leastFresh S hS used ≤ z :=
  by
    classical
    exact Nat.find_min' (hS.exists_notMem_finset used) ⟨hzS, hzused⟩

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let used := historyFinset xs ∪ historyFinset ys
    if h : (currentCore family xs).Infinite then
      leastFresh (currentCore family xs) h used
    else
      leastFresh Set.univ Set.infinite_univ used

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => Nat.strongRecOn t fun t earlier =>
    gen t (fun i => input i) (fun i => earlier i i.isLt)

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory, Nat.strongRecOn_eq]
  congr

lemma mem_historyFinset {n : ℕ} {xs : Fin n → ℕ} {z : ℕ} :
    z ∈ historyFinset xs ↔ ∃ i, xs i = z := by
  simp [historyFinset]

lemma generator_fresh {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∉ historyFinset xs ∪ historyFinset ys := by
  simp only [familyGenerator]
  split_ifs with h
  · exact leastFresh_not_mem _ h _
  · exact leastFresh_not_mem _ Set.infinite_univ _

lemma generator_mem_core {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) :
    familyGenerator family t xs ys ∈ currentCore family xs := by
  simp [familyGenerator, h, leastFresh_mem]

lemma generator_le_core {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentCore family xs).Infinite) {z : ℕ}
    (hz : z ∈ currentCore family xs)
    (hzx : ∀ i, xs i ≠ z) (hzy : ∀ i, ys i ≠ z) :
    familyGenerator family t xs ys ≤ z := by
  rw [familyGenerator]
  simp only [dif_pos h]
  apply leastFresh_le _ h
  · exact hz
  · simp only [Finset.mem_union, mem_historyFinset, not_or, not_exists]
    exact ⟨hzx, hzy⟩

noncomputable def exclusionTime (input : Stream) (L : Language) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input L then 0
  else Nat.find (show ∃ n, input n ∉ L by
    simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

lemma exclusionTime_spec {input : Stream} {L : Language}
    (h : ¬ GenLimit.Generic.StreamIn input L) :
    input (exclusionTime input L) ∉ L := by
  classical
  rw [exclusionTime, dif_neg h]
  exact Nat.find_spec (show ∃ n, input n ∉ L by
    simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  (Finset.univ.sup (fun j => exclusionTime input (family j)) : ℕ)

lemma exclusionTime_le_stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    exclusionTime input (family j) ≤ stabilizationTime family input := by
  classical
  unfold stabilizationTime
  exact Finset.le_sup (s := Finset.univ) (f := fun k : Fin m => exclusionTime input (family k))
    (Finset.mem_univ j)

lemma prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp
    by_contra hstream
    have hw := exclusionTime_spec hstream
    have hle : exclusionTime input (family j) ≤ t :=
      (exclusionTime_le_stabilizationTime family input j).trans ht
    exact hw (hp ⟨exclusionTime input (family j), Nat.lt_succ_of_le hle⟩)
  · intro hstream i
    exact hstream ⟨i, rfl⟩

lemma currentCore_eq_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) = informationCore family input := by
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input ht j).2 hj)
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input ht j).1 hj)

lemma trajectory_fresh {m : ℕ} (family : Fin m → Language) (input : Stream)
    (t : ℕ) :
    trajectory (familyGenerator family) input t ∉
      GenLimit.sample input (t + 1) ∧
    ∀ s, s < t → trajectory (familyGenerator family) input s ≠
      trajectory (familyGenerator family) input t := by
  have hfresh := generator_fresh family t
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i)
  rw [← trajectory_follows (familyGenerator family) input t] at hfresh
  constructor
  · intro hmem
    rw [GenLimit.sample] at hmem
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact hfresh (Finset.mem_union_left _ ((mem_historyFinset).2 ⟨⟨s, hs⟩, heq⟩))
  · intro s hs heq
    exact hfresh (Finset.mem_union_right _ ((mem_historyFinset).2 ⟨⟨s, hs⟩, heq⟩))

lemma eventual_novel {m : ℕ} (family : Fin m → Language) (input output : Stream)
    (hcore : (informationCore family input).Infinite)
    (hfollow : Follows (familyGenerator family) input output)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input output (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  have hEq := currentCore_eq_informationCore family input ht
  have hInf : (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := hEq ▸ hcore
  have hmem := generator_mem_core family t
      (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i) hInf
  rw [← hfollow t] at hmem
  have htarget : output t ∈ family j := by
    rw [hEq] at hmem
    exact hmem j hj
  have hfresh := trajectory_fresh family input t
  have hout : output = trajectory (familyGenerator family) input := by
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rw [hfollow n, trajectory_follows (familyGenerator family) input n]
      congr 1
      funext i
      exact ih i i.isLt
  rw [← hout] at hfresh
  exact ⟨htarget, hfresh.1, hfresh.2⟩


lemma follows_unique {gen : OnlineGenerator} {input output : Stream}
    (hfollow : Follows gen input output) :
    output = trajectory gen input := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hfollow n, trajectory_follows gen input n]
    congr 1
    funext i
    exact ih i i.isLt

lemma trajectory_injective {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Function.Injective (trajectory (familyGenerator family) input) := by
  intro s t heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (trajectory_fresh family input t).2 s hst heq
  · exact (trajectory_fresh family input s).2 t hts heq.symm

lemma follows_injective {m : ℕ} (family : Fin m → Language) (input output : Stream)
    (hfollow : Follows (familyGenerator family) input output) :
    Function.Injective output := by
  rw [follows_unique hfollow]
  exact trajectory_injective family input

lemma core_unpresented_is_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hcore : (informationCore family input).Infinite)
    (hfollow : Follows (familyGenerator family) input output)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hzinput : z ∉ Set.range input) :
    z ∈ GenLimit.GeneratorFirst input output := by
  have houtinj := follows_injective family input output hfollow
  have hzout : z ∈ Set.range output := by
    by_contra hzout
    let shifted : ℕ → ℕ := fun k => output (stabilizationTime family input + k)
    have hshiftinj : Function.Injective shifted := by
      intro a b hab
      exact Nat.add_left_cancel (houtinj hab)
    have hinfinite : (Set.range shifted).Infinite :=
      Set.infinite_range_of_injective hshiftinj
    have hsubset : Set.range shifted ⊆ Set.Iic z := by
      rintro y ⟨k, rfl⟩
      let t := stabilizationTime family input + k
      have ht : stabilizationTime family input ≤ t := Nat.le_add_right _ _
      have hEq := currentCore_eq_informationCore family input ht
      have hInf : (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := hEq ▸ hcore
      have hzcur : z ∈ currentCore family (fun i : Fin (t + 1) => input i) := by
        rw [hEq]
        exact hzcore
      have hzx : ∀ i : Fin (t + 1), input i ≠ z := by
        intro i heq
        exact hzinput ⟨i, heq⟩
      have hzy : ∀ i : Fin t, output i ≠ z := by
        intro i heq
        exact hzout ⟨i, heq⟩
      have hle := generator_le_core family t
        (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i)
        hInf hzcur hzx hzy
      rw [← hfollow t] at hle
      exact hle
    exact (Set.finite_Iic z).not_infinite (hinfinite.mono hsubset)
  obtain ⟨t, ht⟩ := hzout
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hzinput ⟨s, heq⟩

lemma core_covered {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hcore : (informationCore family input).Infinite)
    (hfollow : Follows (familyGenerator family) input output) :
    informationCore family input ⊆ Set.range input ∪ GenLimit.GeneratorFirst input output := by
  intro z hz
  by_cases hzin : z ∈ Set.range input
  · exact Or.inl hzin
  · exact Or.inr (core_unpresented_is_generatorFirst family input output hcore hfollow hz hzin)

end Case017

namespace Case017

open Stage3Case017

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_range] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · filter_upwards [] with n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  · apply Filter.isBoundedUnder_of_eventually_ge
    filter_upwards [] with n
    positivity
  · apply Filter.IsCoboundedUnder.of_frequently_le (a := (1 : ℝ))
    apply Filter.Frequently.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · rw [hzero]
      simp
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono hBK n

lemma missing_core_density_bound {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hcore : (informationCore family input).Infinite)
    (hfollow : Follows (familyGenerator family) input output)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    refine ⟨core_unpresented_is_generatorFirst family input output hcore hfollow hz.1 hz.2, ?_⟩
    exact hz.1 j hj
  · exact Set.inter_subset_right


noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ :=
  Function.invFun input z

lemma input_inputTime {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  exact Function.invFun_eq hz


lemma mem_prefixFinset {S : Set ℕ} {n z : ℕ} :
    z ∈ GenLimit.PatientScope.prefixFinset S n ↔ z < n ∧ z ∈ S := by
  simp [GenLimit.PatientScope.prefixFinset]

lemma prefix_race_bound {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (hfollow : Follows (familyGenerator family) input output)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j) n +
        2 * stabilizationTime family input + 1 := by
  classical
  let T := stabilizationTime family input
  let P := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ family j) n
  let E := GenLimit.sample input T ∪ GenLimit.sample output T
  let A := P \ (D ∪ E)
  have houtinj := follows_injective family input output hfollow
  have hsample_input : (GenLimit.sample input T).card ≤ T := by
    simpa [GenLimit.sample] using
      (Finset.card_image_le (s := Finset.range T) (f := input))
  have hsample_output : (GenLimit.sample output T).card ≤ T := by
    simpa [GenLimit.sample] using
      (Finset.card_image_le (s := Finset.range T) (f := output))
  have hcardE : E.card ≤ 2 * T := by
    calc
      E.card ≤ (GenLimit.sample input T).card + (GenLimit.sample output T).card :=
        Finset.card_union_le _ _
      _ ≤ T + T := Nat.add_le_add hsample_input hsample_output
      _ = 2 * T := by omega
  have hcardA : A.card ≤ D.card + 1 := by
    by_cases hA : A.Nonempty
    · obtain ⟨last, hlastA, hlastmax⟩ := Finset.exists_max_image A (inputTime input) hA
      have hlastData := Finset.mem_sdiff.mp hlastA
      have hlastP : last ∈ P := hlastData.1
      have hlastnotDE : last ∉ D ∪ E := hlastData.2
      have hlastPD := (mem_prefixFinset.mp (show last ∈
        GenLimit.PatientScope.prefixFinset (informationCore family input) n by exact hlastP))
      have hlastcore := hlastPD.2
      have hlastrange : last ∈ Set.range input := by
        rcases core_covered family input output hcore hfollow hlastcore with hrange | hGF
        · exact hrange
        · exfalso
          apply hlastnotDE
          apply Finset.mem_union_left
          apply (mem_prefixFinset).2
          exact ⟨hlastPD.1, hGF, hlastcore j hj⟩
      have hlasttime : input (inputTime input last) = last := input_inputTime hlastrange
      have hmap : Set.MapsTo (fun z => output (inputTime input z))
          (↑(A.erase last) : Set ℕ) (↑D : Set ℕ) := by
        intro z hz
        have hzA : z ∈ A := (Finset.mem_erase.mp hz).2
        have hzne : z ≠ last := (Finset.mem_erase.mp hz).1
        have hzData := Finset.mem_sdiff.mp hzA
        have hzP : z ∈ P := hzData.1
        have hznotDE : z ∉ D ∪ E := hzData.2
        have hzPD := (mem_prefixFinset.mp (show z ∈
          GenLimit.PatientScope.prefixFinset (informationCore family input) n by exact hzP))
        have hzcore := hzPD.2
        have hzrange : z ∈ Set.range input := by
          rcases core_covered family input output hcore hfollow hzcore with hrange | hGF
          · exact hrange
          · exfalso
            apply hznotDE
            apply Finset.mem_union_left
            apply (mem_prefixFinset).2
            exact ⟨hzPD.1, hGF, hzcore j hj⟩
        have hztime : input (inputTime input z) = z := input_inputTime hzrange
        have htlt : inputTime input z < inputTime input last := by
          have hle := hlastmax z hzA
          apply lt_of_le_of_ne hle
          intro heq
          apply hzne
          rw [← hztime, ← hlasttime, heq]
        have htT : T ≤ inputTime input z := by
          by_contra hnot
          have hlt : inputTime input z < T := Nat.lt_of_not_ge hnot
          apply hznotDE
          apply Finset.mem_union_right
          apply Finset.mem_union_left
          unfold GenLimit.sample
          simp only [Finset.mem_image, Finset.mem_range]
          exact ⟨inputTime input z, hlt, hztime⟩
        have hlast_not_input : ∀ i : Fin (inputTime input z + 1), input i ≠ last := by
          intro i hi
          have hieq : (i : ℕ) = inputTime input last := hinj (hi.trans hlasttime.symm)
          omega
        have hlast_not_output : ∀ i : Fin (inputTime input z), output i ≠ last := by
          intro i hi
          have hGF : last ∈ GenLimit.GeneratorFirst input output := by
            refine ⟨i, hi, ?_⟩
            intro s hs hsin
            have hseq : s = inputTime input last := hinj (hsin.trans hlasttime.symm)
            omega
          apply hlastnotDE
          apply Finset.mem_union_left
          apply (mem_prefixFinset).2
          exact ⟨hlastPD.1, hGF, hlastcore j hj⟩
        have hEq := currentCore_eq_informationCore family input htT
        have hInf : (currentCore family
            (fun i : Fin (inputTime input z + 1) => input i)).Infinite := hEq ▸ hcore
        have hlastcur : last ∈ currentCore family
            (fun i : Fin (inputTime input z + 1) => input i) := by
          rw [hEq]
          exact hlastcore
        have hle := generator_le_core family (inputTime input z)
          (fun i : Fin (inputTime input z + 1) => input i)
          (fun i : Fin (inputTime input z) => output i)
          hInf hlastcur hlast_not_input hlast_not_output
        rw [← hfollow (inputTime input z)] at hle
        have houtGF : output (inputTime input z) ∈ GenLimit.GeneratorFirst input output := by
          refine ⟨inputTime input z, rfl, ?_⟩
          intro s hs heq
          have hfresh := generator_fresh family (inputTime input z)
            (fun i : Fin (inputTime input z + 1) => input i)
            (fun i : Fin (inputTime input z) => output i)
          rw [← hfollow (inputTime input z)] at hfresh
          apply hfresh
          apply Finset.mem_union_left
          exact (mem_historyFinset).2 ⟨⟨s, Nat.lt_succ_of_le hs⟩, heq⟩
        have houtcore : output (inputTime input z) ∈ informationCore family input := by
          have hmem := generator_mem_core family (inputTime input z)
            (fun i : Fin (inputTime input z + 1) => input i)
            (fun i : Fin (inputTime input z) => output i) hInf
          rw [← hfollow (inputTime input z), hEq] at hmem
          exact hmem
        apply (mem_prefixFinset).2
        exact ⟨lt_of_le_of_lt hle hlastPD.1, houtGF, houtcore j hj⟩
      have hmapinj : Set.InjOn (fun z => output (inputTime input z))
          (↑(A.erase last) : Set ℕ) := by
        intro x hx y hy heq
        have htimes := houtinj heq
        have hxA : x ∈ A := (Finset.mem_erase.mp hx).2
        have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
        have hxP : x ∈ P := (Finset.mem_sdiff.mp hxA).1
        have hyP : y ∈ P := (Finset.mem_sdiff.mp hyA).1
        have hxPD := (mem_prefixFinset.mp (show x ∈
          GenLimit.PatientScope.prefixFinset (informationCore family input) n by exact hxP))
        have hyPD := (mem_prefixFinset.mp (show y ∈
          GenLimit.PatientScope.prefixFinset (informationCore family input) n by exact hyP))
        have hxrange : x ∈ Set.range input := by
          rcases core_covered family input output hcore hfollow hxPD.2 with h | h
          · exact h
          · exfalso
            have hxnotD : x ∉ D := fun hxD => (Finset.mem_sdiff.mp hxA).2 (Finset.mem_union_left _ hxD)
            apply hxnotD
            apply (mem_prefixFinset).2
            exact ⟨hxPD.1, h, hxPD.2 j hj⟩
        have hyrange : y ∈ Set.range input := by
          rcases core_covered family input output hcore hfollow hyPD.2 with h | h
          · exact h
          · exfalso
            have hynotD : y ∉ D := fun hyD => (Finset.mem_sdiff.mp hyA).2 (Finset.mem_union_left _ hyD)
            apply hynotD
            apply (mem_prefixFinset).2
            exact ⟨hyPD.1, h, hyPD.2 j hj⟩
        rw [← input_inputTime hxrange, ← input_inputTime hyrange, htimes]
      have herase : (A.erase last).card ≤ D.card :=
        Finset.card_le_card_of_injOn _ hmap hmapinj
      have hcarderase := Finset.card_erase_add_one hlastA
      omega
    · have hAempty := Finset.not_nonempty_iff_eq_empty.mp hA
      simp [hAempty]
  have hPsubset : P ⊆ D ∪ E ∪ A := by
    intro z hz
    by_cases hzDE : z ∈ D ∪ E
    · exact Finset.mem_union_left _ hzDE
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨hz, hzDE⟩
  have hcardP : P.card ≤ D.card + E.card + A.card := by
    calc
      P.card ≤ (D ∪ E ∪ A).card := Finset.card_le_card hPsubset
      _ ≤ (D ∪ E).card + A.card := Finset.card_union_le _ _
      _ ≤ D.card + E.card + A.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  change P.card ≤ 2 * D.card + 2 * T + 1
  omega


lemma prefixCount_eq_indicatorSum (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => (1 : ℕ)) k := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ∈ S <;> simp [Set.indicator, h]

lemma prefixCount_tendsto_atTop {S : Set ℕ} (hS : S.Infinite) :
    Filter.Tendsto (GenLimit.PatientScope.prefixCount S) Filter.atTop Filter.atTop := by
  have h := (Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ)
    (r := (1 : ℕ)) (by omega)).1 hS
  simpa only [← prefixCount_eq_indicatorSum] using h

lemma liminf_half_mul (f : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ f n) (h1 : ∀ n, f n ≤ 1) :
    Filter.liminf (fun n => (1 / 2 : ℝ) * f n) Filter.atTop =
      (1 / 2 : ℝ) * Filter.liminf f Filter.atTop := by
  have hc0 : ∀ᶠ n in Filter.atTop, (0 : ℝ) ≤ (1 / 2 : ℝ) :=
    Filter.Eventually.of_forall (fun _ : ℕ => by norm_num)
  have hcb : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun _ : ℕ => (1 / 2 : ℝ)) :=
    Filter.isBoundedUnder_of_eventually_le (a := (1 / 2 : ℝ))
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hf0 : ∀ᶠ n in Filter.atTop, 0 ≤ f n :=
    Filter.Eventually.of_forall h0
  have hfc : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop f :=
    Filter.IsCoboundedUnder.of_frequently_le (a := (1 : ℝ))
      (Filter.Frequently.of_forall h1)
  apply le_antisymm
  · simpa using (liminf_mul_le (f := Filter.atTop)
      (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := f) hc0 hcb hf0 hfc)
  · simpa using (le_liminf_mul (f := Filter.atTop)
      (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := f) hc0 hcb hf0 hfc)

lemma half_core_density_bound {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite)
    (input output : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (hfollow : Follows (familyGenerator family) input output)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
  let coreRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let winRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input output ∩ family j) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let error : ℕ → ℝ := fun n =>
    ((2 * stabilizationTime family input + 1 : ℕ) : ℝ) / 2 /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  have hcore_subset : informationCore family input ⊆ family j := fun z hz => hz j hj
  have hwin_subset : GenLimit.GeneratorFirst input output ∩ family j ⊆ family j :=
    Set.inter_subset_right
  have hcore0 : ∀ n, 0 ≤ coreRatio n := by intro n; positivity
  have hcore1 : ∀ n, coreRatio n ≤ 1 := by
    intro n
    by_cases hk : GenLimit.PatientScope.prefixCount (family j) n = 0
    · simp [coreRatio, hk]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono hcore_subset n
  have hwin0 : ∀ n, 0 ≤ winRatio n := by intro n; positivity
  have hwin1 : ∀ n, winRatio n ≤ 1 := by
    intro n
    by_cases hk : GenLimit.PatientScope.prefixCount (family j) n = 0
    · simp [winRatio, hk]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono hwin_subset n
  have hcount := prefixCount_tendsto_atTop (hfamily j)
  have herr : Filter.Tendsto error Filter.atTop (𝓝 0) := by
    have hdiv := (tendsto_const_div_atTop_nhds_zero_nat
      (((2 * stabilizationTime family input + 1 : ℕ) : ℝ) / 2)).comp hcount
    simpa [error] using hdiv
  have hpoint : ∀ n, (1 / 2 : ℝ) * coreRatio n ≤ winRatio n + error n := by
    intro n
    have hbound := prefix_race_bound family input output hinj hcore hfollow hj n
    by_cases hk : GenLimit.PatientScope.prefixCount (family j) n = 0
    · have hc0 : GenLimit.PatientScope.prefixCount (informationCore family input) n = 0 :=
        Nat.eq_zero_of_le_zero ((prefixCount_mono hcore_subset n).trans_eq hk)
      have hw0 : GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ family j) n = 0 :=
        Nat.eq_zero_of_le_zero ((prefixCount_mono hwin_subset n).trans_eq hk)
      simp [coreRatio, winRatio, error, hk, hc0, hw0]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount (family j) n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hboundR :
          (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) ≤
            2 * (GenLimit.PatientScope.prefixCount
              (GenLimit.GeneratorFirst input output ∩ family j) n : ℝ) +
              (2 * stabilizationTime family input + 1 : ℕ) := by
        exact_mod_cast hbound
      dsimp [coreRatio, winRatio, error]
      field_simp
      nlinarith [hboundR]
  have hmono : Filter.liminf (fun n => (1 / 2 : ℝ) * coreRatio n) Filter.atTop ≤
      Filter.liminf (fun n => winRatio n + error n) Filter.atTop := by
    apply Filter.liminf_le_liminf
    · exact Filter.Eventually.of_forall hpoint
    · apply Filter.isBoundedUnder_of_eventually_ge
      exact Filter.Eventually.of_forall (fun n => mul_nonneg (by norm_num) (hcore0 n))
    · apply Filter.IsCoboundedUnder.of_frequently_le (a := (2 : ℝ))
      apply (herr.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))).and_frequently
        (Filter.Frequently.of_forall hwin1) |>.mono
      intro n hn
      linarith
  have hadd : Filter.liminf (fun n => winRatio n + error n) Filter.atTop ≤
      Filter.liminf winRatio Filter.atTop := by
    have h := liminf_add_le (f := Filter.atTop) (u := error) (v := winRatio)
      herr.isBoundedUnder_ge herr.isBoundedUnder_le
      (Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hwin0))
      (Filter.IsCoboundedUnder.of_frequently_le (a := (1 : ℝ))
        (Filter.Frequently.of_forall hwin1))
    rw [herr.limsup_eq, zero_add] at h
    simpa [add_comm] using h
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * Filter.liminf coreRatio Filter.atTop ≤
    Filter.liminf winRatio Filter.atTop
  rw [← liminf_half_mul coreRatio hcore0 hcore1]
  exact hmono.trans hadd

end Case017
open Case017

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨familyGenerator family, ?_⟩
  intro input hinj hpresentation hcore
  let output := trajectory (familyGenerator family) input
  refine ⟨output, trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨eventual_novel family input output hcore (trajectory_follows _ _) hj, ?_⟩
  apply max_le
  · exact half_core_density_bound family hfamily input output hinj hcore
      (trajectory_follows _ _) hj
  · exact missing_core_density_bound family input output hcore
      (trajectory_follows _ _) hj

import Stage3Model
import Mathlib.Data.Nat.Nth
import GenLimit.Paper39_DenseGeneration.Abstract.Density

namespace Stage3Work
open Set Stage3S2B

structure Hist (n : ℕ) where
  x : Fin n → ℕ
  q : Fin n → Option ℕ
  a : Fin n → Option Bool
  y : Fin n → ℕ

private def extend {n : ℕ} {α : Type} (old : Fin n → α) (new : α) : Fin (n+1) → α :=
  Fin.lastCases new old

lemma core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (by omega))

def Eligible {n : ℕ} (s : Hist n) (z : ℕ) : Prop :=
  (∀ i, s.x i ≠ z) ∧
  (z ∈ core ∨ ((∀ i, s.q i ≠ some z) ∧ (∀ i, s.y i ≠ z)))

lemma exists_eligible {n : ℕ} (s : Hist n) : ∃ z, Eligible s z := by
  have hfinite : (Set.range s.x).Finite := Set.finite_range _
  obtain ⟨z, hzcore, hz⟩ := core_infinite.exists_not_mem_finset hfinite.toFinset
  refine ⟨z, ?_, Or.inl hzcore⟩
  intro i hi
  apply hz
  exact Set.Finite.mem_toFinset hfinite |>.2 ⟨i, hi⟩

noncomputable def nextX {n : ℕ} (s : Hist n) : ℕ := by
  classical
  exact Nat.find (exists_eligible s)

lemma nextX_eligible {n : ℕ} (s : Hist n) : Eligible s (nextX s) := by
  classical
  exact Nat.find_spec (exists_eligible s)

noncomputable def step (gen : FeedbackGenerator) {n : ℕ} (s : Hist n) : Hist (n+1) := by
  classical
  let xnew := nextX s
  let xall : Fin (n+1) → ℕ := extend s.x xnew
  let qnew := gen.query n xall s.a
  let anew := match qnew with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, xall i = z))
  let aall : Fin (n+1) → Option Bool := extend s.a anew
  let ynew := gen.output n xall aall
  exact { x := xall, q := extend s.q qnew, a := aall, y := extend s.y ynew }

noncomputable def run (gen : FeedbackGenerator) : (n : ℕ) → Hist n
  | 0 => { x := Fin.elim0, q := Fin.elim0, a := Fin.elim0, y := Fin.elim0 }
  | n+1 => step gen (run gen n)

noncomputable def presentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (run gen (t+1)).x (Fin.last t)
noncomputable def query (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  (run gen (t+1)).q (Fin.last t)
noncomputable def answer (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  (run gen (t+1)).a (Fin.last t)
noncomputable def output (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (run gen (t+1)).y (Fin.last t)

noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation := presentation gen
  query := query gen
  answer := answer gen
  output := output gen

end Stage3Work

namespace Stage3Work
open Stage3S2B

lemma run_agrees (gen : FeedbackGenerator) : ∀ n (i : Fin n),
    (run gen n).x i = presentation gen i ∧
    (run gen n).q i = query gen i ∧
    (run gen n).a i = answer gen i ∧
    (run gen n).y i = output gen i := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [presentation, query, answer, output]
      · have h := ih j
        simpa [run, step, extend] using h

lemma presentation_eq_nextX (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t = nextX (run gen t) := by
  simp [presentation, run, step, extend]

lemma query_equation (gen : FeedbackGenerator) (t : ℕ) :
    query gen t = gen.query t
      (fun i => presentation gen i) (fun i => answer gen i) := by
  have hx := run_agrees gen (t+1)
  have ha := run_agrees gen t
  simp [query, run, step, extend]
  congr 1 <;> funext i
  · exact (hx i).1
  · exact (ha i).2.2.1

end Stage3Work

namespace Stage3Work
open Set Stage3S2B

noncomputable def target (gen : FeedbackGenerator) : Language :=
  Set.range (presentation gen)

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (presentation gen) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hel := (nextX_eligible (run gen j)).1 ⟨i, hlt⟩
    have hagree := (run_agrees gen j ⟨i, hlt⟩).1
    apply hel
    rw [hagree, ← presentation_eq_nextX gen j, hij]
  · have hel := (nextX_eligible (run gen i)).1 ⟨j, hlt⟩
    have hagree := (run_agrees gen i ⟨j, hlt⟩).1
    apply hel
    rw [hagree, ← presentation_eq_nextX gen i, hij]

lemma core_subset_target (gen : FeedbackGenerator) : core ⊆ target gen := by
  intro z hzcore
  by_contra hz
  have hnever : ∀ t, presentation gen t ≠ z := by
    intro t ht
    exact hz ⟨t, ht⟩
  have hbound : ∀ t, presentation gen t ≤ z := by
    intro t
    rw [presentation_eq_nextX]
    classical
    apply Nat.find_min' (exists_eligible (run gen t))
    exact ⟨fun i hi => hnever i ((run_agrees gen t i).1.symm.trans hi), Or.inl hzcore⟩
  let f : Fin (z+2) → Fin (z+1) := fun i =>
    ⟨presentation gen i, Nat.lt_succ_iff.mpr (hbound i)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    apply presentation_injective gen
    exact congrArg Fin.val h
  have hc := Fintype.card_le_of_injective f hf
  simp at hc

lemma target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨target gen \ core, (by intro z hz; exact hz.2), ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · intro z hz
    rcases hz with hc | hz
    · exact core_subset_target gen hc
    · exact hz.1

end Stage3Work

namespace Stage3Work
open Set Stage3S2B

lemma future_ne_of_query (gen : FeedbackGenerator) {t z s : ℕ}
    (hq : query gen t = some z) (hz : z ∉ core) (hts : t < s) :
    presentation gen s ≠ z := by
  intro hs
  have hel := (nextX_eligible (run gen s)).2
  rw [← presentation_eq_nextX gen s, hs] at hel
  rcases hel with hc | hrest
  · exact hz hc
  · have hrun := (run_agrees gen s ⟨t, hts⟩).2.1
    exact hrest.1 ⟨t, hts⟩ (hrun.trans hq)

lemma future_ne_of_output (gen : FeedbackGenerator) {t z s : ℕ}
    (hy : output gen t = z) (hz : z ∉ core) (hts : t < s) :
    presentation gen s ≠ z := by
  intro hs
  have hel := (nextX_eligible (run gen s)).2
  rw [← presentation_eq_nextX gen s, hs] at hel
  rcases hel with hc | hrest
  · exact hz hc
  · have hrun := (run_agrees gen s ⟨t, hts⟩).2.2.2
    exact hrest.2 ⟨t, hts⟩ (hrun.trans hy)

lemma target_mem_iff_at_query (gen : FeedbackGenerator) {t z : ℕ}
    (hq : query gen t = some z) :
    z ∈ target gen ↔ z ∈ core ∨ ∃ i : Fin (t+1), presentation gen i = z := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · right
      by_cases hst : s ≤ t
      · exact ⟨⟨s, Nat.lt_succ_iff.mpr hst⟩, hs⟩
      · exact False.elim (future_ne_of_query gen hq hc (Nat.lt_of_not_ge hst) hs)
  · rintro (hc | ⟨i, hi⟩)
    · exact core_subset_target gen hc
    · exact ⟨i, hi⟩

lemma answer_equation (gen : FeedbackGenerator) (t : ℕ) :
    answer gen t = match query gen t with
      | none => none
      | some z => some (membershipAnswer (target gen) z) := by
  have hqraw :
      gen.query t (extend (run gen t).x (nextX (run gen t))) (run gen t).a =
        query gen t := by
    simp [query, run, step, extend]
  simp only [answer, run, step, extend, hqraw]
  split
  · rw [Fin.lastCases_last]
  · rename_i z hq
    rw [Fin.lastCases_last]
    have hquery : query gen t = some z := hq
    unfold membershipAnswer
    congr 1
    apply (decide_eq_decide).2
    rw [target_mem_iff_at_query gen hquery]
    constructor
    · rintro (hc | ⟨i, hi⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, (run_agrees gen (t+1) i).1.symm.trans hi⟩
    · rintro (hc | ⟨i, hi⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, (run_agrees gen (t+1) i).1.trans hi⟩

lemma output_equation (gen : FeedbackGenerator) (t : ℕ) :
    output gen t = gen.output t
      (fun i => presentation gen i) (fun i => answer gen i) := by
  have hx := run_agrees gen (t+1)
  have ha := run_agrees gen (t+1)
  simp [output, run, step, extend]
  congr 1 <;> funext i
  · exact (hx i).1
  · exact (ha i).2.2.1

lemma follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  exact ⟨query_equation gen t, answer_equation gen t, output_equation gen t⟩

lemma output_mem_target_fresh_core (gen : FeedbackGenerator) {t : ℕ}
    (hmem : output gen t ∈ target gen)
    (hfresh : output gen t ∉ observedThrough (presentation gen) t) :
    output gen t ∈ core := by
  by_contra hc
  rcases hmem with ⟨s, hs⟩
  by_cases hst : s ≤ t
  · exact hfresh ⟨s, hst, hs⟩
  · exact future_ne_of_output gen rfl hc (Nat.lt_of_not_ge hst) hs

end Stage3Work

namespace Stage3Work
open Set Stage3S2B

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next := fun _ xs qs ans ys => nextX { x := xs, q := qs, a := ans, y := ys }

lemma presented_by (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  change presentation gen t = nextX {
    x := fun i => presentation gen i
    q := fun i => query gen i
    a := fun i => answer gen i
    y := fun i => output gen i }
  rw [presentation_eq_nextX]
  apply congrArg nextX
  cases hs : run gen t with
  | mk x q a y =>
      congr <;> funext i
      · simpa [hs] using (run_agrees gen t i).1
      · simpa [hs] using (run_agrees gen t i).2.1
      · simpa [hs] using (run_agrees gen t i).2.2.1
      · simpa [hs] using (run_agrees gen t i).2.2.2

lemma clean (gen : FeedbackGenerator) :
    Clean (presentation gen) (target gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma complete (gen : FeedbackGenerator) :
    Complete (presentation gen) (target gen) := by
  intro z hz
  exact hz

lemma scored_subset_core_union_initial (gen : FeedbackGenerator) {T : ℕ}
    (hvalid : ∀ t, T ≤ t →
      output gen t ∈ target gen ∧
      output gen t ∉ observedThrough (presentation gen) t) :
    scored (target gen) (presentation gen) (output gen) ⊆
      core ∪ Set.range (fun i : Fin T => output gen i) := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hfresh⟩
  by_cases ht : T ≤ t
  · left
    rw [← hyt]
    exact output_mem_target_fresh_core gen (hvalid t ht).1 (hvalid t ht).2
  · right
    exact ⟨⟨t, Nat.lt_of_not_ge ht⟩, hyt⟩

end Stage3Work

namespace Stage3Work
open Set Stage3S2B

private noncomputable def used {n : ℕ} (s : Hist n) : Finset ℕ := by
  classical
  exact (Finset.univ.image s.x) ∪
    (Finset.univ.biUnion fun i => (s.q i).toFinset) ∪
    (Finset.univ.image s.y)

private lemma range_nextX_subset_used {n : ℕ} (s : Hist n) :
    Finset.range (nextX s) ⊆ used s := by
  classical
  intro z hz
  simp only [Finset.mem_range] at hz
  by_contra hzu
  have hx : ∀ i, s.x i ≠ z := by
    intro i hi
    apply hzu
    simp only [used, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Option.mem_toFinset]
    aesop
  have hq : ∀ i, s.q i ≠ some z := by
    intro i hi
    apply hzu
    simp only [used, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Option.mem_toFinset]
    aesop
  have hy : ∀ i, s.y i ≠ z := by
    intro i hi
    apply hzu
    simp only [used, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Option.mem_toFinset]
    aesop
  have hel : Eligible s z := ⟨hx, Or.inr ⟨hq, hy⟩⟩
  exact (Nat.find_min (exists_eligible s) hz) hel

private lemma card_used_le {n : ℕ} (s : Hist n) :
    (used s).card ≤ 3 * n := by
  classical
  have hx : (Finset.univ.image s.x).card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := s.x))
  have hq : (Finset.univ.biUnion fun i => (s.q i).toFinset).card ≤ n := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), ((s.q i).toFinset).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin n)), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases s.q i <;> simp
      _ = n := by simp
  have hy : (Finset.univ.image s.y).card ≤ n := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := s.y))
  unfold used
  calc
    ((Finset.univ.image s.x ∪ Finset.univ.biUnion fun i => (s.q i).toFinset) ∪
        Finset.univ.image s.y).card
        ≤ (Finset.univ.image s.x ∪ Finset.univ.biUnion fun i => (s.q i).toFinset).card +
          (Finset.univ.image s.y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image s.x).card +
          (Finset.univ.biUnion fun i => (s.q i).toFinset).card) +
          (Finset.univ.image s.y).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (n + n) + n := Nat.add_le_add (Nat.add_le_add hx hq) hy
    _ = 3 * n := by omega

lemma presentation_le_three_mul (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t ≤ 3 * t := by
  rw [presentation_eq_nextX]
  have hcard := Finset.card_le_card (range_nextX_subset_used (run gen t))
  simpa using hcard.trans (card_used_le (run gen t))

end Stage3Work

namespace Stage3Work
open Set Stage3S2B
open GenLimit.KleinbergWei

noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := target gen
  enumeration := Nat.nth (fun z => z ∈ target gen)
  enumeration_injective :=
    (Nat.nth_strictMono ((core_infinite.mono (core_subset_target gen)))).injective
  range_enumeration :=
    Nat.range_nth_of_infinite (core_infinite.mono (core_subset_target gen))

lemma orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (core_infinite.mono (core_subset_target gen))

lemma orderedTarget_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 3 * n := by
  by_contra hle
  have hlt : 3 * n < (orderedTarget gen).enumeration n := Nat.lt_of_not_ge hle
  classical
  let idx : Fin (n+1) → Fin n := fun i => by
    let v := presentation gen i
    have hvK : v ∈ target gen := ⟨i, rfl⟩
    have hvlt : v < (orderedTarget gen).enumeration n :=
      lt_of_le_of_lt ((presentation_le_three_mul gen i).trans (by omega)) hlt
    have hcount : Nat.count (fun z => z ∈ target gen) v < n := by
      by_contra hn
      have hnn : n ≤ Nat.count (fun z => z ∈ target gen) v := Nat.le_of_not_gt hn
      have hmono := (orderedTarget_inherits gen).monotone hnn
      change Nat.nth (fun z => z ∈ target gen) n ≤
        Nat.nth (fun z => z ∈ target gen)
          (Nat.count (fun z => z ∈ target gen) v) at hmono
      rw [Nat.nth_count hvK] at hmono
      exact (not_lt_of_ge hmono) hvlt
    exact ⟨Nat.count (fun z => z ∈ target gen) v, hcount⟩
  have hidx : Function.Injective idx := by
    intro i j hij
    apply Fin.ext
    apply presentation_injective gen
    have hiK : presentation gen i ∈ target gen := ⟨i, rfl⟩
    have hjK : presentation gen j ∈ target gen := ⟨j, rfl⟩
    have hvals :
        Nat.nth (fun z => z ∈ target gen)
            (Nat.count (fun z => z ∈ target gen) (presentation gen i)) =
          Nat.nth (fun z => z ∈ target gen)
            (Nat.count (fun z => z ∈ target gen) (presentation gen j)) := by
      congr 1
      exact congrArg Fin.val hij
    simpa [Nat.nth_count hiK, Nat.nth_count hjK] using hvals
  have hc := Fintype.card_le_of_injective idx hidx
  simp at hc

end Stage3Work

namespace Stage3Work
open Set Stage3S2B Filter
open GenLimit.KleinbergWei
open scoped Topology

lemma orderedTarget_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (3 * n) + 1 := by
  classical
  unfold OrderedLanguage.prefixCount
  let S : Finset ℕ := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  by_cases hn : n = 0
  · simp [S, hn]
  have hM : 3 * n ≠ 0 := by omega
  let exponent : {i // i ∈ S} → ℕ := fun i =>
    Classical.choose (show ∃ k, 2 ^ k = (orderedTarget gen).enumeration i by
      have hiS := Finset.mem_filter.mp i.property
      simpa [Stage3S2B.core] using hiS.2)
  have hexp (i : {i // i ∈ S}) :
      2 ^ exponent i = (orderedTarget gen).enumeration i :=
    Classical.choose_spec (show ∃ k, 2 ^ k = (orderedTarget gen).enumeration i by
      have hiS := Finset.mem_filter.mp i.property
      simpa [Stage3S2B.core] using hiS.2)
  let f : {i // i ∈ S} → Fin (Nat.log2 (3*n) + 1) := fun i => by
    refine ⟨exponent i, Nat.lt_succ_iff.mpr ?_⟩
    apply (Nat.le_log2 hM).2
    rw [hexp]
    exact (orderedTarget_enumeration_le gen i).trans (by
      have hi : i.1 < n := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
      omega)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply (orderedTarget gen).enumeration_injective
    rw [← hexp i, ← hexp j]
    apply congrArg (fun k : ℕ => 2 ^ k)
    change (f i).val = (f j).val
    exact congrArg Fin.val hij
  have hc := Fintype.card_le_of_injective f hf
  simpa [S] using hc

lemma tendsto_log_three_mul_add_one_div :
    Tendsto (fun n : ℕ => ((Nat.log2 (3*n) + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hthree : Tendsto (fun n : ℕ => 3 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hcomp := GenLimit.tendsto_natLog2_div.comp hthree
  have hscaled := hcomp.const_mul (3 : ℝ)
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  convert hscaled.add hone using 1 <;> simp
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · field_simp

lemma orderedTarget_upperDensity_core (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have hratio : Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n) ?_
      tendsto_log_three_mul_add_one_div
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast orderedTarget_prefixCount_core_le gen n
      · positivity
  exact hratio.limsup_eq

end Stage3Work

namespace Stage3Work
open Set Stage3S2B
open GenLimit.KleinbergWei

lemma scored_upperDensity_zero (gen : FeedbackGenerator) {T : ℕ}
    (hvalid : ∀ t, T ≤ t →
      output gen t ∈ target gen ∧
      output gen t ∉ observedThrough (presentation gen) t) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (presentation gen) (output gen)) = 0 := by
  let F : Set ℕ := Set.range (fun i : Fin T => output gen i)
  have hF : F.Finite := Set.finite_range _
  have hsub : scored (target gen) (presentation gen) (output gen) ⊆ core ∪ F :=
    scored_subset_core_union_initial gen hvalid
  have hmono := (orderedTarget gen).upperDensity_mono hsub
  have hunion := (orderedTarget gen).upperDensity_union_le core F
  have hcore := orderedTarget_upperDensity_core gen
  have hfinite := (orderedTarget gen).upperDensity_eq_zero_of_finite hF
  have hle : (orderedTarget gen).upperDensity
      (scored (target gen) (presentation gen) (output gen)) ≤ 0 := by
    calc
      _ ≤ (orderedTarget gen).upperDensity (core ∪ F) := hmono
      _ ≤ (orderedTarget gen).upperDensity core +
          (orderedTarget gen).upperDensity F := hunion
      _ = 0 := by rw [hcore, hfinite]; norm_num
  exact le_antisymm hle ((orderedTarget gen).upperDensity_nonneg _)

lemma negative_claim : NegativeClaim := by
  intro gen huniv
  have hsuccess := huniv (target gen) (target_mem_class gen) (transcript gen)
    (follows_protocol gen)
    (by simpa [transcript] using clean gen)
    (by simpa [transcript] using presentation_injective gen)
    (by simpa [transcript] using complete gen)
  obtain ⟨T, hT⟩ := hsuccess
  refine ⟨target gen, target_mem_class gen, presenter gen, transcript gen,
    orderedTarget gen, ?_⟩
  refine ⟨rfl, orderedTarget_inherits gen, presented_by gen,
    follows_protocol gen, ?_, ?_, ?_, ?_⟩
  · simpa [transcript] using clean gen
  · simpa [transcript] using presentation_injective gen
  · simpa [transcript] using complete gen
  · apply scored_upperDensity_zero gen
    intro t ht
    simpa [transcript] using hT t ht

end Stage3Work

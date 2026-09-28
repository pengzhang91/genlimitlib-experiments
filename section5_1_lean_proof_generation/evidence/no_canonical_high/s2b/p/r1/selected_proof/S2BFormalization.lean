import Stage3Model
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Set Filter
open scoped Topology BigOperators

namespace Stage3Work

open Stage3S2B

private def extend {α : Type} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t+1) → α :=
  fun i => if h : i.val < t then f ⟨i.val, h⟩ else a

private theorem extend_castSucc {α : Type} {t : ℕ} (f : Fin t → α) (a : α) (i : Fin t) :
    extend f a i.castSucc = f i := by
  simp [extend, i.isLt]

private theorem extend_last {α : Type} {t : ℕ} (f : Fin t → α) (a : α) :
    extend f a (Fin.last t) = a := by
  simp [extend]

private structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

private def emptyHist : Hist 0 where
  x := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0

private def safe (h : Hist t) (z : ℕ) : Prop :=
  (∀ i, h.x i < z) ∧
  (∀ i, h.q i = some z → z ∈ core) ∧
  (∀ i, h.y i = z → z ∈ core)

private theorem safe_exists (h : Hist t) : ∃ z, safe h z := by
  let M := ∑ i, h.x i
  refine ⟨2 ^ (M+1), ?_, ?_, ?_⟩
  · intro i
    have hle : h.x i ≤ M := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact lt_of_le_of_lt hle (lt_trans (by omega) (Nat.lt_pow_self (by omega : 1 < 2)))
  · intro i hi
    exact ⟨M+1, rfl⟩
  · intro i hi
    exact ⟨M+1, rfl⟩

private noncomputable def nextX (h : Hist t) : ℕ := by
  classical
  exact Nat.find (safe_exists h)

private theorem nextX_safe (h : Hist t) : safe h (nextX h) := by
  classical
  exact Nat.find_spec (safe_exists h)

private noncomputable def step (gen : FeedbackGenerator) (h : Hist t) : Hist (t+1) := by
  let xnew := nextX h
  let x' := extend h.x xnew
  let qnew := gen.query t x' h.a
  let anew := match qnew with
    | none => none
    | some z => some (membershipAnswer core z || decide (∃ i, x' i = z))
  let a' := extend h.a anew
  let ynew := gen.output t x' a'
  exact { x := x', q := extend h.q qnew, a := a', y := extend h.y ynew }

private noncomputable def hist (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => emptyHist
  | t+1 => step gen (hist gen t)

private noncomputable def trX (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (hist gen (t+1)).x (Fin.last t)
private noncomputable def trQ (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  (hist gen (t+1)).q (Fin.last t)
private noncomputable def trA (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  (hist gen (t+1)).a (Fin.last t)
private noncomputable def trY (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (hist gen (t+1)).y (Fin.last t)

private noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation := trX gen
  query := trQ gen
  answer := trA gen
  output := trY gen

private theorem hist_prefix_x (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen (t+1)).x i.castSucc = (hist gen t).x i := by
  simp [hist, step, extend_castSucc]
private theorem hist_prefix_q (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen (t+1)).q i.castSucc = (hist gen t).q i := by
  simp [hist, step, extend_castSucc]
private theorem hist_prefix_a (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen (t+1)).a i.castSucc = (hist gen t).a i := by
  simp [hist, step, extend_castSucc]
private theorem hist_prefix_y (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen (t+1)).y i.castSucc = (hist gen t).y i := by
  simp [hist, step, extend_castSucc]

private theorem hist_x_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen t).x i = trX gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      by_cases hi : i.val < t
      · let j : Fin t := ⟨i.val, hi⟩
        have hij : i = j.castSucc := by ext; rfl
        rw [hij, hist_prefix_x]
        exact ih j
      · have heq : i = Fin.last t := by ext; simp only [Fin.last]; omega
        subst i
        rfl

private theorem hist_q_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen t).q i = trQ gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      by_cases hi : i.val < t
      · let j : Fin t := ⟨i.val, hi⟩
        have hij : i = j.castSucc := by ext; rfl
        rw [hij, hist_prefix_q]
        exact ih j
      · have heq : i = Fin.last t := by ext; simp only [Fin.last]; omega
        subst i
        rfl

private theorem hist_a_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen t).a i = trA gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      by_cases hi : i.val < t
      · let j : Fin t := ⟨i.val, hi⟩
        have hij : i = j.castSucc := by ext; rfl
        rw [hij, hist_prefix_a]
        exact ih j
      · have heq : i = Fin.last t := by ext; simp only [Fin.last]; omega
        subst i
        rfl

private theorem hist_y_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (hist gen t).y i = trY gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      by_cases hi : i.val < t
      · let j : Fin t := ⟨i.val, hi⟩
        have hij : i = j.castSucc := by ext; rfl
        rw [hij, hist_prefix_y]
        exact ih j
      · have heq : i = Fin.last t := by ext; simp only [Fin.last]; omega
        subst i
        rfl

end Stage3Work

namespace Stage3Work
open Stage3S2B

private theorem trX_step (gen : FeedbackGenerator) (t : ℕ) :
    trX gen t = nextX (hist gen t) := by
  simp [trX, hist, step, extend_last]

private theorem trQ_step (gen : FeedbackGenerator) (t : ℕ) :
    trQ gen t = gen.query t (fun i => trX gen i) (fun i => trA gen i) := by
  simp [trQ, hist, step, extend_last]
  congr 2
  · funext i
    exact hist_x_eq gen (t+1) i
  · funext i
    exact hist_a_eq gen t i

private theorem trA_step (gen : FeedbackGenerator) (t : ℕ) :
    trA gen t = match trQ gen t with
      | none => none
      | some z => some (membershipAnswer core z ||
          decide (∃ i : Fin (t+1), trX gen i = z)) := by
  classical
  simp only [trA, trQ, hist, step, extend_last]
  split <;> rename_i hq
  · rfl
  · congr 2
    have heq : extend (hist gen t).x (nextX (hist gen t)) =
        (fun i : Fin (t+1) => trX gen i) := by
      funext i
      simpa [hist, step] using hist_x_eq gen (t+1) i
    rw [heq]

private theorem trY_step (gen : FeedbackGenerator) (t : ℕ) :
    trY gen t = gen.output t (fun i => trX gen i) (fun i => trA gen i) := by
  simp [trY, hist, step, extend_last]
  congr 2
  · funext i
    exact hist_x_eq gen (t+1) i
  · funext i
    exact hist_a_eq gen (t+1) i

private theorem trX_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    trX gen s < trX gen t := by
  rw [trX_step gen t]
  have hs := (nextX_safe (hist gen t)).1 ⟨s, hst⟩
  simpa [hist_x_eq] using hs

private theorem trX_strictMono (gen : FeedbackGenerator) : StrictMono (trX gen) := by
  intro s t hst
  exact trX_lt gen hst

private theorem future_query_avoid (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t)
    (hq : trQ gen s = some (trX gen t)) : trX gen t ∈ core := by
  rw [trX_step]
  have h := (nextX_safe (hist gen t)).2.1 ⟨s, hst⟩
  apply h
  simpa [hist_q_eq, trX_step] using hq

private theorem future_output_avoid (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t)
    (hy : trY gen s = trX gen t) : trX gen t ∈ core := by
  rw [trX_step]
  have h := (nextX_safe (hist gen t)).2.2 ⟨s, hst⟩
  apply h
  simpa [hist_y_eq, trX_step] using hy

end Stage3Work

namespace Stage3Work
open Stage3S2B

private theorem core_subset_range (gen : FeedbackGenerator) : core ⊆ Set.range (trX gen) := by
  intro p hp
  have hex : ∃ n, p ≤ trX gen n := ⟨p, (trX_strictMono gen).le_apply⟩
  let t := Nat.find hex
  have hpt : p ≤ trX gen t := Nat.find_spec hex
  have hpSafe : safe (hist gen t) p := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_contra hlt
      have hle : p ≤ trX gen i := by
        rw [hist_x_eq] at hlt
        omega
      have := Nat.find_min' hex hle
      dsimp [t] at i ⊢
      omega
    · intro i hi
      exact hp
    · intro i hi
      exact hp
  have hnext : nextX (hist gen t) ≤ p := by
    classical
    exact Nat.find_min' (safe_exists (hist gen t)) hpSafe
  have hxt : trX gen t ≤ p := by simpa [trX_step] using hnext
  exact ⟨t, Nat.le_antisymm hxt hpt⟩

private noncomputable def target (gen : FeedbackGenerator) : Language := Set.range (trX gen)

private theorem target_mem_iff_query_view (gen : FeedbackGenerator) (t z : ℕ)
    (hq : trQ gen t = some z) :
    z ∈ target gen ↔ z ∈ core ∨ ∃ i : Fin (t+1), trX gen i = z := by
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hs : s ≤ t
    · right
      exact ⟨⟨s, by omega⟩, rfl⟩
    · left
      apply future_query_avoid gen (s := t) (t := s) (by omega)
      simpa using hq
  · rintro (hz | ⟨i, hi⟩)
    · exact core_subset_range gen hz
    · exact ⟨i, hi⟩

private theorem answer_correct (gen : FeedbackGenerator) (t : ℕ) :
    trA gen t = match trQ gen t with
      | none => none
      | some z => some (membershipAnswer (target gen) z) := by
  rw [trA_step]
  cases hq : trQ gen t with
  | none => rfl
  | some z =>
      simp only
      congr 2
      classical
      by_cases hc : z ∈ core <;>
        by_cases he : ∃ i : Fin (t+1), trX gen i = z <;>
        simp [membershipAnswer, target_mem_iff_query_view gen t z hq, hc, he]

private theorem follows (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  refine ⟨trQ_step gen t, answer_correct gen t, trY_step gen t⟩

private theorem clean (gen : FeedbackGenerator) : Clean (trX gen) (target gen) := by
  intro t
  exact ⟨t, rfl⟩

private theorem complete (gen : FeedbackGenerator) : Complete (trX gen) (target gen) := by
  intro z hz
  exact hz

private theorem target_in_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨target gen ∩ ordinary, inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · rintro z (hz | ⟨hz, ho⟩)
    · exact core_subset_range gen hz
    · exact hz

private theorem fresh_output_not_target (gen : FeedbackGenerator) (t : ℕ)
    (hfresh : trY gen t ∉ observedThrough (trX gen) t)
    (hordinary : trY gen t ∉ core) : trY gen t ∉ target gen := by
  rintro ⟨s, hs⟩
  by_cases hst : s ≤ t
  · apply hfresh
    exact ⟨s, hst, hs⟩
  · apply hordinary
    have hc := future_output_avoid gen (s := t) (t := s) (by omega) hs.symm
    simpa [hs] using hc

end Stage3Work

namespace Stage3Work
open Stage3S2B

private theorem trX_zero (gen : FeedbackGenerator) : trX gen 0 = 0 := by
  rw [trX_step]
  have hsafe : safe (hist gen 0) 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro i
    all_goals exact Fin.elim0 i
  have hle : nextX (hist gen 0) ≤ 0 := by
    classical
    exact Nat.find_min' (safe_exists (hist gen 0)) hsafe
  omega

private theorem below_classify (gen : FeedbackGenerator) (t z : ℕ)
    (hz : z < trX gen t) :
    (∃ i : Fin t, trX gen i = z) ∨
    (∃ i : Fin t, trQ gen i = some z) ∨
    (∃ i : Fin t, trY gen i = z) := by
  induction t with
  | zero => rw [trX_zero] at hz; omega
  | succ t ih =>
      by_cases hprev : z < trX gen t
      · rcases ih hprev with h | h | h
        · left; rcases h with ⟨i, hi⟩; exact ⟨i.castSucc, hi⟩
        · right; left; rcases h with ⟨i, hi⟩; exact ⟨i.castSucc, hi⟩
        · right; right; rcases h with ⟨i, hi⟩; exact ⟨i.castSucc, hi⟩
      · by_cases heq : z = trX gen t
        · left
          exact ⟨Fin.last t, heq.symm⟩
        · have hlast : trX gen t < z := by omega
          have hallx : ∀ i : Fin (t+1), trX gen i < z := by
            intro i
            exact lt_of_le_of_lt ((trX_strictMono gen).monotone (by omega : (i : ℕ) ≤ t)) hlast
          by_cases hq : ∃ i : Fin (t+1), trQ gen i = some z
          · right; left; exact hq
          · by_cases hy : ∃ i : Fin (t+1), trY gen i = z
            · right; right; exact hy
            · have hsafe : safe (hist gen (t+1)) z := by
                refine ⟨?_, ?_, ?_⟩
                · intro i
                  simpa [hist_x_eq] using hallx i
                · intro i hi
                  exact False.elim (hq ⟨i, by simpa [hist_q_eq] using hi⟩)
                · intro i hi
                  exact False.elim (hy ⟨i, by simpa [hist_y_eq] using hi⟩)
              have hle : trX gen (t+1) ≤ z := by
                rw [trX_step]
                classical
                exact Nat.find_min' (safe_exists (hist gen (t+1))) hsafe
              omega

private theorem trX_le_three_mul (gen : FeedbackGenerator) (t : ℕ) : trX gen t ≤ 3*t := by
  classical
  let P : Finset ℕ := Finset.univ.image (fun i : Fin t => trX gen i)
  let Q : Finset ℕ := Finset.univ.image (fun i : Fin t => (trQ gen i).getD 0)
  let Y : Finset ℕ := Finset.univ.image (fun i : Fin t => trY gen i)
  have hsub : Finset.range (trX gen t) ⊆ P ∪ Q ∪ Y := by
    intro z hz
    have hlt : z < trX gen t := Finset.mem_range.1 hz
    rcases below_classify gen t z hlt with h | h | h
    · rcases h with ⟨i, hi⟩
      apply Finset.mem_union_left Y
      apply Finset.mem_union_left Q
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
    · rcases h with ⟨i, hi⟩
      apply Finset.mem_union_left Y
      apply Finset.mem_union_right P
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, by simp [hi]⟩
    · rcases h with ⟨i, hi⟩
      apply Finset.mem_union_right (P ∪ Q)
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hP : P.card ≤ t := by simpa [P] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := fun i => trX gen i)
  have hQ : Q.card ≤ t := by simpa [Q] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := fun i => (trQ gen i).getD 0)
  have hY : Y.card ≤ t := by simpa [Y] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := fun i => trY gen i)
  calc
    trX gen t = (Finset.range (trX gen t)).card := by simp
    _ ≤ (P ∪ Q ∪ Y).card := Finset.card_le_card hsub
    _ ≤ P.card + Q.card + Y.card := by
      calc
        (P ∪ Q ∪ Y).card ≤ (P ∪ Q).card + Y.card := Finset.card_union_le _ _
        _ ≤ (P.card + Q.card) + Y.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 3*t := by omega

end Stage3Work

namespace Stage3Work
open Stage3S2B

private noncomputable def coreExp (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ core then Classical.choose h else 0

private theorem pow_coreExp {z : ℕ} (hz : z ∈ core) : 2 ^ coreExp z = z := by
  classical
  simp only [coreExp, dif_pos hz]
  exact Classical.choose_spec hz

private theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (GenLimit.KleinbergWei.OrderedLanguage.prefixCount
      { carrier := target gen
        enumeration := trX gen
        enumeration_injective := (trX_strictMono gen).injective
        range_enumeration := rfl } core n) ≤ Nat.log 2 (3*n) + 1 := by
  classical
  let S := (Finset.range n).filter (fun i => trX gen i ∈ core)
  let e : ℕ → ℕ := fun i => coreExp (trX gen i)
  have hinj : Set.InjOn e (S : Set ℕ) := by
    intro i hi j hj he
    have hci : trX gen i ∈ core := (Finset.mem_filter.1 hi).2
    have hcj : trX gen j ∈ core := (Finset.mem_filter.1 hj).2
    apply (trX_strictMono gen).injective
    calc
      trX gen i = 2 ^ e i := (pow_coreExp hci).symm
      _ = 2 ^ e j := by rw [he]
      _ = trX gen j := pow_coreExp hcj
  have himage : Finset.image e S ⊆ Finset.range (Nat.log 2 (3*n) + 1) := by
    intro k hk
    rcases Finset.mem_image.1 hk with ⟨i, hi, rfl⟩
    have hin : i < n := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hci : trX gen i ∈ core := (Finset.mem_filter.1 hi).2
    apply Finset.mem_range.2
    apply Nat.lt_succ_of_le
    apply Nat.le_log_of_pow_le (by omega : 1 < 2)
    rw [pow_coreExp hci]
    exact le_trans (trX_le_three_mul gen i) (by omega)
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  change S.card ≤ _
  calc
    S.card = (Finset.image e S).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (Nat.log 2 (3*n) + 1)).card := Finset.card_le_card himage
    _ = Nat.log 2 (3*n) + 1 := Finset.card_range _

private theorem finite_prefixCount_le (gen : FeedbackGenerator) (T n : ℕ) :
    (GenLimit.KleinbergWei.OrderedLanguage.prefixCount
      { carrier := target gen
        enumeration := trX gen
        enumeration_injective := (trX_strictMono gen).injective
        range_enumeration := rfl }
      {z | ∃ t, t < T ∧ trY gen t = z} n) ≤ T := by
  classical
  let S := (Finset.range n).filter (fun i => ∃ t, t < T ∧ trY gen t = trX gen i)
  let E := Finset.univ.image (fun i : Fin T => trY gen i)
  have himage : Finset.image (trX gen) S ⊆ E := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨i, hi, rfl⟩
    rcases (Finset.mem_filter.1 hi).2 with ⟨t, ht, heq⟩
    exact Finset.mem_image.2 ⟨⟨t, ht⟩, Finset.mem_univ _, heq⟩
  have hinj : Set.InjOn (trX gen) (S : Set ℕ) := (trX_strictMono gen).injective.injOn
  have hcard : S.card ≤ T := by
    calc
      S.card = (Finset.image (trX gen) S).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ E.card := Finset.card_le_card himage
      _ ≤ T := by simpa [E] using Finset.card_image_le (s := (Finset.univ : Finset (Fin T))) (f := fun i => trY gen i)
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  dsimp
  apply le_of_eq_of_le ?_ hcard
  congr 1
  ext i
  simp [S]

end Stage3Work

namespace Stage3Work
open Stage3S2B
open Asymptotics

private theorem natLog_cast_le (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 (3*n) : ℝ) ≤ Real.log (3*(n:ℝ)) / Real.log 2 := by
  have hm : 3*n ≠ 0 := by omega
  have hp : 2 ^ Nat.log 2 (3*n) ≤ 3*n := Nat.pow_log_le_self 2 hm
  have hcast : (2:ℝ) ^ Nat.log 2 (3*n) ≤ (3*n : ℕ) := by exact_mod_cast hp
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ) ^ Nat.log 2 (3*n)) hcast
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).2
  norm_num [Nat.cast_mul] at hlog ⊢
  exact hlog

private theorem log_bound_ratio_tendsto (T : ℕ) :
    Tendsto (fun n : ℕ => ((Nat.log 2 (3*n) + 1 + T : ℕ) : ℝ) / n)
      atTop (𝓝 0) := by
  have hk : Tendsto (fun n : ℕ => (3:ℝ) * (n:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 3))
  have hlo0 := (Real.isLittleO_log_id_atTop.comp_tendsto hk).tendsto_div_nhds_zero
  have hlo : Tendsto (fun n : ℕ => Real.log (3*(n:ℝ)) / (3*(n:ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlo0
  have hlog : Tendsto (fun n : ℕ => Real.log (3*(n:ℝ)) / Real.log 2 / (n:ℝ))
      atTop (𝓝 0) := by
    have h := hlo.const_mul (3 / Real.log 2)
    convert h using 1
    · funext n
      by_cases hn : (n:ℝ) = 0
      · simp [hn]
      · field_simp
        <;> ring
    · simp
  have hconst : Tendsto (fun n : ℕ => ((1+T:ℕ):ℝ) / (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ =>
      Real.log (3*(n:ℝ)) / Real.log 2 / (n:ℝ) + ((1+T:ℕ):ℝ) / (n:ℝ))
      atTop (𝓝 0) := by simpa using hlog.add hconst
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)) hu
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hle := natLog_cast_le n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [Nat.cast_add, Nat.cast_add, ← add_div]
    apply div_le_div_of_nonneg_right ?_ hnR.le
    norm_num [Nat.cast_add]
    linarith

end Stage3Work

namespace Stage3Work
open Stage3S2B

private noncomputable def ordered (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := target gen
  enumeration := trX gen
  enumeration_injective := (trX_strictMono gen).injective
  range_enumeration := rfl

private theorem prefixCount_mono (K : OrderedLanguage) {A B : Language} (h : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, h hi.2⟩

private theorem prefixCount_union_le (K : OrderedLanguage) (A B : Language) (n : ℕ) :
    K.prefixCount (A ∪ B) n ≤ K.prefixCount A n + K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  simp only [Set.mem_union]
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

private theorem scored_subset (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ T, scored (target gen) (trX gen) (trY gen) ⊆
      core ∪ {z | ∃ t, t < T ∧ trY gen t = z} := by
  obtain ⟨T, hT⟩ := hgen (target gen) (target_in_class gen) (transcript gen)
    (follows gen) (clean gen) (trX_strictMono gen).injective (complete gen)
  refine ⟨T, ?_⟩
  rintro z ⟨hzK, t, hyt, hfresh⟩
  by_cases ht : t < T
  · exact Or.inr ⟨t, ht, hyt⟩
  · left
    have hv := hT t (by omega)
    change trY gen t ∈ target gen ∧ trY gen t ∉ observedThrough (trX gen) t at hv
    by_contra hc
    have hc' : trY gen t ∉ core := by simpa [hyt] using hc
    have hnot := fresh_output_not_target gen t hv.2 hc'
    exact hnot hv.1

private theorem scored_prefixCount_bound (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ T, ∀ n, (ordered gen).prefixCount
      (scored (target gen) (trX gen) (trY gen)) n ≤ Nat.log 2 (3*n) + 1 + T := by
  obtain ⟨T, hsub⟩ := scored_subset gen hgen
  refine ⟨T, fun n => ?_⟩
  calc
    (ordered gen).prefixCount (scored (target gen) (trX gen) (trY gen)) n
        ≤ (ordered gen).prefixCount (core ∪ {z | ∃ t, t < T ∧ trY gen t = z}) n :=
          prefixCount_mono (ordered gen) hsub n
    _ ≤ (ordered gen).prefixCount core n +
        (ordered gen).prefixCount {z | ∃ t, t < T ∧ trY gen t = z} n :=
          prefixCount_union_le (ordered gen) core _ n
    _ ≤ (Nat.log 2 (3*n) + 1) + T := Nat.add_le_add (core_prefixCount_le gen n) (finite_prefixCount_le gen T n)

private theorem scored_density_zero (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    (ordered gen).upperDensity (scored (target gen) (trX gen) (trY gen)) = 0 := by
  obtain ⟨T, hbound⟩ := scored_prefixCount_bound gen hgen
  have hratio : Tendsto ((ordered gen).prefixRatio
      (scored (target gen) (trX gen) (trY gen))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
      (log_bound_ratio_tendsto T)
    · filter_upwards with n
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
      split <;> positivity
    · filter_upwards with n
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
      split
      · positivity
      · apply div_le_div_of_nonneg_right
        · exact_mod_cast hbound n
        · positivity
  exact hratio.limsup_eq

private noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next := fun t _ _ _ _ => trX gen t

private theorem negative : NegativeClaim := by
  intro gen hgen
  refine ⟨target gen, target_in_class gen, presenter gen, transcript gen, ordered gen, ?_⟩
  refine ⟨rfl, trX_strictMono gen, ?_, follows gen, clean gen,
    (trX_strictMono gen).injective, complete gen, scored_density_zero gen hgen⟩
  intro t
  rfl

end Stage3Work

namespace Stage3Work
open Stage3S2B

private def code (n : ℕ) : ℕ := 2*n + 3

private theorem code_injective : Function.Injective code := by
  intro a b h
  simp [code] at h
  omega

private theorem code_ordinary (n : ℕ) : code n ∈ ordinary := by
  intro hc
  rcases hc with ⟨k, hk⟩
  cases k with
  | zero => simp [code] at hk
  | succ k =>
      change 2 ^ (k+1) = 2*n+3 at hk
      rw [pow_succ] at hk
      omega

private def encode (A : Set ℕ) : Language := core ∪ code '' A

private theorem encode_mem_class (A : Set ℕ) : encode A ∈ targetClass := by
  refine ⟨code '' A, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact code_ordinary n

private theorem encode_injective : Function.Injective encode := by
  intro A B hAB
  apply Set.ext
  intro n
  constructor
  · intro hn
    have hm : code n ∈ encode A := Or.inr ⟨n, hn, rfl⟩
    rw [hAB] at hm
    rcases hm with hc | ⟨m, hm, heq⟩
    · exact False.elim (code_ordinary n hc)
    · have : m = n := code_injective heq
      simpa [this] using hm
  · intro hn
    have hm : code n ∈ encode B := Or.inr ⟨n, hn, rfl⟩
    rw [← hAB] at hm
    rcases hm with hc | ⟨m, hm, heq⟩
    · exact False.elim (code_ordinary n hc)
    · have : m = n := code_injective heq
      simpa [this] using hm

private theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  have hpre := hcount.preimage encode_injective
  have hall : encode ⁻¹' targetClass = (Set.univ : Set (Set ℕ)) := by
    apply Set.eq_univ_of_forall
    intro A
    exact encode_mem_class A
  rw [hall] at hpre
  obtain ⟨f, hf⟩ := hpre.exists_eq_range (Set.univ_nonempty)
  let D : Set ℕ := {n | n ∉ f n}
  have hD : D ∈ (Set.univ : Set (Set ℕ)) := Set.mem_univ D
  rw [hf] at hD
  rcases hD with ⟨k, hk⟩
  have hdiag : k ∈ D ↔ k ∉ D := by
    change (k ∉ f k) ↔ k ∉ D
    rw [hk]
  by_cases h : k ∈ D
  · exact (hdiag.mp h) h
  · exact h (hdiag.mpr h)

private theorem uniform : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2^t, ?_, 0, ?_⟩
  · exact (strictMono_nat_of_lt_succ (fun n => Nat.pow_lt_pow_right (by omega) (by omega))).injective
  · intro K hK t ht
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

end Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_uncountable, Stage3Work.uniform, Stage3Work.negative⟩

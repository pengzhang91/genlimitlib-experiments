import Stage3Model
import Mathlib.Data.Finset.Image

open Stage3Case019

namespace Case019Formalization

structure FreshState (α : Type*) where
  seen : Finset α
  outputs : Finset α
  last : α

noncomputable def chooseFresh {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (blocked : Finset α) : α :=
  Classical.choose (hK.exists_not_mem_finset blocked)

lemma chooseFresh_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (blocked : Finset α) :
    chooseFresh K hK blocked ∈ K :=
  (Classical.choose_spec (hK.exists_not_mem_finset blocked)).1

lemma chooseFresh_not_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (blocked : Finset α) :
    chooseFresh K hK blocked ∉ blocked :=
  (Classical.choose_spec (hK.exists_not_mem_finset blocked)).2

noncomputable def freshInit {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) : FreshState α :=
  { seen := ∅
    outputs := ∅
    last := chooseFresh K hK ∅ }

noncomputable def freshStep {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (state : FreshState α) (x : α) : FreshState α :=
  let seen := insert x state.seen
  let y := chooseFresh K hK (seen ∪ state.outputs)
  { seen := seen
    outputs := insert y state.outputs
    last := y }

noncomputable def freshRunStream {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (n : ℕ) : FreshState α :=
  (List.ofFn fun i : Fin n => input i).foldl (freshStep K hK) (freshInit K hK)

noncomputable def freshGenerator {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) : Generator α :=
  fun _ history =>
    (List.ofFn history).foldl (freshStep K hK) (freshInit K hK) |>.last

lemma freshRunStream_succ {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (n : ℕ) :
    freshRunStream K hK input (n + 1) =
      freshStep K hK (freshRunStream K hK input n) (input n) := by
  unfold freshRunStream
  rw [List.ofFn_succ_last, List.foldl_append]
  rfl

lemma fresh_output_eq_last {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (t : ℕ) :
    outputAfterInput (freshGenerator K hK) input t =
      (freshRunStream K hK input (t + 1)).last := by
  rfl

lemma freshRunStream_seen {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (n : ℕ) :
    (freshRunStream K hK input n).seen = GenLimit.Generic.sample input n := by
  induction n with
  | zero => simp [freshRunStream, freshInit, GenLimit.Generic.sample]
  | succ n ih =>
      rw [freshRunStream_succ]
      simp only [freshStep]
      rw [ih]
      ext z
      simp only [Finset.mem_insert, GenLimit.Generic.sample, Finset.mem_image,
        Finset.mem_range]
      constructor
      · rintro (rfl | ⟨a, ha, haz⟩)
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · exact ⟨a, ha.trans (Nat.lt_succ_self n), haz⟩
      · rintro ⟨a, ha, haz⟩
        by_cases han : a = n
        · left
          subst a
          exact haz.symm
        · right
          have hat : a < n := by omega
          exact ⟨a, hat, haz⟩

lemma freshRunStream_outputs {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (n : ℕ) :
    (freshRunStream K hK input n).outputs =
      (Finset.range n).image (outputAfterInput (freshGenerator K hK) input) := by
  induction n with
  | zero => simp [freshRunStream, freshInit]
  | succ n ih =>
      rw [freshRunStream_succ]
      simp only [freshStep]
      rw [Finset.range_succ, Finset.image_insert, ← ih]
      congr 1
      rw [fresh_output_eq_last, freshRunStream_succ]
      rfl

lemma fresh_output_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (t : ℕ) :
    outputAfterInput (freshGenerator K hK) input t ∈ K := by
  rw [fresh_output_eq_last, freshRunStream_succ]
  exact chooseFresh_mem K hK _

lemma fresh_output_not_sample {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (t : ℕ) :
    outputAfterInput (freshGenerator K hK) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  rw [fresh_output_eq_last, freshRunStream_succ]
  have hnot := chooseFresh_not_mem K hK
    (insert (input t) (freshRunStream K hK input t).seen ∪
      (freshRunStream K hK input t).outputs)
  simp only [freshStep]
  intro hmem
  apply hnot
  apply Finset.mem_union_left
  rw [← freshRunStream_seen K hK input (t + 1)] at hmem
  rw [freshRunStream_succ] at hmem
  simpa only [freshStep] using hmem

lemma fresh_output_ne_previous {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) {s t : ℕ} (hst : s < t) :
    outputAfterInput (freshGenerator K hK) input s ≠
      outputAfterInput (freshGenerator K hK) input t := by
  rw [fresh_output_eq_last (t := t), freshRunStream_succ]
  have hnot := chooseFresh_not_mem K hK
    (insert (input t) (freshRunStream K hK input t).seen ∪
      (freshRunStream K hK input t).outputs)
  simp only [freshStep]
  have hmem : outputAfterInput (freshGenerator K hK) input s ∈
      (freshRunStream K hK input t).outputs := by
    rw [freshRunStream_outputs]
    exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hst, rfl⟩
  intro heq
  apply hnot
  apply Finset.mem_union_right
  exact heq ▸ hmem

/-- A known infinite target admits an always-valid, sample-fresh, nonrepeating
semantic generator. This is the basic fixed-focus component used by both
constructions in the canonical proof. -/
theorem knownTarget_novel {α : Type*} [DecidableEq α]
    (K : Language α) (hK : K.Infinite) (input : Stream α) :
    NovelGeneratesAfterInput input
      (outputAfterInput (freshGenerator K hK) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  exact ⟨fresh_output_mem K hK input t,
    fresh_output_not_sample K hK input t,
    fun s hst => fresh_output_ne_previous K hK input hst⟩

end Case019Formalization

namespace Case019Formalization

/-- The finite marker block `{0, ..., q}`. -/
def markers (q : ℕ) : Set ℤ :=
  Set.range (fun i : Fin (q + 1) => Int.ofNat i)

/-- A nonnegative integer tail. -/
def nonnegativeTail (j : ℕ) : Set ℤ :=
  Set.range (fun n : ℕ => Int.ofNat (j + n))

/-- The negative half-line, in balanced-order order. -/
def negativeLine : Set ℤ :=
  Set.range (fun n : ℕ => -Int.ofNat (n + 1))

/-- Canonical marker-and-tail witness class from the prose proof. -/
def witnessFamily (q : ℕ) : LanguageClass ℤ :=
  {K | (markers q ⊆ K ∧ ∃ j, nonnegativeTail j ⊆ K) ∨
       (negativeLine ⊆ K ∧ Disjoint K (markers q))}

lemma nonnegativeTail_infinite (j : ℕ) : (nonnegativeTail j).Infinite := by
  apply Set.infinite_range_of_injective
  intro a b hab
  simp [nonnegativeTail] at hab
  omega

lemma negativeLine_infinite : negativeLine.Infinite := by
  apply Set.infinite_range_of_injective
  intro a b hab
  simp [negativeLine] at hab
  omega

lemma witnessFamily_infinite (q : ℕ) (K : Language ℤ)
    (hK : K ∈ witnessFamily q) : K.Infinite := by
  rcases hK with hA | hB
  · rcases hA.2 with ⟨j, hj⟩
    exact (nonnegativeTail_infinite j).mono hj
  · exact negativeLine_infinite.mono hB.1

private def negativeRank (n : ℕ) : ℤ := -Int.ofNat (n + 1)

private lemma negativeRank_injective : Function.Injective negativeRank := by
  intro a b hab
  simp [negativeRank] at hab
  omega

private def diagonalNegatives (f : ℕ → Language ℤ) : Set ℤ :=
  {z | ∃ n, z = negativeRank n ∧ z ∉ f n}

private lemma negativeRank_mem_diagonal_iff (f : ℕ → Language ℤ) (n : ℕ) :
    negativeRank n ∈ diagonalNegatives f ↔ negativeRank n ∉ f n := by
  constructor
  · rintro ⟨m, hmn, hm⟩
    have : m = n := negativeRank_injective hmn.symm
    simpa [this] using hm
  · intro hn
    exact ⟨n, rfl, hn⟩

private lemma negativeRank_not_mem_markers (q n : ℕ) :
    negativeRank n ∉ markers q := by
  rintro ⟨i, hi⟩
  simp [negativeRank] at hi
  have hleft : (0 : ℤ) ≤ Int.ofNat i := Int.ofNat_zero_le i
  have hright : (0 : ℤ) ≤ Int.ofNat n := Int.ofNat_zero_le n
  omega

private lemma negativeRank_not_mem_tail (j n : ℕ) :
    negativeRank n ∉ nonnegativeTail j := by
  rintro ⟨m, hm⟩
  simp [negativeRank] at hm
  have hleft : (0 : ℤ) ≤ Int.ofNat (j + m) := Int.ofNat_zero_le (j + m)
  have hright : (0 : ℤ) ≤ Int.ofNat n := Int.ofNat_zero_le n
  omega

/-- The canonical witness class is extensionally uncountable. -/
theorem witnessFamily_not_countable (q : ℕ) : ¬(witnessFamily q).Countable := by
  intro hcount
  have hbase : markers q ∪ nonnegativeTail (q + 1) ∈ witnessFamily q := by
    left
    exact ⟨Set.subset_union_left, ⟨q + 1, Set.subset_union_right⟩⟩
  have hne : (witnessFamily q).Nonempty := ⟨_, hbase⟩
  rcases hcount.exists_surjective hne with ⟨enumeration, henumeration⟩
  let f : ℕ → Language ℤ := fun n => enumeration n
  let diagonal : Language ℤ :=
    markers q ∪ nonnegativeTail (q + 1) ∪ diagonalNegatives f
  have hdiagonal : diagonal ∈ witnessFamily q := by
    left
    constructor
    · exact fun z hz => Or.inl (Or.inl hz)
    · exact ⟨q + 1, fun z hz => Or.inl (Or.inr hz)⟩
  obtain ⟨n, hn⟩ := henumeration ⟨diagonal, hdiagonal⟩
  have hsets : f n = diagonal := congrArg Subtype.val hn
  have hiff : negativeRank n ∈ diagonal ↔ negativeRank n ∉ diagonal := by
    calc
      negativeRank n ∈ diagonal ↔ negativeRank n ∈ diagonalNegatives f := by
        have hm := negativeRank_not_mem_markers q n
        have ht := negativeRank_not_mem_tail (q + 1) n
        simp [diagonal, hm, ht]
      _ ↔ negativeRank n ∉ f n := negativeRank_mem_diagonal_iff f n
      _ ↔ negativeRank n ∉ diagonal := by rw [hsets]
  by_cases hp : negativeRank n ∈ diagonal
  · exact (hiff.mp hp) hp
  · exact hp (hiff.mpr hp)

end Case019Formalization

namespace Case019Formalization

lemma generic_sample_nat_eq (input : Stream ℕ) (n : ℕ) :
    GenLimit.Generic.sample input n = GenLimit.sample input n := by
  ext z
  simp [GenLimit.Generic.sample, GenLimit.sample, Finset.mem_image, Finset.mem_range]

/-- Natural-number specialization matching the library predicate used by the
countable clause. -/
theorem knownTarget_nat_novel (K : Language ℕ) (hK : K.Infinite)
    (input : Stream ℕ) :
    GenLimit.NovelGeneratesInLimit input
      (outputAfterInput (freshGenerator K hK) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨fresh_output_mem K hK input t, ?_, ?_⟩
  · rw [← generic_sample_nat_eq]
    exact fresh_output_not_sample K hK input t
  · intro s hst
    exact fresh_output_ne_previous K hK input hst

/-- The set-theoretic core of the separation construction: for every level,
the canonical marker-and-tail class is uncountable and all its members are
infinite. -/
theorem witnessFamily_core :
    ∀ q : ℕ, ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  intro q
  exact ⟨witnessFamily q, witnessFamily_not_countable q,
    witnessFamily_infinite q⟩

end Case019Formalization

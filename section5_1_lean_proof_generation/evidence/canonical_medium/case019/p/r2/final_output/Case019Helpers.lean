import Stage3Model

open Set

namespace Case019Formalization

def natToIntEmbedding : ℕ ↪ ℤ where
  toFun := Int.ofNat
  inj' := by
    intro a b hab
    exact Int.ofNat_inj.mp hab

def markers (q : ℕ) : Finset ℤ :=
  (Finset.range (q + 1)).map natToIntEmbedding

@[simp] theorem card_markers (q : ℕ) : (markers q).card = q + 1 := by
  simp [markers]

@[simp] theorem mem_markers {q : ℕ} {z : ℤ} :
    z ∈ markers q ↔ ∃ n ≤ q, z = Int.ofNat n := by
  constructor
  · intro hz
    simp only [markers, Finset.mem_map, Finset.mem_range] at hz
    rcases hz with ⟨n, hn, rfl⟩
    exact ⟨n, Nat.lt_succ_iff.mp hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    rw [markers, Finset.mem_map]
    exact ⟨n, by simpa [Nat.lt_succ_iff] using hn, rfl⟩

def positiveBranch (q : ℕ) (K : Set ℤ) : Prop :=
  ↑(markers q) ⊆ K ∧ ∃ j : ℕ, {z : ℤ | Int.ofNat j ≤ z} ⊆ K

def negativeBranch (q : ℕ) (K : Set ℤ) : Prop :=
  Disjoint (↑(markers q) : Set ℤ) K ∧ {z : ℤ | z < 0} ⊆ K

def witnessFamily (q : ℕ) : Set (Set ℤ) :=
  {K | positiveBranch q K ∨ negativeBranch q K}

theorem positiveBranch_infinite {q : ℕ} {K : Set ℤ}
    (hK : positiveBranch q K) : K.Infinite := by
  obtain ⟨j, hj⟩ := hK.2
  apply Set.Infinite.mono (s := Set.range fun n : ℕ => Int.ofNat (j + n)) (t := K)
  · intro z hz
    apply hj
    rcases hz with ⟨n, rfl⟩
    change Int.ofNat j ≤ Int.ofNat (j + n)
    exact Int.ofNat_le.mpr (Nat.le_add_right j n)
  · exact Set.infinite_range_of_injective (by
      intro a b hab
      simpa using hab)

theorem negativeBranch_infinite {q : ℕ} {K : Set ℤ}
    (hK : negativeBranch q K) : K.Infinite := by
  apply Set.Infinite.mono (s := Set.range fun n : ℕ => -(Int.ofNat (n + 1))) (t := K)
  · intro z hz
    apply hK.2
    rcases hz with ⟨n, rfl⟩
    change -Int.ofNat (n + 1) < 0
    exact neg_lt_zero.mpr (Int.ofNat_lt.mpr (Nat.zero_lt_succ n))
  · exact Set.infinite_range_of_injective (by
      intro a b hab
      have : Int.ofNat (a + 1) = Int.ofNat (b + 1) := neg_injective hab
      simpa using this)

theorem witnessFamily_infinite (q : ℕ) {K : Set ℤ}
    (hK : K ∈ witnessFamily q) : K.Infinite := by
  rcases hK with hK | hK
  · exact positiveBranch_infinite hK
  · exact negativeBranch_infinite hK

theorem markers_not_subset_range_of_negativeBranch
    {q : ℕ} {K : Set ℤ} {input : ℕ → ℤ}
    (hK : negativeBranch q K)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ¬(↑(markers q) : Set ℤ) ⊆ Set.range input := by
  rintro hall
  rcases hp.2.2 with ⟨outside, houtside, hcard⟩
  have hsubset : markers q ⊆ outside := by
    intro z hz
    have hzrange := hall (by simpa using hz)
    have hznotK : z ∉ K := by
      intro hzK
      exact Set.disjoint_left.1 hK.1 (by simpa using hz) hzK
    have hzoutside : z ∈ (Set.range input \ K) := ⟨hzrange, hznotK⟩
    rw [← houtside] at hzoutside
    exact hzoutside
  have hlarge : q + 1 ≤ outside.card := by
    simpa using Finset.card_le_card hsubset
  omega



theorem finset_eventually_subset_sample {α : Type*}
    (F : Finset α) (input : ℕ → α) (hF : (↑F : Set α) ⊆ Set.range input) :
    ∃ T, (↑F : Set α) ⊆ ↑(GenLimit.Generic.sample input T) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a F ha ih =>
      obtain ⟨time, htime⟩ := hF (show a ∈ (↑(insert a F) : Set α) by simp)
      obtain ⟨T, hT⟩ := ih (by
        intro z hz
        exact hF (show z ∈ (↑(insert a F) : Set α) by simp [hz]))
      refine ⟨max (time + 1) T, ?_⟩
      intro z hz
      have hsampmono : GenLimit.Generic.sample input T ⊆
          GenLimit.Generic.sample input (max (time + 1) T) := by
        intro x hx
        unfold GenLimit.Generic.sample at hx ⊢
        rcases Finset.mem_image.mp hx with ⟨n, hn, hnx⟩
        apply Finset.mem_image.mpr
        exact ⟨n, Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hn) (le_max_right _ _)), hnx⟩
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hz
      rcases hz with rfl | hz
      · unfold GenLimit.Generic.sample
        apply Finset.mem_image.mpr
        exact ⟨time, Finset.mem_range.mpr
          (lt_of_lt_of_le (Nat.lt_succ_self time) (le_max_left _ _)), htime⟩
      · exact hsampmono (hT hz)

theorem markers_eventually_sampled_of_positiveBranch
    {q : ℕ} {K : Set ℤ} {input : ℕ → ℤ}
    (hK : positiveBranch q K)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ T, (↑(markers q) : Set ℤ) ⊆ ↑(GenLimit.Generic.sample input T) := by
  apply finset_eventually_subset_sample
  exact fun z hz => hp.2.1 (hK.1 hz)

theorem markers_never_sampled_of_negativeBranch
    {q T : ℕ} {K : Set ℤ} {input : ℕ → ℤ}
    (hK : negativeBranch q K)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ¬(↑(markers q) : Set ℤ) ⊆ ↑(GenLimit.Generic.sample input T) := by
  intro hsample
  apply markers_not_subset_range_of_negativeBranch hK hp
  intro z hz
  have hzsample := hsample hz
  simp only [GenLimit.Generic.sample, Finset.mem_coe, Finset.mem_image] at hzsample
  rcases hzsample with ⟨n, hn, rfl⟩
  exact ⟨n, rfl⟩


def encodedPositive (S : Set ℕ) : Set ℤ :=
  {z : ℤ | 0 ≤ z} ∪ {z : ℤ | ∃ n ∈ S, z = -Int.ofNat (n + 1)}

@[simp] theorem neg_code_mem_encodedPositive {S : Set ℕ} {n : ℕ} :
    -Int.ofNat (n + 1) ∈ encodedPositive S ↔ n ∈ S := by
  constructor
  · rintro (h | ⟨m, hm, heq⟩)
    · have hneg : -Int.ofNat (n + 1) < 0 :=
        neg_lt_zero.mpr (Int.ofNat_lt.mpr (Nat.zero_lt_succ n))
      exact False.elim ((not_lt_of_ge h) hneg)
    · have hcast : Int.ofNat (n + 1) = Int.ofNat (m + 1) := neg_injective heq
      have hsucc : n + 1 = m + 1 := Int.ofNat_inj.mp hcast
      have hnm : n = m := Nat.add_right_cancel hsucc
      simpa [hnm] using hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem encodedPositive_injective : Function.Injective encodedPositive := by
  intro S T hST
  ext n
  rw [← neg_code_mem_encodedPositive (S := S), ← neg_code_mem_encodedPositive (S := T), hST]

theorem encodedPositive_mem_witnessFamily (q : ℕ) (S : Set ℕ) :
    encodedPositive S ∈ witnessFamily q := by
  left
  constructor
  · intro z hz
    left
    rcases mem_markers.mp (by simpa using hz) with ⟨n, hn, rfl⟩
    exact Int.natCast_nonneg n
  · refine ⟨0, ?_⟩
    intro z hz
    left
    simpa using hz

theorem witnessFamily_not_countable (q : ℕ) : ¬(witnessFamily q).Countable := by
  intro hcount
  have hpre : (encodedPositive ⁻¹' witnessFamily q).Countable :=
    hcount.preimage encodedPositive_injective
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    apply Set.Countable.mono (s₁ := Set.univ) (s₂ := encodedPositive ⁻¹' witnessFamily q)
    · intro S hS
      exact encodedPositive_mem_witnessFamily q S
    · exact hpre
  obtain ⟨enumerate, henumerate⟩ := huniv.exists_eq_range (by
    exact ⟨∅, Set.mem_univ ∅⟩)
  let diagonal : Set ℕ := {n | n ∉ enumerate n}
  have hdiag : diagonal ∈ (Set.univ : Set (Set ℕ)) := Set.mem_univ diagonal
  rw [henumerate] at hdiag
  rcases hdiag with ⟨n, hn⟩
  have hiff : n ∈ diagonal ↔ n ∉ diagonal := by
    change (n ∉ enumerate n) ↔ n ∉ diagonal
    rw [hn]
  by_cases hmem : n ∈ diagonal
  · exact (hiff.mp hmem) hmem
  · exact hmem (hiff.mpr hmem)

end Case019Formalization

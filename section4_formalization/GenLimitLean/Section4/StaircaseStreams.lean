import Section4.StaircaseFrontier
import Mathlib.Logic.Denumerable

/-! Equivalence between the finite ordered-history semantics and genuine
infinite injective positive streams. No extendibility hypothesis is assumed:
every legal finite history is explicitly extended with fresh private points. -/
namespace Section4.Staircase.Family

variable (F : Family)

abbrev Stream := ℕ → Point

def LegalStream (i : ℕ) (u : Stream) : Prop :=
  Function.Injective u ∧ ∀ n, u n ∈ F.target i

def observations (u : Stream) (n : ℕ) : History := (List.range n).map u

@[simp] theorem observations_length (u : Stream) (n : ℕ) : (observations u n).length = n := by
  simp [observations]

theorem observations_legal {i : ℕ} {u : Stream} (hu : F.LegalStream i u) (n : ℕ) :
    F.Legal i (observations u n) := by
  refine ⟨List.nodup_range.map hu.1,?_⟩
  intro p hp
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
  exact hu.2 k

def privateBound (h : History) : ℕ :=
  (h.map fun p => match p with | .inl _ => 0 | .inr q => q.2+1).sum

theorem private_index_lt_bound {h : History} {i r : ℕ} (hm : Sum.inr (i,r) ∈ h) :
    r < privateBound h := by
  have hm' : r+1 ∈ h.map (fun p => match p with | .inl _ => 0 | .inr q => q.2+1) :=
    List.mem_map.mpr ⟨_,hm,rfl⟩
  have hh := List.le_sum_of_mem hm'
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hh

def extend (h : History) (i : ℕ) (n : ℕ) : Point :=
  if hn : n < h.length then h.get ⟨n,hn⟩ else Sum.inr (i,privateBound h+n)

theorem extend_fresh_tail (h : History) (i n : ℕ) :
    Sum.inr (i,privateBound h+n) ∉ h := by
  intro hm
  have hh := private_index_lt_bound hm
  omega

theorem extend_legal {i : ℕ} {h : History} (hl : F.Legal i h) :
    F.LegalStream i (extend h i) := by
  constructor
  · intro n m heq
    by_cases hn : n < h.length <;> by_cases hm : m < h.length
    · simp only [extend, dif_pos hn, dif_pos hm] at heq
      have hfin := (List.nodup_iff_injective_get.mp hl.1) heq
      exact congrArg Fin.val hfin
    · simp only [extend, dif_pos hn, dif_neg hm] at heq
      have hmem : Sum.inr (i,privateBound h+m) ∈ h := heq ▸ List.get_mem h ⟨n,hn⟩
      exact False.elim (extend_fresh_tail h i m hmem)
    · simp only [extend, dif_neg hn, dif_pos hm] at heq
      have hmem : Sum.inr (i,privateBound h+n) ∈ h := heq.symm ▸ List.get_mem h ⟨m,hm⟩
      exact False.elim (extend_fresh_tail h i n hmem)
    · simp only [extend, dif_neg hn, dif_neg hm, Sum.inr.injEq, Prod.mk.injEq, true_and] at heq
      omega
  · intro n
    by_cases hn : n < h.length
    · simp only [extend,dif_pos hn]
      exact hl.2 _ (List.get_mem h ⟨n,hn⟩)
    · simp [extend,hn]

theorem observations_extend (h : History) (i : ℕ) :
    observations (extend h i) h.length = h := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    simp [observations,extend,hn']

theorem every_history_extends {i : ℕ} {h : History} (hl : F.Legal i h) :
    ∃ u, F.LegalStream i u ∧ observations u h.length = h :=
  ⟨extend h i,F.extend_legal hl,observations_extend h i⟩

def StreamMistakeBound (G : Generator) (i m : ℕ) : Prop :=
  ∀ u, F.LegalStream i u → ∀ n, (F.mistakeTimes G i (observations u n)).card ≤ m

def StreamDeadlineBound (G : Generator) (i d : ℕ) : Prop :=
  ∀ u, F.LegalStream i u → ∀ n, d ≤ n → G (observations u n) ∈ F.target i

theorem mistakeBound_iff_stream (G : Generator) (i m : ℕ) :
    F.MistakeBound G i m ↔ F.StreamMistakeBound G i m := by
  constructor
  · intro hm u hu n
    exact hm _ (F.observations_legal hu n)
  · intro hm h hl
    obtain ⟨u,hu,heq⟩ := F.every_history_extends hl
    simpa only [heq] using hm u hu h.length

theorem deadlineBound_iff_stream (G : Generator) (i d : ℕ) :
    F.DeadlineBound G i d ↔ F.StreamDeadlineBound G i d := by
  constructor
  · intro hd u hu n hn
    exact hd _ (F.observations_legal hu n) (by simpa using hn)
  · intro hd h hl hn
    obtain ⟨u,hu,heq⟩ := F.every_history_extends hl
    simpa only [heq] using hd u hu h.length hn

/-- Exact schedule guarantees over real infinite injective input streams. -/
theorem schedule_stream_guarantees (σ : ℕ → Bool) (i m d : ℕ) :
    (F.StreamMistakeBound (F.scheduleGenerator σ) i m ↔ mistakeCount σ i ≤ m) ∧
    (F.StreamDeadlineBound (F.scheduleGenerator σ) i d ↔ F.deadline σ i ≤ d) := by
  constructor
  · rw [← F.mistakeBound_iff_stream, F.schedule_mistakeBound_iff]
  · rw [← F.deadlineBound_iff_stream, F.schedule_deadlineBound_iff]



def CompleteStream (i : ℕ) (u : Stream) : Prop :=
  F.LegalStream i u ∧ ∀ p ∈ F.target i, ∃ n, u n = p

/-- Every legal ordered finite history has an injective complete continuation. -/
theorem every_history_completes {i : ℕ} {h : History} (hl : F.Legal i h) :
    ∃ u, F.CompleteStream i u ∧ observations u h.length = h := by
  classical
  have ht : (F.target i).Infinite := by
    have hr := Set.infinite_range_of_injective (f := fun r : ℕ => (Sum.inr (i,r) : Point))
      (by intro a b hab; simpa using hab)
    apply hr.mono
    rintro p ⟨r,rfl⟩
    simp
  let S : Set Point := F.target i \ (h.toFinset : Set Point)
  have hs : S.Infinite := ht.diff h.toFinset.finite_toSet
  letI : Infinite S := hs.to_subtype
  obtain ⟨e⟩ : Nonempty (S ≃ ℕ) := inferInstance
  let v : ℕ → Point := fun n => (e.symm n).val
  have hvfresh : ∀ n, v n ∉ h := by
    intro n
    have hh := (e.symm n).property.2
    simpa only [Finset.mem_coe,List.mem_toFinset] using hh
  have hvlegal : ∀ n, v n ∈ F.target i := fun n => (e.symm n).property.1
  have hvinj : Function.Injective v := by
    intro n m hnm
    exact e.symm.injective (Subtype.ext hnm)
  let u : Stream := fun n =>
    if hn : n < h.length then h.get ⟨n,hn⟩ else v (n-h.length)
  have hu : F.LegalStream i u := by
    constructor
    · intro n m heq
      by_cases hn : n < h.length <;> by_cases hm : m < h.length
      · simp only [u,dif_pos hn,dif_pos hm] at heq
        exact congrArg Fin.val ((List.nodup_iff_injective_get.mp hl.1) heq)
      · simp only [u,dif_pos hn,dif_neg hm] at heq
        exact False.elim (hvfresh (m-h.length) (heq ▸ List.get_mem h ⟨n,hn⟩))
      · simp only [u,dif_neg hn,dif_pos hm] at heq
        exact False.elim (hvfresh (n-h.length) (heq.symm ▸ List.get_mem h ⟨m,hm⟩))
      · simp only [u,dif_neg hn,dif_neg hm] at heq
        have hh := hvinj heq
        omega
    · intro n
      by_cases hn : n < h.length
      · simp only [u,dif_pos hn]
        exact hl.2 _ (List.get_mem h ⟨n,hn⟩)
      · simp only [u,dif_neg hn]
        exact hvlegal _
  refine ⟨u,⟨hu,?_⟩,?_⟩
  · intro p hp
    by_cases hm : p ∈ h
    · obtain ⟨n,hn⟩ := List.mem_iff_get.mp hm
      exact ⟨n,by simpa only [u,dif_pos n.isLt] using hn⟩
    · let q : S := ⟨p,hp,by simpa using hm⟩
      refine ⟨h.length + e q,?_⟩
      have hn : ¬ h.length + e q < h.length := by omega
      simp only [u,dif_neg hn,Nat.add_sub_cancel_left,v]
      exact congrArg Subtype.val (e.symm_apply_apply q)
  · apply List.ext_getElem
    · simp
    · intro n hn hn'
      simp [observations,u,hn']

def CompleteMistakeBound (G : Generator) (i m : ℕ) : Prop :=
  ∀ u, F.CompleteStream i u → ∀ n, (F.mistakeTimes G i (observations u n)).card ≤ m

def CompleteDeadlineBound (G : Generator) (i d : ℕ) : Prop :=
  ∀ u, F.CompleteStream i u → ∀ n, d ≤ n → G (observations u n) ∈ F.target i

theorem mistakeBound_iff_complete (G : Generator) (i m : ℕ) :
    F.MistakeBound G i m ↔ F.CompleteMistakeBound G i m := by
  constructor
  · intro hm u hu n
    exact hm _ (F.observations_legal hu.1 n)
  · intro hm h hl
    obtain ⟨u,hu,heq⟩ := F.every_history_completes hl
    simpa only [heq] using hm u hu h.length

theorem deadlineBound_iff_complete (G : Generator) (i d : ℕ) :
    F.DeadlineBound G i d ↔ F.CompleteDeadlineBound G i d := by
  constructor
  · intro hd u hu n hn
    exact hd _ (F.observations_legal hu.1 n) (by simpa using hn)
  · intro hd h hl hn
    obtain ⟨u,hu,heq⟩ := F.every_history_completes hl
    simpa only [heq] using hd u hu h.length hn

end Section4.Staircase.Family

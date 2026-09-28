import Section4.ReplayMachine
import Section4.ReplaySufficiency

/-! A finite-horizon count of output changes, bounded uniformly by family size. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def changeCount (out : ℕ → ι) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun t => out (t + 1) ≠ out t)).card

@[simp] theorem changeCount_zero (out : ℕ → ι) : changeCount out 0 = 0 := by
  simp [changeCount]

theorem changeCount_succ (out : ℕ → ι) (n : ℕ) :
    changeCount out (n + 1) = changeCount out n + if out (n + 1) ≠ out n then 1 else 0 := by
  classical
  by_cases h : out (n + 1) ≠ out n
  · simp [changeCount, Finset.range_add_one, Finset.filter_insert, h]
  · simp [changeCount, Finset.range_add_one, Finset.filter_insert, h]

/-- One exceptional initial output plus a decreasing nonempty candidate set
allows at most as many changes as the initial set has members. -/
theorem decreasing_candidates_change_bound (C : ℕ → Finset ι) (out : ℕ → ι)
    (f : Finset ι → ι) (hanti : Antitone C) (hne : ∀ n, (C n).Nonempty)
    (houtput : ∀ n, 0 < n → out n = f (C n)) :
    ∀ n, changeCount out n ≤ (C 0).card := by
  have hrank : ∀ n, changeCount out (n + 1) + (C (n + 1)).card ≤ (C 0).card + 1 := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.zero_add]
      have hc := Finset.card_le_card (hanti (show 0 ≤ 1 by omega))
      have hcount : changeCount out 1 ≤ 1 := by
        unfold changeCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    | succ n ih =>
      have hsub := hanti (show n + 1 ≤ n + 1 + 1 by omega)
      by_cases hchange : out (n + 1 + 1) ≠ out (n + 1)
      · have hsets : C (n + 1 + 1) ≠ C (n + 1) := by
          intro heq
          apply hchange
          rw [houtput (n + 1 + 1) (by omega), houtput (n + 1) (by omega), heq]
        have hcard : (C (n + 1 + 1)).card < (C (n + 1)).card := by
          by_contra! hnot
          exact hsets (Finset.eq_of_subset_of_card_le hsub hnot)
        rw [changeCount_succ, if_pos hchange]
        omega
      · have hcard := Finset.card_le_card hsub
        rw [changeCount_succ, if_neg hchange]
        omega
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := hrank n
    have hpos : 0 < (C (n + 1)).card := Finset.card_pos.mpr (hne (n + 1))
    omega

/-- Along every legal replay run the constructed generator changes its index
at most `card ι` times, counting changes after the first actual output. -/
theorem generator_change_bound (L : ι → Set α) (first lower : Finset ι → ι)
    (hlower : LowerSpec L lower) (target : ι) (s : ℕ → α)
    (hgood : GoodFirst L (profile L (s 0)) (first (profile L (s 0))))
    (hlegal : IsProperReplaySequence L (generator L first lower) target s) (n : ℕ) :
    changeCount (fun t => properOutput (generator L first lower) s (t + 1)) n ≤
      Fintype.card ι := by
  classical
  let j := first (profile L (s 0))
  let P := profile L (s 0)
  let C := fun t => candidates L j P s (t + 1)
  have hanti : Antitone C := by
    intro m k hmk
    exact candidates_antitone L j P s (Nat.add_le_add_right hmk 1)
  have hne : ∀ t, (C t).Nonempty := by
    intro t
    exact ⟨target, (generator_invariants L first lower hlower target s hgood hlegal (t + 1) (by omega)).1⟩
  have hout : ∀ t, 0 < t → properOutput (generator L first lower) s (t + 1) =
      chosenOutput L lower j (C t) := by
    intro t ht
    rw [generator_output_succ, if_neg (by omega)]
  have hb := decreasing_candidates_change_bound C
    (fun t => properOutput (generator L first lower) s (t + 1))
    (chosenOutput L lower j) hanti hne hout n
  exact hb.trans (Finset.card_le_univ _)

end Section4.Replay

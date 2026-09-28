import Section4.ReplayConstruction

/-! The joint replay invariant and convergence proof, in P22's exact semantics. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem first_observation_mem (L : ι → Set α) (gen : ProperGenerator ι α)
    (target : ι) (s : ℕ → α) (hlegal : IsProperReplaySequence L gen target s) :
    s 0 ∈ L target := by
  rcases hlegal 0 with h | ⟨k, hk, hle, _⟩
  · exact h
  · omega

/-- The true target survives filtering, and no output expands contamination
outside the union of the target and the first output. -/
theorem generator_invariants (L : ι → Set α) (first lower : Finset ι → ι)
    (hlower : LowerSpec L lower) (target : ι) (s : ℕ → α)
    (hgood : GoodFirst L (profile L (s 0)) (first (profile L (s 0))))
    (hlegal : IsProperReplaySequence L (generator L first lower) target s) :
    ∀ n, 0 < n →
      target ∈ candidates L (first (profile L (s 0))) (profile L (s 0)) s n ∧
      L (properOutput (generator L first lower) s n) ⊆
        L (first (profile L (s 0))) ∪ L target := by
  classical
  have hfirst : s 0 ∈ L target := first_observation_mem L _ target s hlegal
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have htarget : target ∈ candidates L (first (profile L (s 0))) (profile L (s 0)) s n := by
      rw [mem_candidates]
      refine ⟨by simpa using hfirst, ?_⟩
      intro t ht hx
      rcases hlegal t with h | ⟨k, hkpos, hkt, hmem⟩
      · exact h
      · have hout := (ih k (lt_of_le_of_lt hkt ht) hkpos).2 hmem
        exact hout.resolve_left hx
    refine ⟨htarget, ?_⟩
    cases n with
    | zero => omega
    | succ m =>
      rw [generator_output_succ]
      split_ifs with hm
      · exact Set.subset_union_left
      · exact chosenOutput_contained L lower hlower _ _ hgood s (m + 1) htarget

/-- Finitely many target witnesses eventually make the true residual least. -/
theorem eventually_true_least (L : ι → Set α) (j : ι) (P : Finset ι)
    (target : ι) (s : ℕ → α)
    (hkeep : ∀ n, 0 < n → target ∈ candidates L j P s n)
    (hcomplete : ∀ x, x ∈ L target → ∃ n, s n = x) :
    ∃ B, 2 ≤ B ∧ ∀ n, B ≤ n → LeastCandidate L j (candidates L j P s n) target := by
  classical
  have hw : ∀ k : ι, ∃ T : ℕ, ∀ n, T ≤ n → k ∈ candidates L j P s n →
      residual L j target ⊆ residual L j k := by
    intro k
    by_cases hsub : residual L j target ⊆ residual L j k
    · exact ⟨0, fun _ _ _ => hsub⟩
    · obtain ⟨x, hx, hnot⟩ := Set.not_subset.mp hsub
      obtain ⟨t, ht⟩ := hcomplete x hx.1
      refine ⟨t + 1, ?_⟩
      intro n hn hk
      have hmem := (mem_candidates L j P s n k).mp hk |>.2 t (by omega)
      have hxk : s t ∈ L k := hmem (by simpa [ht] using hx.2)
      exact False.elim (hnot ⟨by simpa [ht] using hxk, hx.2⟩)
  choose times htimes using hw
  let B := Finset.univ.sup times + 2
  refine ⟨B, by omega, ?_⟩
  intro n hn
  refine ⟨hkeep n (by omega), ?_⟩
  intro k hk
  have hkbound : times k ≤ Finset.univ.sup times := Finset.le_sup (Finset.mem_univ k)
  exact htimes k n (by omega) hk

/-- The constructed learner stabilizes to one fixed correct index. -/
theorem generator_stabilizes (L : ι → Set α) (first lower : Finset ι → ι)
    (hlower : LowerSpec L lower) (target : ι) (s : ℕ → α)
    (hgood : GoodFirst L (profile L (s 0)) (first (profile L (s 0))))
    (htext : IsProperReplayEnumeration L (generator L first lower) target s) :
    ∃ h, L h ⊆ L target ∧ ∃ B, ∀ n, B ≤ n →
      properOutput (generator L first lower) s n = h := by
  classical
  let j := first (profile L (s 0))
  let P := profile L (s 0)
  have hinv := generator_invariants L first lower hlower target s hgood htext.1
  obtain ⟨B, hB, hleast⟩ := eventually_true_least L j P target s
    (fun n hn => (hinv n hn).1) htext.2
  have htP : target ∈ P := by
    simpa [P] using first_observation_mem L _ target s htext.1
  have hlow := hlower (group L j P target) (hgood target htP)
  refine ⟨lower (group L j P target), hlow target (self_mem_group L j htP), B, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    rw [generator_output_succ, if_neg (show m ≠ 0 by omega)]
    exact chosenOutput_eq_of_least L lower j P s (m + 1) (hleast (m + 1) hn)

theorem generator_correct (L : ι → Set α) (first lower : Finset ι → ι)
    (hfirst : ∀ x, (∃ i, x ∈ L i) → GoodFirst L (profile L x) (first (profile L x)))
    (hlower : LowerSpec L lower) :
    IsProperLimitReplayGenerator L (generator L first lower) := by
  intro target s htext
  have hx : s 0 ∈ L target := first_observation_mem L _ target s htext.1
  obtain ⟨h, hsub, B, hstab⟩ := generator_stabilizes L first lower hlower target s
    (hfirst (s 0) ⟨target, hx⟩) htext
  refine ⟨B, ?_⟩
  intro n hn
  change L (properOutput (generator L first lower) s n) ⊆ L target
  rw [hstab n hn]
  exact hsub

/-- The sufficiency direction of the finite-family characterization. -/
theorem criterion_sufficient (L : ι → Set α) (hc : Criterion L) :
    ProperlyGeneratableInLimitWithReplay L := by
  exact ⟨generator L (firstChoice L) (lowerChoice L),
    generator_correct L (firstChoice L) (lowerChoice L)
      (firstChoice_spec L hc) (lowerChoice_spec L)⟩

end Section4.Replay

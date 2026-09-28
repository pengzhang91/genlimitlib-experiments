import Stage3Model
import Mathlib.Logic.Equiv.Finset
import Mathlib.Tactic

open Set
open Stage3Case025

namespace Case025

noncomputable section

def trajectoryHistory (gen : OnlineGenerator) (input : Stream) :
    (t : ℕ) → (Fin t → ℕ)
  | 0 => Fin.elim0
  | t + 1 =>
      Fin.lastCases
        (gen t (fun i => input i) (trajectoryHistory gen input t))
        (trajectoryHistory gen input t)

def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => gen t (fun i => input i) (trajectoryHistory gen input t)

lemma trajectoryHistory_succ_last (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectoryHistory gen input (t + 1) (Fin.last t) = trajectory gen input t := by
  simp [trajectoryHistory, trajectory]

lemma trajectoryHistory_succ_castSucc (gen : OnlineGenerator) (input : Stream)
    (t : ℕ) (i : Fin t) :
    trajectoryHistory gen input (t + 1) i.castSucc = trajectoryHistory gen input t i := by
  simp [trajectoryHistory]

lemma trajectoryHistory_eq_trajectory (gen : OnlineGenerator) (input : Stream) :
    ∀ (t : ℕ) (i : Fin t), trajectoryHistory gen input t i = trajectory gen input i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact trajectoryHistory_succ_last gen input t
      · rw [trajectoryHistory_succ_castSucc]
        simpa using ih j

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  simp only [trajectory]
  congr 1
  funext i
  exact trajectoryHistory_eq_trajectory gen input t i

def decodedFinset (code : ℕ) : Finset ℕ :=
  (Encodable.decode code : Option (Finset ℕ)).getD ∅

lemma decodedFinset_encode (s : Finset ℕ) :
    decodedFinset (Encodable.encode s) = s := by
  simp [decodedFinset, Encodable.encodek]

def finiteExpansion (family : ℕ → Language) (code : ℕ) : Language :=
  family (Nat.unpair code).1 ∪ (decodedFinset (Nat.unpair code).2 : Set ℕ)

lemma finiteExpansion_pair (family : ℕ → Language) (i : ℕ) (s : Finset ℕ) :
    finiteExpansion family (Nat.pair i (Encodable.encode s)) =
      family i ∪ (s : Set ℕ) := by
  simp [finiteExpansion, decodedFinset_encode]

lemma finiteExpansion_infinite (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) :
    ∀ code, (finiteExpansion family code).Infinite := by
  intro code
  exact (hinf (Nat.unpair code).1).mono subset_union_left

def offTargetValues (input : Stream) (K : Language) : Set ℕ :=
  Set.range input \ K

lemma offTargetValues_finite {input : Stream} {K : Language}
    (hviol : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (offTargetValues input K).Finite := by
  let badTimes := GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)
  have hbad : badTimes.Finite := hviol
  have himage : (input '' badTimes).Finite := hbad.image input
  refine himage.subset ?_
  intro x hx
  rcases hx.1 with ⟨t, rfl⟩
  refine ⟨t, ?_, rfl⟩
  change ¬input t ∈ K
  exact hx.2

lemma range_eq_target_union_offTarget {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ offTargetValues input K := by
  ext x
  constructor
  · intro hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · exact Or.inr ⟨hx, hk⟩
  · rintro (hx | hx)
    · exact hcover hx
    · exact hx.1

lemma contaminated_range_is_expansion {family : ℕ → Language} {i : ℕ}
    {input : Stream}
    (hpresent : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ code, GenLimit.Presents input (finiteExpansion family code) := by
  have hfinite : (offTargetValues input (family i)).Finite :=
    offTargetValues_finite hpresent.2
  let extras : Finset ℕ := hfinite.toFinset
  refine ⟨Nat.pair i (Encodable.encode extras), ?_⟩
  rw [finiteExpansion_pair]
  exact (range_eq_target_union_offTarget hpresent.1).trans <| by
    rw [Set.Finite.coe_toFinset]

lemma tail_injective_of_novel {input output : Stream} {K : Language} {T : ℕ}
    (hnovel : ∀ t, T ≤ t →
      output t ∈ K ∧ output t ∉ GenLimit.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t) :
    Set.InjOn output {t | T ≤ t} := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · exact False.elim ((hnovel b hb).2.2 a hablt hab)
  · rfl
  · exact False.elim ((hnovel a ha).2.2 b hbalt hab.symm)

lemma eventually_avoids_finite_of_tail_injective {output : Stream} {T : ℕ}
    (hinj : Set.InjOn output {t | T ≤ t}) {F : Set ℕ} (hF : F.Finite) :
    ∃ T', ∀ t, T' ≤ t → T ≤ t ∧ output t ∉ F := by
  let bad := {t | T ≤ t ∧ output t ∈ F}
  have hbad : bad.Finite := by
    refine Set.Finite.of_injOn (f := output) (s := bad) (t := F) ?_ ?_ hF
    · intro t ht
      exact ht.2
    · exact hinj.mono (fun _ ht => ht.1)
  obtain ⟨N, hN⟩ := hbad.bddAbove
  refine ⟨max T (N + 1), fun t ht => ⟨le_trans (le_max_left _ _) ht, ?_⟩⟩
  intro hout
  have htbad : t ∈ bad := ⟨le_trans (le_max_left _ _) ht, hout⟩
  have := hN htbad
  omega

def FiniteNoiseTransferWithoutDensity : Prop :=
  PositivePresentationHalfDensity →
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream),
          CompleteFiniteOccurrencePresentation input (family i) →
            ∃ output : Stream,
              Follows gen input output ∧
              GenLimit.NovelGeneratesInLimit input output (family i) ∧
              (1 / 2 : ℝ) ≤
                GenLimit.PatientScope.relativeLowerDensity
                  (GenLimit.GeneratorFirst input output ∩ Set.range input)
                  (Set.range input)

theorem finite_noise_transfer_without_density : FiniteNoiseTransferWithoutDensity := by
  intro positive family hinfinite
  obtain ⟨gen, hgen⟩ := positive (finiteExpansion family)
    (finiteExpansion_infinite family hinfinite)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  obtain ⟨code, hcode⟩ := contaminated_range_is_expansion hpresentation
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen code input hcode
  refine ⟨output, hfollows, ?_, ?_⟩
  · rcases hnovel with ⟨T, hT⟩
    have hfinite : (offTargetValues input (family i)).Finite :=
      offTargetValues_finite hpresentation.2
    have hinjective : Set.InjOn output {t | T ≤ t} :=
      tail_injective_of_novel hT
    obtain ⟨T', hT'⟩ :=
      eventually_avoids_finite_of_tail_injective hinjective hfinite
    refine ⟨T', fun t ht => ?_⟩
    obtain ⟨hTt, hnotbad⟩ := hT' t ht
    have hold := hT t hTt
    refine ⟨?_, hold.2.1, hold.2.2⟩
    have hrange : output t ∈ Set.range input := by
      rw [hcode]
      exact hold.1
    exact Classical.byContradiction fun hnotmem =>
      hnotbad ⟨hrange, hnotmem⟩
  · rw [hcode]
    exact hdensity

end

end Case025


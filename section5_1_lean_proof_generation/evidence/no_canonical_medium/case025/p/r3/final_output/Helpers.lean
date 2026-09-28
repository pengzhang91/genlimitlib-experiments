import Stage3Model

open Set
open Stage3Case025

namespace Stage3Case025

/-- The unique causal trajectory generated from an input stream. -/
noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]


/-- The finitely many off-target values occurring in a finitely contaminated stream. -/
def noiseValues (input : Stream) (K : Language) : Set ℕ :=
  Set.range input \ K

lemma noiseValues_finite {input : Stream} {K : Language}
    (hfin : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (noiseValues input K).Finite := by
  let bad : Set ℕ := GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)
  have hbad : bad.Finite := hfin
  have hsub : noiseValues input K ⊆ input '' bad := by
    intro x hx
    rcases hx.1 with ⟨t, rfl⟩
    exact ⟨t, hx.2, rfl⟩
  exact (hbad.image input).subset hsub

lemma range_eq_target_union_noiseValues {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ noiseValues input K := by
  ext x
  constructor
  · intro hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · exact Or.inr ⟨hx, hk⟩
  · intro hx
    exact hx.elim (fun hk => hcover hk) (fun h => h.1)

lemma novel_injective_on_tail {input output : Stream} {K : Language} {T : ℕ}
    (hnovel : ∀ t, T ≤ t →
      output t ∈ K ∧ output t ∉ GenLimit.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t) :
    Set.InjOn output (Set.Ici T) := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · exact (hnovel b hb).2.2 a hablt hab
  · exact (hnovel a ha).2.2 b hbalt hab.symm

lemma eventually_avoids_finite_of_novel {input output : Stream} {K E : Language}
    (hE : E.Finite)
    (hgen : GenLimit.NovelGeneratesInLimit input output (K ∪ E)) :
    ∃ T, ∀ t, T ≤ t → output t ∈ K := by
  rcases hgen with ⟨T₀, hT₀⟩
  let badTimes : Set ℕ := {t | T₀ ≤ t ∧ output t ∈ E}
  have hinj : Set.InjOn output (Set.Ici T₀) := novel_injective_on_tail hT₀
  have hinjBad : Set.InjOn output badTimes := hinj.mono (fun _ ht => ht.1)
  have himage : (output '' badTimes).Finite := hE.subset (by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ht.2)
  have hbad : badTimes.Finite := (Set.finite_image_iff hinjBad).mp himage
  obtain ⟨T, hT⟩ := hbad.bddAbove
  refine ⟨max T₀ (T + 1), ?_⟩
  intro t ht
  have ht0 : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have hout := (hT₀ t ht0).1
  rcases hout with hk | he
  · exact hk
  · exfalso
    have hmem : t ∈ badTimes := ⟨ht0, he⟩
    have hle : t ≤ T := hT hmem
    have hgt : T < t := lt_of_lt_of_le (Nat.lt_succ_self T) (le_trans (le_max_right _ _) ht)
    exact (Nat.not_lt_of_ge hle) hgt

lemma novel_remove_finite {input output : Stream} {K E : Language}
    (hE : E.Finite)
    (hgen : GenLimit.NovelGeneratesInLimit input output (K ∪ E)) :
    GenLimit.NovelGeneratesInLimit input output K := by
  obtain ⟨T₀, hT₀⟩ := hgen
  obtain ⟨T₁, hT₁⟩ := eventually_avoids_finite_of_novel hE ⟨T₀, hT₀⟩
  refine ⟨max T₀ T₁, ?_⟩
  intro t ht
  have ht0 : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : T₁ ≤ t := le_trans (le_max_right _ _) ht
  exact ⟨hT₁ t ht1, (hT₀ t ht0).2⟩

end Stage3Case025

namespace Stage3Case025

noncomputable local instance : Encodable (Finset ℕ) := Encodable.ofCountable _

noncomputable def decodedFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n : Option (Finset ℕ)).getD ∅

noncomputable def finiteExtensionFamily
    (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪ (decodedFinset (Nat.unpair n).2 : Set ℕ)

lemma finiteExtensionFamily_infinite
    {family : ℕ → Language} (hinf : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteExtensionFamily family n).Infinite := by
  exact (hinf (Nat.unpair n).1).mono Set.subset_union_left

lemma decodedFinset_encode (s : Finset ℕ) :
    decodedFinset (Encodable.encode s) = s := by
  simp [decodedFinset, Encodable.encodek]

lemma finiteExtensionFamily_pair
    (family : ℕ → Language) (i : ℕ) (E : Set ℕ) (hE : E.Finite) :
    finiteExtensionFamily family (Nat.pair i (Encodable.encode hE.toFinset)) = family i ∪ E := by
  simp [finiteExtensionFamily, decodedFinset_encode]

/-- A positive-presentation engine uniformly handles every finite-contaminated
stream after closing the indexed family under finite extensions. -/
lemma positive_engine_on_finite_extensions
    (hpositive : PositivePresentationHalfDensity)
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite) :
    ∃ gen : OnlineGenerator,
      ∀ i (input : Stream), CompleteFiniteOccurrencePresentation input (family i) →
        let E := noiseValues input (family i)
        ∃ output : Stream,
          Follows gen input output ∧
          GenLimit.NovelGeneratesInLimit input output (family i ∪ E) ∧
          (1 / 2 : ℝ) ≤
            GenLimit.PatientScope.relativeLowerDensity
              (GenLimit.GeneratorFirst input output ∩ (family i ∪ E))
              (family i ∪ E) := by
  obtain ⟨gen, hgen⟩ := hpositive (finiteExtensionFamily family)
    (finiteExtensionFamily_infinite hinf)
  refine ⟨gen, ?_⟩
  intro i input hpresent
  dsimp
  have hE : (noiseValues input (family i)).Finite := noiseValues_finite hpresent.2
  let code := Nat.pair i (Encodable.encode hE.toFinset)
  have htarget : finiteExtensionFamily family code =
      family i ∪ noiseValues input (family i) := by
    exact finiteExtensionFamily_pair family i _ hE
  have hp : GenLimit.Presents input (finiteExtensionFamily family code) := by
    rw [GenLimit.Presents, htarget]
    exact range_eq_target_union_noiseValues hpresent.1
  simpa [htarget] using hgen code input hp

end Stage3Case025

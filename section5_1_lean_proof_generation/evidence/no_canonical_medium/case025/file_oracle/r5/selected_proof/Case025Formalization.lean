import Helpers

open Set

namespace Stage3Case025

open GenLimit
open GenLimit.PatientMachine

noncomputable def expandedLanguage
    (family : ℕ → Language) (code : ℕ) : Language :=
  family (Nat.unpair code).1 ∪
    ((Encodable.decode (α := Finset ℕ) (Nat.unpair code).2).getD ∅ : Set ℕ)

lemma expandedLanguage_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (code : ℕ) :
    (expandedLanguage family code).Infinite :=
  (hInfinite (Nat.unpair code).1).mono Set.subset_union_left

noncomputable def expandedOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := expandedLanguage family
  infinite' := expandedLanguage_infinite family hInfinite
  query i x := by
    classical
    exact if x ∈ expandedLanguage family i then true else false
  query_spec i x := by
    classical
    simp

noncomputable def prefixExtension
    (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

lemma prefixExtension_eq (input : Stream) (t : ℕ) :
    ∀ s, s < t + 1 →
      prefixExtension t (fun i => input i) s = input s := by
  intro s hs
  simp [prefixExtension, hs]

noncomputable def patientOnlineGenerator (O : OracleFamily) : OnlineGenerator :=
  fun t xs _ => PatientMachine.output O (prefixExtension t xs) t

lemma patientOnlineGenerator_follows (O : OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input (PatientMachine.output O input) := by
  intro t
  unfold patientOnlineGenerator
  symm
  apply Causality.output_congr
  exact prefixExtension_eq input t

lemma range_diff_finite_of_violations
    {input : Stream} {K : Language}
    (h : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact h.image input

lemma patient_output_injective (O : OracleFamily) (input : Stream) :
    Function.Injective (PatientMachine.output O input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact PatientMachine.output_ne_of_lt O input hlt hst
  · exact PatientMachine.output_ne_of_lt O input hgt hst.symm

lemma eventually_mem_base
    {O : OracleFamily} {input : Stream} {K E : Set ℕ}
    (hfinite : (E \ K).Finite)
    (hvalid : ∃ T, ∀ t, T ≤ t → PatientMachine.output O input t ∈ E) :
    ∃ T, ∀ t, T ≤ t → PatientMachine.output O input t ∈ K := by
  let output := PatientMachine.output O input
  have hinj : Function.Injective output := patient_output_injective O input
  have hbad : (output ⁻¹' (E \ K)).Finite := hfinite.preimage hinj.injOn
  obtain ⟨B, hB⟩ := hbad.bddAbove
  obtain ⟨T, hT⟩ := hvalid
  refine ⟨max T (B + 1), ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htB : B < t := lt_of_lt_of_le (Nat.lt_succ_self B) (le_trans (le_max_right _ _) ht)
  have htE := hT t htT
  by_contra htK
  have : t ∈ output ⁻¹' (E \ K) := ⟨htE, htK⟩
  exact (Nat.not_lt_of_ge (hB this)) htB

lemma expandedLanguage_at_finset
    (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    expandedLanguage family (Nat.pair i (Encodable.encode F)) =
      family i ∪ (F : Set ℕ) := by
  simp [expandedLanguage, Nat.unpair_pair, Encodable.encodek]

end Stage3Case025

open Stage3Case025

 theorem stage3_result : Stage3Case025.MainClaim := by
  classical
  intro family hInfinite
  let O := expandedOracle family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hpresentation
  let K := family i
  let E := Set.range input
  have hKE : K ⊆ E := hpresentation.1
  have hfinite : (E \ K).Finite :=
    range_diff_finite_of_violations hpresentation.2
  let F : Finset ℕ := hfinite.toFinset
  let z := Nat.pair i (Encodable.encode F)
  have hlang : O.language z = E := by
    rw [show O.language z = expandedLanguage family z from rfl]
    rw [expandedLanguage_at_finset]
    change family i ∪ (hfinite.toFinset : Set ℕ) = Set.range input
    rw [Set.Finite.coe_toFinset]
    exact Set.union_diff_cancel hKE
  have hP : GenLimit.Presents input (O.language z) := by
    exact hlang.symm
  obtain ⟨hgeneration, hdensityE⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
  let output : Stream := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨TE, hTE⟩ := hgeneration
    obtain ⟨TK, hTK⟩ := eventually_mem_base
      (O := O) (input := input) (K := K) (E := E) hfinite
      ⟨TE, fun t ht => by rw [← hlang]; exact (hTE t ht).1⟩
    refine ⟨max TE TK, ?_⟩
    intro t ht
    have htE : TE ≤ t := le_trans (le_max_left _ _) ht
    have htK : TK ≤ t := le_trans (le_max_right _ _) ht
    refine ⟨hTK t htK, ?_, (hTE t htE).2.2⟩
    intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact (hTE t htE).2.1 s (Nat.le_of_lt_succ hs) heq
  · have hmono := relativeLowerDensity_mono_finite_extension
        (A := GenLimit.GeneratorFirst input output) hKE hfinite (hInfinite i)
    apply hdensityE.trans
    rw [GenLimit.PatientMachine.patientLowerDensity, hlang] at hdensityE ⊢
    exact hmono

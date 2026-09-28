import output.RecursiveSweep

open Filter
open scoped Topology
open Stage3Case019
open GenLimit.Generic

namespace Case019

lemma boundedSide_afterInput_injective
    (code : ℕ → ℤ) (hinj : Function.Injective code) (stream : ℕ → ℤ) :
    Function.Injective (fun t =>
      GenLimit.Generic.output (boundedSideGenerator code hinj) stream (t + 1)) := by
  intro s t heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hne' := boundedSideGenerator_prior_ne code hinj
        (xs := fun i : Fin (t + 1) => stream i) (s := s) (by omega)
    apply hne'
    simpa [GenLimit.Generic.output] using heq
  · have hne' := boundedSideGenerator_prior_ne code hinj
        (xs := fun i : Fin (s + 1) => stream i) (s := t) (by omega)
    apply hne'
    simpa [GenLimit.Generic.output] using heq.symm

lemma boundedPositive_eventually_in_tail
    (stream : ℕ → ℤ) (j : ℕ) :
    ∃ T, ∀ t, T ≤ t →
      GenLimit.Generic.output boundedPositiveGenerator stream (t + 1) ∈
        GenLimit.UnionClosedness.positiveTail j := by
  let out : ℕ → ℤ := fun t =>
    GenLimit.Generic.output boundedPositiveGenerator stream (t + 1)
  let low : Set ℤ := GenLimit.UnionClosedness.positiveCode '' Set.Iio j
  have hlow : low.Finite := by
    apply Set.Finite.image
    exact Set.finite_Iio j
  have houtinj : Function.Injective out := by
    exact boundedSide_afterInput_injective
      GenLimit.UnionClosedness.positiveCode
      GenLimit.UnionClosedness.positiveCode_injective stream
  have hbad : (out ⁻¹' low).Finite := hlow.preimage houtinj.injOn
  obtain ⟨M, hM⟩ := hbad.exists_le
  refine ⟨M + 1, ?_⟩
  intro t ht
  obtain ⟨k, hk, hout, _hfresh⟩ :=
    boundedSideGenerator_spec GenLimit.UnionClosedness.positiveCode
      GenLimit.UnionClosedness.positiveCode_injective (Nat.succ_pos t)
      (fun i : Fin (t + 1) => stream i)
  have hkj : j ≤ k := by
    by_contra hnot
    have htbad : t ∈ out ⁻¹' low := by
      change out t ∈ low
      refine ⟨k, ?_, ?_⟩
      · simpa using hnot
      · simpa [out, GenLimit.Generic.output] using hout.symm
    have := hM t htbad
    omega
  refine ⟨k - j, ?_⟩
  change GenLimit.UnionClosedness.positiveCode (j + (k - j)) =
    boundedSideGenerator GenLimit.UnionClosedness.positiveCode
      GenLimit.UnionClosedness.positiveCode_injective (t + 1)
        (fun i => stream i)
  rw [hout]
  congr 1
  omega

noncomputable def denseSweepGenerator (q : ℕ) : GenLimit.Generic.Generator ℤ :=
  fun n xs =>
    if GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆ sequenceSample xs then
      boundedPositiveGenerator n xs
    else boundedNegativeGenerator n xs

lemma denseSweep_output_rank_bound
    (q t : ℕ) (input : Stage3Case019.Stream ℤ) :
    ∃ r ≤ 4 * (t + 1),
      Stage3Case019.balanced r =
        outputAfterInput (denseSweepGenerator q) input t := by
  classical
  by_cases hmark : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      sequenceSample (fun i : Fin (t + 1) => input i)
  · obtain ⟨k, hk, hout, _⟩ :=
      boundedSideGenerator_spec GenLimit.UnionClosedness.positiveCode
        GenLimit.UnionClosedness.positiveCode_injective (Nat.succ_pos t)
        (fun i : Fin (t + 1) => input i)
    refine ⟨2 * k + 2, by omega, ?_⟩
    rw [outputAfterInput, GenLimit.Generic.output]
    simp only [denseSweepGenerator, if_pos hmark]
    change Stage3Case019.balanced (2 * k + 2) =
      boundedSideGenerator GenLimit.UnionClosedness.positiveCode
        GenLimit.UnionClosedness.positiveCode_injective (t + 1)
          (fun i => input i)
    rw [hout]
    simp [Stage3Case019.balanced, GenLimit.UnionClosedness.positiveCode]
    omega
  · obtain ⟨k, hk, hout, _⟩ :=
      boundedSideGenerator_spec GenLimit.UnionClosedness.negativeCode
        GenLimit.UnionClosedness.negativeCode_injective (Nat.succ_pos t)
        (fun i : Fin (t + 1) => input i)
    refine ⟨2 * k + 1, by omega, ?_⟩
    rw [outputAfterInput, GenLimit.Generic.output]
    simp only [denseSweepGenerator, if_neg hmark]
    change Stage3Case019.balanced (2 * k + 1) =
      boundedSideGenerator GenLimit.UnionClosedness.negativeCode
        GenLimit.UnionClosedness.negativeCode_injective (t + 1)
          (fun i => input i)
    rw [hout]
    simp [Stage3Case019.balanced, GenLimit.UnionClosedness.negativeCode]
    omega

end Case019

namespace Case019

lemma denseSweep_first_novel
    {q : ℕ} {K : Stage3Case019.Language ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q)
    {input : Stage3Case019.Stream ℤ}
    (henum : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (denseSweepGenerator q) input) K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Tm, hTm⟩ :=
    GenLimit.NoiseLossFeedback.allMarkers_eventually_observed henum hmarkers
  obtain ⟨Tj, hTj⟩ := boundedPositive_eventually_in_tail input j
  refine ⟨max Tm Tj, ?_⟩
  intro t ht
  have hdetect : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      sequenceSample (fun i : Fin (t + 1) => input i) := by
    rw [GenLimit.Generic.sequenceSample_prefix]
    exact hTm t (le_trans (Nat.le_max_left _ _) ht)
  have hpos : outputAfterInput (denseSweepGenerator q) input t =
      GenLimit.Generic.output boundedPositiveGenerator input (t + 1) := by
    simp [outputAfterInput, GenLimit.Generic.output, denseSweepGenerator, hdetect]
  obtain ⟨k, hk, hout, hfresh⟩ :=
    boundedSideGenerator_spec GenLimit.UnionClosedness.positiveCode
      GenLimit.UnionClosedness.positiveCode_injective (Nat.succ_pos t)
      (fun i : Fin (t + 1) => input i)
  have hmemK : outputAfterInput (denseSweepGenerator q) input t ∈ K := by
    rw [hpos]
    exact htail (hTj t (le_trans (Nat.le_max_right _ _) ht))
  have hsample : outputAfterInput (denseSweepGenerator q) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
    rw [hpos]
    simpa [GenLimit.Generic.output, GenLimit.Generic.sequenceSample_prefix] using hfresh
  refine ⟨hmemK, hsample, ?_⟩
  intro s hst heq
  by_cases hsdetect : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      sequenceSample (fun i : Fin (s + 1) => input i)
  · have hne := boundedSideGenerator_prior_ne
        GenLimit.UnionClosedness.positiveCode
        GenLimit.UnionClosedness.positiveCode_injective
        (xs := fun i : Fin (t + 1) => input i) (s := s) (by omega)
    apply hne
    simpa [outputAfterInput, GenLimit.Generic.output, denseSweepGenerator,
      hsdetect, hdetect] using heq
  · obtain ⟨ks, hks, houts, _⟩ :=
      boundedSideGenerator_spec GenLimit.UnionClosedness.negativeCode
        GenLimit.UnionClosedness.negativeCode_injective (Nat.succ_pos s)
        (fun i : Fin (s + 1) => input i)
    have hleft : outputAfterInput (denseSweepGenerator q) input s =
        GenLimit.UnionClosedness.negativeCode ks := by
      rw [outputAfterInput, GenLimit.Generic.output]
      simp only [denseSweepGenerator, if_neg hsdetect]
      exact houts
    have hright : outputAfterInput (denseSweepGenerator q) input t =
        GenLimit.UnionClosedness.positiveCode k := by
      rw [hpos]
      exact hout
    rw [hleft, hright] at heq
    simp [GenLimit.UnionClosedness.negativeCode,
      GenLimit.UnionClosedness.positiveCode] at heq
    have hneg : Int.negSucc ks < 0 := by omega
    rw [heq] at hneg
    omega

lemma denseSweep_second_novel
    {q : ℕ} {K : Stage3Case019.Language ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q)
    {input : Stage3Case019.Stream ℤ}
    (henum : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (denseSweepGenerator q) input) K := by
  classical
  refine ⟨0, ?_⟩
  intro t _ht
  have hnodetect : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      sequenceSample (fun i : Fin (t + 1) => input i) := by
    rw [GenLimit.Generic.sequenceSample_prefix]
    exact GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK henum t
  obtain ⟨k, hk, hout, hfresh⟩ :=
    boundedSideGenerator_spec GenLimit.UnionClosedness.negativeCode
      GenLimit.UnionClosedness.negativeCode_injective (Nat.succ_pos t)
      (fun i : Fin (t + 1) => input i)
  have hneg : outputAfterInput (denseSweepGenerator q) input t =
      GenLimit.UnionClosedness.negativeCode k := by
    rw [outputAfterInput, GenLimit.Generic.output]
    simp only [denseSweepGenerator, if_neg hnodetect]
    exact hout
  refine ⟨hneg ▸ hK.1 (GenLimit.UnionClosedness.negativeCode_mem k), ?_, ?_⟩
  · rw [hneg, ← hout]
    simpa [GenLimit.Generic.sequenceSample_prefix] using hfresh
  · intro s hst heq
    have hsno : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        sequenceSample (fun i : Fin (s + 1) => input i) := by
      rw [GenLimit.Generic.sequenceSample_prefix]
      exact GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK henum s
    have hne := boundedSideGenerator_prior_ne
      GenLimit.UnionClosedness.negativeCode
      GenLimit.UnionClosedness.negativeCode_injective
      (xs := fun i : Fin (t + 1) => input i) (s := s) (by omega)
    apply hne
    simpa [outputAfterInput, GenLimit.Generic.output, denseSweepGenerator,
      hsno, hnodetect] using heq

end Case019

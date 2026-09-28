import output.DensityTransfer

open Set Filter
open GenLimit.Generic
open Stage3Case019

namespace Stage3Case019

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.PatientScope

private theorem novelGenerates_of_finite_extension
    {input output : Stream ℕ} {K E : Set ℕ}
    (hpresents : GenLimit.Generic.Presents input E)
    (hfinite : (E \ K).Finite)
    (hnovel : NovelGeneratesInLimit input output E) :
    NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tnovel, hTnovel⟩ := hnovel
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hpresents hfinite.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max Tnovel Tseen, ?_⟩
  intro t ht
  have htNovel : Tnovel ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨houtE, hfresh, hnew⟩ := hTnovel t htNovel
  refine ⟨?_, hfresh, hnew⟩
  by_contra houtK
  have houtBad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).2 ⟨houtE, houtK⟩
  have houtSeen : output t ∈ GenLimit.Generic.sample input t :=
    GenLimit.Generic.sample_mono htSeen (hTseen houtBad)
  apply hfresh
  simpa [GenLimit.sample, GenLimit.Generic.sample] using
    (GenLimit.Generic.sample_mono (Nat.le_succ t) houtSeen)

 theorem stage3_countable_half_density : CountableClause := by
  intro q family hinfinite
  obtain ⟨gen, hgen⟩ := countable_expansion_patient q family hinfinite
  refine ⟨gen, ?_⟩
  intro i input hinput
  obtain ⟨j, hj, hpresents, hnovel, hdensity⟩ := hgen i input hinput
  let E := (finiteExpansionOracleFamily
    (familyOracle family hinfinite)).language j
  have hE : E = Set.range input := hpresents.symm
  have hsub : family i ⊆ E := by
    rw [hE]
    exact hinput.2.1
  have hfinite : (E \ family i).Finite := by
    rw [hE]
    exact (setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) (family i) q).mp hinput.2.2 |>.1
  refine ⟨novelGenerates_of_finite_extension hpresents hfinite hnovel, ?_⟩
  exact hdensity.trans
    (relativeLowerDensity_finite_extension
      (hinfinite i) hsub hfinite)

end Stage3Case019

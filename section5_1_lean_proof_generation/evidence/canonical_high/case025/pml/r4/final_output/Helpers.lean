import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import Mathlib.Topology.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact {
    language := family
    infinite' := hInfinite
    query := fun i x => if x ∈ family i then true else false
    query_spec := by simp }

namespace Causal

open GenLimit
open GenLimit.PatientMachine

noncomputable def extendPrefix {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else xs ⟨t, Nat.lt_succ_self t⟩

@[simp] theorem extendPrefix_apply {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (n : ℕ) (hn : n < t + 1) :
    extendPrefix xs n = xs ⟨n, hn⟩ := by
  simp [extendPrefix, hn]

theorem sample_eq_of_prefix_eq {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  rw [GenLimit.mem_sample_iff, GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, hs, (h s hs).symm.trans hsx⟩
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, hs, (h s hs).trans hsx⟩

private theorem processRound_congr
    (O : GenLimit.OracleFamily) (a b : Stream) (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hab : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have ht : GenLimit.sample a t = GenLimit.sample b t :=
    sample_eq_of_prefix_eq (fun s hs => hab s (Nat.lt.step hs))
  have hts : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_eq_of_prefix_eq hab
  have hcon_t : GenLimit.Consistent O.language a t =
      GenLimit.Consistent O.language b t := by
    funext i
    apply propext
    simp only [GenLimit.Consistent, ht]
  have hcon_ts : GenLimit.Consistent O.language a (t + 1) =
      GenLimit.Consistent O.language b (t + 1) := by
    funext i
    apply propext
    simp only [GenLimit.Consistent, hts]
  have recursiveCritical_congr
      (u : ℕ)
      (hcon : GenLimit.Consistent O.language a u =
        GenLimit.Consistent O.language b u) :
      GenLimit.RecursiveCritical O.language a u =
        GenLimit.RecursiveCritical O.language b u := by
    funext i
    apply propext
    induction i using Nat.strong_induction_on with
    | h i ih =>
        cases i with
        | zero => simpa only [GenLimit.RecursiveCritical] using
            propext_iff.mp (congrArg (fun p => p 0) hcon)
        | succ n =>
            rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
            constructor
            · rintro ⟨hconsistent, hprior⟩
              refine ⟨(propext_iff.mp (congrArg (fun p => p (n + 1)) hcon)).mp hconsistent, ?_⟩
              intro j hj hjcritical
              exact hprior j hj ((ih j (by omega)).mpr hjcritical)
            · rintro ⟨hconsistent, hprior⟩
              refine ⟨(propext_iff.mp (congrArg (fun p => p (n + 1)) hcon)).mpr hconsistent, ?_⟩
              intro j hj hjcritical
              exact hprior j hj ((ih j (by omega)).mp hjcritical)
  have hcrit_t : GenLimit.RecursiveCritical O.language a t =
      GenLimit.RecursiveCritical O.language b t :=
    recursiveCritical_congr t hcon_t
  have hcrit_ts : GenLimit.RecursiveCritical O.language a (t + 1) =
      GenLimit.RecursiveCritical O.language b (t + 1) :=
    recursiveCritical_congr (t + 1) hcon_ts
  have hdecide :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    unfold GenLimit.PatientMachine.decide
      GenLimit.PatientMachine.stableDecision
      GenLimit.PatientMachine.backtrackDecision
      GenLimit.PatientMachine.consistentIndices
      GenLimit.PatientMachine.survivingCriticalIndices
      GenLimit.PatientMachine.highestSurvivor
      GenLimit.PatientMachine.lowestConsistentInScope
      GenLimit.PatientMachine.lowestConsistent
      GenLimit.PatientMachine.highestCritical
      GenLimit.PatientMachine.criticalIndices
    rw [hcon_ts, hcrit_t, hcrit_ts]
    unfold GenLimit.PatientMachine.survivingCriticalIndices
      GenLimit.PatientMachine.consistentIndices
    rw [hcon_ts, hcrit_t, hcrit_ts]
  have hleast (focus : ℕ) :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a
          (t + 1) old.used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b
          (t + 1) old.used focus := by
    apply Nat.le_antisymm
    · apply GenLimit.PatientMachine.leastAvailable_minimal
      simpa [GenLimit.PatientMachine.Available, hts] using
        (GenLimit.PatientMachine.leastAvailable_spec
          O.language O.infinite' b (t + 1) old.used focus)
    · apply GenLimit.PatientMachine.leastAvailable_minimal
      simpa [GenLimit.PatientMachine.Available, hts] using
        (GenLimit.PatientMachine.leastAvailable_spec
          O.language O.infinite' a (t + 1) old.used focus)
  unfold GenLimit.PatientMachine.processRound
  rw [hdecide]
  simp only [hleast]


private theorem run_congr_of_prefix_eq
    (O : GenLimit.OracleFamily) (a b : Stream) :
    ∀ t, (∀ s, s < t → a s = b s) →
      GenLimit.PatientMachine.run O a t =
        GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
      intro hab
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, ih (fun s hs => hab s (Nat.lt.step hs))]
      exact processRound_congr O a b t _ hab

theorem output_congr_of_prefix_eq
    (O : GenLimit.OracleFamily) (a b : Stream) (t : ℕ)
    (hab : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr_of_prefix_eq O a b (t + 1) hab]

noncomputable def onlineGenerator (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (extendPrefix input) t

theorem follows_onlineGenerator (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineGenerator O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_congr_of_prefix_eq
  intro s hs
  simp [extendPrefix, hs]

end Causal

end Stage3Case025


namespace Stage3Case025

open Filter
open scoped Topology

namespace DensityTransfer

open GenLimit
open GenLimit.PatientScope

private theorem prefixCount_le_add_of_diff_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold prefixCount
  calc
    (prefixFinset A n).card ≤
        (prefixFinset B n ∪ hfinite.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_union]
      by_cases hxB : x ∈ B
      · exact Or.inl (mem_prefixFinset.mpr ⟨(mem_prefixFinset.mp hx).1, hxB⟩)
      · exact Or.inr ((Set.Finite.mem_toFinset hfinite).mpr ⟨(mem_prefixFinset.mp hx).2, hxB⟩)
    _ ≤ (prefixFinset B n).card + hfinite.toFinset.card :=
      Finset.card_union_le _ _

private theorem prefixRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by
  positivity

private theorem prefixRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast prefixCount_mono hAK n

theorem half_relativeLowerDensity_of_finite_super
    {Q K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤ relativeLowerDensity (Q ∩ R) R) :
    (1 / 2 : ℝ) ≤ relativeLowerDensity (Q ∩ K) K := by
  let ratioR : ℕ → ℝ := fun n =>
    (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  have hnumFinite : ((Q ∩ R) \ (Q ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  let err : ℕ → ℝ := fun n =>
    (hnumFinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
  have hKcount : Tendsto (prefixCount K) atTop atTop :=
    tendsto_prefixCount_atTop hK
  have herr : Tendsto err atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun m : ℕ => (hnumFinite.toFinset.card : ℝ) / (m : ℝ))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h := hbase.comp hKcount
    simpa only [err, Function.comp_apply] using h
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioR n ≤ ratioK n + err n := by
    have hpositive : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
      hKcount.eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hden : prefixCount K n ≤ prefixCount R n := prefixCount_mono hKR n
    have hnum := prefixCount_le_add_of_diff_finite hnumFinite n
    dsimp only [ratioR, ratioK, err]
    calc
      (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ) ≤
          (prefixCount (Q ∩ R) n : ℝ) / (prefixCount K n : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hnR
        · exact_mod_cast hden
      _ ≤ ((prefixCount (Q ∩ K) n + hnumFinite.toFinset.card : ℕ) : ℝ) /
          (prefixCount K n : ℝ) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hnum
        · exact hnR.le
      _ = (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ) +
          (hnumFinite.toFinset.card : ℝ) / (prefixCount K n : ℝ) := by
        push_cast
        rw [add_div]
  have hRlower : IsBoundedUnder (· ≥ ·) atTop ratioR := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, ratioR n ≥ b
    exact ⟨0, Filter.Eventually.of_forall (fun n => prefixRatio_nonneg _ _ n)⟩
  have hKlower : IsBoundedUnder (· ≥ ·) atTop ratioK := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, ratioK n ≥ b
    exact ⟨0, Filter.Eventually.of_forall (fun n => prefixRatio_nonneg _ _ n)⟩
  have hKupper : IsCoboundedUnder (· ≥ ·) atTop ratioK :=
    isCoboundedUnder_ge_of_le atTop
      (fun n => prefixRatio_le_one Set.inter_subset_right n)
  unfold relativeLowerDensity at hhalf ⊢
  change (1 / 2 : ℝ) ≤ liminf ratioR atTop at hhalf
  change (1 / 2 : ℝ) ≤ liminf ratioK atTop
  rw [le_liminf_iff hKupper hKlower]
  intro y hy
  let δ : ℝ := ((1 / 2 : ℝ) - y) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hthreshold : y + δ < liminf ratioR atTop := by
    calc
      y + δ < (1 / 2 : ℝ) := by dsimp [δ]; linarith
      _ ≤ liminf ratioR atTop := hhalf
  have hRlarge : ∀ᶠ n : ℕ in atTop, y + δ < ratioR n :=
    eventually_lt_of_lt_liminf hthreshold hRlower
  have herrSmall : ∀ᶠ n : ℕ in atTop, err n < δ :=
    herr.eventually_lt_const hδ
  filter_upwards [hRlarge, herrSmall, hcompare] with n hyn hen hcomp
  linarith

end DensityTransfer
end Stage3Case025

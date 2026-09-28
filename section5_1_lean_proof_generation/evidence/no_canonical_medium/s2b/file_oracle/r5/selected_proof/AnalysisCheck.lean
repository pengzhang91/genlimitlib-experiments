import GenLimit.Paper39_DenseGeneration.Abstract.Density
open Filter
open scoped Topology

example : Tendsto (fun n : ℕ => Real.logb 2 (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (𝓝 0) := by
  have hk0 : Tendsto (fun n : ℕ => 12 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
  have hk : Tendsto (fun n : ℕ => 12 * (n : ℝ) + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9 hk0
  have hlo := (Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).comp_tendsto hk
  have hz := hlo.tendsto_div_nhds_zero
  have h9 : Tendsto (fun n : ℕ => (9 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hratio' : Tendsto (fun n : ℕ => (12 : ℝ) + 9 / (n : ℝ)) atTop (𝓝 12) := by
    simpa using tendsto_const_nhds.add h9
  have hratio : Tendsto (fun n : ℕ => (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (𝓝 12) := by
    apply hratio'.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  have hmul := hz.mul hratio
  simp only [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  dsimp only [Function.comp_apply, id_eq]
  field_simp

example : Tendsto
    (fun n : ℕ => ((Nat.log2 (12 * n + 9) + 1 : ℕ) : ℝ) / (n : ℝ))
    atTop (𝓝 0) := by
  have hlogb : Tendsto (fun n : ℕ => Real.logb 2 (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (𝓝 0) := by
    have hk0 : Tendsto (fun n : ℕ => 12 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
    have hk : Tendsto (fun n : ℕ => 12 * (n : ℝ) + 9) atTop atTop :=
      tendsto_atTop_add_const_right atTop 9 hk0
    have hz := ((Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).comp_tendsto hk).tendsto_div_nhds_zero
    have h9 : Tendsto (fun n : ℕ => (9 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hratio' : Tendsto (fun n : ℕ => (12 : ℝ) + 9 / (n : ℝ)) atTop (𝓝 12) := by
      simpa using tendsto_const_nhds.add h9
    have hratio : Tendsto (fun n : ℕ => (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (𝓝 12) := by
      apply hratio'.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    have hmul := hz.mul hratio
    simp only [zero_mul] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    dsimp only [Function.comp_apply, id_eq]
    field_simp
  have hnat : Tendsto
      (fun n : ℕ => (Nat.log2 (12 * n + 9) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    exact squeeze_zero
      (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (fun n => by
        apply div_le_div_of_nonneg_right
        · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
            (Real.log2_le_logb (12 * n + 9))
        · exact Nat.cast_nonneg _)
      hlogb
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, Nat.cast_one, add_div, zero_add] using hnat.add hone

import Case019Formalization
open Filter
#check Finset.card_le_card_of_injOn
#check Finset.card_image_iff
#check Finset.card_image_of_injective
#check Set.Finite.image
#check Set.finite_Iio
#check tendsto_natCast_atTop_iff
#check tendsto_inv_atTop_zero
#check tendsto_one_div_add_atTop_nhds_zero_nat
#check tendsto_const_nhds.div_atTop
#check Filter.EventuallyLE.liminf_le_liminf

example (f : ℕ → ℝ) :
    liminf (fun n => f (n / 2)) atTop = liminf f atTop := by
  rw [show (fun n => f (n / 2)) = f ∘ (fun n => n / 2) by rfl]
  rw [liminf_comp, Filter.map_div_atTop_eq_nat 2 (by omega)]

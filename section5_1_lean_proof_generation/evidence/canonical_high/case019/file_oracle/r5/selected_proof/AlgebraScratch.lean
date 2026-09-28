import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

example (d k u c : ℝ) (hk : 0 < k) (hu : 0 < u)
    (hdk : d ≤ k) (hku : k ≤ u) (hukc : u ≤ k + c) (hd0 : 0 ≤ d) (hc0 : 0 ≤ c) :
    d / k ≤ d / u + c / k := by
  rw [div_le_iff₀ hk]
  field_simp [hu.ne']
  nlinarith

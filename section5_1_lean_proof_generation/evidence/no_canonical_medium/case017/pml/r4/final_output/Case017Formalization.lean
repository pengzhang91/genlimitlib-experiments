import Stage3Model
import «output».Helpers

open Case017Helpers

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨onlineRule family, ?_⟩
  intro input hinjective hpresentation hcore
  obtain ⟨T, hstable⟩ := eventual_currentCore family input
  refine ⟨trajectory family input, follows_trajectory family input, ?_⟩
  intro j hcompat
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    have hn := trajectory_novel family input hcore hstable ht
    refine ⟨hn.1 j hcompat, ?_, hn.2.2⟩
    intro hsample
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hn.2.1 s (Nat.le_of_lt_succ hs) heq
  · apply max_le
    · exact half_core_density family hinfinite input hcore hstable j hcompat
    · exact missing_core_density family input hcore hstable j hcompat

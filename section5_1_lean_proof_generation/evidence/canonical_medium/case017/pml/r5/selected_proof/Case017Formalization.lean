import Helpers

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  exact ⟨Case017.generator family, Case017.succeeds family hinfinite⟩

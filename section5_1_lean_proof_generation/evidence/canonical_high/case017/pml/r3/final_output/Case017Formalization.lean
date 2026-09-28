import Helpers

open Stage3Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  exact ⟨Case017Proof.onlineGenerator family,
    Case017Proof.succeeds family hfamily⟩

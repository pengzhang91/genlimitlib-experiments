import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Case025

abbrev Language := Set ℕ

structure Node where
  focus : Language
  serial : ℕ

structure Machine where
  stack : List Node
  nextSerial : ℕ
  age : ℕ
  seen : Finset ℕ

def root : Node := { focus := Set.univ, serial := 0 }

def initial : Machine where
  stack := [root]
  nextSerial := 1
  age := 0
  seen := ∅

def topFocus (m : Machine) : Language :=
  match m.stack with
  | [] => Set.univ
  | node :: _ => node.focus

noncomputable def prune (x : ℕ) (stack : List Node) : List Node := by
  classical
  let kept := stack.dropWhile (fun node => x ∉ node.focus)
  exact if kept = [] then [root] else kept
noncomputable def chooseFocus (seen : Finset ℕ) (candidate parent : Language) : Language := by
  classical
  exact if (↑seen : Set ℕ) ⊆ candidate ∧ candidate ⊆ parent then candidate else parent

noncomputable def advance (family : ℕ → Language) (m : Machine) (x : ℕ) : Machine := by
  classical
  let seen := insert x m.seen
  let stack := prune x m.stack
  if hdelete : stack.length < m.stack.length then
    exact { stack := stack, nextSerial := m.nextSerial, age := 1, seen := seen }
  else if hpush : 2 ^ m.nextSerial ≤ m.age then
    let parent := match stack with
      | [] => Set.univ
      | node :: _ => node.focus
    let index := stack.length - 1
    let candidate := family index
    let focus := chooseFocus seen candidate parent
    exact {
      stack := { focus := focus, serial := m.nextSerial } :: stack
      nextSerial := m.nextSerial + 1
      age := 1
      seen := seen
    }
  else
    exact { stack := stack, nextSerial := m.nextSerial, age := m.age + 1, seen := seen }

noncomputable def runFrom (family : ℕ → Language) (m : Machine) (xs : List ℕ) : Machine :=
  xs.foldl (advance family) m

noncomputable def run (family : ℕ → Language) (xs : List ℕ) : Machine :=
  runFrom family initial xs

noncomputable def leastFresh (focus : Language) (forbidden : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ x, x ∈ focus ∧ x ∉ forbidden then Nat.find h else 0

noncomputable def generator (family : ℕ → Language) : Stage3Case025.OnlineGenerator :=
  fun _ inputs outputs =>
    let m := run family (List.ofFn inputs)
    leastFresh (topFocus m) (m.seen ∪ Finset.univ.image outputs)

noncomputable def trajectory
    (gen : Stage3Case025.OnlineGenerator) (input : Stage3Case025.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

 theorem trajectory_follows (gen : Stage3Case025.OnlineGenerator)
    (input : Stage3Case025.Stream) :
    Stage3Case025.Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem leastFresh_spec {focus : Language} (hfocus : focus.Infinite) (forbidden : Finset ℕ) :
    leastFresh focus forbidden ∈ focus ∧ leastFresh focus forbidden ∉ forbidden := by
  classical
  rw [leastFresh]
  simp only [dif_pos (hfocus.exists_not_mem_finset forbidden)]
  exact Nat.find_spec (hfocus.exists_not_mem_finset forbidden)


def AllInfinite (m : Machine) : Prop :=
  ∀ node ∈ m.stack, node.focus.Infinite

theorem initial_allInfinite : AllInfinite initial := by
  intro node hnode
  simp [initial, root] at hnode
  subst node
  exact Set.infinite_univ

theorem prune_allInfinite (x : ℕ) {stack : List Node}
    (hstack : ∀ node ∈ stack, node.focus.Infinite) :
    ∀ node ∈ prune x stack, node.focus.Infinite := by
  classical
  intro node hnode
  unfold prune at hnode
  dsimp only at hnode
  split at hnode
  · simp [root] at hnode
    subst node
    exact Set.infinite_univ
  · exact hstack node (List.Sublist.mem hnode (List.dropWhile_sublist _))

theorem chooseFocus_infinite {seen : Finset ℕ} {candidate parent : Language}
    (hcandidate : candidate.Infinite) (hparent : parent.Infinite) :
    (chooseFocus seen candidate parent).Infinite := by
  classical
  unfold chooseFocus
  split
  · exact hcandidate
  · exact hparent

theorem advance_allInfinite (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) {m : Machine} (hm : AllInfinite m) (x : ℕ) :
    AllInfinite (advance family m x) := by
  classical
  have hprune : ∀ node ∈ prune x m.stack, node.focus.Infinite :=
    prune_allInfinite x hm
  have hparent : (match prune x m.stack with
      | [] => Set.univ
      | node :: _ => node.focus).Infinite := by
    cases hstack : prune x m.stack with
    | nil => exact Set.infinite_univ
    | cons head tail => exact hprune head (by simp [hstack])
  unfold advance
  dsimp only
  split
  · exact hprune
  · split
    · intro node hnode
      simp only [List.mem_cons] at hnode
      rcases hnode with rfl | hnode
      · exact chooseFocus_infinite (hfamily _) hparent
      · exact hprune node hnode
    · exact hprune

theorem runFrom_allInfinite (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) {m : Machine} (hm : AllInfinite m) (xs : List ℕ) :
    AllInfinite (runFrom family m xs) := by
  induction xs generalizing m with
  | nil => simpa [runFrom] using hm
  | cons x xs ih =>
      simp only [runFrom, List.foldl_cons]
      exact ih (advance_allInfinite family hfamily hm x)

theorem run_allInfinite (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) (xs : List ℕ) :
    AllInfinite (run family xs) := by
  exact runFrom_allInfinite family hfamily initial_allInfinite xs

theorem topFocus_infinite_of_allInfinite {m : Machine} (hm : AllInfinite m)
    (hne : m.stack ≠ []) : (topFocus m).Infinite := by
  cases hstack : m.stack with
  | nil => contradiction
  | cons node rest =>
      simpa [topFocus, hstack] using hm node (by simp [hstack])


theorem prune_ne_nil (x : ℕ) (stack : List Node) : prune x stack ≠ [] := by
  classical
  unfold prune
  dsimp only
  split <;> simp_all

theorem advance_stack_ne_nil (family : ℕ → Language) (m : Machine) (x : ℕ) :
    (advance family m x).stack ≠ [] := by
  classical
  unfold advance
  dsimp only
  split
  · exact prune_ne_nil x m.stack
  · split
    · simp
    · exact prune_ne_nil x m.stack

theorem runFrom_stack_ne_nil (family : ℕ → Language) {m : Machine} (hm : m.stack ≠ [])
    (xs : List ℕ) : (runFrom family m xs).stack ≠ [] := by
  induction xs generalizing m with
  | nil => simpa [runFrom] using hm
  | cons x xs ih =>
      simp only [runFrom, List.foldl_cons]
      exact ih (advance_stack_ne_nil family m x)

theorem run_stack_ne_nil (family : ℕ → Language) (xs : List ℕ) :
    (run family xs).stack ≠ [] := by
  exact runFrom_stack_ne_nil family (by simp [initial]) xs

theorem advance_seen (family : ℕ → Language) (m : Machine) (x : ℕ) :
    (advance family m x).seen = insert x m.seen := by
  classical
  unfold advance
  dsimp only
  split <;> (try split) <;> rfl

theorem runFrom_seen (family : ℕ → Language) (m : Machine) (xs : List ℕ) :
    (runFrom family m xs).seen = m.seen ∪ xs.toFinset := by
  induction xs generalizing m with
  | nil => simp [runFrom]
  | cons x xs ih =>
      simp only [runFrom, List.foldl_cons]
      change (runFrom family (advance family m x) xs).seen = _
      rw [ih, advance_seen]
      ext z
      simp [or_assoc, or_left_comm]

theorem run_seen (family : ℕ → Language) (xs : List ℕ) :
    (run family xs).seen = xs.toFinset := by
  rw [run, runFrom_seen]
  simp [initial]

theorem generator_spec (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (t : ℕ) (inputs : Fin (t + 1) → ℕ) (outputs : Fin t → ℕ) :
    let y := generator family t inputs outputs
    let m := run family (List.ofFn inputs)
    y ∈ topFocus m ∧ (∀ i, y ≠ inputs i) ∧ ∀ i, y ≠ outputs i := by
  classical
  dsimp only
  let m := run family (List.ofFn inputs)
  have htop : (topFocus m).Infinite :=
    topFocus_infinite_of_allInfinite (run_allInfinite family hfamily _) (run_stack_ne_nil family _)
  have hspec := leastFresh_spec htop (m.seen ∪ Finset.univ.image outputs)
  change leastFresh (topFocus m) (m.seen ∪ Finset.univ.image outputs) ∈ topFocus m ∧ _
  refine ⟨hspec.1, ?_, ?_⟩
  · intro i heq
    change leastFresh (topFocus m) (m.seen ∪ Finset.univ.image outputs) = inputs i at heq
    have hinSeen : inputs i ∈ m.seen := by
      rw [run_seen]
      simp only [List.mem_toFinset, List.mem_ofFn]
      exact ⟨i, rfl⟩
    apply hspec.2
    simp only [Finset.mem_union]
    exact Or.inl (by rw [heq]; exact hinSeen)
  · intro i heq
    change leastFresh (topFocus m) (m.seen ∪ Finset.univ.image outputs) = outputs i at heq
    apply hspec.2
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨i, heq.symm⟩

theorem trajectory_globally_fresh (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) (input : Stage3Case025.Stream) (t : ℕ) :
    trajectory (generator family) input t ∉ GenLimit.sample input (t + 1) ∧
      ∀ s, s < t → trajectory (generator family) input s ≠ trajectory (generator family) input t := by
  have hspec := generator_spec family hfamily t (fun i => input i)
    (fun i => trajectory (generator family) input i)
  have hout : trajectory (generator family) input t =
      generator family t (fun i => input i) (fun i => trajectory (generator family) input i) := by
    rw [trajectory]
  constructor
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    apply hspec.2.1 ⟨s, hs⟩
    exact hout.symm.trans heq.symm
  · intro s hs heq
    apply hspec.2.2 ⟨s, hs⟩
    exact hout.symm.trans heq.symm


theorem trajectory_mem_topFocus (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) (input : Stage3Case025.Stream) (t : ℕ) :
    trajectory (generator family) input t ∈
      topFocus (run family (List.ofFn (fun i : Fin (t + 1) => input i))) := by
  have hspec := generator_spec family hfamily t (fun i => input i)
    (fun i => trajectory (generator family) input i)
  rw [trajectory]
  exact hspec.1

theorem trajectory_novel_of_eventual_focus
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stage3Case025.Stream) (target : Language)
    (hfocus : ∃ T, ∀ t, T ≤ t →
      topFocus (run family (List.ofFn (fun i : Fin (t + 1) => input i))) ⊆ target) :
    GenLimit.NovelGeneratesInLimit input (trajectory (generator family) input) target := by
  obtain ⟨T, hT⟩ := hfocus
  refine ⟨T, fun t ht => ?_⟩
  have hfresh := trajectory_globally_fresh family hfamily input t
  exact ⟨hT t ht (trajectory_mem_topFocus family hfamily input t), hfresh.1, hfresh.2⟩

theorem generatorFirst_of_trajectory (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) (input : Stage3Case025.Stream) (t : ℕ) :
    trajectory (generator family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  refine ⟨t, rfl, fun s hs => ?_⟩
  have hfresh := (trajectory_globally_fresh family hfamily input t).1
  intro heq
  apply hfresh
  simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range]
  exact ⟨s, Nat.lt_succ_iff.mpr hs, heq⟩

theorem uniform_global_fresh_generator :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : Stage3Case025.OnlineGenerator,
        ∀ input : Stage3Case025.Stream,
          ∃ output : Stage3Case025.Stream,
            Stage3Case025.Follows gen input output ∧
            ∀ t, output t ∉ GenLimit.sample input (t + 1) ∧
              ∀ s, s < t → output s ≠ output t := by
  intro family hfamily
  refine ⟨generator family, fun input => ⟨trajectory (generator family) input, ?_, ?_⟩⟩
  · exact trajectory_follows _ _
  · exact trajectory_globally_fresh family hfamily input

end Case025

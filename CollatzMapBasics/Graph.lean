import Mathlib
import CollatzMapBasics.Compact

namespace CollatzMapBasics

open Classical

/-- The Collatz graph of `T`: a directed graph on `ℕ` with an edge from `n` to `T n`. -/
def collatz_graph : Digraph ℕ where
  Adj n m := m = T n

private lemma T_one : T 1 = 2 := by rw [T_odd (by omega)]

private lemma T_two : T 2 = 1 := by rw [T_even (by omega)]

private lemma T_iter_one_cycle (j : ℕ) : T_iter j 1 = 1 ∨ T_iter j 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rcases ih with h | h <;> simp only [T_iter, h]
    · right; exact T_one
    · left; exact T_two

private lemma collatz_graph_adj_iff (a b : ℕ) :
    collatz_graph.toSimpleGraphInclusive.Adj a b ↔ a ≠ b ∧ (b = T a ∨ a = T b) := by
  simp [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj, collatz_graph]

private lemma T_iter_reachable (k n : ℕ) :
    collatz_graph.toSimpleGraphInclusive.Reachable n (T_iter k n) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    apply ih.trans
    by_cases heq : T_iter k n = T (T_iter k n)
    · rw [T_iter, ← heq]
    · exact SimpleGraph.Adj.reachable ((collatz_graph_adj_iff _ _).mpr ⟨heq, Or.inl rfl⟩)

private lemma confluence_step (i j : ℕ) (a b c : ℕ)
    (hij : T_iter i a = T_iter j b)
    (hadj : collatz_graph.toSimpleGraphInclusive.Adj b c) :
    ∃ i' j', T_iter i' a = T_iter j' c := by
  rw [collatz_graph_adj_iff] at hadj
  rcases hadj.2 with hbc | hcb
  · -- c = T b: forward edge b → c
    refine ⟨i + 1, j, ?_⟩
    calc T_iter (i + 1) a = T (T_iter i a) := rfl
      _ = T (T_iter j b) := by rw [hij]
      _ = T_iter (j + 1) b := rfl
      _ = T_iter j (T_iter 1 b) := by rw [T_iter_add]
      _ = T_iter j (T b) := rfl
      _ = T_iter j c := by rw [hbc]
  · -- b = T c: backward edge c → b
    refine ⟨i, j + 1, ?_⟩
    calc T_iter i a = T_iter j b := hij
      _ = T_iter j (T c) := by rw [hcb]
      _ = T_iter j (T_iter 1 c) := rfl
      _ = T_iter (j + 1) c := by rw [← T_iter_add]

private lemma confluence_of_reachable (a b : ℕ) :
    collatz_graph.toSimpleGraphInclusive.Reachable a b →
    ∃ i j, T_iter i a = T_iter j b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  intro h
  induction h with
  | refl => exact ⟨0, 0, rfl⟩
  | tail _ hab ih =>
    obtain ⟨i, j, hij⟩ := ih
    exact confluence_step i j _ _ _ hij hab

/-- The Collatz graph restricted to the positive integers is weakly connected
    iff the Collatz conjecture holds. -/
lemma collatz_graph_weakly_connected_iff_collatz :
    (∀ a b : ℕ, a ≥ 1 → b ≥ 1 → collatz_graph.toSimpleGraphInclusive.Reachable a b) ↔
    (∀ n : ℕ, n = 0 ∨ ∃ k, collatz_iter k n = 1) := by
  constructor
  · -- (⇒) Weakly connected → Collatz
    intro hconn n
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      obtain ⟨i, j, hij⟩ := confluence_of_reachable n 1 (hconn n 1 (by omega) le_rfl)
      rcases T_iter_one_cycle j with hj | hj
      · -- T_iter j 1 = 1
        rw [hj] at hij
        obtain ⟨m, hm⟩ := T_iter_to_collatz_iter i n
        exact ⟨m, by rw [hm, hij]⟩
      · -- T_iter j 1 = 2, so T_iter i n = 2, then T_iter (i+1) n = T 2 = 1
        have : T_iter (i + 1) n = 1 := by
          show T (T_iter i n) = 1
          rw [hij, hj, T_two]
        obtain ⟨m, hm⟩ := T_iter_to_collatz_iter (i + 1) n
        exact ⟨m, by rw [hm, this]⟩
  · -- (⇐) Collatz → Weakly connected
    intro hcoll a b ha hb
    have reach_one : ∀ n, n ≥ 1 → collatz_graph.toSimpleGraphInclusive.Reachable n 1 := by
      intro n hn
      rcases hcoll n with rfl | ⟨j, hj⟩
      · omega
      obtain ⟨k, hk⟩ := collatz_iter_to_T_iter j n hn hj
      have := T_iter_reachable k n
      rwa [hk] at this
    exact (reach_one a ha).trans (reach_one b hb).symm

end CollatzMapBasics

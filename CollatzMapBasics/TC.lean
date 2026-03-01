import Mathlib
import CollatzMapBasics.Basic
import CollatzMapBasics.Terras

namespace CollatzMapBasics

open Classical


/-- One T step equals one or two collatz_steps. -/
lemma T_step_collatz (n : ℕ) :
    ∃ j, j ≥ 1 ∧ collatz_iter j n = T n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : (k + k) % 2 = 0 := by omega
    exact ⟨1, le_refl _, by simp [collatz_iter, collatz_step, h1, T_even h1]⟩
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (3 * (2 * k + 1) + 1) % 2 = 0 := by omega
    exact ⟨2, by omega, by simp [collatz_iter, collatz_step, h1, h2, T_odd h1]⟩

/-- For any k, T_iter k n can be simulated by some number of collatz_iter steps. -/
lemma T_iter_to_collatz_iter (k n : ℕ) :
    ∃ j, collatz_iter j n = T_iter k n := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨j₀, hj₀⟩ := ih
    obtain ⟨j₁, _, hj₁⟩ := T_step_collatz (T_iter k n)
    exact ⟨j₁ + j₀, by rw [collatz_iter_add, hj₀, hj₁]; rfl⟩

private lemma collatz_step_even' {n : ℕ} (h : n % 2 = 0) : collatz_step n = n / 2 := by
  simp [collatz_step, h]

private lemma collatz_step_odd' {n : ℕ} (h : n % 2 = 1) : collatz_step n = 3 * n + 1 := by
  simp [collatz_step]; omega

/-- If collatz_iter reaches 1, then T_iter also reaches 1. -/
lemma collatz_iter_to_T_iter (j n : ℕ) (hn : n ≥ 1) (hj : collatz_iter j n = 1) :
    ∃ k, T_iter k n = 1 := by
  induction j generalizing n with | zero => exact ⟨0, hj⟩ | succ j ih =>
  rw [collatz_iter] at hj
  by_cases h : n % 2 = 0
  · obtain ⟨k, hk⟩ := ih (n / 2) (by omega) (by rwa [collatz_step_even' h] at hj)
    exact ⟨k + 1, by rw [T_iter_add k 1]; dsimp [T_iter]; rw [T_even h, hk]⟩
  · have h1 : n % 2 = 1 := by omega
    obtain ⟨k, hk⟩ := ih (3 * n + 1) (by omega) (by rwa [collatz_step_odd' h1] at hj)
    have hk_pos : k ≥ 1 := by by_contra! r; interval_cases k; simp_all [T_iter]
    exact ⟨k, by
      have hk_eq : k = (k - 1) + 1 := by omega
      rw [hk_eq, T_iter_add (k - 1) 1] at hk ⊢
      dsimp [T_iter] at hk ⊢
      rw [T_even (by omega)] at hk
      rwa [T_odd h1]
    ⟩

/-- The Collatz graph of `T`: a directed graph on `ℕ` with an edge from `n` to `T n`. -/
def collatz_graph : Digraph ℕ where
  Adj n m := m = T n

lemma collatz_graph_adj_iff (a b : ℕ) :
    collatz_graph.toSimpleGraphInclusive.Adj a b ↔ a ≠ b ∧ (b = T a ∨ a = T b) := by
  simp [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj, collatz_graph]

lemma T_iter_reachable (k n : ℕ) :
    collatz_graph.toSimpleGraphInclusive.Reachable n (T_iter k n) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    apply ih.trans
    by_cases heq : T_iter k n = T (T_iter k n)
    · rw [T_iter, ← heq]
    · exact SimpleGraph.Adj.reachable ((collatz_graph_adj_iff _ _).mpr ⟨heq, Or.inl rfl⟩)

lemma confluence_step (i j : ℕ) (a b c : ℕ)
    (hij : T_iter i a = T_iter j b)
    (hadj : collatz_graph.toSimpleGraphInclusive.Adj b c) :
    ∃ i' j', T_iter i' a = T_iter j' c := by
  rw [collatz_graph_adj_iff] at hadj
  rcases hadj.2 with rfl | rfl
  · exact ⟨i + 1, j, by calc T_iter (i + 1) a = T (T_iter i a) := rfl
      _ = T (T_iter j b) := by rw [hij]
      _ = T_iter (j + 1) b := rfl
      _ = T_iter j (T_iter 1 b) := by rw [T_iter_add]
      _ = T_iter j (T b) := rfl⟩
  · exact ⟨i, j + 1, by calc T_iter i a = T_iter j (T c) := hij
      _ = T_iter j (T_iter 1 c) := rfl
      _ = T_iter (j + 1) c := by rw [← T_iter_add]⟩

lemma confluence_of_reachable (a b : ℕ) :
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
  · intro hconn n
    rcases eq_or_ne n 0 with rfl | hn
    · exact Or.inl rfl
    · right
      obtain ⟨i, j, hij⟩ := confluence_of_reachable n 1 (hconn n 1 (by omega) le_rfl)
      rcases T_iter_one_cycle j with hj | hj
      · obtain ⟨m, hm⟩ := T_iter_to_collatz_iter i n
        exact ⟨m, by simp [hm, hij, hj]⟩
      · obtain ⟨m, hm⟩ := T_iter_to_collatz_iter (i + 1) n
        exact ⟨m, by rw [hm]; exact calc T_iter (i + 1) n = T (T_iter i n) := rfl
                                       _ = T (T_iter j 1) := by rw [hij]
                                       _ = T 2 := by rw [hj]
                                       _ = 1 := rfl⟩
  · intro hcoll a b ha hb
    have reach_one : ∀ n ≥ 1, collatz_graph.toSimpleGraphInclusive.Reachable n 1 := by
      intro n hn
      obtain rfl | ⟨j, hj⟩ := hcoll n
      · omega
      obtain ⟨k, hk⟩ := collatz_iter_to_T_iter j n hn hj
      exact hk ▸ T_iter_reachable k n
    exact (reach_one a ha).trans (reach_one b hb).symm


end CollatzMapBasics

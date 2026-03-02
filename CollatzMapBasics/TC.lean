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

lemma T_iter_implies_collatz_iter (k n : ℕ) :
    ∃ j ≥ k, collatz_iter j n = T_iter k n := by
  induction k generalizing n with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨j1, h1, eq1⟩ := T_step_collatz n
    obtain ⟨j2, h2, eq2⟩ := ih (T n)
    exact ⟨j1 + j2, by omega, by
      rw [T_iter_succ_right, ← eq2, ← eq1, ← collatz_iter_add, Nat.add_comm j2 j1]
    ⟩


def count_T_steps : ℕ → ℕ → ℕ
| 0, _ => 0
| d + 1, n => count_T_steps d n + if collatz_iter d n % 2 = 1 then 0 else 1

private lemma T_iter_count_T_steps (d n : ℕ) :
    (collatz_iter d n % 2 = 1 → T_iter (count_T_steps d n) n = collatz_iter d n) ∧
    (collatz_iter d n % 2 = 0 → T_iter (count_T_steps d n + 1) n = collatz_iter d n / 2) := by
  induction d with
  | zero =>
    simp [count_T_steps, collatz_iter, T_iter]
    intro h_even; rw [T_even h_even]
  | succ d ih =>
    rcases ih with ⟨ih_odd, ih_even⟩
    rw [collatz_iter_succ_right']
    constructor
    · intro h_odd
      have hd_even : collatz_iter d n % 2 = 0 := by
        by_contra! h
        have h1 : collatz_iter d n % 2 = 1 := by omega
        have h2 : collatz_step (collatz_iter d n) = 3 * collatz_iter d n + 1 := collatz_step_odd _ h1
        omega
      unfold count_T_steps
      rw [if_neg (by omega)]
      rw [collatz_step_even _ hd_even]
      exact ih_even hd_even
    · intro h_even
      by_cases hd_odd : collatz_iter d n % 2 = 1
      · unfold count_T_steps
        rw [if_pos hd_odd]
        have h_eq := ih_odd hd_odd
        have h_add : count_T_steps d n + 0 + 1 = count_T_steps d n + 1 := by omega
        rw [h_add]
        change T (T_iter (count_T_steps d n) n) = collatz_step (collatz_iter d n) / 2
        rw [h_eq, T_odd hd_odd]
        have h_step : collatz_step (collatz_iter d n) = 3 * collatz_iter d n + 1 := collatz_step_odd _ hd_odd
        rw [h_step]
      · have hd_even : collatz_iter d n % 2 = 0 := by omega
        unfold count_T_steps
        rw [if_neg hd_odd]
        have h_eq := ih_even hd_even
        have h_add : count_T_steps d n + 1 + 1 = count_T_steps d n + 1 + 1 := rfl
        rw [h_add]
        change T (T_iter (count_T_steps d n + 1) n) = collatz_step (collatz_iter d n) / 2
        rw [h_eq]
        have hs : collatz_step (collatz_iter d n) % 2 = 0 := h_even
        rw [← collatz_step_even _ hd_even]
        rw [T_even hs]

private lemma count_T_steps_ge_one (d n : ℕ) (h_odd : n % 2 = 1) : count_T_steps (d + 2) n ≥ 1 := by
  induction d with
  | zero =>
    unfold count_T_steps
    have h1 : collatz_iter 1 n = 3 * n + 1 := collatz_step_odd n h_odd
    have h_even : collatz_iter 1 n % 2 = 0 := by omega
    simp [h_even, count_T_steps]
  | succ d ih =>
    unfold count_T_steps
    by_cases h : collatz_iter (d + 2) n % 2 = 1
    · simp [h]; exact ih
    · simp [h]

lemma collatz_cycle_iff_compact_collatz_cycle (n : ℕ) (h_odd : n % 2 = 1) :
    (∃ k > 0, collatz_iter k n = n) ↔ (∃ k > 0, T_iter k n = n) := by
  constructor
  · rintro ⟨j, hj, hcycle⟩
    rcases j with _ | _ | j
    · omega
    · have h_even : collatz_iter 1 n % 2 = 0 := by
        have h1 : collatz_iter 1 n = 3 * n + 1 := collatz_step_odd n h_odd
        omega
      have : collatz_iter 1 n = n := hcycle
      omega
    · use count_T_steps (j + 2) n
      constructor
      · exact count_T_steps_ge_one j n h_odd
      · have h_eq := (T_iter_count_T_steps (j + 2) n).1
        rw [hcycle] at h_eq
        exact h_eq h_odd
  · rintro ⟨k, hk, hcycle⟩
    obtain ⟨j, hj_ge, hiter⟩ := T_iter_implies_collatz_iter k n
    have hj_pos : j > 0 := by omega
    exact ⟨j, hj_pos, by rwa [hiter]⟩

lemma collatz_bounded_iff_compact_collatz_bounded (n : ℕ) :
    (∃ B, ∀ k, collatz_iter k n ≤ B) ↔ (∃ B, ∀ k, T_iter k n ≤ B) := by
  constructor
  · exact fun ⟨B, hB⟩ ↦ ⟨B, fun k ↦ by
      obtain ⟨j, _, h_eq⟩ := T_iter_implies_collatz_iter k n
      exact h_eq ▸ hB j⟩
  · rintro ⟨B, hB⟩
    use 2 * B + 1
    intro d
    by_cases h_mod : collatz_iter d n % 2 = 1
    · have h_eq := (T_iter_count_T_steps d n).1 h_mod
      have hT := hB (count_T_steps d n)
      omega
    · have h_even : collatz_iter d n % 2 = 0 := by omega
      have h_eq := (T_iter_count_T_steps d n).2 h_even
      have hT := hB (count_T_steps d n + 1)
      omega

/- Graph lemmas below -/

/-- If collatz_iter reaches 1, then T_iter also reaches 1. -/
lemma collatz_iter_to_T_iter (j n : ℕ) (hn : n ≥ 1) (hj : collatz_iter j n = 1) :
    ∃ k, T_iter k n = 1 := by
  induction j generalizing n with | zero => exact ⟨0, hj⟩ | succ j ih =>
  rw [collatz_iter] at hj
  by_cases h : n % 2 = 0
  · obtain ⟨k, hk⟩ := ih (n / 2) (by omega) (by rwa [collatz_step_even n h] at hj)
    exact ⟨k + 1, by rw [T_iter_add k 1]; dsimp [T_iter]; rw [T_even h, hk]⟩
  · have h1 : n % 2 = 1 := by omega
    obtain ⟨k, hk⟩ := ih (3 * n + 1) (by omega) (by rwa [collatz_step_odd n h1] at hj)
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
      · obtain ⟨m, _, hm⟩ := T_iter_implies_collatz_iter i n
        exact ⟨m, by simp [hm, hij, hj]⟩
      · obtain ⟨m, _, hm⟩ := T_iter_implies_collatz_iter (i + 1) n
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

import Mathlib
import CollatzMapBasics.Compact

namespace CollatzMapBasics

/-- The number of odd iterates among the first `k` steps starting from `n`. -/
def num_odd_steps (k n : ℕ) : ℕ :=
  (Finset.range k).sum (fun i => X (T_iter i n))

/-- The Garner correction term: `Q(0) = 0`, `Q(k+1) = 3^{x_k} · Q(k) + 2^k · x_k`,
    where `x_k = X(T^k(n))`. -/
def garner_correction : ℕ → ℕ → ℕ
  | 0, _     => 0
  | k + 1, n => 3 ^ X (T_iter k n) * garner_correction k n + 2 ^ k * X (T_iter k n)

lemma T_expand (m : ℕ) : 2 * T m = 3 ^ X m * m + X m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega), X_even (by omega)]; omega
  · rw [T_odd (by omega), X_odd (by omega)]; omega

/-- **Garner's formula** [Gar81]. After `k` steps of the Collatz map `T`,
    `2^k · T^k(n) = 3^{S_k} · n + Q_k`
    where `S_k` is the number of odd iterates and `Q_k` is the accumulated correction. -/
lemma garner_formula (k n : ℕ) :
    2 ^ k * T_iter k n = 3 ^ num_odd_steps k n * n + garner_correction k n := by
  induction k with
  | zero => simp [T_iter, num_odd_steps, garner_correction]
  | succ k ih =>
    simp only [T_iter, num_odd_steps, garner_correction, Finset.sum_range_succ]
    have hexp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hexp]
    have hT := T_expand (T_iter k n)
    calc 2 * 2 ^ k * T (T_iter k n)
        = 2 ^ k * (2 * T (T_iter k n)) := by ring
      _ = 2 ^ k * (3 ^ X (T_iter k n) * T_iter k n + X (T_iter k n)) := by rw [hT]
      _ = 3 ^ X (T_iter k n) * (2 ^ k * T_iter k n) + 2 ^ k * X (T_iter k n) := by ring
      _ = 3 ^ X (T_iter k n) * (3 ^ num_odd_steps k n * n + garner_correction k n)
          + 2 ^ k * X (T_iter k n) := by rw [ih]
      _ = 3 ^ (num_odd_steps k n + X (T_iter k n)) * n
          + (3 ^ X (T_iter k n) * garner_correction k n + 2 ^ k * X (T_iter k n)) := by
        rw [pow_add]; ring

lemma num_odd_steps_mono {j k : ℕ} (hjk : j ≤ k) (n : ℕ) :
    num_odd_steps j n ≤ num_odd_steps k n := by
  unfold num_odd_steps
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

lemma num_odd_steps_succ (k n : ℕ) :
    num_odd_steps (k + 1) n = num_odd_steps k n + X (T_iter k n) := by
  simp [num_odd_steps, Finset.sum_range_succ]

/-- Closed-form expression for `garner_correction`:
    `Q(k) = ∑_{j<k} X(T^j n) · 2^j · 3^{S_k - S_{j+1}}`,
    where `S_m = num_odd_steps m n`. -/
def garner_correction_sum (k n : ℕ) : ℕ :=
  (Finset.range k).sum (fun j =>
    X (T_iter j n) * 2 ^ j * 3 ^ (num_odd_steps k n - num_odd_steps (j + 1) n))

lemma garner_correction_eq_sum (k n : ℕ) :
    garner_correction k n = garner_correction_sum k n := by
  induction k with
  | zero => simp [garner_correction, garner_correction_sum]
  | succ k ih =>
    simp only [garner_correction, garner_correction_sum, Finset.sum_range_succ]
    -- last term: 3^(S_{k+1} - S_{k+1}) = 3^0 = 1
    have hlast : num_odd_steps (k + 1) n - num_odd_steps (k + 1) n = 0 := Nat.sub_self _
    rw [hlast, pow_zero, mul_one, mul_comm (2 ^ k)]
    -- prefix sum: factor out 3^{x_k}
    congr 1
    rw [ih, garner_correction_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hle : num_odd_steps (j + 1) n ≤ num_odd_steps k n :=
      num_odd_steps_mono (by omega) n
    have : num_odd_steps (k + 1) n - num_odd_steps (j + 1) n =
        X (T_iter k n) + (num_odd_steps k n - num_odd_steps (j + 1) n) := by
      rw [num_odd_steps_succ]; omega
    rw [this, pow_add]
    ring

/-- The Garner coefficient: `C k n = 3^(num_odd_steps k n) / 2^k` as a rational number. -/
def C (k n : ℕ) : ℚ := (3 ^ num_odd_steps k n : ℚ) / (2 ^ k : ℚ)

end CollatzMapBasics

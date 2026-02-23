import Mathlib
import CollatzMapBasics.Basic

namespace CollatzMapBasics

open Classical

/-- `X n` is `(1 - (-1)^n) / 2`, i.e., 0 when `n` is even and 1 when `n` is odd. -/
def X (n : ℕ) : ℕ := ((1 - (-1 : ℤ)^n) / 2).toNat

lemma X_even {n : ℕ} (h : n % 2 = 0) : X n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  simp [X, pow_mul, Int.one_pow]

lemma X_odd {n : ℕ} (h : n % 2 = 1) : X n = 1 := by
  obtain ⟨k, hk⟩ := Nat.odd_iff.mpr h
  subst hk
  simp [X, pow_succ, pow_mul, Int.one_pow]

lemma X_eq_mod (n : ℕ) : X n = n % 2 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [X_even (by omega)]; omega
  · rw [X_odd (by omega)]; omega

/-- `T n` is one step of the Collatz map in the compact form `(n * 3^X(n) + X(n)) / 2`,
    where `X(n) = n % 2`. When `n` is even this gives `n / 2`; when `n` is odd, `(3n + 1) / 2`. -/
def T (n : ℕ) : ℕ := (n * 3 ^ X n + X n) / 2

lemma T_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by
  simp [T, X_even h]

lemma T_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  simp [T, X_odd h]; ring_nf

/-- `T_iter k n` applies `T` to `n` a total of `k` times: `T^0 = id`, `T^(k+1) = T ∘ T^k`. -/
def T_iter : ℕ → ℕ → ℕ
  | 0, n     => n
  | k + 1, n => T (T_iter k n)

/-- The stopping time of `n` under `T` is the smallest positive `k` such that `T_iter k n < n`,
    or `⊤` if no such `k` exists. [Ter76] -/
noncomputable def stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n then
    (Nat.find h : ℕ∞)
  else
    ⊤

lemma stopping_time_ne_top_iff (n : ℕ) :
    stopping_time n ≠ ⊤ ↔ ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n := by
  simp only [stopping_time]; constructor
  · intro h; split at h
    · assumption
    · exact absurd rfl h
  · intro ⟨k, hk1, hklt⟩; split
    · exact WithTop.natCast_ne_top _
    · rename_i h; exact absurd ⟨k, hk1, hklt⟩ h


/-- The total stopping time of `n` under `T` is the least positive `k` such that `T_iter k n = 1`,
    or `⊤` if no such `k` exists. -/
noncomputable def total_stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n = 1 then
    (Nat.find h : ℕ∞)
  else
    ⊤

lemma T_pos {n : ℕ} (hn : n ≥ 1) : T n ≥ 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega)]; omega
  · rw [T_odd (by omega)]; omega

lemma T_iter_pos {n : ℕ} (hn : n ≥ 1) (k : ℕ) : T_iter k n ≥ 1 := by
  induction k with
  | zero => exact hn
  | succ k ih => exact T_pos ih

lemma T_iter_add (a b n : ℕ) : T_iter (a + b) n = T_iter a (T_iter b n) := by
  induction a with
  | zero => simp only [Nat.zero_add, T_iter]
  | succ a ih =>
    simp only [Nat.succ_add, T_iter, ih]

lemma T_iter_succ_right (i n : ℕ) : T_iter (i + 1) n = T_iter i (T n) := by
  rw [T_iter_add i 1 n]; rfl

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
  induction j generalizing n with
  | zero => exact ⟨0, hj⟩
  | succ j ih =>
    simp only [collatz_iter] at hj
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- even case
      have he : (m + m) % 2 = 0 := by omega
      have hdiv : (m + m) / 2 = m := by omega
      rw [collatz_step_even' he, hdiv] at hj
      obtain ⟨k', hk'⟩ := ih m (by omega) hj
      exact ⟨k' + 1, by rw [T_iter_add k' 1]; simp only [T_iter]; rw [T_even he, hdiv]; exact hk'⟩
    · -- odd case
      have hodd : (2 * m + 1) % 2 = 1 := by omega
      rw [collatz_step_odd' hodd] at hj
      obtain ⟨k', hk'⟩ := ih (3 * (2 * m + 1) + 1) (by omega) hj
      have hk'_pos : k' ≥ 1 := by
        by_contra h0; push_neg at h0; interval_cases k'; simp [T_iter] at hk'
      refine ⟨k', ?_⟩
      have hsplit : k' = (k' - 1) + 1 := by omega
      rw [hsplit, T_iter_add _ 1]; simp only [T_iter]; rw [T_odd hodd]
      rw [hsplit, T_iter_add _ 1] at hk'; simp only [T_iter] at hk'
      rwa [T_even (by omega)] at hk'


end CollatzMapBasics

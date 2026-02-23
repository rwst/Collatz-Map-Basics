import Mathlib

namespace CollatzMapBasics

/-- do a single collatz-step. `collatz_step n` returns 1 if `n < 2`, otherwise `n/2` if `n` is even, otherwise `3 * n + 1`-/
def collatz_step (n : ℕ) : ℕ :=
  if n % 2 == 0 then
    (n / 2)
  else
    (3 * n + 1)

/-- `collatz_iter k n` does `k` collatz-steps on `n` -/
def collatz_iter : ℕ → ℕ → ℕ
| 0, n     => n
| (k + 1), n => collatz_iter k (collatz_step n)

lemma collatz_step_pow_two (k : ℕ) (hk : k ≥ 1) : collatz_step (2^k) = 2^(k-1) := by
  simp only [collatz_step]
  have h : 2^k % 2 = 0 := by
    have : 2 ∣ 2^k := dvd_pow_self 2 (by omega : k ≠ 0)
    exact Nat.dvd_iff_mod_eq_zero.mp this
  simp only [h, beq_self_eq_true, ↓reduceIte]
  have hk' : k = k - 1 + 1 := by omega
  conv_lhs => rw [hk', Nat.pow_succ]
  simp

lemma collatz_iter_pow_two (l : ℕ) : collatz_iter l (2^l) = 1 := by
  induction l with
  | zero => simp [collatz_iter]
  | succ l ih =>
    simp only [collatz_iter]
    have h : collatz_step (2^(l+1)) = 2^l := by
      rw [collatz_step_pow_two (l+1) (by omega)]
      simp
    rw [h]
    exact ih

lemma collatz_iter_pow_two_ne_one (l k : ℕ) (hk : k < l) : collatz_iter k (2^l) ≠ 1 := by
  induction k generalizing l with
  | zero =>
    simp only [collatz_iter]
    have : 2^l ≥ 2 := by
      have : l ≥ 1 := by omega
      calc 2^l ≥ 2^1 := Nat.pow_le_pow_right (by norm_num) this
           _ = 2 := by norm_num
    omega
  | succ k ih =>
    simp only [collatz_iter]
    have hl : l ≥ 1 := by omega
    have hstep : collatz_step (2^l) = 2^(l-1) := collatz_step_pow_two l hl
    rw [hstep]
    apply ih
    omega

lemma exists_collatz_reverse_strict (l : ℕ) :
  ∃ n : ℕ, collatz_iter l n = 1 ∧ ∀ k, k < l → collatz_iter k n ≠ 1 := by
  exact ⟨2^l, collatz_iter_pow_two l, collatz_iter_pow_two_ne_one l⟩

/--
Relation asserting that `n` reaches 1 with exactly `m` steps of the form `3n+1`.
Any number of `n/2` steps are allowed and do not contribute to the count `m`.
-/
inductive CollatzOddSteps : ℕ → ℕ → Prop where
  -- Base case: We are at 1. We have used 0 odd steps.
  | base : CollatzOddSteps 1 0

  -- Even step: If n is even, divide by 2.
  -- The count 'm' passes through unchanged.
  | even {n m : ℕ} :
      n % 2 = 0 →
      n ≠ 0 →            -- safety to prevent 0 loop
      CollatzOddSteps (n / 2) m →
      CollatzOddSteps n m

  -- Odd step: If n is odd (and not 1), do 3n+1.
  -- The count increases to 'm + 1'.
  | odd {n m : ℕ} :
      n % 2 = 1 →
      n > 1 →            -- prevent stepping away from 1
      CollatzOddSteps (3 * n + 1) m →
      CollatzOddSteps n (m + 1)

lemma CollatzOddSteps_pos (n m : ℕ) (h : CollatzOddSteps n m) : n ≥ 1 := by
  cases h with
  | base => simp
  | even _ hn _ => omega
  | odd _ hgt1 _ => omega

lemma collatz_iter_add (a b n : ℕ) : collatz_iter (a + b) n = collatz_iter a (collatz_iter b n) := by
  induction b generalizing n with
  | zero => simp [collatz_iter]
  | succ b ih =>
    rw [Nat.add_succ, collatz_iter, ih (collatz_step n)]
    rfl

end CollatzMapBasics

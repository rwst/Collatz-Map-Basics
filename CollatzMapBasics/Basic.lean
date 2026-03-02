import Mathlib
import CollatzMapBasics.Elementary

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

@[simp]
lemma collatz_step_odd (n : ℕ) (h : n % 2 = 1) : collatz_step n = 3 * n + 1 := by
  unfold collatz_step
  have : (n % 2 == 0) = false := by
    apply beq_false_of_ne
    omega
  simp [this]

@[simp]
lemma collatz_step_even (n : ℕ) (h : n % 2 = 0) : collatz_step n = n / 2 := by
  have h_eq : (n % 2 == 0) = true := beq_iff_eq.mpr h
  simp [collatz_step, h_eq]

@[simp] lemma collatz_step_zero : collatz_step 0 = 0 := by native_decide

@[simp]
lemma collatz_iter_zero (k : ℕ) : collatz_iter k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [collatz_iter, ih]

/-- If `n` is positive, then its Collatz step is also positive. -/
lemma collatz_step_pos (n : ℕ) (hn : n ≥ 1) : collatz_step n ≥ 1 := by
  unfold collatz_step; split_ifs with h
  · have : n ≥ 2 := by
      rcases n with _|_|n <;> simp at h ⊢; contradiction
    omega
  · omega

/-- If `n` is positive, then all its Collatz iterates are positive. -/
lemma collatz_iter_pos (i n : ℕ) (hn : n ≥ 1) : collatz_iter i n ≥ 1 := by
  induction i generalizing n with
  | zero => exact hn
  | succ i ih => exact ih _ (collatz_step_pos n hn)

lemma collatz_iter_succ_right' (d n : ℕ) : collatz_iter (d + 1) n = collatz_step (collatz_iter d n) := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    calc collatz_iter (d + 2) n = collatz_iter (d + 1) (collatz_step n) := rfl
    _ = collatz_step (collatz_iter d (collatz_step n)) := ih (collatz_step n)
    _ = collatz_step (collatz_iter (d + 1) n) := rfl

@[simp]
lemma collatz_step_pow_two (k : ℕ) (hk : k ≥ 1) : collatz_step (2^k) = 2^(k-1) := by
  rcases k with _ | k
  · contradiction
  · simp [collatz_step, Nat.pow_succ]

@[simp]
lemma collatz_iter_pow_two (l : ℕ) : collatz_iter l (2^l) = 1 := by
  induction l with
  | zero => rfl
  | succ l ih => simp [collatz_iter, Nat.pow_succ, ih]

lemma collatz_iter_two_pow_mul (k m : ℕ) : collatz_iter k (2^k * m) = m := by
  induction k with
  | zero => simp [collatz_iter]
  | succ k ih =>
    have h : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    have step : collatz_step (2 * (2^k * m)) = 2^k * m := by
      unfold collatz_step; simp [show 2 * (2^k * m) % 2 = 0 by omega]
    calc collatz_iter (k + 1) (2^(k+1) * m)
      _ = collatz_iter k (collatz_step (2 * (2^k * m))) := by rw [h]; rfl
      _ = collatz_iter k (2^k * m) := by rw [step]
      _ = m := ih

lemma collatz_iter_pow_two_ne_one (l k : ℕ) (hk : k < l) : collatz_iter k (2^l) ≠ 1 := by
  induction k generalizing l with
  | zero => simp [collatz_iter]; omega
  | succ k ih =>
    have hl : l ≥ 1 := by omega
    simp [collatz_iter, collatz_step_pow_two l hl]
    apply ih; omega

lemma exists_collatz_reverse_strict (l : ℕ) :
  ∃ n : ℕ, collatz_iter l n = 1 ∧ ∀ k, k < l → collatz_iter k n ≠ 1 := by
  exact ⟨2^l, collatz_iter_pow_two l, collatz_iter_pow_two_ne_one l⟩

-- Helper lemmas for cycle_implies_not_collatz

lemma collatz_iter_add (a b n : ℕ) :
    collatz_iter (a + b) n = collatz_iter a (collatz_iter b n) := by
  induction b generalizing n with
  | zero => rfl
  | succ b ih => exact ih (collatz_step n)

lemma collatz_iter_mul_cycle (k n m : ℕ) (h : collatz_iter k n = n) :
    collatz_iter (m * k) n = n := by
  induction m with
  | zero => simp [collatz_iter]
  | succ m ih => rw [Nat.succ_mul, collatz_iter_add, h, ih]

lemma collatz_iter_mem_124 (i n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    collatz_iter i n = 1 ∨ collatz_iter i n = 2 ∨ collatz_iter i n = 4 := by
  induction i generalizing n with
  | zero => exact hn
  | succ i ih =>
    simp only [collatz_iter]
    apply ih
    rcases hn with rfl | rfl | rfl <;> native_decide

lemma collatz_iter_one_le_four (i : ℕ) : collatz_iter i 1 ≤ 4 := by
  rcases collatz_iter_mem_124 i 1 (Or.inl rfl) with h | h | h <;> omega

/-- The Collatz function `C(n)` has the closed form `((7n+2) - (5n+2)(-1)^n) / 4`. -/
lemma collatz_step_closed_form (n : ℕ) :
    (collatz_step n : ℤ) = (7 * (n : ℤ) + 2 - (5 * (n : ℤ) + 2) * (-1 : ℤ)^n) / 4 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h_pow : (-1 : ℤ)^n = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      rw [hk, pow_mul]
      norm_num
      exact one_pow k
    unfold collatz_step
    simp [h, h_pow]
    omega
  · have h_pow : (-1 : ℤ)^n = -1 := by
      obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      rw [hk, pow_add, pow_mul]
      norm_num
      exact one_pow k
    unfold collatz_step
    simp [h, h_pow]
    omega

theorem collatz_conjecture : ∀ (n : ℕ), n = 0 ∨ ∃ k, collatz_iter k n = 1 :=
  sorry

/-- If some number greater than 4 is a fixed point of `collatz_iter k` (i.e., it lies on a
nontrivial cycle), then the Collatz conjecture fails: not every positive natural number
eventually reaches 1. -/
lemma cycle_implies_not_collatz (n k : ℕ) (hn : n > 4) (hk : k ≥ 1)
    (hcycle : collatz_iter k n = n) :
    ¬ ∀ (m : ℕ), m = 0 ∨ ∃ j, collatz_iter j m = 1 := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, collatz_iter j n = 1 := (h n).resolve_left (by omega)
  have : n = collatz_iter (j * k) n := (collatz_iter_mul_cycle k n j hcycle).symm
  rw [← Nat.sub_add_cancel (Nat.le_mul_of_pos_right j hk), collatz_iter_add, hj] at this
  have : n ≤ 4 := this.symm ▸ collatz_iter_one_le_four _
  omega

/-- If some orbit is unbounded, the Collatz conjecture fails. -/
lemma unbounded_orbit_implies_not_collatz (n : ℕ)
    (h_unbounded : ∀ B, ∃ k, collatz_iter k n > B) :
    ¬ ∀ (m : ℕ), m = 0 ∨ ∃ j, collatz_iter j m = 1 := by
  intro h
  rcases h n with rfl | ⟨j, hj⟩
  · obtain ⟨k, hk⟩ := h_unbounded 0; simp [collatz_iter_zero] at hk
  · set M := (Finset.range (j + 1)).sup (collatz_iter · n)
    obtain ⟨k, hk⟩ := h_unbounded (M + 4)
    by_cases h_lt : k < j + 1
    · have h_le : collatz_iter k n ≤ M := Finset.le_sup (f := (collatz_iter · n)) (Finset.mem_range.mpr h_lt)
      omega
    · have h_ge : k ≥ j := by omega
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h_ge
      rw [add_comm, collatz_iter_add, hj] at hk
      have h_le_4 : collatz_iter i 1 ≤ 4 := collatz_iter_one_le_four i
      omega

/-- If no number above 4 lies on a nontrivial cycle and every orbit is bounded,
    then every positive natural number eventually reaches 1. -/
lemma bounded_no_cycle_implies_collatz
    (h_no_cycle : ∀ n k, n > 4 → k ≥ 1 → collatz_iter k n ≠ n)
    (h_bounded  : ∀ n, ∃ B, ∀ k, collatz_iter k n ≤ B) :
    ∀ m, m = 0 ∨ ∃ j, collatz_iter j m = 1 := by
  intro m; rcases eq_or_ne m 0 with rfl | hm; · left; rfl
  right; have hm_pos : m ≥ 1 := Nat.pos_of_ne_zero hm
  obtain ⟨B, hB⟩ := h_bounded m
  -- Pigeonhole: ℕ → Fin (B+1) must have a collision
  have ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨collatz_iter k m, Nat.lt_succ_of_le (hB k)⟩ : Fin (B + 1)))
  simp only [Fin.mk.injEq] at heq
  wlog h_lt : i < j generalizing i j
  · exact this j i hij.symm heq.symm (hij.lt_or_gt.resolve_left h_lt)
  set c := collatz_iter i m
  have h_cycle : collatz_iter (j - i) c = c := by
    rw [← collatz_iter_add, Nat.sub_add_cancel h_lt.le, heq]
  -- c must be ≤ 4 (otherwise h_no_cycle gives contradiction)
  have hc_le : c ≤ 4 := by
    by_contra h; exact h_no_cycle c (j - i) (by omega) (by omega) h_cycle
  -- c ≥ 1 since m ≥ 1
  have hc_pos : c ≥ 1 := collatz_iter_pos i m hm_pos
  -- Every value in {1,2,3,4} reaches 1
  have ⟨j', hj'⟩ : ∃ j', collatz_iter j' c = 1 := by
    interval_cases c
    · exact ⟨0, rfl⟩              -- c = 1
    · exact ⟨1, by native_decide⟩ -- c = 2
    · exact ⟨7, by native_decide⟩ -- c = 3
    · exact ⟨2, by native_decide⟩ -- c = 4
  -- Compose: m reaches c in i steps, c reaches 1 in j' steps
  exact ⟨j' + i, by rw [collatz_iter_add, hj']⟩

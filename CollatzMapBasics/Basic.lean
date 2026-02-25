import Mathlib

-- 2^k mod 3 is 1 if k is even (and k > 0), 2 if k is odd
lemma pow_two_mod_three (k : ℕ) : 2^k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with | zero => rfl | succ k ih =>
  rw [Nat.pow_succ, Nat.mul_mod, ih]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1 <;> simp [*] at * <;> omega

lemma exists_predecessor_of_odd (y : ℕ) (h_odd : y % 2 = 1) (h_not_div3 : y % 3 ≠ 0) :
  ∃ x k : ℕ, x % 2 = 1 ∧ (3 * x + 1) = 2^k * y := by
  obtain h | h : y % 3 = 1 ∨ y % 3 = 2 := by omega
  · exact ⟨(4 * y - 1) / 3, 2, by omega, by omega⟩
  · exact ⟨(2 * y - 1) / 3, 1, by omega, by omega⟩

/--
If `y` is a multiple of 3, it implies there is no number `n`
(and shift `k`) such that performing a `3n+1` step and `k` divisions reaches `y`.
-/
lemma no_odd_predecessor_for_div3 (y : ℕ) (h_div3 : y % 3 = 0) :
  ∀ n k : ℕ, 3 * n + 1 ≠ y * 2^k := by
  intro n k h
  have := congrArg (· % 3) h
  simp [Nat.add_mod, Nat.mul_mod, h_div3] at this

/-- For y ≡ 1 (mod 6), there exists x > 1 odd such that 3x+1 = 4y -/
lemma exists_predecessor_gt_one_mod1 (y : ℕ) (hy_mod6 : y % 6 = 1) (hy_gt : y > 1) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^2 * y := by
  use (4 * y - 1) / 3
  have : 3 * ((4 * y - 1) / 3) = 4 * y - 1 := Nat.mul_div_cancel' (by omega)
  refine ⟨by omega, by omega, by omega⟩

/-- For y ≡ 5 (mod 6), there exists x > 1 odd such that 3x+1 = 2y -/
lemma exists_predecessor_gt_one_mod5 (y : ℕ) (hy_mod6 : y % 6 = 5) :
    ∃ x : ℕ, x % 2 = 1 ∧ x > 1 ∧ (3 * x + 1) = 2^1 * y := by
  use (2 * y - 1) / 3
  have : 3 * ((2 * y - 1) / 3) = 2 * y - 1 := Nat.mul_div_cancel' (by omega)
  refine ⟨by omega, by omega, by omega⟩


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

@[simp] lemma collatz_step_zero : collatz_step 0 = 0 := by native_decide

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

lemma collatz_step_pow_two (k : ℕ) (hk : k ≥ 1) : collatz_step (2^k) = 2^(k-1) := by
  rcases k with _ | k
  · contradiction
  · simp [collatz_step, Nat.pow_succ]

lemma collatz_iter_pow_two (l : ℕ) : collatz_iter l (2^l) = 1 := by
  induction l with
  | zero => rfl
  | succ l ih => simp [collatz_iter, collatz_step_pow_two, ih]

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

theorem collatz_conjecture : ∀ (n : ℕ), n = 0 ∨ ∃ k, collatz_iter k n = 1 :=
  sorry

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

/-- CollatzOddSteps is preserved under multiplication by powers of 2 -/
lemma CollatzOddSteps_mul_pow_two (y m k : ℕ) (hy : CollatzOddSteps y m) (hk : k ≥ 1) :
    CollatzOddSteps (2^k * y) m := by
  have hy_pos : y ≥ 1 := by
    cases hy with
    | base => simp
    | even _ hn _ => omega
    | odd _ hn _ => omega
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk' : k' = 0
    · simp only [hk', zero_add, pow_one]
      apply CollatzOddSteps.even
      · simp only [Nat.mul_mod_right]
      · omega
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]; exact hy
    · have hk'' : k' ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk'
      have ih' := ih hk''
      apply CollatzOddSteps.even
      · have : 2^(k' + 1) * y = 2 * (2^k' * y) := by ring
        rw [this]; simp
      · -- 2^(k'+1) * y ≠ 0
        have hpow : 2^k' ≥ 1 := Nat.one_le_pow k' 2 (by omega)
        have : 2^(k' + 1) * y ≥ 2 := by
          calc 2^(k' + 1) * y = 2 * 2^k' * y := by ring
            _ ≥ 2 * 1 * 1 := by nlinarith
            _ = 2 := by ring
        omega
      · have hdiv : 2^(k' + 1) * y / 2 = 2^k' * y := by
          have : 2^(k' + 1) * y = 2 * (2^k' * y) := by ring
          rw [this]
          exact Nat.mul_div_cancel_left _ (by omega)
        rw [hdiv]
        exact ih'

/-- Numbers reachable via CollatzOddSteps are positive -/
lemma CollatzOddSteps_pos (n m : ℕ) (h : CollatzOddSteps n m) : n ≥ 1 := by
  cases h with
  | base => simp
  | even _ hn _ => omega
  | odd _ hgt1 _ => omega

/-- Strengthened Main Lemma: exists n with CollatzOddSteps n m AND n % 3 ≠ 0 AND (m > 0 → n is odd and n > 1) -/
lemma exists_n_with_m_odd_steps_not_div3 (m : ℕ) :
    ∃ n : ℕ, CollatzOddSteps n m ∧ n % 3 ≠ 0 ∧ (m > 0 → n % 2 = 1 ∧ n > 1) := by
  induction m with
  | zero =>
    -- Case 0: n=1 works, 1 % 3 = 1 ≠ 0
    use 1
    refine ⟨CollatzOddSteps.base, by simp, by simp⟩
  | succ m_prev ih =>
    obtain ⟨y, hy, hy_not_div3, hy_odd_gt1⟩ := ih
    by_cases hm_prev : m_prev = 0
    · -- m_prev = 0: use n = 5
      -- 5 % 3 = 2 ≠ 0, 5 is odd, 5 > 1, and CollatzOddSteps 5 1
      use 5
      refine ⟨?_, by simp, by simp⟩
      apply CollatzOddSteps.odd (by simp) (by omega)
      have h16 : CollatzOddSteps 16 0 := by
        apply CollatzOddSteps.even; simp; omega
        apply CollatzOddSteps.even; simp; omega
        apply CollatzOddSteps.even; simp; omega
        apply CollatzOddSteps.even; simp; omega
        exact CollatzOddSteps.base
      rw [hm_prev]; exact h16
    · -- m_prev > 0, so y is odd and y > 1 (from our strengthened IH)
      have hm_prev_pos : m_prev > 0 := Nat.pos_of_ne_zero hm_prev
      have ⟨hy_odd, hy_gt1⟩ := hy_odd_gt1 hm_prev_pos
      -- Find predecessor with x % 3 ≠ 0
      obtain ⟨x, k, hx_odd, hx_eq⟩ :=
        exists_predecessor_of_odd y hy_odd hy_not_div3
      -- First build CollatzOddSteps x (m_prev + 1)
      have hx_gt1 : x > 1 := by
        -- x is odd, so x ≥ 1; if x = 1 then 4 = 2^k * y, but y is odd and > 1
        rcases Nat.eq_or_lt_of_le (show x ≥ 1 by omega) with rfl | h
        · -- x = 1 → 4 = 2^k * y
          have h4 : 2 ^ k * y = 4 := by omega
          have hk2 : k ≤ 2 := by
            by_contra hk; push_neg at hk
            have : 2 ^ k ≥ 8 := le_trans (by norm_num : (8 : ℕ) ≤ 2^3) (Nat.pow_le_pow_right (by omega) hk)
            nlinarith [show y ≥ 1 from by omega]
          interval_cases k <;> omega
        · omega
      have hx_steps : CollatzOddSteps x (m_prev + 1) := by
        apply CollatzOddSteps.odd hx_odd hx_gt1
        rw [hx_eq]
        by_cases hk : k = 0
        · simp [hk]; exact hy
        · exact CollatzOddSteps_mul_pow_two y m_prev k hy (Nat.one_le_iff_ne_zero.mpr hk)
      -- Now handle x % 3 ≠ 0
      by_cases hx3 : x % 3 ≠ 0
      · exact ⟨x, hx_steps, hx3, fun _ => ⟨hx_odd, hx_gt1⟩⟩
      · -- x % 3 = 0: use 4*x + 1 instead (inline CollatzOddSteps_4n_add_1)
        push_neg at hx3
        use 4 * x + 1
        refine ⟨?_, by omega, fun _ => ⟨by omega, by omega⟩⟩
        -- Prove CollatzOddSteps (4*x+1) (m_prev + 1)
        -- Since x is odd and > 1, hx_steps uses the odd constructor
        cases hx_steps with
        | even h_ev _ _ => omega
        | @odd _ m' _ _ h_next =>
          apply CollatzOddSteps.odd (by omega) (by omega)
          apply CollatzOddSteps.even (by omega) (by omega)
          apply CollatzOddSteps.even (by omega) (by omega)
          convert h_next using 1; omega

/-- Main Lemma -/
lemma exists_n_with_m_odd_steps (m : ℕ) : ∃ n : ℕ, CollatzOddSteps n m := by
  obtain ⟨n, hn, _⟩ := exists_n_with_m_odd_steps_not_div3 m
  exact ⟨n, hn⟩

/--
If `n` is odd and greater than 1, then `4n + 1` requires the same number of odd steps `m` as `n`.
This is because `4n + 1` reaches `3n + 1` (the successor of `n`) using exactly 1 odd step,
just like `n` reaches `3n + 1` using exactly 1 odd step.
-/
lemma CollatzOddSteps_4n_add_1 (n m : ℕ) (h_odd : n % 2 = 1) (h_gt1 : n > 1)
    (h : CollatzOddSteps n m) : CollatzOddSteps (4 * n + 1) m := by
  -- Since n is odd and > 1, h must use the `odd` constructor
  -- So m = m_prev + 1 for some m_prev, and CollatzOddSteps (3n+1) m_prev
  cases h with
  | base =>
    -- Contradiction: n > 1 but base case has n = 1
    contradiction
  | even h_even _ _ =>
    -- Contradiction: n is odd but even constructor requires n even
    rw [h_odd] at h_even; contradiction
  | @odd n' m_prev _ _ h_next =>
    -- h_next : CollatzOddSteps (3 * n + 1) m_prev
    -- Goal: CollatzOddSteps (4 * n + 1) (m_prev + 1)

    apply CollatzOddSteps.odd (by omega) (by omega)
    apply CollatzOddSteps.even (by omega) (by omega)
    apply CollatzOddSteps.even (by omega) (by omega)
    convert h_next using 1; omega

/-- Sequence: iterate (4*x + 1) starting from n₀ -/
def iter_4n_plus_1 (n₀ : ℕ) : ℕ → ℕ
  | 0 => n₀
  | i + 1 => 4 * iter_4n_plus_1 n₀ i + 1

lemma iter_4n_plus_1_odd (n₀ : ℕ) (h_odd : n₀ % 2 = 1) : ∀ i, iter_4n_plus_1 n₀ i % 2 = 1 := by
  intro i
  induction i with
  | zero => exact h_odd
  | succ i ih => simp [iter_4n_plus_1]; omega

lemma iter_4n_plus_1_gt_one (n₀ : ℕ) (h_gt1 : n₀ > 1) : ∀ i, iter_4n_plus_1 n₀ i > 1 := by
  intro i
  induction i with
  | zero => exact h_gt1
  | succ i ih => simp [iter_4n_plus_1]; omega

lemma iter_4n_plus_1_growth (n₀ : ℕ) (h_pos : n₀ ≥ 1) : ∀ i, iter_4n_plus_1 n₀ i ≥ i + 1 := by
  intro i
  induction i with
  | zero => simp [iter_4n_plus_1]; omega
  | succ i ih =>
    simp [iter_4n_plus_1]
    have h1 : 4 * iter_4n_plus_1 n₀ i + 1 ≥ 4 * (i + 1) + 1 := by omega
    omega

/--
For every step count `m`, there are infinitely many `n` (forall k, exists n > k)
that reach 1 using exactly `m` odd steps.
-/
lemma infinitely_many_collatz_odd_steps (m : ℕ) : ∀ k, ∃ n, n > k ∧ CollatzOddSteps n m := by
  intro k
  cases m with
  | zero =>
    -- Case m = 0: Powers of 2.
    use 2^(k+1)
    exact ⟨by have := Nat.lt_two_pow_self (n := k + 1); omega,
      by simpa using CollatzOddSteps_mul_pow_two 1 0 (k+1) CollatzOddSteps.base (by omega)⟩

  | succ m_prev =>
    -- Case m > 0.
    obtain ⟨n₀, h_steps, _, h_cond⟩ := exists_n_with_m_odd_steps_not_div3 (m_prev + 1)
    have ⟨h_odd, h_gt1⟩ := h_cond (by omega : m_prev + 1 > 0)

    refine ⟨iter_4n_plus_1 n₀ k,
      by have := iter_4n_plus_1_growth n₀ (by omega : n₀ ≥ 1) k; omega, ?_⟩
    induction k with
    | zero => simp [iter_4n_plus_1]; exact h_steps
    | succ i ih =>
      simp [iter_4n_plus_1]
      exact CollatzOddSteps_4n_add_1 _ _ (iter_4n_plus_1_odd n₀ h_odd i)
        (iter_4n_plus_1_gt_one n₀ h_gt1 i) ih

/--
A "primitive" for step count `m` is an odd number `n` that reaches 1 in `m` steps,
but is not the child of another *odd* number `k` (via `4k+1`) that also reaches 1 in `m` steps.

Since the "Odd Step" count is preserved between `k` and `4k+1` only when `k` is odd,
we explicitly require the predecessor to be odd.
-/
def IsPrimitive4x1 (n m : ℕ) : Prop :=
  CollatzOddSteps n m ∧
  n % 2 = 1 ∧
  ∀ k, k % 2 = 1 → 4 * k + 1 = n → ¬ CollatzOddSteps k m

/--
Lemma: The definition of a primitive simplifies to a modular arithmetic check.
If `n` is odd and has step count `m`, it is primitive if and only if `n % 8 ≠ 5` or `n = 5`.
-/
lemma is_primitive_iff_mod_8_ne_5 (n m : ℕ) (h_odd : n % 2 = 1) (h_steps : CollatzOddSteps n m)
    (h_ne5 : n ≠ 5) : IsPrimitive4x1 n m ↔ n % 8 ≠ 5 := by
  constructor
  · intro h_prim h_mod5
    unfold IsPrimitive4x1 at h_prim
    have ⟨k, hk⟩ : ∃ k, n = 8 * k + 5 := by
      use n / 8
      have := Nat.div_add_mod n 8
      omega
    let x := 2 * k + 1
    have hx_odd : x % 2 = 1 := by simp [x]
    have hk_pos : k ≥ 1 := by omega
    have hx_gt1 : x > 1 := by simp [x]; omega
    have h_map : 4 * x + 1 = n := by
      rw [hk]; simp [x]; ring
    have h_x_steps : CollatzOddSteps x m := by
      cases h_steps with
      | base => omega
      | even h_even _ _ => omega
      | odd h_odd' h_gt1' h_next =>
        have h_strip : ∀ v m', CollatzOddSteps v m' → v % 2 = 0 → v ≠ 0 →
            CollatzOddSteps (v / 2) m' := fun v m' hv heven hne => by
          cases hv with
          | base => omega
          | even _ _ h => exact h
          | odd hodd _ _ => omega
        have h1 := h_strip (3 * n + 1) _ h_next (by omega) (by omega)
        have h2 := h_strip ((3 * n + 1) / 2) _ h1 (by omega) (by omega)
        apply CollatzOddSteps.odd hx_odd hx_gt1
        have h_eq : 3 * x + 1 = (3 * n + 1) / 4 := by simp only [x]; omega
        rw [h_eq]
        rwa [Nat.div_div_eq_div_mul] at h2
    exact h_prim.2.2 x hx_odd h_map h_x_steps
  · intro h_mod8_ne_5
    refine ⟨h_steps, h_odd, fun k hk_odd h_map => absurd ?_ h_mod8_ne_5⟩
    have := (Nat.div_add_mod k 2).symm; rw [hk_odd] at this; omega

/--
For every level `m`, there are infinitely many members not divisible by 3.
-/
lemma infinitely_many_not_div3 (m : ℕ) : ∀ B, ∃ n, n > B ∧ CollatzOddSteps n m ∧ n % 3 ≠ 0 := by
  intro B
  obtain ⟨n₀, h_steps, h_mod3, _⟩ := exists_n_with_m_odd_steps_not_div3 m
  have h_pos := CollatzOddSteps_pos n₀ m h_steps
  use 2 ^ (B + 1) * n₀
  refine ⟨?_, CollatzOddSteps_mul_pow_two n₀ m (B + 1) h_steps (by omega), ?_⟩
  · -- 2^(B+1) * n₀ > B
    have h_2pow : 2 ^ (B + 1) ≥ B + 1 := by
      have := Nat.lt_two_pow_self (n := B + 1)
      omega
    nlinarith
  · -- (2^(B+1) * n₀) % 3 ≠ 0
    rw [Nat.mul_mod]
    have h2k : 2 ^ (B + 1) % 3 = 1 ∨ 2 ^ (B + 1) % 3 = 2 := by
      have := pow_two_mod_three (B + 1)
      split_ifs at this <;> omega
    have hn0 : n₀ % 3 = 1 ∨ n₀ % 3 = 2 := by
      have := Nat.mod_lt n₀ (show (0 : ℕ) < 3 by omega)
      omega
    rcases h2k with h1 | h1 <;> rcases hn0 with h2 | h2 <;> simp [h1, h2]

/--
Every odd number `y` (not div 3) at level `m` generates a Primitive at level `m+1`.
-/
lemma odd_node_generates_primitive (y m : ℕ)
  (h_steps : CollatzOddSteps y m)
  (h_odd : y % 2 = 1)
  (h_not_div3 : y % 3 ≠ 0) :
  ∃ n, IsPrimitive4x1 n (m + 1) := by
  by_cases hy1 : y = 1
  · -- y = 1: must have m = 0; use n = 5
    subst hy1
    cases h_steps with
    | base =>
      use 5
      refine ⟨?_, by norm_num, ?_⟩
      · -- CollatzOddSteps 5 1
        apply CollatzOddSteps.odd (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        apply CollatzOddSteps.even (by norm_num) (by omega)
        exact CollatzOddSteps.base
      · -- Primitivity: only predecessor is k=1, which lacks CollatzOddSteps 1 1
        intro k _ hk_eq
        have : k = 1 := by omega
        subst this
        intro h; cases h with
        | even h_ev _ _ => omega
        | odd _ h_gt _ => omega
    | even h_ev _ _ => omega
    | odd _ h_gt _ => omega
  · -- y > 1
    have hy_gt1 : y > 1 := by have := CollatzOddSteps_pos y m h_steps; omega
    have hy_mod6 : y % 6 = 1 ∨ y % 6 = 5 := by omega
    rcases hy_mod6 with h6 | h6
    · -- y ≡ 1 (mod 6): predecessor via shift k = 2
      obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod1 y h6 hy_gt1
      use x
      have hx_steps : CollatzOddSteps x (m + 1) := by
        apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
        exact CollatzOddSteps_mul_pow_two y m 2 h_steps (by omega)
      obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 1 := ⟨y / 6, by omega⟩
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4] at hx_eq
      have hx_val : x = 8 * q + 1 := by omega
      exact (is_primitive_iff_mod_8_ne_5 x (m + 1) hx_odd hx_steps (by omega)).mpr (by omega)
    · -- y ≡ 5 (mod 6): predecessor via shift k = 1
      obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod5 y h6
      use x
      have hx_steps : CollatzOddSteps x (m + 1) := by
        apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
        exact CollatzOddSteps_mul_pow_two y m 1 h_steps (by omega)
      obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 5 := ⟨y / 6, by omega⟩
      have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
      rw [h2] at hx_eq
      have hx_val : x = 4 * q + 3 := by omega
      exact (is_primitive_iff_mod_8_ne_5 x (m + 1) hx_odd hx_steps (by omega)).mpr (by omega)

/-- Primitives at level m+1 generated by different odd numbers at level m are distinct.
    The generation relationship is 3*p+1 = 2^k * y: p does an odd step then k halvings to reach y.
    Since 3p+1 has a unique odd part, different generators y produce different primitives p. -/
lemma primitives_from_distinct_generators_ne
    (y₁ y₂ p₁ p₂ k₁ k₂ m : ℕ)
    (hy₁_odd : y₁ % 2 = 1) (hy₂_odd : y₂ % 2 = 1)
    (hp₂_prim : IsPrimitive4x1 p₂ (m + 1))
    (hgen₁ : 3 * p₁ + 1 = 2 ^ k₁ * y₁)
    (hgen₂ : 3 * p₂ + 1 = 2 ^ k₂ * y₂)
    (hy_ne : y₁ ≠ y₂) : p₁ ≠ p₂ := by
  intro heq
  subst heq
  apply hy_ne
  have h := hgen₁.symm.trans hgen₂
  -- h : 2 ^ k₁ * y₁ = 2 ^ k₂ * y₂
  have hk : k₁ = k₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- k₁ < k₂ implies 2 ∣ y₁, contradicting oddness
      have : 2 ^ k₂ = 2 ^ k₁ * 2 ^ (k₂ - k₁) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_assoc] at h
      have h1 := Nat.eq_of_mul_eq_mul_left (by positivity) h
      obtain ⟨c, hc⟩ : 2 ∣ y₁ := by
        rw [h1]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) y₂
      omega
    · -- k₂ < k₁ implies 2 ∣ y₂, contradicting oddness
      have : 2 ^ k₁ = 2 ^ k₂ * 2 ^ (k₁ - k₂) := by
        rw [← pow_add]; congr 1; omega
      rw [this, mul_assoc] at h
      have h1 := (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm
      obtain ⟨c, hc⟩ : 2 ∣ y₂ := by
        rw [h1]; exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) y₁
      omega
  subst hk
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

lemma iter_4n_plus_1_mod3 (n₀ i : ℕ) : iter_4n_plus_1 n₀ i % 3 = (n₀ + i) % 3 := by
  induction i with
  | zero => simp [iter_4n_plus_1]
  | succ i ih => simp [iter_4n_plus_1, Nat.add_mod, Nat.mul_mod, ih]; omega

/--
For every level `m`, there are infinitely many primitive numbers.
-/
lemma infinite_primitives (m : ℕ) (h2le: 2 ≤ m) : ∀ B, ∃ n, n > B ∧ IsPrimitive4x1 n m := by
  intro B
  have hm : m - 1 + 1 = m := by omega
  -- Get seed at level m-1: odd, > 1, % 3 ≠ 0
  obtain ⟨n₀, hn₀_steps, hn₀_mod3, hn₀_cond⟩ := exists_n_with_m_odd_steps_not_div3 (m - 1)
  have ⟨hn₀_odd, hn₀_gt1⟩ := hn₀_cond (by omega : m - 1 > 0)
  -- Build large odd y at level m-1
  set y := iter_4n_plus_1 n₀ (3 * (B + 1)) with hy_def
  have hy_odd : y % 2 = 1 := iter_4n_plus_1_odd n₀ hn₀_odd _
  have hy_gt1 : y > 1 := iter_4n_plus_1_gt_one n₀ hn₀_gt1 _
  have hy_mod3 : y % 3 ≠ 0 := by
    rw [hy_def, iter_4n_plus_1_mod3]
    have : (n₀ + 3 * (B + 1)) % 3 = n₀ % 3 := by omega
    rw [this]; exact hn₀_mod3
  have hy_large : y ≥ 3 * B + 4 := by
    have := iter_4n_plus_1_growth n₀ (by omega : n₀ ≥ 1) (3 * (B + 1))
    omega
  -- y has CollatzOddSteps at level m-1 (by iterating CollatzOddSteps_4n_add_1)
  have hy_steps : CollatzOddSteps y (m - 1) := by
    rw [hy_def]
    induction (3 * (B + 1)) with
    | zero => simp [iter_4n_plus_1]; exact hn₀_steps
    | succ i ih =>
      simp [iter_4n_plus_1]
      exact CollatzOddSteps_4n_add_1 _ _ (iter_4n_plus_1_odd n₀ hn₀_odd i)
        (iter_4n_plus_1_gt_one n₀ hn₀_gt1 i) ih
  -- Construct primitive at level m from y (inline from odd_node_generates_primitive)
  have hy_mod6 : y % 6 = 1 ∨ y % 6 = 5 := by omega
  rcases hy_mod6 with h6 | h6
  · -- y ≡ 1 (mod 6): primitive x with 3x+1 = 4y
    obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod1 y h6 (by omega)
    use x
    have hx_steps : CollatzOddSteps x (m - 1 + 1) := by
      apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
      exact CollatzOddSteps_mul_pow_two y (m - 1) 2 hy_steps (by omega)
    rw [hm] at hx_steps
    obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 1 := ⟨y / 6, by omega⟩
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4] at hx_eq
    have hx_val : x = 8 * q + 1 := by omega
    exact ⟨by omega, (is_primitive_iff_mod_8_ne_5 x m hx_odd hx_steps (by omega)).mpr (by omega)⟩
  · -- y ≡ 5 (mod 6): primitive x with 3x+1 = 2y
    obtain ⟨x, hx_odd, hx_gt1, hx_eq⟩ := exists_predecessor_gt_one_mod5 y h6
    use x
    have hx_steps : CollatzOddSteps x (m - 1 + 1) := by
      apply CollatzOddSteps.odd hx_odd hx_gt1; rw [hx_eq]
      exact CollatzOddSteps_mul_pow_two y (m - 1) 1 hy_steps (by omega)
    rw [hm] at hx_steps
    obtain ⟨q, hq⟩ : ∃ q, y = 6 * q + 5 := ⟨y / 6, by omega⟩
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h2] at hx_eq
    have hx_val : x = 4 * q + 3 := by omega
    exact ⟨by omega, (is_primitive_iff_mod_8_ne_5 x m hx_odd hx_steps (by omega)).mpr (by omega)⟩

/-- The odd Collatz successor of an odd number n is the odd part of 3n+1,
    i.e., (3n+1) / 2^v₂(3n+1). This exceeds n only when n ≡ 3 (mod 4). -/
lemma odd_collatz_successor_gt_iff_mod4 (n : ℕ) (h_mod4 : n % 4 = 3)
    (k : ℕ) (hk : k ≥ 1) (hk_val : (3 * n + 1) = 2 ^ k * ((3 * n + 1) / 2 ^ k))
    (hk_odd : (3 * n + 1) / 2 ^ k % 2 = 1) :
    ((3 * n + 1) / 2 ^ k > n ↔ n % 4 = 3) := by
  refine ⟨fun _ => h_mod4, fun _ => ?_⟩
  have hk_eq : k = 1 := by
    by_contra hne
    have : (4 : ℕ) ∣ (3 * n + 1) :=
      hk_val ▸ dvd_mul_of_dvd_left (by simpa using Nat.pow_dvd_pow 2 (show k ≥ 2 by omega)) _
    omega
  subst hk_eq; simp only [pow_one] at hk_val ⊢; omega

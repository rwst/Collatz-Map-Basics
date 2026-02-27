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


/-- The reduced Collatz map `R` maps an odd natural number `n` to the odd part of `3n + 1`. -/
def reduced_collatz_step (n : ℕ) : ℕ := ordCompl[2] (3 * n + 1)

def R_iter : ℕ → ℕ → ℕ
| 0, n     => n
| (k + 1), n => R_iter k (reduced_collatz_step n)

@[simp]
lemma R_iter_succ (k n : ℕ) : R_iter (k + 1) n = R_iter k (reduced_collatz_step n) := rfl

@[simp]
lemma R_zero : reduced_collatz_step 0 = 1 := by
  simp [reduced_collatz_step]

@[simp]
lemma R_one : reduced_collatz_step 1 = 1 := by
  native_decide

lemma reduced_collatz_step_pos (n : ℕ) : reduced_collatz_step n ≥ 1 := by
  simp [reduced_collatz_step]
  exact Nat.ordCompl_pos 2 (by omega)

lemma R_pos (n i : ℕ) (hn : n ≥ 1) : R_iter i n ≥ 1 := by
  induction i generalizing n with
  | zero => exact hn
  | succ i ih => exact ih _ (reduced_collatz_step_pos n)

lemma reduced_collatz_step_odd (n : ℕ) : reduced_collatz_step n % 2 = 1 := by
  simp only [reduced_collatz_step]
  have h := Nat.coprime_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  rwa [Nat.coprime_two_left, Nat.odd_iff] at h

lemma R_odd (n i : ℕ) (hi : i ≥ 1) : R_iter i n % 2 = 1 := by
  induction i generalizing n with
  | zero => omega
  | succ i ih =>
    simp only [R_iter]
    rcases Nat.eq_zero_or_pos i with rfl | hi'
    · exact reduced_collatz_step_odd n
    · exact ih _ (by omega)

lemma reduced_collatz_step_iff_mod4 (n : ℕ) (hn: 0 < n) :
    reduced_collatz_step n > n ↔ n % 4 = 3 := by
  sorry

lemma not_exists_R_with_m_div3 (m : ℕ) (hdiv3: m % 3 = 0) :
    ¬ ∃ n : ℕ, reduced_collatz_step n = m := by
  intro ⟨n, hn⟩
  have h3 : 3 ∣ m := Nat.dvd_of_mod_eq_zero hdiv3
  rw [← hn] at h3
  simp only [reduced_collatz_step] at h3
  have : 3 ∣ (3 * n + 1) := dvd_trans h3 (Nat.ordCompl_dvd (3 * n + 1) 2)
  omega

private lemma ordCompl_two_mul_pow (k m : ℕ) (hm_odd : m % 2 = 1) :
    ordCompl[2] (2^k * m) = m := by
  show 2^k * m / 2 ^ (2^k * m).factorization 2 = m
  have hcoprime : Nat.Coprime (2^k) m :=
    Nat.Coprime.pow_left k (by rwa [Nat.coprime_two_left, Nat.odd_iff])
  rw [Nat.factorization_mul_of_coprime hcoprime, Finsupp.coe_add, Pi.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_apply, if_pos rfl,
      Nat.factorization_eq_zero_of_not_dvd (by omega)]
  simp [Nat.mul_div_cancel_left _ (by positivity : (2:ℕ)^k > 0)]

lemma exists_R_with_m_not_div3 (m : ℕ) (hpos: m > 0) (hodd : m % 2 = 1) (hdiv3: m % 3 ≠ 0) :
    ∃ n : ℕ, reduced_collatz_step n = m ∧ n % 2 = 1 ∧ n > 1 := by
  obtain rfl | hm : m = 1 ∨ m > 1 := by omega
  · exact ⟨5, by native_decide, by decide, by decide⟩
  obtain h | h : m % 3 = 1 ∨ m % 3 = 2 := by omega
  · exact ⟨(4 * m - 1) / 3, by change ordCompl[2] _ = m; rw [show 3 * _ + 1 = 2^2 * m by omega,
      ordCompl_two_mul_pow 2 _ hodd], by omega, by omega⟩
  · exact ⟨(2 * m - 1) / 3, by change ordCompl[2] _ = m; rw [show 3 * _ + 1 = 2^1 * m by omega,
      ordCompl_two_mul_pow 1 _ hodd], by omega, by omega⟩

private lemma ordCompl_two_pow_mul (k x : ℕ) (hx : x ≠ 0) :
    ordCompl[2] (2^k * x) = ordCompl[2] x := by
  show 2^k * x / 2 ^ (2^k * x).factorization 2 = x / 2 ^ x.factorization 2
  have h4ne : 2^k ≠ 0 := by positivity
  rw [Nat.factorization_mul h4ne hx, Finsupp.coe_add, Pi.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_apply, if_pos rfl,
      pow_add, Nat.mul_div_mul_left _ _ (by positivity : (2:ℕ)^k > 0)]

lemma R_4n_add_1 (n : ℕ) (h_gt1 : n > 1) :
    reduced_collatz_step (4 * n + 1) = reduced_collatz_step n := by
  simp only [reduced_collatz_step]
  rw [show 3 * (4 * n + 1) + 1 = 4 * (3 * n + 1) from by ring,
      show (4 : ℕ) = 2^2 from rfl]
  exact ordCompl_two_pow_mul 2 (3 * n + 1) (by omega)

lemma R_iter_4n_add_1 (n i : ℕ) (hi : i > 0) (hn : n > 1) :
    R_iter i (4 * n + 1) = R_iter i n := by
  cases i with | zero => contradiction | succ i => exact congrArg (R_iter i) (R_4n_add_1 n hn)

/--
A "primitive" for step count `i` is an odd number `n` that reaches 1 in `i` steps,
but is not the child of another *odd* number `k` (via `4k+1`) that also reaches 1 in `i` steps.

Since the "Odd Step" count is preserved between `k` and `4k+1` only when `k` is odd,
we explicitly require the predecessor to be odd.
-/
def IsPrimitive4x1 (n i : ℕ) : Prop :=
  R_iter i n = 1 ∧
  i > 1 ∧
  n > 1 ∧
  n % 2 = 1 ∧
  ∀ k, k % 2 = 1 → 4 * k + 1 = n → ¬ R_iter i k = 1

/--
Lemma: The definition of a primitive simplifies to a modular arithmetic check.
If `n` is odd and has step count `i`, it is primitive if and only if `n % 8 ≠ 5` or `n = 5`.
-/
lemma is_primitive_iff_mod_8_ne_5 (n i : ℕ) (h_odd : n % 2 = 1) (hi: i > 1) (hn: n > 1)
    (h_steps : R_iter i n = 1) (h_ne5 : n ≠ 5) :
    IsPrimitive4x1 n i ↔ n % 8 ≠ 5 := by
  unfold IsPrimitive4x1
  simp only [h_steps, hi, hn, h_odd, true_and]
  constructor
  · intro h h_mod8
    obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
    have hk_gt : 2 * k + 1 > 1 := by omega
    have step2 : R_iter i (2 * k + 1) = 1 := by
      have := R_iter_4n_add_1 (2 * k + 1) i (by omega) hk_gt
      rw [show 4 * (2 * k + 1) + 1 = 8 * k + 5 by omega] at this
      rwa [← this]
    exact h (2 * k + 1) (by omega) (by omega) step2
  · intro h_mod8 k hk_odd hk_eq hk_steps
    have : n % 8 = 5 := by
      subst hk_eq
      obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      have : 4 * (2 * m + 1) + 1 = 8 * m + 5 := by omega
      rw [this]
      omega
    omega

lemma primitive_ancestor (x : ℕ) (hx_odd : x % 2 = 1) (hx_gt1 : x > 1)
    (hx_rcs : reduced_collatz_step x ≠ 1) :
    ∃ n : ℕ, reduced_collatz_step n = reduced_collatz_step x ∧ n % 2 = 1 ∧ n > 1 ∧ n % 8 ≠ 5 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases h_x5 : x % 8 = 5
    · obtain ⟨k, rfl⟩ : ∃ k, x = 8 * k + 5 := ⟨x / 8, by omega⟩
      have h_step : reduced_collatz_step (8 * k + 5) = reduced_collatz_step (2 * k + 1) := by
        have hk_gt : 2 * k + 1 > 1 := by
          by_contra h
          have : k = 0 := by omega
          subst this
          exact absurd (by native_decide : reduced_collatz_step 5 = 1) hx_rcs
        have := R_4n_add_1 (2 * k + 1) hk_gt
        rw [show 4 * (2 * k + 1) + 1 = 8 * k + 5 by omega] at this
        exact this
      have hk_odd : (2 * k + 1) % 2 = 1 := by omega
      have hk_gt : 2 * k + 1 > 1 := by
        by_contra h
        have : k = 0 := by omega
        subst this
        exact absurd (by native_decide : reduced_collatz_step 5 = 1) hx_rcs
      have hk_rcs : reduced_collatz_step (2 * k + 1) ≠ 1 := h_step ▸ hx_rcs
      have h_lt : 2 * k + 1 < 8 * k + 5 := by omega
      obtain ⟨n, hn_step, hn_odd, hn_gt1, hn_mod⟩ := ih (2 * k + 1) h_lt hk_odd hk_gt hk_rcs
      exact ⟨n, hn_step.trans h_step.symm, hn_odd, hn_gt1, hn_mod⟩
    · exact ⟨x, rfl, hx_odd, hx_gt1, h_x5⟩

/--
Every odd number `y` (not div 3) at level `m` generates a Primitive at level `m+1`.
-/
lemma odd_node_generates_primitive (y i : ℕ)
  (h_steps : R_iter i y = 1)
  (h_odd : y % 2 = 1)
  (h_not_div3 : y % 3 ≠ 0)
  (h_y_gt1 : y > 1) :
  ∃ n, IsPrimitive4x1 n (i + 1) ∧ reduced_collatz_step n = y := by
  have y_pos : y > 0 := by omega
  obtain ⟨x, hx_step, hx_odd, hx_gt1⟩ := exists_R_with_m_not_div3 y y_pos h_odd h_not_div3
  have hi : i ≥ 1 := by
    rcases i with _ | i
    · simp [R_iter] at h_steps; omega
    · omega
  have hx_rcs : reduced_collatz_step x ≠ 1 := by rw [hx_step]; omega
  obtain ⟨n, hn_step, hn_odd, hn_gt1, hn_mod⟩ := primitive_ancestor x hx_odd hx_gt1 hx_rcs
  use n
  have hn_ne5 : n ≠ 5 := by intro h; subst h; revert hn_mod; decide
  have h_steps_n : R_iter (i + 1) n = 1 := by
    rw [R_iter_succ, hn_step, hx_step, h_steps]
  exact ⟨(is_primitive_iff_mod_8_ne_5 n (i + 1) hn_odd (by omega) hn_gt1 h_steps_n hn_ne5).mpr hn_mod,
         hn_step.trans hx_step⟩

def reduce4x1 (n : ℕ) : ℕ :=
  if n % 8 = 5 then
    reduce4x1 ((n - 1) / 4)
  else
    n
termination_by n
decreasing_by
  have : n % 8 = 5 := by assumption
  omega

lemma rcs_reduce4x1 (n : ℕ) :
    reduced_collatz_step (reduce4x1 n) = reduced_collatz_step n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold reduce4x1
    split
    · rename_i h5
      obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
      have h_div : (8 * k + 5 - 1) / 4 = 2 * k + 1 := by omega
      rw [h_div]
      rw [ih (2 * k + 1) (by omega)]
      by_cases hk : k = 0
      · subst hk; native_decide
      · have hk_gt : 2 * k + 1 > 1 := by omega
        have := R_4n_add_1 (2 * k + 1) hk_gt
        rw [show 4 * (2 * k + 1) + 1 = 8 * k + 5 by omega] at this
        exact this.symm
    · rfl

/-- Primitives at level m+1 generated by different odd numbers at level m are distinct. -/
lemma primitives_from_distinct_generators_ne
    (x₁ x₂ y₁ y₂ : ℕ)
    (hx₁_rcs : reduced_collatz_step x₁ = y₁)
    (hx₂_rcs : reduced_collatz_step x₂ = y₂)
    (hy_ne : y₁ ≠ y₂) : reduce4x1 x₁ ≠ reduce4x1 x₂ := by
  intro h
  apply hy_ne
  rw [← hx₁_rcs, ← hx₂_rcs, ← rcs_reduce4x1 x₁, ← rcs_reduce4x1 x₂, h]

lemma rcs_ge (n : ℕ) (h_odd : n % 2 = 1) :
    2 * reduced_collatz_step n ≤ 3 * n + 1 := by
  have h_dvd : reduced_collatz_step n ∣ (3 * n + 1) :=
    Nat.ordCompl_dvd (3 * n + 1) 2
  obtain ⟨q, hq⟩ := h_dvd
  have h_rcs_odd := reduced_collatz_step_odd n
  have h_pos := reduced_collatz_step_pos n
  have h_even : (3 * n + 1) % 2 = 0 := by omega
  have hq_ge2 : q ≥ 2 := by
    rcases q with _ | _ | q
    · omega
    · rw [Nat.mul_one] at hq; omega
    · omega
  nlinarith

/-- From any seed at level `m`, produce an arbitrarily large number at level `m`
    that is odd, `> 1`, and not divisible by 3. -/
lemma exists_large_not_div3_from_seed (m : ℕ) (hm : m ≥ 1) (y₀ : ℕ)
    (hy₀_iter : R_iter m y₀ = 1) (hy₀_odd : y₀ % 2 = 1) (hy₀_gt1 : y₀ > 1) (B : ℕ) :
    ∃ y, y > B ∧ R_iter m y = 1 ∧ y % 2 = 1 ∧ y > 1 ∧ y % 3 ≠ 0 := by
  have h_large : ∃ y, y > B ∧ R_iter m y = 1 ∧ y % 2 = 1 ∧ y > 1 := by
    induction B with
    | zero => exact ⟨y₀, by omega, hy₀_iter, hy₀_odd, hy₀_gt1⟩
    | succ B ih =>
      obtain ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1⟩ := ih
      exact ⟨4 * y + 1, by omega,
        by rwa [R_iter_4n_add_1 y m (by omega) hy_gt1], by omega, by omega⟩
  obtain ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1⟩ := h_large
  by_cases h3 : y % 3 = 0
  · exact ⟨4 * y + 1, by omega,
      by rwa [R_iter_4n_add_1 y m (by omega) hy_gt1], by omega, by omega, by omega⟩
  · exact ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1, h3⟩

/--
For every level `m`, there are infinitely many primitive numbers.
-/
lemma infinite_primitives (m : ℕ) (h2le: 2 ≤ m) : ∀ B, ∃ n, n > B ∧ IsPrimitive4x1 n m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  clear h2le
  induction k with
  | zero =>
    intro B
    obtain ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1, hy_not3⟩ :=
      exists_large_not_div3_from_seed 1 (by omega) 5
        (by native_decide) (by decide) (by omega) (2 * B + 2)
    obtain ⟨n, hn_prim, hn_rcs⟩ :=
      odd_node_generates_primitive y 1 hy_iter hy_odd hy_not3 hy_gt1
    have h_bound := rcs_ge n
    rw [hn_rcs] at h_bound
    exact ⟨n, by omega, hn_prim⟩
  | succ k ih =>
    intro B
    obtain ⟨p, _, hp_prim⟩ := ih 0
    obtain ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1, hy_not3⟩ :=
      exists_large_not_div3_from_seed (k + 2) (by omega) p
        hp_prim.1 hp_prim.2.2.2.1 hp_prim.2.2.1 (2 * B + 2)
    obtain ⟨n, hn_prim, hn_rcs⟩ :=
      odd_node_generates_primitive y (k + 2) hy_iter hy_odd hy_not3 hy_gt1
    have h_bound := rcs_ge n
    rw [hn_rcs] at h_bound
    exact ⟨n, by omega, hn_prim⟩

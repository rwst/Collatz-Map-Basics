import Mathlib
import CollatzMapBasics.Basic

namespace CollatzMapBasics

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


lemma not_exists_R_with_m_div3 (m : ℕ) (hdiv3: m % 3 = 0) :
    ¬ ∃ n : ℕ, reduced_collatz_step n = m := by
  intro ⟨n, hn⟩
  have h3 : 3 ∣ m := Nat.dvd_of_mod_eq_zero hdiv3
  rw [← hn] at h3
  simp only [reduced_collatz_step] at h3
  have : 3 ∣ (3 * n + 1) := dvd_trans h3 (Nat.ordCompl_dvd (3 * n + 1) 2)
  omega

lemma exists_R_with_m_not_div3 (m : ℕ) (hpos: m > 0) (hodd : m % 2 = 1) (hdiv3: m % 3 ≠ 0) :
    ∃ n : ℕ, reduced_collatz_step n = m ∧ n % 2 = 1 ∧ n > 1 := by
  obtain rfl | hm : m = 1 ∨ m > 1 := by omega
  · exact ⟨5, by native_decide, by decide, by decide⟩
  obtain h | h : m % 3 = 1 ∨ m % 3 = 2 := by omega
  · exact ⟨(4 * m - 1) / 3, by change ordCompl[2] _ = m; rw [show 3 * _ + 1 = 2^2 * m by omega,
      ordCompl_two_mul_pow 2 _ hodd], by omega, by omega⟩
  · exact ⟨(2 * m - 1) / 3, by change ordCompl[2] _ = m; rw [show 3 * _ + 1 = 2^1 * m by omega,
      ordCompl_two_mul_pow 1 _ hodd], by omega, by omega⟩

lemma reduced_collatz_step_iff_mod4 (n : ℕ) (hn: 0 < n) (h_odd : n % 2 = 1) :
    reduced_collatz_step n > n ↔ n % 4 = 3 := by
  constructor
  · intro h_gt
    have h14 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases h14 with h1 | h3
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
      simp only [reduced_collatz_step] at h_gt
      rw [show 3 * (4 * k + 1) + 1 = 2 ^ 2 * (3 * k + 1) from by ring,
          ordCompl_two_pow_mul 2 (3 * k + 1)] at h_gt
      have : ordCompl[2] (3 * k + 1) ≤ 3 * k + 1 :=
        Nat.le_of_dvd (by omega) (Nat.ordCompl_dvd (3 * k + 1) 2)
      omega
    · exact h3
  · intro h_mod4
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
    simp only [reduced_collatz_step]
    rw [show 3 * (4 * k + 3) + 1 = 2 ^ 1 * (6 * k + 5) from by ring,
        ordCompl_two_mul_pow 1 (6 * k + 5) (by omega)]
    omega

private lemma collatz_step_even (n : ℕ) (h : n % 2 = 0) : collatz_step n = n / 2 := by
  unfold collatz_step
  have htrue : (n % 2 == 0) = true := by
    apply beq_iff_eq.mpr
    omega
  simp [htrue]

private lemma collatz_iter_even_div_two_pow (n d : ℕ) (h_dvd : 2^d ∣ n) : collatz_iter d n = n / 2^d := by
  obtain ⟨k, rfl⟩ := h_dvd
  rw [collatz_iter_two_pow_mul d k, Nat.mul_div_cancel_left _ (by positivity)]

/-- If `n > 0` and `n` is odd, then $R(n) = m$ implies there is some $i \ge 1$ such that $C^i(n) = m$. -/
lemma reduced_collatz_step_implies_collatz_iter (n m : ℕ) (h_odd : n % 2 = 1)
    (hR : reduced_collatz_step n = m) :
    ∃ i ≥ 1, collatz_iter i n = m := by
  set k := (3 * n + 1).factorization 2
  have h_decomp : 3 * n + 1 = 2^k * m := by
    calc 3 * n + 1 = 2^k * ordCompl[2] (3 * n + 1) := (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm
    _ = 2^k * m := by rw [←hR]; rfl
  have hm_odd : m % 2 = 1 := hR ▸ reduced_collatz_step_odd n
  have hk_pos : k ≥ 1 := by
    by_contra hk
    have : (3 * n + 1) % 2 = m % 2 := by rw [h_decomp, show k = 0 by omega]; ring_nf
    omega
  use (k + 1), (by omega)
  calc collatz_iter (k + 1) n = collatz_iter k (collatz_step n) := rfl
  _ = collatz_iter k (3 * n + 1) := by rw [collatz_step_odd n h_odd]
  _ = collatz_iter k (2^k * m) := by rw [h_decomp]
  _ = m := collatz_iter_two_pow_mul k m

lemma reduced_collatz_iter_implies_collatz_iter (n m : ℕ) (h_odd : n % 2 = 1) (k : ℕ)
    (hR : R_iter k n = m) :
    ∃ i ≥ k, collatz_iter i n = m := by
  induction k generalizing n with
  | zero => exact ⟨0, by omega, by simp [R_iter] at hR; simp [hR, collatz_iter]⟩
  | succ k ih =>
    obtain ⟨i, hi, h_iter⟩ := ih (reduced_collatz_step n) (reduced_collatz_step_odd n) hR
    obtain ⟨j, hj, h_step⟩ := reduced_collatz_step_implies_collatz_iter n _ h_odd rfl
    exact ⟨i + j, by omega, by rw [collatz_iter_add, h_step, h_iter]⟩

def count_odds : ℕ → ℕ → ℕ
| 0, _ => 0
| d + 1, n => count_odds d n + if collatz_iter d n % 2 = 1 then 1 else 0

private lemma count_odds_pos (d n : ℕ) (hd : d > 0) (hn_odd : n % 2 = 1) : count_odds d n > 0 := by
  induction d with
  | zero => contradiction
  | succ d ih =>
    unfold count_odds
    by_cases hd0 : d = 0
    · subst hd0
      unfold count_odds
      have h0 : collatz_iter 0 n = n := rfl
      rw [h0, if_pos hn_odd]
      omega
    · have h_pos : d > 0 := by omega
      have : count_odds d n > 0 := ih h_pos
      omega

private lemma collatz_iter_succ_right (d n : ℕ) : collatz_iter (d + 1) n = collatz_step (collatz_iter d n) := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    calc collatz_iter (d + 2) n = collatz_iter (d + 1) (collatz_step n) := rfl
    _ = collatz_step (collatz_iter d (collatz_step n)) := ih (collatz_step n)
    _ = collatz_step (collatz_iter (d + 1) n) := rfl

private lemma R_iter_succ_right (k n : ℕ) : R_iter (k + 1) n = reduced_collatz_step (R_iter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    calc R_iter (k + 2) n = R_iter (k + 1) (reduced_collatz_step n) := rfl
    _ = reduced_collatz_step (R_iter k (reduced_collatz_step n)) := ih (reduced_collatz_step n)
    _ = reduced_collatz_step (R_iter (k + 1) n) := rfl

lemma ordCompl_collatz_iter (d n : ℕ) (hn_odd : n % 2 = 1) :
    ordCompl[2] (collatz_iter d n) = R_iter (count_odds d n) n := by
  induction d with
  | zero =>
    simp [count_odds, collatz_iter]
    exact (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr (by omega))
  | succ d ih =>
    rw [collatz_iter_succ_right]
    unfold count_odds
    by_cases h_odd : collatz_iter d n % 2 = 1
    · rw [collatz_step_odd _ h_odd, if_pos h_odd, R_iter_succ_right, ←ih]
      have : ordCompl[2] (collatz_iter d n) = collatz_iter d n :=
        (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (Or.inr (by omega))
      rw [this]
      rfl
    · have h_even : collatz_iter d n % 2 = 0 := by omega
      rw [collatz_step_even _ h_even, if_neg (by omega), add_zero]
      rw [ordCompl_two_div_two _ h_even]
      exact ih

lemma collatz_cycle_iff_reduced_collatz_cycle (n : ℕ) (h_odd : n % 2 = 1) :
    (∃ k > 0, collatz_iter k n = n) ↔ (∃ k > 0, R_iter k n = n) := by
  constructor
  · rintro ⟨k, hk, hcycle⟩
    use count_odds k n, count_odds_pos k n hk h_odd
    have h_ord := ordCompl_collatz_iter k n h_odd
    rw [hcycle] at h_ord
    have h_self : ordCompl[2] n = n :=
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr (by omega))
    rw [h_self] at h_ord
    exact h_ord.symm
  · rintro ⟨k, hk, hcycle⟩
    obtain ⟨i, hi, hiter⟩ := reduced_collatz_iter_implies_collatz_iter n n h_odd k hcycle
    exact ⟨i, by omega, hiter⟩

lemma collatz_bounded_iff_reduced_collatz_bounded (n : ℕ) (h_odd : n % 2 = 1) :
    (∃ B, ∀ k, collatz_iter k n ≤ B) ↔ (∃ B, ∀ k, R_iter k n ≤ B) := by
  constructor
  · exact fun ⟨B, hB⟩ ↦ ⟨B, fun k ↦ by
      obtain ⟨i, _, h_eq⟩ := reduced_collatz_iter_implies_collatz_iter n _ h_odd k rfl
      exact h_eq ▸ hB i⟩
  · rintro ⟨B, hB⟩
    refine ⟨max n (3 * B + 1), fun d ↦ ?_⟩
    induction d with
    | zero => exact le_max_left _ _
    | succ d ih =>
      rw [collatz_iter_succ_right]
      by_cases h_even : collatz_iter d n % 2 = 0
      · rw [collatz_step_even _ h_even]
        exact (Nat.div_le_self _ _).trans ih
      · have h_odd2 : collatz_iter d n % 2 = 1 := by omega
        rw [collatz_step_odd _ h_odd2]
        have h_ord := ordCompl_collatz_iter d n h_odd
        have h_self : ordCompl[2] (collatz_iter d n) = collatz_iter d n :=
          (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (Or.inr (by omega))
        rw [h_self] at h_ord
        have hd_le_B : collatz_iter d n ≤ B := h_ord ▸ hB _
        exact (by omega : 3 * collatz_iter d n + 1 ≤ 3 * B + 1).trans (le_max_right _ _)

lemma R_4n_add_1 (n : ℕ) :
    reduced_collatz_step (4 * n + 1) = reduced_collatz_step n := by
  simp only [reduced_collatz_step]
  rw [show 3 * (4 * n + 1) + 1 = 4 * (3 * n + 1) from by ring,
      show (4 : ℕ) = 2^2 from rfl]
  exact ordCompl_two_pow_mul 2 (3 * n + 1)

lemma R_iter_4n_add_1 (n i : ℕ) (hi : i > 0) :
    R_iter i (4 * n + 1) = R_iter i n := by
  cases i with | zero => contradiction | succ i => exact congrArg (R_iter i) (R_4n_add_1 n)

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
    (h_steps : R_iter i n = 1) (_h_ne5 : n ≠ 5) :
    IsPrimitive4x1 n i ↔ n % 8 ≠ 5 := by
  unfold IsPrimitive4x1
  simp only [h_steps, hi, hn, h_odd, true_and]
  constructor
  · intro h h_mod8
    have h_eq : 4 * (2 * (n / 8) + 1) + 1 = n := by omega
    have step2 : R_iter i (2 * (n / 8) + 1) = 1 := by
      have := R_iter_4n_add_1 (2 * (n / 8) + 1) i (by omega)
      rw [h_eq] at this
      exact this.symm.trans h_steps
    exact h (2 * (n / 8) + 1) (by omega) h_eq step2
  · intro h_mod8 k _ hk_eq _
    have : k = 2 * (k / 2) + 1 := by omega
    have : n % 8 = 5 := by omega
    omega

lemma primitive_ancestor (x : ℕ) (hx_odd : x % 2 = 1) (hx_gt1 : x > 1)
    (hx_rcs : reduced_collatz_step x ≠ 1) :
    ∃ n : ℕ, reduced_collatz_step n = reduced_collatz_step x ∧ n % 2 = 1 ∧ n > 1 ∧ n % 8 ≠ 5 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases h_x5 : x % 8 = 5
    · have h_eq : x = 4 * (2 * (x / 8) + 1) + 1 := by omega
      have hk_gt : 2 * (x / 8) + 1 > 1 := by
        by_contra h
        have : x = 5 := by omega
        subst this
        exact absurd (by native_decide : reduced_collatz_step 5 = 1) hx_rcs
      have h_step : reduced_collatz_step x = reduced_collatz_step (2 * (x / 8) + 1) := by
        have := R_4n_add_1 (2 * (x / 8) + 1)
        rw [←h_eq] at this
        exact this
      obtain ⟨n, hn_step, hn_odd, hn_gt1, hn_mod⟩ :=
        ih (2 * (x / 8) + 1) (by omega) (by omega) hk_gt (h_step ▸ hx_rcs)
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
  exact ⟨n, (is_primitive_iff_mod_8_ne_5 n (i + 1) hn_odd (by omega) hn_gt1
    (by rw [R_iter_succ, hn_step, hx_step, h_steps]) (by intro h; subst h; revert hn_mod; decide)).mpr hn_mod,
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
        have := R_4n_add_1 (2 * k + 1)
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
        by rwa [R_iter_4n_add_1 y m (by omega)], by omega, by omega⟩
  obtain ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1⟩ := h_large
  by_cases h3 : y % 3 = 0
  · exact ⟨4 * y + 1, by omega,
      by rwa [R_iter_4n_add_1 y m (by omega)], by omega, by omega, by omega⟩
  · exact ⟨y, hy_gt, hy_iter, hy_odd, hy_gt1, h3⟩

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

/--
For every level `m`, there are infinitely many primitive numbers.
-/
lemma infinite_primitives (m : ℕ) (h2le: 2 ≤ m) : ∀ B, ∃ n, n > B ∧ IsPrimitive4x1 n m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  clear h2le
  induction k with
  | zero =>
    intro B
    have ⟨y, _, hy_iter, hy_odd, hy_gt1, hy_not3⟩ :=
      exists_large_not_div3_from_seed 1 (by omega) 5 (by native_decide) (by decide) (by omega) (2 * B + 2)
    have ⟨n, hn_prim, hn_rcs⟩ := odd_node_generates_primitive y 1 hy_iter hy_odd hy_not3 hy_gt1
    exact ⟨n, by have := rcs_ge n hn_prim.2.2.2.1; rw [hn_rcs] at this; omega, hn_prim⟩
  | succ k ih =>
    intro B
    have ⟨p, _, hp_prim⟩ := ih 0
    have ⟨y, _, hy_iter, hy_odd, hy_gt1, hy_not3⟩ :=
      exists_large_not_div3_from_seed (k + 2) (by omega) p hp_prim.1 hp_prim.2.2.2.1 hp_prim.2.2.1 (2 * B + 2)
    have ⟨n, hn_prim, hn_rcs⟩ := odd_node_generates_primitive y (k + 2) hy_iter hy_odd hy_not3 hy_gt1
    exact ⟨n, by have := rcs_ge n hn_prim.2.2.2.1; rw [hn_rcs] at this; omega, hn_prim⟩

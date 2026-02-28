import Mathlib

namespace CollatzMapBasics

open Classical

lemma parity_of_mod_pow_succ {k m n : ℕ} (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
    m % 2 = n % 2 := by
  have h1 : m % 2 ^ (k + 1) % 2 = m % 2 :=
    Nat.mod_mod_of_dvd m (dvd_pow_self 2 (Nat.succ_ne_zero k))
  have h2 : n % 2 ^ (k + 1) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (dvd_pow_self 2 (Nat.succ_ne_zero k))
  omega

lemma int_dvd_sub_of_mod_eq {a b c : ℕ} (h : a % c = b % c) :
    (c : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
  Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by exact_mod_cast h))

lemma nat_mod_eq_of_int_dvd_sub {a b c : ℕ} (h : (c : ℤ) ∣ ((a : ℤ) - (b : ℤ))) :
    a % c = b % c := by
  exact_mod_cast Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp h)

lemma coprime_pow_three_pow_two (s k : ℕ) : Nat.Coprime (3 ^ s) (2 ^ k) := by
  apply Nat.Coprime.pow; decide

lemma pow_two_mod_three (k : ℕ) (hk : k ≥ 1) : 2^k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      simp only [Nat.pow_succ]
      rw [Nat.mul_mod, ih hn']
      by_cases hparity : n % 2 = 0
      · simp only [hparity, ↓reduceIte]
        have : (n + 1) % 2 = 1 := by omega
        simp [this]
      · have hnodd : n % 2 = 1 := by omega
        simp only [hnodd]
        have : (n + 1) % 2 = 0 := by omega
        simp [this]


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

lemma X_congr {m n : ℕ} (h : m % 2 = n % 2) : X m = X n := by
  rw [X_eq_mod, X_eq_mod, h]

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

lemma T_one : T 1 = 2 := by rw [T_odd (by omega)]

lemma T_two : T 2 = 1 := by rw [T_even (by omega)]

lemma T_iter_one_cycle (j : ℕ) : T_iter j 1 = 1 ∨ T_iter j 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rcases ih with h | h <;> simp only [T_iter, h]
    · right; exact T_one
    · left; exact T_two

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

/-- The number of odd iterates among the first `k` steps starting from `n`. -/
def num_odd_steps (k n : ℕ) : ℕ :=
  (Finset.range k).sum (fun i => X (T_iter i n))

lemma num_odd_steps_le (j n : ℕ) : num_odd_steps j n ≤ j := by
  unfold num_odd_steps
  have h (i : ℕ) : X (T_iter i n) ≤ 1 := by rw [X_eq_mod]; omega
  refine (Finset.sum_le_card_nsmul (Finset.range j) (fun i => X (T_iter i n)) 1 (fun i _ => h i)).trans_eq (by simp)

lemma T_expand (m : ℕ) : 2 * T m = 3 ^ X m * m + X m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega), X_even (by omega)]; omega
  · rw [T_odd (by omega), X_odd (by omega)]; omega

lemma T_congr (k m n : ℕ) (h : m % 2 ^ (k + 1) = n % 2 ^ (k + 1)) :
    T m % 2 ^ k = T n % 2 ^ k := by
  have hparity := parity_of_mod_pow_succ h
  have hX : X m = X n := X_congr hparity
  have hTm := T_expand m
  have hTn := T_expand n
  rw [← hX] at hTn
  -- In ℤ: 2*(Tm - Tn) = 3^(Xm)*(m - n), and 2^(k+1) | (m - n)
  have h_dvd_mn : (2 ^ (k + 1) : ℤ) ∣ ((m : ℤ) - (n : ℤ)) := int_dvd_sub_of_mod_eq h
  have h_eq : (2 : ℤ) * ((T m : ℤ) - (T n : ℤ)) =
      (3 ^ X m : ℤ) * ((m : ℤ) - (n : ℤ)) := by
    have hTm' : (2 * T m : ℤ) = (3 ^ X m : ℤ) * m + (X m : ℤ) := by exact_mod_cast hTm
    have hTn' : (2 * T n : ℤ) = (3 ^ X m : ℤ) * n + (X m : ℤ) := by exact_mod_cast hTn
    linarith
  have h_dvd_final : (2 ^ k : ℤ) ∣ ((T m : ℤ) - (T n : ℤ)) := by
    have h2 : (2 ^ (k + 1) : ℤ) ∣ ((2 : ℤ) * ((T m : ℤ) - (T n : ℤ))) := h_eq ▸ dvd_mul_of_dvd_right h_dvd_mn _
    rwa [show (2 ^ (k + 1) : ℤ) = 2 * 2 ^ k from by ring,
         mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)] at h2
  exact nat_mod_eq_of_int_dvd_sub h_dvd_final

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

end CollatzMapBasics

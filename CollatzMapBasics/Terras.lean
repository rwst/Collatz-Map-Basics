import Mathlib
import CollatzMapBasics.Compact
import CollatzMapBasics.Garner

namespace CollatzMapBasics

open Classical

/-- `E_vec k n` is the parity vector `(X(n), X(T n), …, X(T^{k-1} n))` as a function `Fin k → ℕ`,
    where each entry is 0 or 1. -/
def E_vec (k : ℕ) (n : ℕ) : Fin k → ℕ :=
  fun i => X (T_iter i.val n)

@[simp]
lemma E_vec_apply (k n : ℕ) (i : Fin k) : E_vec k n i = X (T_iter i.val n) := rfl

lemma E_vec_le_one (k n : ℕ) (i : Fin k) : E_vec k n i ≤ 1 := by
  simp only [E_vec_apply, X_eq_mod]; omega

lemma num_odd_steps_eq_E_vec_sum (k n : ℕ) :
    num_odd_steps k n = Finset.sum Finset.univ (E_vec k n) := by
  simp [num_odd_steps, E_vec]; exact Finset.sum_range _

lemma X_congr {m n : ℕ} (h : m % 2 = n % 2) : X m = X n := by
  rw [X_eq_mod, X_eq_mod, h]

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

-- Backward direction: m % 2^k = n % 2^k → E_vec k m = E_vec k n
lemma terras_backward (k : ℕ) : ∀ m n : ℕ, m % 2 ^ k = n % 2 ^ k →
    E_vec k m = E_vec k n := by
  induction k with
  | zero => intro m n _; ext i; exact i.elim0
  | succ k ih =>
    intro m n h
    have hparity := parity_of_mod_pow_succ h
    have ih_applied := ih (T m) (T n) (T_congr k m n h)
    ext ⟨i, hi⟩
    cases i with
    | zero =>
      simp only [E_vec_apply, T_iter]
      exact X_congr hparity
    | succ i =>
      simp only [E_vec_apply, T_iter_succ_right]
      have hi' : i < k := by omega
      have := congr_fun ih_applied ⟨i, hi'⟩
      simpa [E_vec_apply] using this

lemma E_vec_restrict (k m n : ℕ) (h : E_vec (k + 1) m = E_vec (k + 1) n) :
    E_vec k m = E_vec k n := by
  ext ⟨i, hi⟩
  have := congr_fun h ⟨i, by omega⟩
  simpa [E_vec_apply] using this

lemma num_odd_steps_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    num_odd_steps k m = num_odd_steps k n := by
  simp only [num_odd_steps]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have := congr_fun h ⟨i, hi⟩
  simpa [E_vec_apply] using this

lemma garner_correction_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    garner_correction k m = garner_correction k n := by
  induction k with
  | zero => simp [garner_correction]
  | succ k ih =>
    simp only [garner_correction]
    have hk : E_vec k m = E_vec k n := E_vec_restrict k m n h
    have hXk : X (T_iter k m) = X (T_iter k n) := by
      have := congr_fun h ⟨k, lt_add_one k⟩
      simpa [E_vec_apply] using this
    rw [hXk, ih hk]

lemma coprime_pow_three_pow_two (s k : ℕ) : Nat.Coprime (3 ^ s) (2 ^ k) := by
  apply Nat.Coprime.pow; decide

-- Forward direction: E_vec k m = E_vec k n → m % 2^k = n % 2^k
lemma terras_forward (k m n : ℕ) (_hm : m ≥ 1) (_hn : n ≥ 1)
    (h : E_vec k m = E_vec k n) : m % 2 ^ k = n % 2 ^ k := by
  have hS := num_odd_steps_eq_of_E_vec_eq k m n h
  have hQ := garner_correction_eq_of_E_vec_eq k m n h
  have gm := garner_formula k m
  have gn := garner_formula k n
  rw [← hS, ← hQ] at gn
  set S := num_odd_steps k m
  set Q := garner_correction k m
  have h_eq : (3 ^ S : ℤ) * ((m : ℤ) - (n : ℤ)) =
      (2 ^ k : ℤ) * ((T_iter k m : ℤ) - (T_iter k n : ℤ)) := by
    have gm' : (2 ^ k * T_iter k m : ℤ) = (3 ^ S * m + Q : ℤ) := by exact_mod_cast gm
    have gn' : (2 ^ k * T_iter k n : ℤ) = (3 ^ S * n + Q : ℤ) := by exact_mod_cast gn
    linarith
  have h_dvd : (2 ^ k : ℤ) ∣ ((3 ^ S : ℤ) * ((m : ℤ) - (n : ℤ))) :=
    h_eq ▸ dvd_mul_of_dvd_left dvd_rfl _
  have h_dvd_mn : (2 ^ k : ℤ) ∣ ((m : ℤ) - (n : ℤ)) :=
    ((coprime_pow_three_pow_two S k).isCoprime.symm).dvd_of_dvd_mul_left h_dvd
  exact nat_mod_eq_of_int_dvd_sub h_dvd_mn

/-- **Terras periodicity theorem** [Ter76]. Two positive integers have the same parity vector
    `E_k` if and only if they are congruent modulo `2^k`. -/
theorem terras_periodicity (k : ℕ) (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    E_vec k m = E_vec k n ↔ m % 2 ^ k = n % 2 ^ k :=
  ⟨terras_forward k m n hm hn, terras_backward k m n⟩

/-- The coefficient stopping time `τ(n)` is the least `j ≥ 1` such that `C j n < 1`,
    or `⊤` if no such `j` exists. -/
noncomputable def coeff_stopping_time (n : ℕ) : ℕ∞ :=
  if h : ∃ j : ℕ, j ≥ 1 ∧ C j n < 1 then
    (Nat.find h : ℕ∞)
  else
    ⊤

end CollatzMapBasics

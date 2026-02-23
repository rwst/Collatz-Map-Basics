import Mathlib

namespace CollatzMapBasics

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

end CollatzMapBasics

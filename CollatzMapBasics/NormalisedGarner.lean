import CollatzMapBasics.Compact
import CollatzMapBasics.Garner
import CollatzMapBasics.Parity

namespace CollatzMapBasics

/-- The Garner correction ratio: `E j n = Q_j(n) / 2^j`. -/
def E (j n : ℕ) : ℚ := (garner_correction j n : ℚ) / (2 ^ j : ℚ)

lemma E_zero (n : ℕ) : E 0 n = 0 := by
  simp [E, garner_correction]

lemma E_succ (k n : ℕ) :
    E (k + 1) n = (3 ^ X (T_iter k n) : ℚ) / 2 * E k n +
      (X (T_iter k n) : ℚ) / 2 := by
  simp only [E, garner_correction]
  rw [show (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k from by ring]
  have h2k : (2 ^ k : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

lemma E_step_strict_mono (x : ℕ) (a b : ℚ) (hab : a < b) :
    (3 ^ x : ℚ) / 2 * a + (x : ℚ) / 2 < (3 ^ x : ℚ) / 2 * b + (x : ℚ) / 2 := by
  have h3 : (3 ^ x : ℚ) / 2 > 0 := by positivity
  nlinarith

end CollatzMapBasics

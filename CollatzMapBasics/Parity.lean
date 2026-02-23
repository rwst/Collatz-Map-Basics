import Mathlib
import CollatzMapBasics.Compact

namespace CollatzMapBasics

/-- Parity vectors are essentially binary words. We represent 0 as `false` and 1 as `true`. -/
def ParityVector := List Bool

deriving instance DecidableEq for ParityVector

instance : GetElem ParityVector ℕ Bool fun v i => i < v.length :=
  inferInstanceAs (GetElem (List Bool) ℕ Bool _)

namespace ParityVector

def toNat (b : Bool) : ℕ := if b then 1 else 0

/-- `q v` is the number of ones (true entries) in the parity vector `v`. -/
def q (v : ParityVector) : ℕ := v.count true

/-- The size (length) of a parity vector. -/
def size (v : ParityVector) : ℕ := v.length

/-- The ones-ratio `q / size` as a rational number. Returns 0 for the empty vector. -/
def onesRatio (v : ParityVector) : ℚ := (q v : ℚ) / (size v : ℚ)

/-- `V j n` is the parity vector of length `j` for the Collatz sequence starting at `n`. -/
def V (j n : ℕ) : ParityVector :=
  (List.finRange j).map (fun i => decide (X (T_iter i.val n) = 1))

@[simp]
lemma V_length (j n : ℕ) : (V j n).length = j := by
  simp [V]

lemma V_get (j n : ℕ) (i : Fin j) :
    (V j n).get ⟨i.val, by simp [V_length]⟩ = decide (X (T_iter i.val n) = 1) := by
  simp [V]


/-- The elementary precedence relation (swapping 01 to 10). -/
inductive ElementaryPrecedes : ParityVector → ParityVector → Prop
  | swap (w1 w2 : List Bool) :
      ElementaryPrecedes (w1 ++ [false, true] ++ w2) (w1 ++ [true, false] ++ w2)

/-- reflexive transitive closure of the elementary relation. -/
def Precedes (v1 v2 : ParityVector) : Prop :=
  Relation.ReflTransGen ElementaryPrecedes v1 v2

infix:50 " ≼ " => Precedes

end ParityVector

end CollatzMapBasics

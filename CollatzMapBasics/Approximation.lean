import Mathlib
import CollatzMapBasics.Basic

namespace CollatzMapBasics

/-- The irrational constant `log 2 / log 3`. -/
noncomputable def ξ : ℝ := Real.log 2 / Real.log 3

/-- The bound δ(ε) used in the inequality equivalence. -/
noncomputable def delta (ε : ℝ) : ℝ := -Real.log (1 - ε) / Real.log 3


/-- Helper to prove 2^b = 3^a over ℚ implies b = 0 -/
lemma rat_zpow_eq (a b : ℤ) (h : (2 : ℚ)^b = (3 : ℚ)^a) : b = 0 := by
  obtain ⟨a_nat, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · obtain ⟨b_nat, rfl | rfl⟩ := Int.eq_nat_or_neg b
    · simp only [zpow_natCast] at h
      rcases eq_or_ne b_nat 0 with rfl | hb
      · rfl
      · have he : Even (3 ^ a_nat) :=
          (by exact_mod_cast h : 2 ^ b_nat = 3 ^ a_nat) ▸ Even.pow_of_ne_zero (by decide) hb
        have ho : Odd (3 ^ a_nat) := Odd.pow (by decide)
        obtain ⟨k, hk⟩ := he
        obtain ⟨m, hm⟩ := ho
        omega
    · simp only [zpow_natCast, zpow_neg] at h
      have hh_nat : 2 ^ b_nat * 3 ^ a_nat = 1 := by
        exact_mod_cast (show (2 : ℚ) ^ b_nat * (3 : ℚ) ^ a_nat = 1 by
          rw [← h]; exact mul_inv_cancel₀ (by positivity))
      cases b_nat
      · rfl
      · rename_i n
        have : 2 * (2 ^ n * 3 ^ a_nat) = 1 := by
          calc 2 * (2 ^ n * 3 ^ a_nat) = 2 ^ (n + 1) * 3 ^ a_nat := by ring
            _ = 1 := hh_nat
        omega
  · obtain ⟨b_nat, rfl | rfl⟩ := Int.eq_nat_or_neg b
    · simp only [zpow_natCast, zpow_neg] at h
      have hh_nat : 3 ^ a_nat * 2 ^ b_nat = 1 := by
        exact_mod_cast (show (3 : ℚ) ^ a_nat * (2 : ℚ) ^ b_nat = 1 by
          rw [h]; exact mul_inv_cancel₀ (by positivity))
      cases b_nat
      · rfl
      · rename_i n
        have : 2 * (3 ^ a_nat * 2 ^ n) = 1 := by
          calc 2 * (3 ^ a_nat * 2 ^ n) = 3 ^ a_nat * 2 ^ (n + 1) := by ring
            _ = 1 := hh_nat
        omega
    · simp only [zpow_neg, inv_inj] at h
      rcases eq_or_ne b_nat 0 with rfl | hb
      · rfl
      · have he : Even (3 ^ a_nat) :=
          (by exact_mod_cast h : 2 ^ b_nat = 3 ^ a_nat) ▸ Even.pow_of_ne_zero (by decide) hb
        have ho : Odd (3 ^ a_nat) := Odd.pow (by decide)
        obtain ⟨k, hk⟩ := he
        obtain ⟨m, hm⟩ := ho
        omega

/-- Auxiliary Lemma 1: ξ is irrational. -/
lemma irrational_xi : Irrational ξ := by
  rw [ξ, irrational_iff_ne_rational]
  rintro a b hb h
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have h1 : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3 := by
    calc (b : ℝ) * Real.log 2 = (b : ℝ) * (Real.log 2 / Real.log 3) * Real.log 3 := by rw [mul_assoc, div_mul_cancel₀ _ hl3.ne']
      _ = (b : ℝ) * (a / b) * Real.log 3 := by rw [h]
      _ = (a : ℝ) * Real.log 3 := by rw [mul_div_cancel₀ _ hb']
  have eq2 : Real.log ((2 : ℝ) ^ b) = Real.log ((3 : ℝ) ^ a) := by
    rw [Real.log_zpow, Real.log_zpow, h1]
  have eq3 : (2 : ℝ) ^ b = (3 : ℝ) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) eq2
  have eq4 : ((2 : ℚ) ^ b : ℝ) = ((3 : ℚ) ^ a : ℝ) := by
    push_cast
    exact eq3
  exact hb (rat_zpow_eq a b (by exact_mod_cast eq4))

/-- Auxiliary Lemma 2: Equivalence of the original inequality and the rational approximation. -/
lemma inequality_equiv (a b : ℕ) (hb : 0 < b) (ε : ℝ) (hε₁ : ε < 1) :
    (1 - ε < (3 : ℝ)^a / (2 : ℝ)^b ∧ (3 : ℝ)^a / (2 : ℝ)^b < 1) ↔
    (0 < ξ - (a : ℝ) / (b : ℝ) ∧ ξ - (a : ℝ) / (b : ℝ) < delta ε / b) := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos3 : 0 < (3:ℝ)^a := by positivity
  have hpos2 : 0 < (2:ℝ)^b := by positivity
  rw [ξ, delta]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := Real.log_lt_log_iff (by linarith) (div_pos hpos3 hpos2) |>.mpr h1
    have h2' := Real.log_lt_log_iff (div_pos hpos3 hpos2) (by norm_num) |>.mpr h2
    rw [Real.log_div hpos3.ne' hpos2.ne', Real.log_pow, Real.log_pow] at h1' h2'
    rw [Real.log_one] at h2'
    have : (a : ℝ) * Real.log 3 < (b : ℝ) * Real.log 2 := by linarith
    have h2_bound : (b : ℝ) * Real.log 2 - (a : ℝ) * Real.log 3 < -Real.log (1 - ε) := by linarith
    constructor
    · field_simp [hlog3.ne', hb'.ne']
      linarith
    · field_simp [hlog3.ne', hb'.ne']
      linarith
  · rintro ⟨h1, h2⟩
    have h1_bound : (a : ℝ) * Real.log 3 < (b : ℝ) * Real.log 2 := by
      field_simp [hlog3.ne', hb'.ne'] at h1
      linarith
    have h2_bound : (b : ℝ) * Real.log 2 - (a : ℝ) * Real.log 3 < -Real.log (1 - ε) := by
      field_simp [hlog3.ne', hb'.ne'] at h2
      linarith
    constructor
    · apply Real.log_lt_log_iff (by linarith) (div_pos hpos3 hpos2) |>.mp
      rw [Real.log_div hpos3.ne' hpos2.ne', Real.log_pow, Real.log_pow]
      linarith
    · apply Real.log_lt_log_iff (div_pos hpos3 hpos2) (by norm_num) |>.mp
      rw [Real.log_one, Real.log_div hpos3.ne' hpos2.ne', Real.log_pow, Real.log_pow]
      linarith

/-- Helper: delta is positive when 0 < ε < 1 -/
lemma delta_pos (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) : 0 < delta ε := by
  unfold delta
  apply div_pos
  · rw [neg_pos]
    exact Real.log_neg (by linarith) (by linarith)
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 3)

/-- For any b, the pair (⌊ξ*b⌋, b) gives a good approximation from below. -/
lemma floor_approx_pos (b : ℕ) (hb : 0 < b) :
    0 < ξ - (Int.toNat ⌊ξ * ↑b⌋ : ℝ) / (↑b : ℝ) ∧
    ξ - (Int.toNat ⌊ξ * ↑b⌋ : ℝ) / (↑b : ℝ) < 1 / (↑b : ℝ) := by
  have hb_pos : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hξ_pos : (0 : ℝ) < ξ := by
    unfold ξ
    exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  -- ⌊ξ*b⌋ is non-negative since ξ > 0 and b > 0
  have hfloor_nn : 0 ≤ ⌊ξ * ↑b⌋ := Int.floor_nonneg.mpr (mul_nonneg hξ_pos.le hb_pos.le)
  have htonat : (Int.toNat ⌊ξ * ↑b⌋ : ℤ) = ⌊ξ * ↑b⌋ := Int.toNat_of_nonneg hfloor_nn
  have htonat_r : (Int.toNat ⌊ξ * ↑b⌋ : ℝ) = (⌊ξ * ↑b⌋ : ℝ) := by
    exact_mod_cast htonat
  rw [htonat_r]
  constructor
  · -- 0 < ξ - ⌊ξ*b⌋/b
    have hle : (⌊ξ * ↑b⌋ : ℝ) ≤ ξ * ↑b := Int.floor_le _
    have hne : (⌊ξ * ↑b⌋ : ℝ) ≠ ξ * ↑b := by
      intro h
      -- ξ * b is an integer, so ξ is rational
      have hrat : ξ = (⌊ξ * ↑b⌋ : ℝ) / (↑b : ℝ) := by
        field_simp; linarith
      exact irrational_xi ⟨(⌊ξ * (↑b : ℝ)⌋ : ℤ) / (↑b : ℤ), by push_cast; linarith⟩
    have hlt : (⌊ξ * ↑b⌋ : ℝ) < ξ * ↑b := lt_of_le_of_ne hle hne
    have : (⌊ξ * ↑b⌋ : ℝ) / ↑b < ξ := (div_lt_iff₀ hb_pos).mpr hlt
    linarith
  · -- ξ - ⌊ξ*b⌋/b < 1/b
    have hlt_add := Int.lt_floor_add_one (ξ * ↑b)
    -- ξ * b < ⌊ξ*b⌋ + 1, so ξ < (⌊ξ*b⌋ + 1) / b = ⌊ξ*b⌋/b + 1/b
    have : ξ < (⌊ξ * ↑b⌋ : ℝ) / ↑b + 1 / ↑b := by
      rw [← add_div]
      exact (lt_div_iff₀ hb_pos).mpr (by linarith)
    linarith

/-- The pair (⌊ξ*b⌋, b) has a > 0 for b ≥ 2. -/
lemma floor_mul_pos (b : ℕ) (hb : 2 ≤ b) :
    0 < Int.toNat ⌊ξ * ↑b⌋ := by
  have hξ_pos : (0 : ℝ) < ξ := by
    unfold ξ; exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hb_pos : (0 : ℝ) < (↑b : ℝ) := Nat.cast_pos.mpr (by omega)
  -- ξ * b ≥ ξ * 2 > 1 since ξ = log2/log3 and log 4 > log 3 (4 > 3)
  have hξ_bound : 1 < ξ * 2 := by
    unfold ξ
    rw [div_mul_eq_mul_div, one_lt_div (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
    calc Real.log 3 < Real.log 4 :=
          (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num)
    _ = Real.log (2 ^ 2) := by norm_num
    _ = 2 * Real.log 2 := Real.log_pow 2 2
    _ = Real.log 2 * 2 := mul_comm _ _
  have hprod : 1 ≤ ξ * ↑b := le_of_lt (by
    calc (1 : ℝ) < ξ * 2 := hξ_bound
    _ ≤ ξ * ↑b := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hb
      · exact hξ_pos.le)
  have hfloor_pos : 0 < ⌊ξ * ↑b⌋ := Int.floor_pos.mpr hprod
  omega

open GenContFract

lemma B_pos {v : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) < ((GenContFract.of v).contsAux (n + 1)).b := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Decidable.em ((GenContFract.of v).TerminatedAt n) with h | h
    · rcases Decidable.em (1 ≤ n) with hn1 | hn1
      · rw [GenContFract.contsAux_stable_step_of_terminated h]
        exact ih hn1
      · simp at hn1
        subst hn1
        have : (GenContFract.of v).TerminatedAt 0 := h
        rw [GenContFract.terminatedAt_iff_s_none] at this
        simp [GenContFract.contsAux, this]
    · calc (0 : ℝ) < Nat.fib (n + 2) := by exact_mod_cast (Nat.fib_pos.mpr (by omega))
      _ ≤ ((GenContFract.of v).contsAux (n + 2)).b :=
        GenContFract.fib_le_of_contsAux_b (Or.inr h)

lemma pB_nonneg {v : ℝ} (n : ℕ) :
    (0 : ℝ) ≤ ((GenContFract.of v).contsAux n).b :=
  GenContFract.zero_le_of_contsAux_b

lemma frac_lt_one_of_ifp {v : ℝ} (ifp : IntFractPair ℝ) (n : ℕ) (h : IntFractPair.stream v n = some ifp) :
    ifp.fr < 1 :=
  GenContFract.IntFractPair.nth_stream_fr_lt_one h

lemma frac_pos_of_ifp {v : ℝ} (ifp : IntFractPair ℝ) (n : ℕ) (h : IntFractPair.stream v n = some ifp) (h_irr : Irrational v) :
    0 < ifp.fr := by
  have h_nn : 0 ≤ ifp.fr := GenContFract.IntFractPair.nth_stream_fr_nonneg h
  have h_lt : ifp.fr < 1 := GenContFract.IntFractPair.nth_stream_fr_lt_one h
  rcases (lt_or_eq_of_le h_nn) with hlt | heq
  · exact hlt
  · exfalso
    have h0 : ifp.fr = 0 := heq.symm
    have hterm : IntFractPair.stream v (n + 1) = none := by
      simp [IntFractPair.stream, h, h0]
    have : (GenContFract.of v).TerminatedAt n := by
      rw [GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none]
      exact hterm
    have hterminates : (GenContFract.of v).Terminates := ⟨n, this⟩
    rw [GenContFract.terminates_iff_rat] at hterminates
    obtain ⟨q, hq⟩ := hterminates
    exact h_irr ⟨q, hq.symm⟩

noncomputable def convergent_pair (v : ℝ) (n : ℕ) : GenContFract.Pair ℚ :=
  Classical.choose (GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux v n)

lemma convergent_pair_spec (v : ℝ) (n : ℕ) :
    (GenContFract.of v).contsAux n = GenContFract.Pair.map Rat.cast (convergent_pair v n) :=
  Classical.choose_spec (GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux v n)

noncomputable def convergent_rat (v : ℝ) (n : ℕ) : ℚ :=
  (convergent_pair v (n + 1)).a / (convergent_pair v (n + 1)).b

lemma convergent_rat_eq (v : ℝ) (n : ℕ) : (convergent_rat v n : ℝ) = (GenContFract.of v).convs n := by
  convert congr_arg _ (convergent_pair_spec v (n + 1)) using 1
  rotate_right
  exact fun (p : GenContFract.Pair ℝ) => p.a / p.b
  · unfold convergent_rat
    rw [convergent_pair_spec]
    norm_num [GenContFract.Pair.map]
  · rw [← convergent_pair_spec]
    rfl

lemma convergent_pair_is_int (v : ℝ) (n : ℕ) :
    ∃ (num den : ℤ), (convergent_pair v n).a = num ∧ (convergent_pair v n).b = den := by
  have h_int_coeffs : ∀ m, ∃ (a_int b_int : ℤ), (GenContFract.of v).contsAux m = ⟨(a_int : ℝ), (b_int : ℝ)⟩ := by
    intro m
    induction' m using Nat.strong_induction_on with m ih
    rcases m with ( _ | _ | m' ) <;> simp_all [GenContFract.of, GenContFract.IntFractPair.seq1]
    · constructor
      · refine ⟨1, by norm_num⟩
      · refine ⟨0, by norm_num⟩
    · obtain ⟨a_int, b_int, h⟩ := ih (m' + 1) (by omega)
      obtain ⟨a_int', b_int', h'⟩ := ih m' (by omega)
      simp_all [GenContFract.contsAux]
      cases h'' : GenContFract.IntFractPair.stream v (m' + 1) <;> simp_all [GenContFract.nextConts]
      rename_i val
      unfold GenContFract.nextNum GenContFract.nextDen
      norm_cast
      exact ⟨⟨a_int' + val.b * a_int, by ring⟩, ⟨b_int' + val.b * b_int, by ring⟩⟩
  obtain ⟨a_int, b_int, h⟩ := h_int_coeffs n
  have := convergent_pair_spec v n
  rw [h] at this
  simp [GenContFract.Pair.map] at this
  exact ⟨a_int, b_int, by exact_mod_cast this.1.symm, by exact_mod_cast this.2.symm⟩

lemma den_le_dens (v : ℝ) (n : ℕ) (hdens_pos : 0 < (GenContFract.of v).dens n) : ((convergent_rat v n).den : ℝ) ≤ (GenContFract.of v).dens n := by
  obtain ⟨num, den, h_pair⟩ := convergent_pair_is_int v (n + 1)
  have h_convergent_rat : (convergent_rat v n : ℝ) = num / den := by
    unfold convergent_rat; aesop
  have h_den_eq : (den : ℝ) = (GenContFract.of v).dens n := by
    have := convergent_pair_spec v (n + 1)
    replace := congr_arg (fun (x : GenContFract.Pair ℝ) => x.b) this
    change ((GenContFract.of v).contsAux (n + 1)).b = (convergent_pair v (n + 1)).b at this
    have h2 : (convergent_pair v (n + 1)).b = ↑den := h_pair.2
    rw [h2] at this
    convert this.symm using 1
  have h_den_le : (convergent_rat v n).den ≤ den.natAbs := by
    have h_convergent_rat_def : convergent_rat v n = num / den := by
      exact_mod_cast h_convergent_rat
    rw [h_convergent_rat_def, div_eq_mul_inv]
    erw [Rat.mul_den]
    norm_num
    split_ifs with hsign <;> simp [Int.natAbs_mul]
    · have h_den_eq_zero_real : (den : ℝ) = 0 := by exact_mod_cast hsign
      rw [h_den_eq] at h_den_eq_zero_real
      linarith
    · exact Nat.div_le_self _ _
  convert h_den_le using 1
  rw [← h_den_eq, ← @Nat.cast_le ℝ]
  norm_num
  rw [abs_of_nonneg (by exact_mod_cast h_den_eq.symm ▸ hdens_pos |> le_of_lt)]

lemma dens_zero_val (v : ℝ) : (GenContFract.of v).dens 0 = 1 := rfl

lemma dens_pos (v : ℝ) (n : ℕ) : 0 < (GenContFract.of v).dens n := by
  cases n with
  | zero => rw [dens_zero_val]; norm_num
  | succ m => exact B_pos (m + 1) (Nat.succ_le_succ (Nat.zero_le _))

lemma convergent_rat_exists (v : ℝ) (n : ℕ) :
    ∃ q : ℚ, (q : ℝ) = (GenContFract.of v).convs n ∧ (q.den : ℝ) ≤ (GenContFract.of v).dens n :=
  ⟨convergent_rat v n, convergent_rat_eq v n, den_le_dens v n (dens_pos v n)⟩

lemma not_terminated (v : ℝ) (h_irr : Irrational v) (n : ℕ) : ¬(GenContFract.of v).TerminatedAt n :=
  fun h => (GenContFract.terminates_iff_rat (v := v) |>.mp ⟨n, h⟩).elim fun q hq => h_irr ⟨q, hq.symm⟩

lemma s_defined (v : ℝ) (h_irr : Irrational v) (n : ℕ) : (GenContFract.of v).s.get? n ≠ none := by
  have h := not_terminated v h_irr n
  unfold GenContFract.TerminatedAt Stream'.Seq.TerminatedAt at h
  exact h

lemma part_dens_ge_one (v : ℝ) (n : ℕ) {b : ℝ} (h : (GenContFract.of v).partDens.get? n = some b) : 1 ≤ b :=
  GenContFract.of_one_le_get?_partDen h

lemma dens_recurrence_val' (v : ℝ) (h_irr : Irrational v) (n : ℕ) :
    ∃ b : ℝ, (GenContFract.of v).partDens.get? (n + 1) = some b ∧
    (GenContFract.of v).dens (n + 2) = b * (GenContFract.of v).dens (n + 1) + (GenContFract.of v).dens n := by
      obtain ⟨gp, hgp⟩ : ∃ gp : GenContFract.Pair ℝ, (GenContFract.of v).s.get? (n + 1) = some gp :=
        Option.ne_none_iff_exists'.mp ( s_defined v h_irr _ )
      use gp.b
      simp_all [ GenContFract.partDens ]
      rw [ GenContFract.dens ]
      rw [ Stream'.map, Stream'.map, Stream'.map ]
      rw [ Stream'.get ]
      rw [ GenContFract.conts ]
      rw [ Stream'.get ]
      rw [ Stream'.tail, Stream'.tail ]
      rw [ Stream'.get ]
      rw [ GenContFract.contsAux ]
      simp [ GenContFract.nextConts ]
      simp [ GenContFract.nextDen ]
      rw [ GenContFract.of ] at *
      aesop

lemma dens_strict_mono (v : ℝ) (h_irr : Irrational v) (n : ℕ) (hn : 1 ≤ n) : (GenContFract.of v).dens n < (GenContFract.of v).dens (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => contradiction
    | 1 =>
      obtain ⟨b, hb1, hb2⟩ := dens_recurrence_val' v h_irr 0
      rw [hb2, dens_zero_val]
      have h_b : 1 ≤ b := part_dens_ge_one v 1 hb1
      have h_d1 : 0 < (GenContFract.of v).dens 1 := dens_pos v 1
      nlinarith
    | m + 2 =>
      obtain ⟨b, hb1, hb2⟩ := dens_recurrence_val' v h_irr (m + 1)
      rw [hb2]
      have h_b : 1 ≤ b := part_dens_ge_one v (m + 2) hb1
      have h_dm1 : 0 < (GenContFract.of v).dens (m + 1) := dens_pos v (m + 1)
      have h_dm2 : 0 < (GenContFract.of v).dens (m + 2) := dens_pos v (m + 2)
      nlinarith

lemma convs_even_lt_xi (n : ℕ) : (GenContFract.of ξ).convs (2 * n) < ξ := by
  have h_stream_some : ∃ ifp, GenContFract.IntFractPair.stream ξ (2 * n) = some ifp := by
    rcases n with _ | n'
    · exact ⟨GenContFract.IntFractPair.of ξ, rfl⟩
    · have h := not_terminated ξ irrational_xi (2 * n' + 1)
      have h2 : GenContFract.IntFractPair.stream ξ (2 * n' + 1 + 1) ≠ none := mt GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr h
      have h3 : GenContFract.IntFractPair.stream ξ (2 * (n' + 1)) ≠ none := by
        have : 2 * n' + 1 + 1 = 2 * (n' + 1) := by omega
        rwa [this] at h2
      rw [← Option.ne_none_iff_exists']
      exact h3
  obtain ⟨ifp, h_ifp⟩ := h_stream_some
  have h_not_term := not_terminated ξ irrational_xi (2 * n)
  have h_fr_ne_zero : ifp.fr ≠ 0 := by
    intro h_zero
    have h_stream_succ : GenContFract.IntFractPair.stream ξ (2 * n + 1) = none := by
      simp [GenContFract.IntFractPair.stream, h_ifp, h_zero]
    exact h_not_term (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr h_stream_succ)
  have h_eq := GenContFract.sub_convs_eq h_ifp
  have h_sub_pos : 0 < ξ - (GenContFract.of ξ).convs (2 * n) := by
    rw [h_eq]
    rw [if_neg h_fr_ne_zero]
    rw [show (-1 : ℝ) ^ (2 * n) = 1 from by simp]
    apply one_div_pos.mpr
    have hB : 0 < ((GenContFract.of ξ).contsAux (2 * n + 1)).b := dens_pos ξ (2 * n)
    have hpB : 0 ≤ ((GenContFract.of ξ).contsAux (2 * n)).b := GenContFract.zero_le_of_contsAux_b
    have h_fr_pos : 0 < ifp.fr⁻¹ := by
      have h1 : 0 ≤ ifp.fr := GenContFract.IntFractPair.nth_stream_fr_nonneg h_ifp
      have h2 : 0 < ifp.fr := lt_of_le_of_ne h1 h_fr_ne_zero.symm
      positivity
    positivity
  linarith

lemma tendsto_convs (v : ℝ) : Filter.Tendsto (fun n => (GenContFract.of v).convs n) Filter.atTop (nhds v) :=
  GenContFract.of_convergence v

lemma approximation_ineq (n : ℕ) (hn : 1 ≤ n) :
    |ξ - (GenContFract.of ξ).convs n| < 1 / ((GenContFract.of ξ).dens n) ^ 2 := by
  have h_dens_pos : 0 < (GenContFract.of ξ).dens n := dens_pos ξ n
  have h_mono : (GenContFract.of ξ).dens n < (GenContFract.of ξ).dens (n + 1) := dens_strict_mono ξ irrational_xi n hn
  have h_bound : |ξ - (GenContFract.of ξ).convs n| ≤ 1 / ((GenContFract.of ξ).dens n * (GenContFract.of ξ).dens (n + 1)) :=
    GenContFract.abs_sub_convs_le <| not_terminated ξ irrational_xi n
  have h_strict : 1 / ((GenContFract.of ξ).dens n * (GenContFract.of ξ).dens (n + 1)) < 1 / ((GenContFract.of ξ).dens n) ^ 2 := by
    rw [sq]
    exact one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  exact lt_of_le_of_lt h_bound h_strict

/-- There are infinitely many rationals below ξ with |ξ - q| < 1/q.den².
    This follows from the alternating nature of continued fraction convergents. -/
lemma infinite_rat_approx_from_below :
    {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  let f : ℕ → ℚ := fun k => Classical.choose (convergent_rat_exists ξ (2 * k + 2))
  have hf : ∀ k, (f k : ℝ) = (GenContFract.of ξ).convs (2 * k + 2) ∧ ((f k).den : ℝ) ≤ (GenContFract.of ξ).dens (2 * k + 2) :=
    fun k => Classical.choose_spec (convergent_rat_exists ξ (2 * k + 2))

  have hinS : ∀ k, f k ∈ {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2} := by
    intro k
    simp only [Set.mem_setOf_eq]
    constructor
    · rw [(hf k).1]
      have : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [this]
      exact convs_even_lt_xi (k + 1)
    · have h_approx := approximation_ineq (2 * k + 2) (by omega)
      rw [← (hf k).1] at h_approx
      refine lt_of_lt_of_le h_approx ?_
      apply one_div_le_one_div_of_le
      · have : (0 : ℝ) < (f k).den := Nat.cast_pos.mpr (f k).pos
        exact sq_pos_of_pos this
      · apply sq_le_sq.mpr
        have h1 : 0 ≤ ((f k).den : ℝ) := Nat.cast_nonneg _
        have h2 : 0 ≤ (GenContFract.of ξ).dens (2 * k + 2) := le_of_lt (dens_pos ξ (2 * k + 2))
        rw [abs_of_nonneg h1, abs_of_nonneg h2]
        exact (hf k).2

  have htendsto : Filter.Tendsto (fun k => (f k : ℝ)) Filter.atTop (nhds ξ) := by
    have h1 : Filter.Tendsto (fun k => (GenContFract.of ξ).convs (2 * k + 2)) Filter.atTop (nhds ξ) :=
      Filter.Tendsto.comp (tendsto_convs ξ) (Filter.tendsto_atTop_mono (fun k => by linarith : ∀ k, k ≤ 2 * k + 2) Filter.tendsto_id)
    convert h1 using 1
    ext k
    exact (hf k).1

  have hnotconst : ¬ ∃ q : ℚ, ∀ᶠ k in Filter.atTop, f k = q := by
    rintro ⟨q, hq⟩
    have h2 : Filter.Tendsto (fun k => (f k : ℝ)) Filter.atTop (nhds (q : ℝ)) := by
      have ht : Filter.Tendsto (fun (_ : ℕ) => (q : ℝ)) Filter.atTop (nhds (q : ℝ)) := tendsto_const_nhds
      apply Filter.Tendsto.congr' _ ht
      filter_upwards [hq] with k hk
      exact congrArg Rat.cast hk.symm
    have heq : ξ = (q : ℝ) := tendsto_nhds_unique htendsto h2
    exact irrational_xi ⟨q, heq.symm⟩

  contrapose! hnotconst
  have h_finite : {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Finite := hnotconst
  have h_image_finite : (Set.range (fun n => (f n : ℝ))).Finite := by
    have h_sub : Set.range f ⊆ {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2} := by
      rintro x ⟨n, rfl⟩
      exact hinS n
    have h_finite_range : (Set.range f).Finite := Set.Finite.subset h_finite h_sub
    have hr : (Set.range (fun n => (f n : ℝ))) = (fun q : ℚ => (q : ℝ)) '' (Set.range f) := Set.range_comp _ _
    rw [hr]
    exact Set.Finite.image (fun q : ℚ => (q : ℝ)) h_finite_range
  have h_closed : IsClosed (Set.range (fun n => (f n : ℝ))) := Set.Finite.isClosed h_image_finite
  have h_mem : ξ ∈ Set.range (fun n => (f n : ℝ)) := by
    apply IsClosed.mem_of_tendsto h_closed htendsto
    filter_upwards
    intro n
    exact Set.mem_range_self n
  obtain ⟨n, hn⟩ := h_mem
  exfalso
  exact irrational_xi ⟨f n, hn⟩

/-- The set of rational approximations from below with denominator bounded below is infinite. -/
lemma infinite_rat_approx_filtered (N₀ : ℕ) :
    {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2 ∧ N₀ ≤ q.den}.Infinite := by
  have h_combined : {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2 ∧ q.den < N₀}.Finite := by
    -- For each fixed denominator $d < N₀$, there are only finitely many numerators $n$ such that $|ξ - n/d| < 1/d^2$.
    have h_finite_num_den : ∀ d : ℕ, d < N₀ → {n : ℤ | |ξ - (n : ℝ) / d| < 1 / (d : ℝ) ^ 2}.Finite := by
      intro d hd; by_cases hd' : d = 0 <;> simp_all [ abs_lt ]
      · exact Set.finite_empty.subset fun x hx => (lt_asymm hx.1 hx.2).elim
      · refine' Set.Finite.subset ( Set.finite_Ico ( ⌈ ( ξ - ( ( d : ℝ ) ^ 2 ) ⁻¹ ) * d⌉ ) ( ⌊ ( ( d : ℝ ) ^ 2 ) ⁻¹ * d + ξ * d⌋ + 1 ) ) _
        intro n hn
        obtain ⟨h1, h2⟩ := hn
        constructor
        · apply Int.ceil_le.mpr
          have h_d_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
          have h3 : ξ - ((d : ℝ)^2)⁻¹ < (n : ℝ) / d := by linarith
          have h4 := (lt_div_iff₀ h_d_pos).mp h3
          nlinarith
        · apply Int.lt_add_one_iff.mpr
          apply Int.le_floor.mpr
          have h_d_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
          have h3 : (n : ℝ) / d < ((d : ℝ)^2)⁻¹ + ξ := by linarith
          have h4 := (div_lt_iff₀ h_d_pos).mp h3
          nlinarith
    have h_finite_num_den : {q : ℚ | ∃ d : ℕ, d < N₀ ∧ ∃ n : ℤ, q = n / d ∧ |ξ - (n : ℝ) / d| < 1 / (d : ℝ) ^ 2}.Finite :=
      Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_lt_nat N₀ ) fun d hd => Set.Finite.image ( fun n : ℤ => ( n : ℚ ) / d ) ( h_finite_num_den d hd ) ) fun x hx => by aesop
    refine h_finite_num_den.subset ?_
    exact fun x hx => ⟨ x.den, hx.2.2, x.num, x.num_div_den.symm, by simpa [ Rat.cast_def ] using hx.2.1 ⟩
  exact Set.Infinite.mono (by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    have h3 : ¬(q.den < N₀) := fun h_lt => h2 ⟨h1.1, h1.2, h_lt⟩
    exact ⟨h1.1, h1.2, not_lt.mp h3⟩
  ) (Set.Infinite.diff infinite_rat_approx_from_below h_combined)

/-- The map q ↦ (q.num.toNat, q.den) is injective on the set of positive rationals. -/
lemma rat_map_injOn (S : Set ℚ) (h : ∀ q ∈ S, 0 < q) :
    Set.InjOn (fun q : ℚ => (q.num.toNat, q.den)) S := by
  intro q1 hq1 q2 hq2 heq
  simp only [Prod.mk.injEq] at heq
  have hq1_pos := h q1 hq1
  have hq2_pos := h q2 hq2
  have h1 := Rat.num_pos.mpr hq1_pos
  have h2 := Rat.num_pos.mpr hq2_pos
  have hnum : q1.num = q2.num := by omega
  have hden : q1.den = q2.den := heq.2
  exact Rat.ext hnum hden

/-- A rational approximation from below with large enough denominator is positive. -/
lemma q_pos_of_in_S_filtered {q : ℚ} {N₀ : ℕ} (hN₀ : 2 ≤ N₀)
    (hq_lt : (q : ℝ) < ξ) (hq_bound : |ξ - q| < 1 / (q.den : ℝ) ^ 2) (hq_den_ge : N₀ ≤ q.den) :
    0 < q := by
  have hξ_pos : (0 : ℝ) < ξ := by
    unfold ξ; exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hξ_lt_one : ξ < 1 := by
    unfold ξ
    rw [div_lt_one (Real.log_pos (by norm_num : (1:ℝ) < 3))]
    exact Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
  have hden_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr (by omega)
  have hden_sq_pos : (0 : ℝ) < (q.den : ℝ) ^ 2 := by positivity
  have habs : |ξ - q| = ξ - q := abs_of_pos (sub_pos.mpr hq_lt)
  rw [habs] at hq_bound
  have h1 : (q : ℝ) > ξ - 1 / (q.den : ℝ) ^ 2 := by linarith
  have h2 : (q.den : ℝ) ^ 2 ≥ 4 := by
    have : (q.den : ℝ) ≥ 2 := by exact_mod_cast (le_trans hN₀ hq_den_ge : 2 ≤ q.den)
    nlinarith
  have hξ_gt : ξ > 1 / 2 := by
    unfold ξ
    rw [gt_iff_lt, lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 3))]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]; push_cast; ring
    have : Real.log 3 < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  have : (q : ℝ) > 0 := by
    have h3 : 1 / (q.den : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hden_sq_pos (by positivity : (0:ℝ) < 4)]
      linarith
    linarith
  exact_mod_cast this

/-- The numerator of a positive rational is positive. -/
lemma num_toNat_pos_of_pos {q : ℚ} (hq : 0 < q) : 0 < q.num.toNat := by
  have := Rat.num_pos.mpr hq; omega

/-- Lemma 3.1 from [Roz25]:
    For any `ε ∈ (0, 1)`, there are infinitely many pairs of positive integers `(a, b)`
    such that `1 - ε < 3^a / 2^b < 1`. -/
lemma exists_infinite_pairs_approx (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ (1 - ε : ℝ) < (3 : ℝ)^p.1 / (2 : ℝ)^p.2 ∧ (3 : ℝ)^p.1 / (2 : ℝ)^p.2 < 1}.Infinite := by
  have hδ := delta_pos ε hε₀ hε₁

  -- S is the set of good approximations from below
  set S := {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2}
  have hS_inf : S.Infinite := infinite_rat_approx_from_below

  -- We need b = q.den to be large enough: b ≥ max 2 (⌈1 / delta ε⌉ + 1)
  set N₀ := max 2 (Nat.ceil (1 / delta ε) + 1)

  set S_filtered := {q : ℚ | (q : ℝ) < ξ ∧ |ξ - q| < 1 / (q.den : ℝ) ^ 2 ∧ N₀ ≤ q.den}
  have hS_filtered_inf : S_filtered.Infinite := infinite_rat_approx_filtered N₀

  -- The map q ↦ (q.num.toNat, q.den)
  let f : ℚ → ℕ × ℕ := fun q => (q.num.toNat, q.den)
  have hf_inj : Set.InjOn f S_filtered :=
    rat_map_injOn _ (fun _ hq => q_pos_of_in_S_filtered (le_max_left 2 _) hq.1 hq.2.1 hq.2.2)

  apply Set.Infinite.mono _ (Set.Infinite.image hf_inj hS_filtered_inf)
  intro p hp
  simp only [Set.mem_image] at hp
  obtain ⟨q, ⟨hq_lt, hq_bound, hq_den_ge⟩, hfb⟩ := hp
  rw [← hfb]
  simp only [f, Set.mem_setOf_eq]

  -- Extract b = q.den ≥ N₀ ≥ 2
  have hb2 : 2 ≤ q.den := le_trans (le_max_left 2 _) hq_den_ge
  have hb_pos : 0 < q.den := by omega
  have hb_pos_real : (0 : ℝ) < q.den := Nat.cast_pos.mpr hb_pos

  -- Since q < ξ, ξ - q > 0 and |ξ - q| = ξ - q
  have hq_pos_diff : 0 < ξ - q := sub_pos.mpr hq_lt
  have hq_abs : |ξ - q| = ξ - q := abs_of_pos hq_pos_diff
  have hq_bound_orig := hq_bound
  rw [hq_abs] at hq_bound

  -- Since q.den ≥ N₀ > 1/delta(ε), 1/q.den < delta(ε)
  have hb_large : Nat.ceil (1 / delta ε) + 1 ≤ q.den := le_trans (le_max_right 2 _) hq_den_ge
  have h_inv_lt : 1 / (q.den : ℝ) < delta ε := by
    rw [div_lt_iff₀ hb_pos_real]
    calc 1 ≤ ↑(Nat.ceil (1 / delta ε)) * delta ε := by
          rw [← div_le_iff₀ hδ]; exact Nat.le_ceil _
    _ = delta ε * ↑(Nat.ceil (1 / delta ε)) := mul_comm _ _
    _ < delta ε * q.den := by
          have h1 : (Nat.ceil (1 / delta ε) : ℝ) < q.den := by exact_mod_cast (by omega : Nat.ceil (1 / delta ε) < q.den)
          nlinarith

  -- Therefore, ξ - q < 1/q.den^2 = (1/q.den) * (1/q.den) < delta(ε) * 1/q.den = delta(ε)/q.den
  have hq_bound2 : ξ - (q : ℝ) < delta ε / q.den := by
    calc ξ - q < 1 / (q.den : ℝ) ^ 2 := hq_bound
    _ = (1 / (q.den : ℝ)) * (1 / (q.den : ℝ)) := by ring
    _ < delta ε * (1 / (q.den : ℝ)) := by nlinarith [one_div_pos.mpr hb_pos_real]
    _ = delta ε / (q.den : ℝ) := by ring

  -- Now we know 0 < ξ - q < delta(ε)/q.den
  -- To apply inequality_equiv, we need q = a/b. Wait, q = q.num / q.den.
  have ha : 0 < q.num.toNat := num_toNat_pos_of_pos <| q_pos_of_in_S_filtered (le_max_left 2 _) hq_lt hq_bound_orig hq_den_ge
  have h_q_eq : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
    have hq_pos := q_pos_of_in_S_filtered (le_max_left 2 _) hq_lt hq_bound_orig hq_den_ge
    have hnum_pos := Rat.num_pos.mpr hq_pos
    rw [Rat.cast_def]
    congr 1
    have : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum_pos.le
    exact_mod_cast this.symm
  have hq_pos_diff' : 0 < ξ - (q.num.toNat : ℝ) / (q.den : ℝ) := by rwa [← h_q_eq]
  have hq_bound2' : ξ - (q.num.toNat : ℝ) / (q.den : ℝ) < delta ε / q.den := by rwa [← h_q_eq]
  have hequiv := (inequality_equiv q.num.toNat q.den hb_pos ε hε₁).mpr ⟨hq_pos_diff', hq_bound2'⟩

  -- The target conditions are 0 < a, 0 < b, and the inequality
  exact ⟨ha, hb_pos, hequiv⟩


end CollatzMapBasics

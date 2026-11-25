module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace HardyGridPaperCheck

theorem shifted_schedules (x : ℝ) (hx : 0 ≤ x) :
    let k := 3 + x
    4*(k^2+5*k+6) ≤ 100*k^2-2-k ∧
    101*k^2+9*k+7 ≤ 110*k^2 ∧
    (24+100*k^2+800*k^2)*(110*k^2) ≤ 100000*k^4 ∧
    3224+100*k^2 ≤ 500*k^2 ∧
    5+8*(100000*k^4) ≤ 1000000*k^4 ∧
    k+11 ≤ 500000*k^4 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply sub_nonneg.mp
    ring_nf
    positivity

theorem degree_schedules (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let k := 3+x
    let d := 1+y
    4*(6+k+d*(k+4)) ≤ 100*d*k-d-2 ∧
    101*d*k+9*d+k+7 ≤ 110*d*k ∧
    24*(110*d*k)+(100*d*k)*(101*k)+(20*110*d*k)*(40*k) ≤ 100000*d*k^2 ∧
    6+8*(100000*d*k^2) ≤ 1000000*d*k^2 ∧
    k+11 ≤ 500000*d*k^2 ∧
    20+10*k+4*d*(k+4) ≤ 1000000*d*k^2 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply sub_nonneg.mp
    ring_nf
    positivity

private theorem nat_le_two_pow (k : ℕ) : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    linarith [show (0 : ℝ) ≤ k by positivity]

theorem clip_loss {k : ℕ} (hk : 3 ≤ k) {e : ℝ}
    (he : e ≤ 348480000*(k:ℝ)^4/(2:ℝ)^(40*k) +
      121000000*(k:ℝ)^6/(2:ℝ)^(100*k)) : e < 1/(2:ℝ)^(k+6) := by
  have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hd : (2:ℝ)^(40*k) ≤ (2:ℝ)^(100*k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp : (k:ℝ)^4 ≤ (k:ℝ)^6 := pow_le_pow_right₀ hk1 (by decide)
  have hinner : 348480000*(k:ℝ)^4/(2:ℝ)^(40*k) ≤ 348480000*(k:ℝ)^6/(2:ℝ)^(40*k) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
  have houter : 121000000*(k:ℝ)^6/(2:ℝ)^(100*k) ≤ 121000000*(k:ℝ)^6/(2:ℝ)^(40*k) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have hnear : e ≤ 469480000*(k:ℝ)^6/(2:ℝ)^(40*k) := by
    calc
      _ ≤ 348480000*(k:ℝ)^6/(2:ℝ)^(40*k)+121000000*(k:ℝ)^6/(2:ℝ)^(40*k) :=
        he.trans (add_le_add hinner houter)
      _ = _ := by ring
  apply lt_of_le_of_lt hnear
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hkpow : (k:ℝ)^6 ≤ ((2:ℝ)^k)^6 :=
    pow_le_pow_left₀ (by positivity) (by linarith [nat_le_two_pow k]) _
  have hpos : (0:ℝ) < k := by linarith
  calc
    _ < ((2:ℝ)^29*(k:ℝ)^6)*(2:ℝ)^(k+6) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ ≤ ((2:ℝ)^29*((2:ℝ)^k)^6)*(2:ℝ)^(k+6) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkpow (by positivity)) (by positivity)
    _ = (2:ℝ)^(29+k*6+(k+6)) := by simp only [pow_add, pow_mul]
    _ ≤ (2:ℝ)^(40*k) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = _ := by ring

theorem corrected_squared_gap {R U l e η Δ ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hΔ0 : 0 ≤ Δ)
    (hl1 : l ≤ 1) (hRU : R ≤ U) (hU : U ≤ (l+Δ)^2)
    (hl : l^2 ≤ R + 2*(e+η))
    (he : e < ε/64) (hη : η ≤ ε/64) (hΔ : Δ ≤ ε/64) :
    0 ≤ U-R ∧ U-R < (385/4096)*ε := by
  have hprod : l*Δ ≤ Δ := by nlinarith [mul_nonneg (sub_nonneg.mpr hl1) hΔ0]
  have hsq : Δ^2 ≤ (ε/64)^2 := by
    exact sq_le_sq' (by linarith) hΔ
  have hεsq : ε^2 ≤ ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
  exact ⟨sub_nonneg.mpr hRU, by nlinarith⟩

private theorem log_loss_le {w : ℝ} (hw : 0 ≤ w) (hhalf : w ≤ 1/2) :
    0 ≤ -Real.log (1-w)/2 ∧ -Real.log (1-w)/2 ≤ w := by
  have ht : 0 < 1-w := by linarith
  have hl := Real.log_nonpos ht.le (show 1-w ≤ 1 by linarith)
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at hi
  have hmul : 1 ≤ (2*w+1)*(1-w) := by
    nlinarith [mul_nonneg hw (show 0 ≤ 1-2*w by linarith)]
  have hrec : (1-w)⁻¹ ≤ 2*w+1 := by
    rw [← one_div]
    exact (div_le_iff₀ ht).2 hmul
  exact ⟨by linarith, by linarith⟩

theorem log_guard {U X η : ℝ} (hX : 0 < X) (hη : η ≤ 1/2) (hR : 1-X ≤ U)
    (herr : U-(1-X) < η*X) :
    U < 1 ∧ 0 ≤ -Real.log (1-U)/2 + Real.log X/2 ∧
      -Real.log (1-U)/2 + Real.log X/2 < η := by
  let w := (U-(1-X))/X
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hR) hX.le
  have hwη : w < η := (div_lt_iff₀ hX).2 herr
  have hw1 : 0 < 1-w := by linarith
  have hfac : 1-U = X*(1-w) := by
    dsimp [w]
    field_simp
    ring
  obtain ⟨hlo, hup⟩ := log_loss_le hw0 (hwη.le.trans hη)
  have heq : -Real.log (1-U)/2+Real.log X/2 = -Real.log (1-w)/2 := by
    rw [hfac, Real.log_mul hX.ne' hw1.ne']
    ring
  have : 0 < 1-U := hfac ▸ mul_pos hX hw1
  exact ⟨by linarith, heq ▸ hlo, heq ▸ hup.trans_lt hwη⟩

theorem dyadic_log_guard {k b : ℕ} {U X : ℝ}
    (hX : 1/(2:ℝ)^(2*b) ≤ X) (hR : 1-X ≤ U)
    (herr : U-(1-X) < 1/(2:ℝ)^(2*b+k+1)) :
    U < 1 ∧ 0 ≤ -Real.log (1-U)/2 + Real.log X/2 ∧
      -Real.log (1-U)/2 + Real.log X/2 < 1/(2:ℝ)^(k+1) := by
  have hXp : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h2 : (2:ℝ) ≤ (2:ℝ)^(k+1) := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ k+1 by omega))
  have hm : 1/(2:ℝ)^(k+1) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) h2
  apply log_guard hXp hm hR
  apply herr.trans_le
  calc
    _ = (1/(2:ℝ)^(k+1))*(1/(2:ℝ)^(2*b)) := by
      rw [show 2*b+k+1 = 2*b+(k+1) by omega, pow_add]
      simp only [one_div, mul_inv_rev]
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)

end HardyGridPaperCheck

#print axioms HardyGridPaperCheck.shifted_schedules
#print axioms HardyGridPaperCheck.degree_schedules
#print axioms HardyGridPaperCheck.clip_loss
#print axioms HardyGridPaperCheck.corrected_squared_gap
#print axioms HardyGridPaperCheck.log_guard
#print axioms HardyGridPaperCheck.dyadic_log_guard

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Algebra for the normalized Sobolev line Gram kernel at exponent two.
The Hilbert-space result assumes the kernel, separation by its waves and
biorthogonality. The accompanying note treats the infinite trace estimates. -/

open scoped InnerProductSpace ComplexConjugate

namespace NearestGram

noncomputable section

private def kernel (u v : ℝ) : ℝ := Real.exp (-|u - v|)
private def weight (p : ℝ) : ℝ := p ^ 2 / (1 - p ^ 2)
private def off (p : ℝ) : ℝ := p / (1 - p ^ 2)
private def diagonal (p q : ℝ) : ℝ := 1 + weight p + weight q

private theorem kernel_self (t : ℝ) : kernel t t = 1 := by simp [kernel]

private theorem kernel_comm (u v : ℝ) : kernel u v = kernel v u := by
  simp only [kernel, abs_sub_comm u v]

private theorem kernel_chain {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w) :
    kernel u w = kernel u v * kernel v w := by
  simp only [kernel, abs_of_nonpos (sub_nonpos.mpr (huv.trans hvw)),
    abs_of_nonpos (sub_nonpos.mpr huv), abs_of_nonpos (sub_nonpos.mpr hvw)]
  rw [← Real.exp_add]
  congr 1
  ring

private theorem kernel_denom {u v : ℝ} (h : u < v) : 1 - kernel u v ^ 2 ≠ 0 := by
  have h₀ : 0 < kernel u v := Real.exp_pos _
  have h₁ : kernel u v < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact neg_lt_zero.mpr (abs_pos.mpr (sub_ne_zero.mpr h.ne))
  nlinarith [mul_pos (sub_pos.mpr h₁) (by linarith : 0 < 1 + kernel u v)]

private theorem weight_eq_gap {u v : ℝ} (h : u < v) :
    weight (kernel u v) = 1 / (Real.exp (2 * (v - u)) - 1) := by
  have hprod : kernel u v ^ 2 * Real.exp (2 * (v - u)) = 1 := by
    simp only [kernel, abs_of_nonpos (sub_nonpos.mpr h.le), neg_neg, pow_two, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hpos : 1 < Real.exp (2 * (v - u)) := Real.one_lt_exp_iff.mpr (by linarith)
  unfold weight
  field_simp [kernel_denom h, (sub_pos.mpr hpos).ne']
  linarith

private def localValue (l t r u : ℝ) : ℝ :=
  diagonal (kernel l t) (kernel t r) * kernel u t -
    off (kernel l t) * kernel u l - off (kernel t r) * kernel u r

private theorem local_center (l t r : ℝ) : localValue l t r t = 1 := by
  rw [localValue, kernel_self, kernel_comm t l]
  unfold diagonal off weight
  ring

private theorem local_left {l t r u : ℝ} (hl : l < t) (hr : t < r) (hu : u ≤ l) :
    localValue l t r u = 0 := by
  unfold localValue
  rw [kernel_chain (hu.trans hl.le) hr.le, kernel_chain hu hl.le]
  unfold diagonal off weight
  field_simp [kernel_denom hl, kernel_denom hr]
  ring

private theorem local_right {l t r u : ℝ} (hl : l < t) (hr : t < r) (hu : r ≤ u) :
    localValue l t r u = 0 := by
  unfold localValue
  rw [kernel_comm u l, kernel_comm u t, kernel_comm u r,
    kernel_chain hl.le (hr.le.trans hu), kernel_chain hr.le hu]
  unfold diagonal off weight
  field_simp [kernel_denom hl, kernel_denom hr]
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- With a nearest point on each side, these two gaps give the exact norm of
the normalized biorthogonal vector. The totality condition holds on the closed
span of the waves. -/
theorem orbit_coordinate_norm_sq
    (T : Set ℝ) (k : ℝ → H)
    (hgram : ∀ u ∈ T, ∀ v ∈ T, ⟪k u, k v⟫_ℂ = ((Real.exp (-|u - v|) : ℝ) : ℂ))
    (htotal : ∀ w : H, (∀ u ∈ T, ⟪k u, w⟫_ℂ = 0) → w = 0)
    {l t r : ℝ} (hl : l < t) (hr : t < r) (hlT : l ∈ T) (htT : t ∈ T) (hrT : r ∈ T)
    (hnear : ∀ u ∈ T, u ≠ t → u ≤ l ∨ r ≤ u)
    (x : H) (hx : ∀ u ∈ T, ⟪k u, x⟫_ℂ = if u = t then 1 else 0) :
    ‖x‖ ^ 2 = 1 + 1 / (Real.exp (2 * (t - l)) - 1) +
        1 / (Real.exp (2 * (r - t)) - 1) := by
  let p := kernel l t
  let q := kernel t r
  let y : H := (diagonal p q : ℂ) • k t - (off p : ℂ) • k l - (off q : ℂ) • k r
  have heval (u : ℝ) (hu : u ∈ T) : ⟪k u, y⟫_ℂ = (localValue l t r u : ℂ) := by
    simp only [y, inner_sub_right, inner_smul_right, hgram u hu t htT,
      hgram u hu l hlT, hgram u hu r hrT, localValue, p, q, kernel,
      Complex.ofReal_sub, Complex.ofReal_mul]
  have hy (u : ℝ) (hu : u ∈ T) : ⟪k u, y⟫_ℂ = if u = t then 1 else 0 := by
    rw [heval u hu]
    by_cases h : u = t
    · subst u
      simp [local_center]
    · rw [ite_eq_right h]
      rcases hnear u hu h with hlo | hhi
      · rw [local_left hl hr hlo, Complex.ofReal_zero]
      · rw [local_right hl hr hhi, Complex.ofReal_zero]
  have heq : y = x := sub_eq_zero.mp (htotal (y - x) (by
    intro u hu
    rw [inner_sub_right, hy u hu, hx u hu, sub_self]))
  have hself : ⟪x, x⟫_ℂ = (diagonal p q : ℂ) := by
    have htc : ⟪k t, x⟫_ℂ = 1 := by simpa using hx t htT
    have hlc : ⟪k l, x⟫_ℂ = 0 := by simpa [hl.ne] using hx l hlT
    have hrc : ⟪k r, x⟫_ℂ = 0 := by simpa [hr.ne'] using hx r hrT
    conv_lhs => lhs; rw [← heq]
    simp only [y, inner_sub_left, inner_smul_left, Complex.conj_ofReal,
      htc, hlc, hrc, mul_one, mul_zero, sub_zero]
  have hn : ‖x‖ ^ 2 = diagonal p q := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hself
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_pow] using hself)
  simpa only [diagonal, p, q, weight_eq_gap hl, weight_eq_gap hr] using hn

/-- A site at an end of the ordered set has just one neighboring contribution. -/
theorem endpoint_coordinate_norm_sq
    (T : Set ℝ) (k : ℝ → H)
    (hgram : ∀ u ∈ T, ∀ v ∈ T, ⟪k u, k v⟫_ℂ = ((Real.exp (-|u - v|) : ℝ) : ℂ))
    (htotal : ∀ w : H, (∀ u ∈ T, ⟪k u, w⟫_ℂ = 0) → w = 0)
    {t v : ℝ} (htT : t ∈ T) (hvT : v ∈ T)
    (hside : (v < t ∧ ∀ u ∈ T, u ≠ t → u ≤ v) ∨ (t < v ∧ ∀ u ∈ T, u ≠ t → v ≤ u))
    (x : H) (hx : ∀ u ∈ T, ⟪k u, x⟫_ℂ = if u = t then 1 else 0) :
    ‖x‖ ^ 2 = 1 + 1 / (Real.exp (2 * |t - v|) - 1) := by
  let p := kernel t v
  let a := 1 / (1 - p ^ 2)
  have hne : v ≠ t := hside.elim (fun h ↦ h.1.ne) (fun h ↦ h.1.ne')
  have hd : 1 - p ^ 2 ≠ 0 := by
    rcases hside with h | h
    · simpa only [p, kernel_comm t v] using kernel_denom h.1
    · exact kernel_denom h.1
  have hfar (u : ℝ) (hu : u ∈ T) (hut : u ≠ t) : kernel u t = p * kernel u v := by
    rcases hside with h | h
    · rw [kernel_chain (h.2 u hu hut) h.1.le, kernel_comm v t]
      exact mul_comm _ _
    · rw [kernel_comm u t, kernel_chain h.1.le (h.2 u hu hut), kernel_comm v u]
  let y : H := (a : ℂ) • k t - (off p : ℂ) • k v
  have heval (u : ℝ) (hu : u ∈ T) :
      ⟪k u, y⟫_ℂ = ((a * kernel u t - off p * kernel u v : ℝ) : ℂ) := by
    simp only [y, inner_sub_right, inner_smul_right, hgram u hu t htT, hgram u hu v hvT,
      kernel, Complex.ofReal_sub, Complex.ofReal_mul]
  have hy (u : ℝ) (hu : u ∈ T) : ⟪k u, y⟫_ℂ = if u = t then 1 else 0 := by
    rw [heval u hu]
    by_cases h : u = t
    · subst u
      have hcenter : a * kernel t t - off p * kernel t v = 1 := by
        rw [kernel_self]
        change 1 / (1 - p ^ 2) * 1 - p / (1 - p ^ 2) * p = 1
        field_simp [hd]
      simp [hcenter]
    · have hout : a * kernel u t - off p * kernel u v = 0 := by
        rw [hfar u hu h]
        unfold a off
        ring
      simp [h, hout]
  have heq : y = x := sub_eq_zero.mp (htotal (y - x) (by
    intro u hu
    rw [inner_sub_right, hy u hu, hx u hu, sub_self]))
  have hself : ⟪x, x⟫_ℂ = (a : ℂ) := by
    have htc : ⟪k t, x⟫_ℂ = 1 := by simpa using hx t htT
    have hvc : ⟪k v, x⟫_ℂ = 0 := by simpa [hne] using hx v hvT
    conv_lhs => lhs; rw [← heq]
    simp only [y, inner_sub_left, inner_smul_left, Complex.conj_ofReal,
      htc, hvc, mul_one, mul_zero, sub_zero]
  have hn : ‖x‖ ^ 2 = a := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hself
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_pow] using hself)
  have ha : a = 1 + weight p := by
    unfold a weight
    field_simp [hd]
    ring
  rw [hn, ha]
  congr 1
  rcases hside with h | h
  · rw [abs_of_pos (sub_pos.mpr h.1)]
    simpa only [p, kernel_comm t v] using weight_eq_gap h.1
  · rw [abs_of_neg (sub_neg.mpr h.1), neg_sub]
    exact weight_eq_gap h.1

/-- A single unit wave is its own cardinal vector on its closed span. -/
theorem singleton_coordinate_norm_sq
    (k x : H) (hunit : ⟪k, k⟫_ℂ = 1) (hcardinal : ⟪k, x⟫_ℂ = 1)
    (htotal : ∀ w : H, ⟪k, w⟫_ℂ = 0 → w = 0) : ‖x‖ ^ 2 = 1 := by
  have h : x = k := sub_eq_zero.mp (htotal (x - k) (by
    rw [inner_sub_right, hcardinal, hunit, sub_self]))
  rw [h]
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hunit
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_pow, Complex.ofReal_one] using hunit)

/-- On the normalized difference of two adjacent waves a linear multiplier
splits into its diagonal and one adjacent difference of its symbol. -/
theorem adjacent_multiplier_identity
    (B : H →L[ℂ] H) (k₀ k₁ : H) (b₀ b₁ r s : ℂ)
    (h₀ : B k₀ = b₀ • k₀) (h₁ : B k₁ = b₁ • k₁) :
    B (s • (k₁ - r • k₀)) =
      b₁ • (s • (k₁ - r • k₀)) + (s * r * (b₁ - b₀)) • k₀ := by
  simp only [map_smul, map_sub, h₁, h₀, smul_sub, smul_smul]
  module

/-- Each column of the multiplier in the orthonormal basis has an exact
Pythagorean norm. Summing over an orthonormal basis gives the Hilbert–Schmidt
identity in the accompanying note. -/
theorem adjacent_multiplier_column_norm_sq
    (B : H →L[ℂ] H) (k₀ k₁ : H) (b₀ b₁ r s : ℂ)
    (h₀ : B k₀ = b₀ • k₀) (h₁ : B k₁ = b₁ • k₁)
    (he : ‖s • (k₁ - r • k₀)‖ = 1) (hk : ‖k₀‖ = 1)
    (hperp : ⟪s • (k₁ - r • k₀), k₀⟫_ℂ = 0) :
    ‖B (s • (k₁ - r • k₀))‖ ^ 2 = ‖b₁‖ ^ 2 + ‖s * r * (b₁ - b₀)‖ ^ 2 := by
  have hz : ⟪b₁ • (s • (k₁ - r • k₀)), (s * r * (b₁ - b₀)) • k₀⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, hperp, mul_zero, mul_zero]
  rw [adjacent_multiplier_identity B k₀ k₁ b₀ b₁ r s h₀ h₁, norm_add_sq (𝕜 := ℂ),
    hz, norm_smul, he, mul_one, norm_smul, hk, mul_one]
  simp

end

end NearestGram

#print axioms NearestGram.orbit_coordinate_norm_sq
#print axioms NearestGram.endpoint_coordinate_norm_sq
#print axioms NearestGram.singleton_coordinate_norm_sq
#print axioms NearestGram.adjacent_multiplier_identity
#print axioms NearestGram.adjacent_multiplier_column_norm_sq

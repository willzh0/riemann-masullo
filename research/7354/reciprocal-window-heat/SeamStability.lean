module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatMeanZeroHeat
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Trigonometric.SincIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-! Scalar and rank-one bounds for Gaussian displacements across the rational norm-one seam. -/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal InnerProductSpace CompactlySupported

namespace RiemannMasullo.ThroughOneStability

/-- Changing the scale of a sine integral costs at most the logarithmic displacement,
uniformly in the original phase, including at phase zero. -/
theorem sincPrimitive_logShift (a z : ℝ) :
    |(∫ v in (0 : ℝ)..a * exp z, sinc v) - ∫ v in (0 : ℝ)..a, sinc v| ≤ |z| := by
  let F (t : ℝ) := ∫ v in (0 : ℝ)..a * exp t, sinc v
  have hd (t : ℝ) : HasDerivAt F (sin (a * exp t)) t := by
    have hp := (continuous_sinc.integral_hasStrictDerivAt 0 (a * exp t)).hasDerivAt
    have h := hp.comp t ((hasDerivAt_exp t).const_mul a)
    apply h.congr_deriv
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [sinc_of_ne_zero (mul_ne_zero ha (exp_pos t).ne'), div_mul_cancel₀ _ (mul_ne_zero ha (exp_pos t).ne')]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := z)
    (fun t _ ↦ hd t) ((continuous_sin.comp (continuous_const.mul continuous_exp)).intervalIntegrable 0 z)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := z)
    (f := fun t : ℝ ↦ sin (a * exp t)) (C := 1)
    (fun t _ ↦ by simpa [Real.norm_eq_abs] using abs_le.mpr ⟨neg_one_le_sin _, sin_le_one _⟩)
  rw [hi] at hb
  simpa [F, Real.norm_eq_abs] using hb

/-- The direct scalar kernel at nonzero reciprocal phase. Its totalized value at zero
does not affect any of the spatial Haar averages. -/
def phaseKernel (R c : ℝ) : ℝ := (π * c)⁻¹ * ∫ t in (0 : ℝ)..(2 * π * c * R), sinc t

/-- After one phase zero, varying the band cutoff is uniformly logarithmically Lipschitz. -/
theorem phaseKernel_logShift_zeroWeight {C R c z y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C * |c|) :
    |y * (phaseKernel (R * exp z) c - phaseKernel R c)| ≤ C / π * |z| := by
  by_cases hc : c = 0
  · simp [hc, phaseKernel]
    positivity
  have hsi := sincPrimitive_logShift (2 * π * c * R) z
  simp only [phaseKernel, ← mul_sub, abs_mul, abs_inv, abs_of_pos pi_pos]
  rw [← mul_assoc (2 * π * c) R (exp z)]
  calc
    |y| * ((π * |c|)⁻¹ * _) ≤ (C * |c|) * ((π * |c|)⁻¹ * |z|) := by
      gcongr
    _ = _ := by field_simp [hc, pi_ne_zero]

/-- The two sides of the translated reciprocal-phase interval remain uniformly away from
zero. Their lengths of motion are controlled independently. -/
theorem phaseWindow_endpoints {δ r : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hh : (1 + δ) * |r - 1| ≤ δ / 2) :
    (r * (1 - δ) - 1 ≤ -δ / 2) ∧ (δ / 2 ≤ r * (1 + δ) - 1) ∧
    |(r * (1 - δ) - 1) - (-δ)| = (1 - δ) * |r - 1| ∧
    |(r * (1 + δ) - 1) - δ| = (1 + δ) * |r - 1| := by
  have hl : |(r * (1 - δ) - 1) - (-δ)| = (1 - δ) * |r - 1| := by
    rw [show r * (1 - δ) - 1 - (-δ) = (1 - δ) * (r - 1) by ring, abs_mul, abs_of_pos (by linarith : 0 < 1 - δ)]
  have hr : |(r * (1 + δ) - 1) - δ| = (1 + δ) * |r - 1| := by
    rw [show r * (1 + δ) - 1 - δ = (1 + δ) * (r - 1) by ring, abs_mul, abs_of_pos (by linarith : 0 < 1 + δ)]
  have hleft := le_abs_self ((r * (1 - δ) - 1) - (-δ))
  have hright := neg_abs_le ((r * (1 + δ) - 1) - δ)
  rw [hl] at hleft
  rw [hr] at hright
  refine ⟨?_, by linarith, hl, hr⟩
  have hh' := (mul_le_mul_of_nonneg_right (show 1-δ ≤ 1+δ by linarith) (abs_nonneg (r-1))).trans hh
  linarith

/-- Moving either endpoint only sees the two endpoint strips. -/
theorem move_endpoints_bound (f : ℝ → ℝ) (a b a' b' M : ℝ)
    (h₁ : IntervalIntegrable f volume a' a) (h₂ : IntervalIntegrable f volume a b)
    (h₃ : IntervalIntegrable f volume b b')
    (ha : ∀ x ∈ uIoc a' a, |f x| ≤ M) (hb : ∀ x ∈ uIoc b b', |f x| ≤ M) :
    |(∫ x in a'..b', f x) - ∫ x in a..b, f x| ≤ M * (|a'-a| + |b'-b|) := by
  have he := intervalIntegral.integral_add_adjacent_intervals h₁ (h₂.trans h₃)
  have hi := intervalIntegral.integral_add_adjacent_intervals h₂ h₃
  have hL := intervalIntegral.norm_integral_le_of_norm_le_const (a := a') (b := a) (f := f)
    (C := M) (fun x hx ↦ by simpa [Real.norm_eq_abs] using ha x hx)
  have hR := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := b') (f := f)
    (C := M) (fun x hx ↦ by simpa [Real.norm_eq_abs] using hb x hx)
  rw [← he, ← hi, show (∫ x in a'..a, f x) + ((∫ x in a..b, f x) + (∫ x in b..b', f x)) -
      (∫ x in a..b, f x) = (∫ x in a'..a, f x) + (∫ x in b..b', f x) by ring, mul_add]
  rw [abs_sub_comm a' a]
  exact (abs_add_le _ _).trans (add_le_add hL hR)

/-- The fixed-window universal reference is written in logarithmic band coordinates after
the exact Fubini identity of the sharp finite part. Additive constants drop out. -/
def logReference (δ u : ℝ) : ℝ :=
  (2 / π) * ∫ t in (0 : ℝ)..u, (∫ x in (0 : ℝ)..(2 * π * δ * exp t), sinc x)

/-- The reference changes by a controlled quantity even though its value grows like log R. -/
theorem logReference_move (δ u v : ℝ) :
    |logReference δ v - logReference δ u| ≤ (2/π) * (π / 2 + 2) * |v-u| := by
  let F (t : ℝ) := ∫ x in (0 : ℝ)..(2 * π * δ * exp t), sinc x
  have hf : Continuous F := continuous_integral_sinc.comp (continuous_const.mul continuous_exp)
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable 0 u) (hf.intervalIntegrable u v)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v) (f := F)
    (C := π/2+2) (fun t _ ↦ by simpa only [F, Real.norm_eq_abs] using abs_integral_sinc_le (2*π*δ*exp t))
  change |(2/π)*(∫ t in (0:ℝ)..v, F t) - (2/π)*(∫ t in (0:ℝ)..u, F t)| ≤ _
  rw [← h, ← mul_sub, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : 0 < 2/π), mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- A bounded second log derivative controls the translated profile after removal of its
value at the shifted seam. Both factors are retained, so integration against 1/|c| is harmless. -/
theorem logProfile_mixed_displacement (W V : ℝ → ℝ) (K : ℝ)
    (hW : ∀ t, HasDerivAt W (V t) t) (hV : ∀ t u, |V t-V u| ≤ K * |t-u|)
    (x z : ℝ) : |W (x-z)-W x-(W (-z)-W 0)| ≤ K * |z| * |x| := by
  let G (t : ℝ) := W (t-z) - W t
  have hG (t : ℝ) : HasDerivAt G (V (t-z)-V t) t := by
    have h := ((hW (t-z)).comp t ((hasDerivAt_id' t).sub_const z)).fun_sub (hW t)
    simpa only [G, Function.comp_def, mul_one] using h
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ (hG t).hasDerivWithinAt) (fun t _ ↦ by
      have h' := hV (t-z) t
      rw [show t-z-t = -z by ring, abs_neg] at h'
      simpa only [Real.norm_eq_abs] using h') (mem_univ (0 : ℝ)) (mem_univ x)
  simpa only [G, Real.norm_eq_abs, zero_sub, sub_zero] using h

/-- Centering removes a test's linear log shift exactly. The physical sandwich has
variance twice its heat parameter. -/
theorem gaussian_centered_quadratic (τ : ℝ≥0) (F : ℝ → ℝ) (c b K : ℝ)
    (hF : Integrable F (gaussianReal 0 (τ + τ)))
    (hK : ∀ z, |F z - c - b * z| ≤ K * z ^ 2) :
    |(∫ z, F z ∂gaussianReal 0 (τ + τ)) - c| ≤ K * (2 * (τ : ℝ)) := by
  let μ := gaussianReal 0 (τ + τ)
  have h₂ : Integrable (fun z : ℝ ↦ z^2) μ :=
    (memLp_two_iff_integrable_sq (μ := μ) measurable_id'.aestronglyMeasurable).mp (memLp_id_gaussianReal 2)
  have h₁ : Integrable (fun z : ℝ ↦ z) μ := (memLp_id_gaussianReal (μ := 0) (v := τ+τ) 1).integrable le_rfl
  have hmean : (∫ z : ℝ, z ∂μ) = 0 := by simp [μ]
  have hmoment : (∫ z : ℝ, z ^ 2 ∂μ) = 2 * (τ : ℝ) := by
    have hv := variance_eq_integral (μ := μ) measurable_id'.aemeasurable
    rw [variance_fun_id_gaussianReal] at hv
    simpa [μ, two_mul] using hv.symm
  have h := norm_integral_le_of_norm_le (f := fun z : ℝ ↦ F z - c - b*z) ((h₂.const_mul K) : Integrable (fun z : ℝ ↦ K * z^2) μ)
    (.of_forall fun z ↦ by simpa [Real.norm_eq_abs] using hK z)
  change |(∫ z : ℝ, F z - c - b*z ∂μ)| ≤ _ at h
  have hc : Integrable (fun _ : ℝ ↦ c) μ := integrable_const c
  have hfc : Integrable (fun z : ℝ ↦ F z - c) μ := hF.sub hc
  rw [integral_sub (f := fun z : ℝ ↦ F z-c) (g := fun z ↦ b*z) hfc (h₁.const_mul b), integral_sub (μ := μ) hF hc,
    integral_const_mul, hmean, integral_const_mul, hmoment] at h
  simpa using h

#print axioms logProfile_mixed_displacement
#print axioms move_endpoints_bound
#print axioms sincPrimitive_logShift
#print axioms phaseKernel_logShift_zeroWeight
#print axioms phaseWindow_endpoints
#print axioms logReference_move
#print axioms gaussian_centered_quadratic

end RiemannMasullo.ThroughOneStability

namespace RiemannMasullo.FlatPolar

local notation "H" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

private theorem heatCorrection_bound {B : ℝ} (hB : 0 < B) (h L : ℝ) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
    ‖hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)) -
      hilbertTrace (logHeatSandwich τ (compactCosineTraceOperator 0 B h L φ)) +
      ⟪bandVector B, T (bandVector B)⟫_ℂ‖ ≤ 2 * ‖T‖ * Real.sqrt (Real.sqrt ((τ+τ : ℝ≥0) : ℝ)) := by
  let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp (compactDilationAction φ)
  let A := compactCosineTraceOperator 0 B h L φ
  let M := meanZeroCompactCosineTraceOperator h L B φ
  obtain ⟨Q, hQ, htr⟩ := exists_sandwich_compressionDifference (logHeat τ) T (isSelfAdjoint_logHeat τ)
    (frequencyBand B) (norm_bandVector hB) (bandVector_mem_frequencyBand B)
  have he : Q = logHeatSandwich τ M - logHeatSandwich τ A := by
    apply Subtype.ext
    exact (hQ.trans (sandwich_compressionDifference_eq_two_rows (logHeat τ) T (isSelfAdjoint_logHeat τ)
      (frequencyBand B) (norm_bandVector hB))).trans (meanZeroCompactCosine_heatDifference_eq_two_rows hB h L τ φ).symm
  obtain ⟨tr, htr'⟩ := hilbertTrace_linear («H» := H)
  have hQtr : hilbertTrace Q = hilbertTrace (logHeatSandwich τ M) - hilbertTrace (logHeatSandwich τ A) := by
    exact (congrArg hilbertTrace he).trans ((htr' _).symm.trans
      ((map_sub tr (logHeatSandwich τ M) (logHeatSandwich τ A)).trans
        (congrArg₂ (fun x y : ℂ ↦ x-y) (htr' _) (htr' _))))
  rw [hQtr, ← logHeat_add τ τ (bandVector B)] at htr
  exact htr.trans (mul_le_mul_of_nonneg_left
    ((Real.le_sqrt (norm_nonneg _) (Real.sqrt_nonneg _)).mpr (norm_logHeat_sub_bandVector_sq_le (τ+τ) hB)) (by positivity))

/-- The motion of the actual removed mean row is uniform even when the radial window crosses
one. The cold and hot compressions have the same spatial floor and ceiling. -/
theorem centralWindow_meanZeroHeat_cold_difference {B : ℝ} (hB : 0 < B) (h L : ℝ) (τ : ℝ≥0)
    (φ : C_c(ℝ≥0ˣ, ℂ)) :
    let M := meanZeroCompactCosineTraceOperator h L B φ
    let A := compactCosineTraceOperator 0 B h L φ
    ‖(hilbertTrace (logHeatSandwich τ M) - hilbertTrace (logHeatSandwich τ A)) -
      (hilbertTrace (logHeatSandwich 0 M) - hilbertTrace (logHeatSandwich 0 A))‖ ≤
      2 * ‖compactDilationAction φ‖ * Real.sqrt (Real.sqrt ((τ + τ : ℝ≥0) : ℝ)) := by
  let V := positiveRayInverseCosine
  let U := compactDilationAction φ
  let T := (spatialCutoffInChart positiveRayInverseCosine h L).comp U
  let k := ⟪bandVector B, T (bandVector B)⟫_ℂ
  let C (t : ℝ≥0) := hilbertTrace (logHeatSandwich t (meanZeroCompactCosineTraceOperator h L B φ)) -
    hilbertTrace (logHeatSandwich t (compactCosineTraceOperator 0 B h L φ))
  have hc : C 0 + k = 0 := by
    have h0 := heatCorrection_bound hB h L 0 φ
    change ‖C 0 + k‖ ≤ _ at h0
    exact norm_le_zero_iff.mp (by simpa using h0)
  have hV : ‖spatialCutoffInChart V h L‖ ≤ 1 := calc
    _ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖(spatialCutoff h L).comp V.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
      apply mul_le_mul _ _ (norm_nonneg _) zero_le_one
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (norm_spatialCutoff_le _ _)
          V.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one)
    _ = _ := by norm_num
  have hT : ‖T‖ ≤ ‖U‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hV (norm_nonneg U)).trans_eq (one_mul _))
  change ‖C τ - C 0‖ ≤ _
  rw [show C 0 = -k by exact eq_neg_of_add_eq_zero_left hc, sub_neg_eq_add]
  exact (heatCorrection_bound hB h L τ φ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by norm_num)) (by positivity))

#print axioms centralWindow_meanZeroHeat_cold_difference

end RiemannMasullo.FlatPolar

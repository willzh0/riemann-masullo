module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The real even flat Schwartz space in the log-weighted positive ray -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

/-- The even subspace of the real-place flat Schwartz space in the untwisted rational model. -/
def evenFlatRealSchwartz : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := {f | f ∈ realSchwartzFlatAtOrigin ∧ Function.Even (f : ℝ → ℂ)}
  zero_mem' := ⟨realSchwartzFlatAtOrigin.zero_mem, Function.Even.zero⟩
  add_mem' hf hg := ⟨realSchwartzFlatAtOrigin.add_mem hf.1 hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨realSchwartzFlatAtOrigin.smul_mem c hf.1, hf.2.const_smul c⟩

theorem mem_evenFlatRealSchwartz_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ evenFlatRealSchwartz ↔ f ∈ realSchwartzFlatAtOrigin ∧ Function.Even (f : ℝ → ℂ) := Iff.rfl

/-- Flatness is closed, as is each equality of evaluations at opposite points. -/
theorem evenFlatRealSchwartz_isClosed : IsClosed (evenFlatRealSchwartz : Set 𝓢(ℝ, ℂ)) := by
  change IsClosed ((realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)) ∩
    {f : 𝓢(ℝ, ℂ) | ∀ x : ℝ, f (-x) = f x})
  apply realSchwartzFlatAtOrigin_isClosed.inter
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_eq
    (TemperedDistribution.delta (-x)).continuous (TemperedDistribution.delta x).continuous

/-- The measure of the untwisted rational model at real Sobolev exponent `s`. -/
def positiveRayLogMeasure (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun x ↦ ENNReal.ofReal ((1 + Real.log x ^ 2) ^ (s / 2)))

private theorem positiveRayLogWeight_measurable (s : ℝ) :
    Measurable (fun x : ℝ ↦ ENNReal.ofReal ((1 + Real.log x ^ 2) ^ (s / 2))) := by
  fun_prop

/-- The positive continuous density on the open ray preserves its null sets. -/
theorem positiveRayLogMeasure_ae_eq_iff {β : Type*} (s : ℝ) (f g : ℝ → β) :
    f =ᵐ[positiveRayLogMeasure s] g ↔ f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g :=
  withDensity_ae_eq (positiveRayLogWeight_measurable s).aemeasurable
    (.of_forall fun _ ↦ (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)).ne')

/-- The Bessel weight in the logarithmic variable against a two-sided exponential is integrable. -/
private theorem integrable_realLogWeight_exp (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun t : ℝ ↦ Real.exp (-|t|) * (1 + t ^ 2) ^ (s / 2)) := by
  have hΓ : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * t ^ s) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using
      (Real.GammaIntegral_convergent (s := s + 1) (by linarith))
  have hp : IntegrableOn (fun t : ℝ ↦ Real.exp (-|t|) * (1 + t ^ 2) ^ (s / 2)) (Ioi 0) := by
    apply (((integrableOn_exp_neg_Ioi 0).add hΓ).const_mul ((2 : ℝ) ^ (s / 2))).mono'
      (by fun_prop)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    change 0 < t at ht
    simp only [abs_of_pos ht, Real.norm_of_nonneg (show 0 ≤
      Real.exp (-t) * (1 + t ^ 2) ^ (s / 2) by positivity)]
    have hpow : (1 + t ^ 2) ^ (s / 2) ≤ (2 : ℝ) ^ (s / 2) * (1 + t ^ s) := by
      rcases le_total t 1 with h | h
      · have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.le h
        calc
          _ ≤ (2 : ℝ) ^ (s / 2) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
          _ = (2 : ℝ) ^ (s / 2) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg ht.le s))
            (by positivity)
      · have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ h
        calc
          _ ≤ (2 * t ^ 2) ^ (s / 2) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
          _ = (2 : ℝ) ^ (s / 2) * t ^ s := by
            rw [Real.mul_rpow (by norm_num) (sq_nonneg t), ← Real.rpow_two t,
              ← Real.rpow_mul ht.le, show (2 : ℝ) * (s / 2) = s by ring]
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
    have hb := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-t)).le
    change Real.exp (-t) * (1 + t ^ 2) ^ (s / 2) ≤
      2 ^ (s / 2) * (Real.exp (-t) + Real.exp (-t) * t ^ s)
    calc
      _ ≤ _ := hb
      _ = _ := by ring
  have hn : IntegrableOn (fun t : ℝ ↦ Real.exp (-|t|) * (1 + t ^ 2) ^ (s / 2)) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero] using hp
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hn, hp⟩

private theorem exp_div_one_add_exp_sq_le (t : ℝ) :
    Real.exp t / (1 + Real.exp t) ^ 2 ≤ Real.exp (-|t|) := by
  have hpos := Real.exp_pos t
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, Real.exp_neg, ← one_div,
      div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  · rw [abs_of_nonpos ht, neg_neg, div_le_iff₀ (by positivity)]
    have h : 1 ≤ (1 + Real.exp t) ^ 2 := by nlinarith [sq_nonneg (Real.exp t)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h hpos.le

/-- In logarithmic coordinates the Jacobian divided by the quadratic damping is
bounded by `exp (-|t|)`. -/
theorem positiveRayLogMeasure_integrable_quadratic (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x : ℝ ↦ (1 + ‖x‖) ^ (-(2 : ℝ))) (positiveRayLogMeasure s) := by
  rw [positiveRayLogMeasure, integrable_withDensity_iff (positiveRayLogWeight_measurable s)
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  change IntegrableOn _ (Ioi (0 : ℝ))
  apply (integrable_comp_exp _).mp
  apply (integrable_realLogWeight_exp s hs).mono' (by fun_prop)
  filter_upwards with t
  have hbase : 0 < 1 + Real.exp t := by positivity
  have hweight : 0 < (1 + t ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
  simp only [Real.log_exp, Real.norm_of_nonneg (Real.exp_pos t).le,
    ENNReal.toReal_ofReal hweight.le, smul_eq_mul, Real.rpow_neg hbase.le, Real.rpow_two]
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ = (Real.exp t / (1 + Real.exp t) ^ 2) * (1 + t ^ 2) ^ (s / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (exp_div_one_add_exp_sq_le t) hweight.le

/-- Power two witnesses temperate growth for every nonnegative Sobolev exponent. -/
theorem positiveRayLogMeasure_hasTemperateGrowth (s : ℝ) (hs : 0 ≤ s) :
    (positiveRayLogMeasure s).HasTemperateGrowth :=
  ⟨2, positiveRayLogMeasure_integrable_quadratic s hs⟩

/-- Paper: Theorem 12.4.1.1, pp. 514–517.
The untwisted inclusion of the even flat real Schwartz space in the rational weighted
positive-ray Hilbert space. The parameter `s` is the Sobolev exponent in the log weight. -/
def evenFlatToPositiveRayLp (s : ℝ) (hs : 0 ≤ s) :
    ↥evenFlatRealSchwartz →L[ℂ] Lp ℂ 2 (positiveRayLogMeasure s) := by
  letI := positiveRayLogMeasure_hasTemperateGrowth s hs
  exact (SchwartzMap.toLpCLM ℂ ℂ 2 (positiveRayLogMeasure s)).comp evenFlatRealSchwartz.subtypeL

/-- The Hilbert class is represented by the original function on the weighted ray. -/
theorem evenFlatToPositiveRayLp_coeFn (s : ℝ) (hs : 0 ≤ s) (f : ↥evenFlatRealSchwartz) :
    (evenFlatToPositiveRayLp s hs f : ℝ → ℂ) =ᵐ[positiveRayLogMeasure s] f.val := by
  let := positiveRayLogMeasure_hasTemperateGrowth s hs
  exact f.val.coeFn_toLp 2 (positiveRayLogMeasure s)

/-- Two zeroth-derivative Schwartz seminorms suffice for all nonnegative exponents.
The constant is the weighted `L²` norm of `(1 + |x|)⁻¹`. -/
theorem evenFlatToPositiveRayLp_norm_le (s : ℝ) (hs : 0 ≤ s) (f : ↥evenFlatRealSchwartz) :
    ‖evenFlatToPositiveRayLp s hs f‖ ≤
      (eLpNorm (fun x : ℝ ↦ (1 + ‖x‖)⁻¹) 2 (positiveRayLogMeasure s)).toReal *
        (SchwartzMap.seminorm ℂ 0 0 f.val + SchwartzMap.seminorm ℂ 1 0 f.val) := by
  let q (x : ℝ) := (1 + ‖x‖)⁻¹
  have hq : MemLp q 2 (positiveRayLogMeasure s) := by
    apply (memLp_two_iff_integrable_sq (by dsimp [q]; fun_prop)).mpr
    apply (positiveRayLogMeasure_integrable_quadratic s hs).congr
    exact .of_forall fun x ↦ by
      change (1 + ‖x‖) ^ (-(2 : ℝ)) = ((1 + ‖x‖)⁻¹) ^ 2
      rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
  let P := SchwartzMap.seminorm ℂ 0 0 f.val + SchwartzMap.seminorm ℂ 1 0 f.val
  have hP : 0 ≤ P := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  calc
    ‖evenFlatToPositiveRayLp s hs f‖ ≤ ‖P • hq.toLp q‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [evenFlatToPositiveRayLp_coeFn s hs f,
        Lp.coeFn_smul P (hq.toLp q), hq.coeFn_toLp] with x hf hp hx
      rw [hf, hp, Pi.smul_apply, hx]
      change ‖f.val x‖ ≤ ‖P * (1 + ‖x‖)⁻¹‖
      rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h₀ := SchwartzMap.norm_le_seminorm ℂ f.val x
      have h₁ := SchwartzMap.norm_pow_mul_le_seminorm ℂ f.val 1 x
      rw [pow_one] at h₁
      calc
        _ = ‖f.val x‖ + ‖x‖ * ‖f.val x‖ := by ring
        _ ≤ _ := add_le_add h₀ h₁
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg hP, Lp.norm_toLp, mul_comm]

/-- Equality in the weighted Hilbert space determines an even flat Schwartz function uniquely. -/
theorem evenFlatToPositiveRayLp_injective (s : ℝ) (hs : 0 ≤ s) :
    Function.Injective (evenFlatToPositiveRayLp s hs) := by
  intro f g h
  have he : (f.val : ℝ → ℂ) =ᵐ[positiveRayLogMeasure s] g.val :=
    (evenFlatToPositiveRayLp_coeFn s hs f).symm.trans
      (h ▸ evenFlatToPositiveRayLp_coeFn s hs g)
  have heq := Measure.eqOn_open_of_ae_eq ((positiveRayLogMeasure_ae_eq_iff s _ _).mp he)
    isOpen_Ioi f.val.continuous.continuousOn g.val.continuous.continuousOn
  apply Subtype.ext
  apply SchwartzMap.ext
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← f.property.2 x, ← g.property.2 x]
    exact heq (neg_pos.mpr hx)
  · have hf := (mem_realSchwartzFlatAtOrigin_iff _).mp f.property.1 0
    have hg := (mem_realSchwartzFlatAtOrigin_iff _).mp g.property.1 0
    simpa only [iteratedDeriv_zero] using hf.trans hg.symm
  · exact heq hx

end RiemannMasullo

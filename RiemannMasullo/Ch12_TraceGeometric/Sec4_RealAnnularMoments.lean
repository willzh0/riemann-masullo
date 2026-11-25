module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The moment rows of the real annular factor

The factorial expansion used here is due to dyknapp (issue #7354).
Moment expansion of the fixed-band, positive-dilation cosine kernel at the rational real place.
The restricted frequency measure also allows an arbitrary complex input on the band.
the cosine transform automatically uses its even part.
-/

@[expose] public section

open MeasureTheory Set Filter Real
open scoped ComplexConjugate ENNReal FourierTransform

noncomputable section
namespace RiemannMasullo.RealAnnularMoments

local notation "volI" => (fun a b : ℝ ↦ Measure.restrict (volume : Measure ℝ) (Icc a b))

/-- The real signed coefficient in the cosine series. -/
def evenScalar (t : ℝ) (n : ℕ) : ℝ :=
  (-1) ^ n * t ^ (2 * n) / (2 * n).factorial

private theorem abs_evenScalar (t : ℝ) (n : ℕ) :
    |evenScalar t n| = |t| ^ (2 * n) / (2 * n).factorial := by
  simp [evenScalar, abs_div, abs_mul, abs_pow]

/-- Absolute summability of the scalar sequence, at every finite scale. -/
theorem summable_abs_evenScalar (t : ℝ) : Summable (fun n ↦ |evenScalar t n|) := by
  simpa only [abs_evenScalar] using (Real.hasSum_cosh |t|).summable

private theorem norm_ofReal_pow_le {y : ℝ} (hy : |y| ≤ 1) (k : ℕ) :
    ‖((y ^ k : ℝ) : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_pow] using
    (pow_le_one₀ (abs_nonneg y) hy (n := k))

private theorem bandRatio_bound (B : ℝ) (hB : 0 < B) :
    ∀ᵐ ξ ∂volI (-B) B, |ξ / B| ≤ 1 := by
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := -B) (b := B))] with ξ hξ
  rw [abs_div, abs_of_pos hB, div_le_one hB]
  exact abs_le.mpr hξ

private theorem dilationRatio_bound (c d : ℝ) (hc : 0 < c) :
    ∀ᵐ g ∂volI c d, |c / g| ≤ 1 := by
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := c) (b := d))] with g hg
  have hg' := hc.trans_le hg.1
  rw [abs_of_nonneg (div_nonneg hc.le hg'.le), div_le_one hg']
  exact hg.1

/-- The normalized frequency weight is square integrable on the fixed band. -/
theorem freqWeight_memLp (B : ℝ) (hB : 0 < B) (n : ℕ) :
    MemLp (fun ξ : ℝ ↦ (((ξ / B) ^ (2 * n) : ℝ) : ℂ)) 2 (volI (-B) B) := by
  refine MemLp.of_bound (by fun_prop) 1 ?_
  filter_upwards [bandRatio_bound B hB] with ξ hξ
  exact norm_ofReal_pow_le hξ _

/-- The normalized even frequency moment as a continuous complex-linear functional. -/
def frequencyMoment (B : ℝ) (hB : 0 < B) (n : ℕ) : Lp ℂ 2 (volI (-B) B) →L[ℂ] ℂ :=
  innerSL ℂ ((freqWeight_memLp B hB n).toLp _)

/-- The functional is integration against the indicated real polynomial. -/
theorem frequencyMoment_apply (B : ℝ) (hB : 0 < B) (n : ℕ) (f : Lp ℂ 2 (volI (-B) B)) :
    frequencyMoment B hB n f = ∫ ξ in Icc (-B) B, (((ξ / B) ^ (2 * n) : ℝ) : ℂ) * f ξ := by
  rw [frequencyMoment, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(freqWeight_memLp B hB n).coeFn_toLp] with ξ hξ
  rw [RCLike.inner_apply, hξ]
  simp [mul_comm]

/-- The frequency moment has operator norm at most the square root of the band length. -/
theorem norm_frequencyMoment_le (B : ℝ) (hB : 0 < B) (n : ℕ) :
    ‖frequencyMoment B hB n‖ ≤ Real.sqrt (2 * B) := by
  rw [frequencyMoment, innerSL_apply_norm]
  have hbnd : ∀ᵐ ξ ∂volI (-B) B, ‖(freqWeight_memLp B hB n).toLp _ ξ‖ ≤ 1 := by
    filter_upwards [(freqWeight_memLp B hB n).coeFn_toLp, bandRatio_bound B hB] with ξ hξ hi
    rw [hξ]
    exact norm_ofReal_pow_le hi _
  have h := Lp.norm_le_of_ae_bound (zero_le_one' ℝ) hbnd
  have hlen : (↑(measureUnivNNReal (volI (-B) B)) : ℝ) = 2 * B := by
    change ((volI (-B) B) univ).toReal = _
    rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  simpa [hlen, Real.sqrt_eq_rpow, one_div] using h

/-- The signed cosine expansion can be integrated against any integrable complex input
and any measurable real coordinate bounded in absolute value by one. -/
private theorem hasSum_integral_cos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : α → ℝ) (hu : Measurable u) (hu1 : ∀ᵐ a ∂μ, |u a| ≤ 1)
    (f : α → ℂ) (hf : Integrable f μ) (t : ℝ) :
    HasSum (fun n ↦ (evenScalar t n : ℂ) *
      ∫ a, (((u a) ^ (2 * n) : ℝ) : ℂ) * f a ∂μ)
      (∫ a, (Real.cos (t * u a) : ℂ) * f a ∂μ) := by
  let F := fun (n : ℕ) (a : α) ↦ (evenScalar t n : ℂ) *
    ((((u a) ^ (2 * n) : ℝ) : ℂ) * f a)
  have hs : HasSum (fun n ↦ ∫ a, F n a ∂μ) (∫ a, (Real.cos (t * u a) : ℂ) * f a ∂μ) := by
    apply hasSum_integral_of_dominated_convergence (fun n a ↦ |evenScalar t n| * ‖f a‖)
    · intro n
      have hm : Measurable (fun a ↦ (((u a) ^ (2 * n) : ℝ) : ℂ)) := by fun_prop
      exact (hm.aestronglyMeasurable.mul hf.1).const_mul _
    · intro n
      filter_upwards [hu1] with a ha
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_ofReal_pow_le ha _)
    · exact Eventually.of_forall fun a ↦ (summable_abs_evenScalar t).mul_right _
    · simp only [tsum_mul_right]
      exact hf.norm.const_mul _
    · refine Eventually.of_forall fun a ↦ ?_
      have h := (Complex.ofRealCLM.hasSum (Real.hasSum_cos (t * u a))).mul_right (f a)
      apply h.congr_fun
      intro n
      simp only [F, evenScalar, Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, mul_pow]
      ring
  apply hs.congr_fun
  intro n
  simp only [F, integral_const_mul]

/-- Positive-representative dilation density relative to additive Lebesgue measure. -/
def dilationDensity (φ : ℝ → ℂ) (g : ℝ) : ℂ :=
  φ g * (g ^ (-(3 / 2) : ℝ) : ℝ)

/-- A continuous test on a compact positive dilation interval gives an integrable density. -/
theorem integrableOn_dilationDensity {c d : ℝ} (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc c d)) : IntegrableOn (dilationDensity φ) (Icc c d) := by
  refine ContinuousOn.integrableOn_Icc (hφ.mul ?_)
  intro g hg
  exact (Complex.continuous_ofReal.continuousAt.comp
    (Real.continuousAt_rpow_const g _ (Or.inl (hc.trans_le hg.1).ne'))).continuousWithinAt

/-- The normalized moment of the dilation density. -/
def dilationMoment (c d : ℝ) (φ : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ g in Icc c d, (((c / g) ^ (2 * n) : ℝ) : ℂ) * dilationDensity φ g

/-- In unnormalized notation the dilation moment integrates
`φ(g) g^(-2n-3/2)`, with a scalar prefactor `c^(2*n)`. -/
theorem dilationMoment_eq_rpow {c d : ℝ} (hc : 0 < c) (φ : ℝ → ℂ) (n : ℕ) :
    dilationMoment c d φ n = ((c ^ (2 * n) : ℝ) : ℂ) *
      ∫ g in Icc c d, φ g * (g ^ (-((2 * n : ℕ) : ℝ) - 3 / 2) : ℝ) := by
  rw [dilationMoment, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := c) (b := d))] with g hg
  have hg' : 0 < g := hc.trans_le hg.1
  have ha : (c / g) ^ (2 * n) * g ^ (-(3 / 2) : ℝ) =
      c ^ (2 * n) * g ^ (-((2 * n : ℕ) : ℝ) - 3 / 2) := by
    simp only [sub_eq_add_neg, Real.rpow_add hg', Real.rpow_neg hg'.le, Real.rpow_natCast, div_pow]
    ring
  change (((c / g) ^ (2 * n) : ℝ) : ℂ) * (φ g * (g ^ (-(3 / 2) : ℝ) : ℝ)) = _
  calc
    _ = φ g * (((c / g) ^ (2 * n) * g ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul]; ring
    _ = _ := by rw [ha, Complex.ofReal_mul]; ring

/-- The norm of every normalized dilation moment is bounded by the same `L¹` mass. -/
theorem norm_dilationMoment_le {c d : ℝ} (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : IntegrableOn (dilationDensity φ) (Icc c d)) (n : ℕ) :
    ‖dilationMoment c d φ n‖ ≤ ∫ g in Icc c d, ‖dilationDensity φ g‖ := by
  have hb : ∀ᵐ g ∂volI c d, ‖(((c / g) ^ (2 * n) : ℝ) : ℂ)‖ ≤ 1 := by
    filter_upwards [dilationRatio_bound c d hc] with g hg
    exact norm_ofReal_pow_le hg _
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hφ.bdd_mul (by fun_prop) hb).norm hφ.norm
  filter_upwards [hb] with g hg
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hg

/-- The normalized coefficient row, before the factorially summable scalar is applied. -/
def coefficientRow (B : ℝ) (hB : 0 < B) (c d : ℝ) (φ : ℝ → ℂ) (n : ℕ) :
    Lp ℂ 2 (volI (-B) B) →L[ℂ] ℂ :=
  (dilationMoment c d φ n) • frequencyMoment B hB n

/-- A uniform operator norm bound for the continuous coefficient rows. -/
theorem norm_coefficientRow_le {B c d : ℝ} (hB : 0 < B) (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : IntegrableOn (dilationDensity φ) (Icc c d)) (n : ℕ) :
    ‖coefficientRow B hB c d φ n‖ ≤
      (∫ g in Icc c d, ‖dilationDensity φ g‖) * Real.sqrt (2 * B) := by
  rw [coefficientRow, norm_smul]
  exact mul_le_mul (norm_dilationMoment_le hc hφ n) (norm_frequencyMoment_le B hB n)
    (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _)

/-- The even inverse transform, evaluated directly on a frequency-band `L²` class. -/
def cosineEvaluation (B : ℝ) (f : Lp ℂ 2 (volI (-B) B)) (x : ℝ) : ℂ :=
  ∫ ξ in Icc (-B) B, (Real.cos (2 * Real.pi * x * ξ) : ℂ) * f ξ

/-- The rational positive-representative dilation operator without a spatial mask. -/
def dilationEvaluation (B c d : ℝ) (φ : ℝ → ℂ) (f : Lp ℂ 2 (volI (-B) B)) (x : ℝ) : ℂ :=
  ∫ g in Icc c d, dilationDensity φ g * cosineEvaluation B f (x / g)

private theorem hasSum_product_cos {B c d : ℝ} (hB : 0 < B) (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : IntegrableOn (dilationDensity φ) (Icc c d)) (f : Lp ℂ 2 (volI (-B) B)) (x : ℝ) :
    HasSum (fun n ↦ (evenScalar (2 * Real.pi * x * B / c) n : ℂ) *
      (dilationMoment c d φ n * frequencyMoment B hB n f))
      (dilationEvaluation B c d φ f x) := by
  let u := fun p : ℝ × ℝ ↦ (c / p.1) * (p.2 / B)
  let t := 2 * Real.pi * x * B / c
  let F := fun p : ℝ × ℝ ↦ dilationDensity φ p.1 * f p.2
  have hF : Integrable F ((volI c d).prod (volI (-B) B)) :=
    hφ.mul_prod ((Lp.memLp f).integrable (by norm_num))
  have hu : Measurable u := by dsimp [u]; fun_prop
  have hu1 : ∀ᵐ p ∂(volI c d).prod (volI (-B) B), |u p| ≤ 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (dilationRatio_bound c d hc),
      Measure.quasiMeasurePreserving_snd.ae (bandRatio_bound B hB)] with p h1 h2
    dsimp [u]
    rw [abs_mul]
    exact (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans (by simp)
  have hs := hasSum_integral_cos u hu hu1 F hF t
  have hi : Integrable (fun p ↦ (Real.cos (t * u p) : ℂ) * F p) ((volI c d).prod (volI (-B) B)) := by
    apply hF.bdd_mul (c := 1) (by fun_prop)
    exact Eventually.of_forall fun p ↦ by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (t * u p)
  have hv : (∫ p, (Real.cos (t * u p) : ℂ) * F p ∂(volI c d).prod (volI (-B) B)) =
      dilationEvaluation B c d φ f x := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := c) (b := d))] with g hg
    change _ = dilationDensity φ g * ∫ ξ in Icc (-B) B, (Real.cos (2 * Real.pi * (x / g) * ξ) : ℂ) * f ξ
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall fun ξ ↦ ?_
    have hphase : t * u (g, ξ) = 2 * Real.pi * (x / g) * ξ := by
      dsimp [t, u]
      field_simp [hc.ne', hB.ne', (hc.trans_le hg.1).ne']
    change (Real.cos (t * u (g, ξ)) : ℂ) * F (g, ξ) = _
    rw [hphase]
    dsimp only [F]
    ring
  rw [← hv]
  apply hs.congr_fun
  intro n
  congr 1
  rw [frequencyMoment_apply, dilationMoment, ← integral_prod_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun p ↦ ?_
  dsimp only [u, F]
  rw [mul_pow, Complex.ofReal_mul]
  ring

/-- Paper: Theorem 12.4.1.1, pp. 515–517. For the real place, the normalized factorial
expansion converges at every point to the masked dilation of the even inverse band transform.
Reconstruction: This is the scalar identification used in the fixed-cutoff annular factor. -/
theorem hasSum_maskedDilation {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    {φ : ℝ → ℂ} (hφ : IntegrableOn (dilationDensity φ) (Icc c d)) (ρ : ℝ → ℂ)
    (f : Lp ℂ 2 (volI (-B) B)) (x : ℝ) :
    HasSum (fun n ↦ (evenScalar (4 * Real.pi * A * B / c) n : ℂ) *
      coefficientRow B hB c d φ n f * (ρ x * (((x / (2 * A)) ^ (2 * n) : ℝ) : ℂ)))
      (ρ x * dilationEvaluation B c d φ f x) := by
  apply ((hasSum_product_cos hB hc hφ f x).mul_left (ρ x)).congr_fun
  intro n
  have ht : 2 * Real.pi * x * B / c = (4 * Real.pi * A * B / c) * (x / (2 * A)) := by
    field_simp [hA.ne', hc.ne']; ring
  have hc' : evenScalar (2 * Real.pi * x * B / c) n =
      evenScalar (4 * Real.pi * A * B / c) n * (x / (2 * A)) ^ (2 * n) := by
    rw [ht]; simp only [evenScalar, mul_pow]; ring
  rw [hc', Complex.ofReal_mul]
  simp only [coefficientRow, smul_apply, smul_eq_mul]
  ring

/-- After precomposition by any bounded frequency map, the actual coefficient functionals
satisfy an explicit factorial bound. -/
theorem norm_scaled_comp_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {B c d : ℝ} (hB : 0 < B) (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : IntegrableOn (dilationDensity φ) (Icc c d)) (T : H →L[ℂ] Lp ℂ 2 (volI (-B) B))
    (t : ℝ) (n : ℕ) :
    ‖(evenScalar t n : ℂ) • ((coefficientRow B hB c d φ n).comp T)‖ ≤
      (|t| ^ (2 * n) / (2 * n).factorial) *
        ((∫ g in Icc c d, ‖dilationDensity φ g‖) * Real.sqrt (2 * B) * ‖T‖) := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_evenScalar]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact ((coefficientRow B hB c d φ n).opNorm_comp_le T).trans
    (mul_le_mul_of_nonneg_right (norm_coefficientRow_le hB hc hφ n) (norm_nonneg T))

/-- Absolute norm summability of the scaled coefficient rows for every bounded frequency map. -/
theorem summable_norm_scaled_comp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {B c d : ℝ} (hB : 0 < B) (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : IntegrableOn (dilationDensity φ) (Icc c d)) (T : H →L[ℂ] Lp ℂ 2 (volI (-B) B))
    (t : ℝ) :
    Summable (fun n ↦ ‖(evenScalar t n : ℂ) • ((coefficientRow B hB c d φ n).comp T)‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_scaled_comp_le hB hc hφ T t)
    ((Real.hasSum_cosh |t|).summable.mul_right _)

/-- A frequency representative on the line gives the same even inverse transform as its
band class. The line representative may be specified up to almost-everywhere equality. -/
theorem cosineEvaluation_eq_evenFourierInv (B : ℝ) (f : Lp ℂ 2 (volI (-B) B))
    (b : ℝ → ℂ) (hb : Integrable b)
    (hband : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ Icc (-B) B → b ξ = 0)
    (hrep : (f : ℝ → ℂ) =ᵐ[volI (-B) B] b) (x : ℝ) :
    cosineEvaluation B f x = (𝓕⁻ b x + 𝓕⁻ b (-x)) / 2 := by
  let a := fun ξ : ℝ ↦ 2 * Real.pi * x * ξ
  let e := fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)
  have he (t : ℝ) : ‖e t‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hip : Integrable (fun ξ ↦ e (a ξ) * b ξ) :=
    hb.bdd_mul (c := 1) (by dsimp [e, a]; fun_prop) (Eventually.of_forall fun ξ ↦ (he _).le)
  have him : Integrable (fun ξ ↦ e (-(a ξ)) * b ξ) :=
    hb.bdd_mul (c := 1) (by dsimp [e, a]; fun_prop) (Eventually.of_forall fun ξ ↦ (he _).le)
  have hpos : 𝓕⁻ b x = ∫ ξ, e (a ξ) * b ξ := by
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    refine Eventually.of_forall fun ξ ↦ ?_
    dsimp only [a, e, smul_eq_mul]
    rw [show -2 * Real.pi * ξ * (-x) = 2 * Real.pi * x * ξ by ring]
  have hneg : 𝓕⁻ b (-x) = ∫ ξ, e (-(a ξ)) * b ξ := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    refine Eventually.of_forall fun ξ ↦ ?_
    dsimp only [a, e, smul_eq_mul]
    rw [show -2 * Real.pi * ξ * x = -(2 * Real.pi * x * ξ) by ring]
  have hglobal : cosineEvaluation B f x = ∫ ξ, (Real.cos (a ξ) : ℂ) * b ξ := by
    calc
      _ = ∫ ξ in Icc (-B) B, (Real.cos (a ξ) : ℂ) * b ξ := by
        apply integral_congr_ae
        filter_upwards [hrep] with ξ hξ
        change (Real.cos (a ξ) : ℂ) * f ξ = _
        rw [hξ]
      _ = _ := setIntegral_eq_integral_of_ae_compl_eq_zero <| by
        filter_upwards [hband] with ξ hξ
        intro hξ'
        simp [hξ hξ']
  rw [hglobal, hpos, hneg, ← integral_add hip him, div_eq_mul_inv, ← integral_mul_const]
  apply integral_congr_ae
  refine Eventually.of_forall fun ξ ↦ ?_
  change (Real.cos (a ξ) : ℂ) * b ξ =
    (e (a ξ) * b ξ + e (-(a ξ)) * b ξ) * (2 : ℂ)⁻¹
  simp only [e, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  ring

/-- For an arbitrary band class, extension by zero provides a concrete line representative.
The even inverse can thus be read directly in terms of two Mathlib Fourier evaluations. -/
theorem cosineEvaluation_eq_zeroExtendedInverse (B : ℝ) (f : Lp ℂ 2 (volI (-B) B)) (x : ℝ) :
    let b := (Icc (-B) B).indicator (f : ℝ → ℂ)
    cosineEvaluation B f x = (𝓕⁻ b x + 𝓕⁻ b (-x)) / 2 := by
  let b := (Icc (-B) B).indicator (f : ℝ → ℂ)
  apply cosineEvaluation_eq_evenFourierInv B f b
  · exact (integrable_indicator_iff measurableSet_Icc).2 ((Lp.memLp f).integrable (by norm_num))
  · exact Eventually.of_forall fun ξ hξ ↦ indicator_of_notMem hξ _
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := -B) (b := B))] with ξ hξ
    exact (indicator_of_mem hξ _).symm

/-- For an even line representative the full Mathlib inverse Fourier transform is exactly
the band cosine evaluation at each point. -/
theorem cosineEvaluation_eq_fourierInv_of_even (B : ℝ) (f : Lp ℂ 2 (volI (-B) B))
    (b : ℝ → ℂ) (hb : Integrable b)
    (hband : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ Icc (-B) B → b ξ = 0)
    (hrep : (f : ℝ → ℂ) =ᵐ[volI (-B) B] b)
    (heven : (fun ξ ↦ b (-ξ)) =ᵐ[volume] b) (x : ℝ) :
    cosineEvaluation B f x = 𝓕⁻ b x := by
  have hinv : 𝓕⁻ b x = 𝓕 b x := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    exact Real.fourier_congr_ae heven x
  rw [cosineEvaluation_eq_evenFourierInv B f b hb hband hrep x,
    Real.fourierInv_eq_fourier_neg b (-x), neg_neg, ← hinv]
  ring

/-- The interval integral computes the positive-ray dilation of a test supported
on the indicated positive compact interval. -/
theorem dilationEvaluation_eq_positiveRay {B c d : ℝ} (hc : 0 < c)
    (φ : ℝ → ℂ) (hφ : Function.support φ ⊆ Icc c d)
    (f : Lp ℂ 2 (volI (-B) B)) (x : ℝ) :
    dilationEvaluation B c d φ f x =
      ∫ g in Ioi (0 : ℝ), dilationDensity φ g * cosineEvaluation B f (x / g) := by
  let F := fun g ↦ dilationDensity φ g * cosineEvaluation B f (x / g)
  have hz {g : ℝ} (hg : g ∉ Icc c d) : F g = 0 := by
    have hφg : φ g = 0 := not_ne_iff.mp (fun hg' ↦ hg (hφ hg'))
    simp [F, dilationDensity, hφg]
  change (∫ g in Icc c d, F g) = ∫ g in Ioi (0 : ℝ), F g
  calc
    _ = ∫ g, F g := setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hg ↦ hz hg)
    _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg ↦
      hz (fun hg' ↦ hg (hc.trans_le hg'.1))).symm

/-- With a bounded frequency map and an even representative of its value, the normalized
series converges to the masked positive-ray dilation of the Mathlib inverse Fourier transform. -/
theorem hasSum_maskedFourierInv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Icc c d)) (hφsupp : Function.support φ ⊆ Icc c d) (ρ : ℝ → ℂ)
    (T : H →L[ℂ] Lp ℂ 2 (volI (-B) B)) (v : H) (b : ℝ → ℂ) (hb : Integrable b)
    (hband : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ Icc (-B) B → b ξ = 0)
    (hrep : (T v : ℝ → ℂ) =ᵐ[volI (-B) B] b)
    (heven : (fun ξ ↦ b (-ξ)) =ᵐ[volume] b) (x : ℝ) :
    HasSum (fun n ↦ (evenScalar (4 * Real.pi * A * B / c) n : ℂ) *
      ((coefficientRow B hB c d φ n).comp T) v * (ρ x * (((x / (2 * A)) ^ (2 * n) : ℝ) : ℂ)))
      (ρ x * ∫ g in Ioi (0 : ℝ), (φ g * (g ^ (-(3 / 2) : ℝ) : ℝ)) * 𝓕⁻ b (x / g)) := by
  have hev : cosineEvaluation B (T v) = 𝓕⁻ b :=
    funext (cosineEvaluation_eq_fourierInv_of_even B (T v) b hb hband hrep heven)
  have hs := hasSum_maskedDilation hA hB hc (integrableOn_dilationDensity hc hφ) ρ (T v) x
  rw [dilationEvaluation_eq_positiveRay hc φ hφsupp, hev] at hs
  exact hs

end RiemannMasullo.RealAnnularMoments

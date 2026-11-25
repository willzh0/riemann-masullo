module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularBand
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularFactor
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# The uncompressed annular dilation on the actual rational weighted band

The angular group is trivial over the rationals at the empty finite stage.
The half-twisted chart sends an even profile `f` to `sqrt(r) * f(r)` on norm
classes. The input projection is orthogonal in the given weighted Hilbert space.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped FourierTransform ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.AnnularBand

set_option maxSynthPendingDepth 8
set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

open RealAnnularMoments

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν(" s ")" => (μ).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (R(g)))))
local notation "H(" s ")" => Lp ℂ 2 ν(s)
local notation "Band(" B ")" => Lp ℂ 2 (volume.restrict (Icc (-B) B))
local notation "V(" hs "," B ")" => sLocalInvariantPWSobolev (F := ℚ) (S := ∅)
  hs (show (0 : ℝ) < 1/2 by norm_num) (1 : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) B


local notation "Ray(" s ")" => Lp ℂ 2 (positiveRayLogMeasure s)
local notation "c₀" => (sLocalNormOneQuotientMeasure ℚ ∅).real univ

private theorem modulus_measurable : Measurable (fun q : J ↦ R(q)) := by
  let : BorelSpace J := ⟨rfl⟩
  exact (NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)).measurable

/-- A positive integrable comparison allows the integral substitution to detect integrability
even when the input has zero integral. -/
private theorem rayIntegrable_nonneg (g : ℝ → ℝ) (hg : Measurable g)
    (hn : ∀ x, 0 ≤ g x) (hi : IntegrableOn g (Ioi 0)) :
    Integrable (fun q : J ↦ R(q) * g (R(q))) μ := by
  have hj := rayIntegral (fun x ↦ g x + Real.exp (-x)) (hg.add (by fun_prop))
  have hp : 0 < ∫ x in Ioi (0 : ℝ), g x + Real.exp (-x) := by
    rw [integral_add hi (integrableOn_exp_neg_Ioi 0), integral_exp_neg_Ioi_zero]
    exact add_pos_of_nonneg_of_pos (integral_nonneg hn) zero_lt_one
  have hi' := Integrable.of_integral_ne_zero
    (hj.trans_ne (mul_pos sLocalNormOneQuotientMeasure_ratEmpty_mass_pos hp).ne')
  apply hi'.mono' (modulus_measurable.mul (hg.comp modulus_measurable)).aestronglyMeasurable
  exact .of_forall fun q ↦ by
    change ‖R(q) * g (R(q))‖ ≤ R(q) * (g (R(q)) + Real.exp (-R(q)))
    rw [Real.norm_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (hn _))]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le) (NNReal.coe_nonneg _)

/-- Transport of a nonnegative weighted density under the actual idèle quotient norm. -/
private theorem weightedRayTransport (s : ℝ) (g : ℝ → ℝ) (hg : Measurable g)
    (hn : ∀ x, 0 ≤ g x) :
    (Integrable g (positiveRayLogMeasure s) → Integrable (fun q : J ↦ R(q) * g (R(q))) ν(s)) ∧
    (∫ q : J, R(q) * g (R(q)) ∂ν(s)) = c₀ * ∫ x, g x ∂positiveRayLogMeasure s := by
  let w (x : ℝ) := intervalSobolevDensity 0 0 s (Real.log x)
  have hwdef (x : ℝ) : w x = (1 + Real.log x ^ 2) ^ (s / 2) := by simp [w, intervalSobolevDensity]
  have hw : Measurable w := by simp only [show w = _ from funext hwdef]; fun_prop
  have hwn (x : ℝ) : 0 ≤ w x := by rw [hwdef]; positivity
  have hμ : positiveRayLogMeasure s = (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun x ↦ ENNReal.ofReal (w x)) := by simp [positiveRayLogMeasure, hwdef]
  have hm := hw.ennreal_ofReal
  have hmq : Measurable (fun q : J ↦ ENNReal.ofReal (w (R(q)))) :=
    (hw.comp modulus_measurable).ennreal_ofReal
  have hw' (x : ℝ) := ENNReal.toReal_ofReal (hwn x)
  have hq : (fun q : J ↦ (ENNReal.ofReal (w (R(q)))).toReal • (R(q) * g (R(q)))) =
      fun q : J ↦ R(q) * (w (R(q)) * g (R(q))) := by
    funext q
    rw [hw', smul_eq_mul, mul_left_comm]
  have hx : (fun x : ℝ ↦ (ENNReal.ofReal (w x)).toReal • g x) = fun x ↦ w x * g x := by
    funext x
    rw [hw', smul_eq_mul]
  have htx : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal (w x) < ⊤ :=
    .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have htq : ∀ᵐ q ∂μ, ENNReal.ofReal (w (R(q))) < ⊤ :=
    .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  constructor
  · intro hi
    rw [hμ, integrable_withDensity_iff_integrable_smul' hm htx, hx] at hi
    change Integrable _ ((μ).withDensity fun q : J ↦ ENNReal.ofReal (w (R(q))))
    rw [integrable_withDensity_iff_integrable_smul' hmq htq, hq]
    exact rayIntegrable_nonneg _ (hw.mul hg) (fun x ↦ mul_nonneg (hwn x) (hn x)) hi
  · change (∫ q : J, R(q) * g (R(q)) ∂(μ).withDensity (fun q : J ↦ ENNReal.ofReal (w (R(q))))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hmq htq, hq, hμ,
      integral_withDensity_eq_integral_toReal_smul hm htx, hx]
    exact rayIntegral _ (hw.mul hg)

/-- Half-twist of a representative on the positive norm ray. -/
def quotientHalfTwistFun (f : ℝ → ℂ) (q : J) : ℂ := (Real.sqrt (R(q)) : ℂ) * f (R(q))

private theorem halfTwist_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (quotientHalfTwistFun f) :=
  (Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp modulus_measurable)).mul
    (hf.comp modulus_measurable)

private theorem halfTwist_sq (f : ℝ → ℂ) (q : J) :
    ‖quotientHalfTwistFun f q‖ ^ 2 = R(q) * ‖f (R(q))‖ ^ 2 := by
  rw [quotientHalfTwistFun, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (NNReal.coe_nonneg _)]

private theorem halfTwist_memLp (s : ℝ) (f : ℝ → ℂ) (hf : Measurable f)
    (h : MemLp f 2 (positiveRayLogMeasure s)) : MemLp (quotientHalfTwistFun f) 2 ν(s) := by
  apply (memLp_two_iff_integrable_sq_norm (halfTwist_measurable f hf).aestronglyMeasurable).mpr
  simp_rw [halfTwist_sq]
  apply (weightedRayTransport s _ (hf.norm.pow_const 2) (fun _ ↦ sq_nonneg _)).1
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp h

private theorem halfTwist_sq_integral (s : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    (∫ q : J, ‖quotientHalfTwistFun f q‖ ^ 2 ∂ν(s)) =
      c₀ * ∫ x, ‖f x‖ ^ 2 ∂positiveRayLogMeasure s := by
  simp_rw [halfTwist_sq]
  exact (weightedRayTransport s _ (hf.norm.pow_const 2) (fun _ ↦ sq_nonneg _)).2

private theorem halfTwist_congr (s : ℝ) (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (h : f =ᵐ[positiveRayLogMeasure s] g) :
    quotientHalfTwistFun f =ᵐ[ν(s)] quotientHalfTwistFun g := by
  let d (x : ℝ) := f x - g x
  have hdm : Measurable d := hf.sub hg
  have hd : d =ᵐ[positiveRayLogMeasure s] 0 := h.mono fun x hx ↦ sub_eq_zero.mpr hx
  have hdl : MemLp d 2 (positiveRayLogMeasure s) := (memLp_congr_ae hd).mpr MemLp.zero
  have hq := halfTwist_memLp s d hdm hdl
  have hid : (∫ x, ‖d x‖ ^ 2 ∂positiveRayLogMeasure s) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂positiveRayLogMeasure s := integral_congr_ae (hd.mono fun x hx ↦ by
        change d x = 0 at hx
        simp [hx])
      _ = _ := by simp
  have h0 := (halfTwist_sq_integral s d hdm).trans (by rw [hid, mul_zero])
  have hz := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)
    ((memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq)).mp h0
  filter_upwards [hz] with q hq'
  have he : quotientHalfTwistFun d q = 0 := by
    change ‖quotientHalfTwistFun d q‖ ^ 2 = 0 at hq'
    simpa only [pow_eq_zero_iff (by decide : 2 ≠ 0), norm_eq_zero] using hq'
  simpa only [quotientHalfTwistFun, d, mul_sub, sub_eq_zero] using he

private def quotientHalfTwistVal (s : ℝ) (f : Ray(s)) : H(s) :=
  (halfTwist_memLp s f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).toLp _

private theorem quotientHalfTwistVal_coeFn (s : ℝ) (f : Ray(s)) :
    (quotientHalfTwistVal s f : J → ℂ) =ᵐ[ν(s)] quotientHalfTwistFun f :=
  (halfTwist_memLp s f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).coeFn_toLp

private theorem quotientHalfTwistVal_norm (s : ℝ) (f : Ray(s)) :
    ‖quotientHalfTwistVal s f‖ = Real.sqrt c₀ * ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt sLocalNormOneQuotientMeasure_ratEmpty_mass_pos.le, ← L2.integral_sq_norm (𝕜 := ℂ) f,
    ← L2.integral_sq_norm (𝕜 := ℂ) (quotientHalfTwistVal s f)]
  exact (integral_congr_ae ((quotientHalfTwistVal_coeFn s f).mono fun _ hx ↦ by rw [hx])).trans
    (halfTwist_sq_integral s f (Lp.stronglyMeasurable f).measurable)

/-- On the whole weighted ray Hilbert space the half-twist defines a scaled linear isometry
into the actual local quotient Sobolev Hilbert space. -/
def positiveRayToQuotientLp (s : ℝ) : Ray(s) →L[ℂ] H(s) := by
  let T : Ray(s) →ₗ[ℂ] H(s) := {
    toFun := quotientHalfTwistVal s
    map_add' := fun f g ↦ by
      apply Lp.ext
      have ha := halfTwist_congr s _ _ (Lp.stronglyMeasurable (f + g)).measurable
        ((Lp.stronglyMeasurable f).measurable.add (Lp.stronglyMeasurable g).measurable) (Lp.coeFn_add f g)
      filter_upwards [quotientHalfTwistVal_coeFn s (f + g), quotientHalfTwistVal_coeFn s f,
        quotientHalfTwistVal_coeFn s g, Lp.coeFn_add (quotientHalfTwistVal s f) (quotientHalfTwistVal s g),
        ha] with q hp hf hg hq he
      rw [hp, he, hq, Pi.add_apply, hf, hg]
      simp only [quotientHalfTwistFun, Pi.add_apply, mul_add]
    map_smul' := fun c f ↦ by
      apply Lp.ext
      have ha := halfTwist_congr s _ (c • (f : ℝ → ℂ)) (Lp.stronglyMeasurable (c • f)).measurable
        ((Lp.stronglyMeasurable f).measurable.const_smul c) (Lp.coeFn_smul c f)
      filter_upwards [quotientHalfTwistVal_coeFn s (c • f), quotientHalfTwistVal_coeFn s f,
        Lp.coeFn_smul c (quotientHalfTwistVal s f), ha] with q hp hf hq he
      change quotientHalfTwistVal s (c • f) q = (c • quotientHalfTwistVal s f) q
      rw [hp, he, hq, Pi.smul_apply, hf]
      change (Real.sqrt (R(q)) : ℂ) * (c * f (R(q))) = c * ((Real.sqrt (R(q)) : ℂ) * f (R(q)))
      ring
  }
  exact T.mkContinuous (Real.sqrt c₀) fun f ↦ (quotientHalfTwistVal_norm s f).le

theorem positiveRayToQuotientLp_coeFn (s : ℝ) (f : Ray(s)) :
    (positiveRayToQuotientLp s f : J → ℂ) =ᵐ[ν(s)] quotientHalfTwistFun f :=
  quotientHalfTwistVal_coeFn s f

/-- Every measurable representative of the ray class gives the same twisted quotient class. -/
theorem positiveRayToQuotientLp_coeFn_of_ae_eq (s : ℝ) (f : Ray(s)) (g : ℝ → ℂ)
    (hg : Measurable g) (h : (f : ℝ → ℂ) =ᵐ[positiveRayLogMeasure s] g) :
    (positiveRayToQuotientLp s f : J → ℂ) =ᵐ[ν(s)] quotientHalfTwistFun g :=
  (positiveRayToQuotientLp_coeFn s f).trans (halfTwist_congr s f g (Lp.stronglyMeasurable f).measurable hg h)

theorem positiveRayToQuotientLp_norm (s : ℝ) (f : Ray(s)) :
    ‖positiveRayToQuotientLp s f‖ = Real.sqrt c₀ * ‖f‖ := quotientHalfTwistVal_norm s f

theorem positiveRayToQuotientLp_injective (s : ℝ) : Injective (positiveRayToQuotientLp s) := by
  intro f g h
  have he := positiveRayToQuotientLp_norm s (f - g)
  rw [map_sub, h, sub_self, norm_zero] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left
    (Real.sqrt_pos.mpr sLocalNormOneQuotientMeasure_ratEmpty_mass_pos).ne'))

/-- The diagram commutes on the actual polar-free Paley–Wiener generators: inserting the
untwisted profile recovers its original weighted local theta class. -/
theorem positiveRayToQuotientLp_profile (s B : ℝ) (hs : 0 ≤ s) (f : tests B) :
    letI := positiveRayLogMeasure_hasTemperateGrowth s hs
    positiveRayToQuotientLp s ((profile f.val.val).toLp 2 (positiveRayLogMeasure s)) = thetaLift s B f := by
  let := positiveRayLogMeasure_hasTemperateGrowth s hs
  let P := profile f.val.val
  let u := P.toLp 2 (positiveRayLogMeasure s)
  apply Lp.ext
  have h := positiveRayToQuotientLp_coeFn_of_ae_eq s u P P.continuous.measurable
    (P.coeFn_toLp 2 (positiveRayLogMeasure s))
  exact h.trans ((withDensity_absolutelyContinuous μ _).ae_eq (thetaLift_ae_haar s B f)).symm

/-- Paper: Theorem 12.4.1.1, pp. 514–517.
In the rational real-place model the even flat output, half-twisted, lives in the actual
quotient Hilbert space. -/
def evenFlatToQuotientLp (s : ℝ) (hs : 0 ≤ s) : ↥evenFlatRealSchwartz →L[ℂ] H(s) :=
  (positiveRayToQuotientLp s).comp (evenFlatToPositiveRayLp s hs)

theorem evenFlatToQuotientLp_coeFn (s : ℝ) (hs : 0 ≤ s) (f : ↥evenFlatRealSchwartz) :
    (evenFlatToQuotientLp s hs f : J → ℂ) =ᵐ[ν(s)]
      fun q ↦ (Real.sqrt (R(q)) : ℂ) * f.val (R(q)) :=
  positiveRayToQuotientLp_coeFn_of_ae_eq s _ _ f.val.continuous.measurable (evenFlatToPositiveRayLp_coeFn s hs f)

theorem evenFlatToQuotientLp_coeFn_haar (s : ℝ) (hs : 0 ≤ s) (f : ↥evenFlatRealSchwartz) :
    (evenFlatToQuotientLp s hs f : J → ℂ) =ᵐ[μ]
      fun q ↦ (Real.sqrt (R(q)) : ℂ) * f.val (R(q)) :=
  (weight_ge_one s hs).absolutelyContinuous.ae_eq (evenFlatToQuotientLp_coeFn s hs f)

theorem evenFlatToQuotientLp_norm (s : ℝ) (hs : 0 ≤ s) (f : ↥evenFlatRealSchwartz) :
    ‖evenFlatToQuotientLp s hs f‖ = Real.sqrt c₀ * ‖evenFlatToPositiveRayLp s hs f‖ :=
  positiveRayToQuotientLp_norm s _

theorem evenFlatToQuotientLp_injective (s : ℝ) (hs : 0 ≤ s) : Injective (evenFlatToQuotientLp s hs) :=
  (positiveRayToQuotientLp_injective s).comp (evenFlatToPositiveRayLp_injective s hs)

private theorem inverseBandPhase (B : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-B) B))) (x : ℝ) :
    𝓕⁻ ((Icc (-B) B).indicator (f : ℝ → ℂ)) x =
      ∫ t in Icc (-B) B, Real.fourierChar (t * x) • f t := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq]
  simp_rw [mul_neg, neg_neg]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact .of_forall fun t ↦ ((Icc (-B) B).indicator_smul_apply
    (fun y ↦ Real.fourierChar (y * x)) (f : ℝ → ℂ) t).symm

private theorem cosineEvaluation_eq_evenPhase (B : ℝ) (f : Lp ℂ 2 (volume.restrict (Icc (-B) B))) (x : ℝ) :
    cosineEvaluation B f x = ((∫ t in Icc (-B) B, Real.fourierChar (t * x) • f t) +
      (∫ t in Icc (-B) B, Real.fourierChar (t * -x) • f t)) / 2 := by
  rw [cosineEvaluation_eq_zeroExtendedInverse, inverseBandPhase, inverseBandPhase]


/-- Paper: Theorem 12.4.1.1, pp. 514–517.
A fixed smooth annular cutoff and a positive compactly supported dilation test give a
nuclear operator from the weighted Hilbert space to the even flat Schwartz space. The
first identity recovers the actual orthogonally projected *input* in its Hilbert space.
The second gives the full output at each real point.
Reconstruction: The annular factor proposed by dyknapp in issue #7354 uses the positive
inner cutoff of footnote 2, p. 514, together with the real-place argument of Step II. -/
theorem exists_ratEmptyInvariantAnnularFactor (s : ℝ) (hs : 0 ≤ s)
    {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Icc c d)) (hφsupp : Function.support φ ⊆ Icc c d)
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ (∞ : ℕ∞ω) ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (he : Function.Even ρ) :
    ∃ (U : V(hs,B) →L[ℂ] Band(B)) (T : H(s) →L[ℂ] ↥evenFlatRealSchwartz),
      ‖U‖ ≤ Real.sqrt (2 / (sLocalNormOneQuotientMeasure ℚ ∅).real univ) ∧
      IsNuclearOperator T ∧
      (let f (h : H(s)) (x : ℝ) := bandEval B x (U (levelProjection s B hs h))
       (∀ h, ((levelProjection s B hs h).val : J → ℂ) =ᵐ[ν(s)]
         fun q ↦ (Real.sqrt (R(q)) : ℂ) * f h (R(q))) ∧
       ∀ h x, (T h).val x = ρ x *
         ∫ g in Ioi (0 : ℝ), (φ g * (g ^ (-(3 / 2) : ℝ) : ℝ)) * f h (x / g)) := by
  with_reducible refine (existsBandOperator s B hs).elim fun U hu ↦ ?_
  with_reducible refine hu.elim fun P hp ↦ ?_
  have hP : P = U.comp (levelProjection s B hs) := hp.2.2.1
  have hgen := hp.2.2.2
  with_reducible refine (exists_realAnnularNuclearDilation (H := H(s)) hA hB hc
    (integrableOn_dilationDensity hc hφ) ρ hρ hK h0 he P).elim fun T ht ↦ ?_
  have hval := ht.2
  with_reducible refine ⟨U, T, hp.2.1, ht.1, ?_, ?_⟩
  · intro h
    let v := levelProjection s B hs h
    have hPv : P v.val = U v := by
      rw [hP]
      let : IsClosed (V(hs,B) : Set H(s)) := by
        rw [actualLevel]; exact Submodule.isClosed_topologicalClosure _
      change U ((V(hs,B)).orthogonalProjectionOnto v.val) = U v
      exact congrArg U ((V(hs,B)).orthogonalProjectionOnto_mem_subspace_eq_self v)
    simpa only [hPv] using allLevel_inversion s B hs P hgen v
  · intro h x
    have hev (t : ℝ) : cosineEvaluation B (P h) t = bandEval B t (P h) := by
      rw [cosineEvaluation_eq_evenPhase, ← bandEval_integral, ← bandEval_integral,
        bandEval_even_after_projection s B hs P U hgen hP]
      ring
    refine (hval h x).trans (congrArg (fun z : ℂ ↦ ρ x * z) ?_)
    refine (dilationEvaluation_eq_positiveRay hc φ hφsupp (P h) x).trans ?_
    apply integral_congr_ae
    refine .of_forall fun g ↦ ?_
    have hPh : P h = U (levelProjection s B hs h) :=
      congrArg (fun L : H(s) →L[ℂ] Band(B) ↦ L h) hP
    exact congrArg (fun z : ℂ ↦ dilationDensity φ g * z)
      ((hev (x / g)).trans (congrArg (bandEval B (x / g)) hPh))

/-- Paper: Lemma C.3.2.2, p. 695, applied to the fixed annular factor.
Both compositions with the actual half-twisted inclusion are nuclear. The
quotient output is represented by the annular dilation of the projected input.
Reconstruction: This is the fixed rational annular model for the reduction on p. 515. -/
theorem exists_ratEmptyAnnularHilbertFactor (s : ℝ) (hs : 0 ≤ s)
    {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Icc c d)) (hφsupp : Function.support φ ⊆ Icc c d)
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ (∞ : ℕ∞ω) ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (he : Function.Even ρ) :
    ∃ (U : V(hs,B) →L[ℂ] Band(B)) (T : H(s) →L[ℂ] ↥evenFlatRealSchwartz),
      IsNuclearOperator T ∧ IsNuclearOperator (T.comp (evenFlatToQuotientLp s hs)) ∧
      IsNuclearOperator ((evenFlatToQuotientLp s hs).comp T) ∧
      (let f (h : H(s)) (x : ℝ) := bandEval B x (U (levelProjection s B hs h))
       (∀ h, ((levelProjection s B hs h).val : J → ℂ) =ᵐ[ν(s)]
         fun q ↦ (Real.sqrt (R(q)) : ℂ) * f h (R(q))) ∧
       ∀ h, (evenFlatToQuotientLp s hs (T h) : J → ℂ) =ᵐ[ν(s)] fun q ↦
         (Real.sqrt (R(q)) : ℂ) * (ρ (R(q)) *
           ∫ g in Ioi (0 : ℝ), (φ g * (g ^ (-(3 / 2) : ℝ) : ℝ)) * f h ((R(q)) / g))) := by
  with_reducible refine (exists_ratEmptyInvariantAnnularFactor s hs hA hB hc hφ hφsupp
    ρ hρ hK h0 he).elim fun U hu ↦ ?_
  with_reducible refine hu.elim fun T ht ↦ ?_
  have hj := isNuclearOperator_factor_comps _ (evenFlatToQuotientLp_injective s hs) T ht.2.1
  have hval := ht.2.2.2
  with_reducible refine ⟨U, T, ht.2.1, hj.1, hj.2, ht.2.2.1, fun h ↦ ?_⟩
  filter_upwards [evenFlatToQuotientLp_coeFn s hs (T h)] with q hq
  exact hq.trans (congrArg (fun z : ℂ ↦ (Real.sqrt (R(q)) : ℂ) * z) (hval h (R(q))))

/-- Every vector in the smaller space has an actual flat adelic theta preimage. -/
theorem evenFlatToQuotientLp_eq_flatTheta (s : ℝ) (hs : 0 ≤ s) (v : ↥evenFlatRealSchwartz) :
    ∃ g : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      realCoordinates.symm g ∈ realSchwartzFlatAtOrigin ∧
      (evenFlatToQuotientLp s hs v : J → ℂ) =ᵐ[ν(s)]
        modulationWeight m (1/2) (sLocalHomogeneousAdelicThetaLinearMap ℚ ∅
          (1 : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) g) := by
  obtain ⟨g, hg, hp⟩ := exists_flat_profile_preimage
    (⟨v.val, v.property.1⟩ : ↥realSchwartzFlatAtOrigin) v.property.2
  refine ⟨g, hg, (evenFlatToQuotientLp_coeFn s hs v).trans (.of_forall fun q ↦ ?_)⟩
  rw [weightedTheta_eq, hp]


private theorem quotientHalfTwistFun_eq_sqrt_mul (f : ℝ → ℂ) (q : J) :
    quotientHalfTwistFun f q = (Real.sqrt (R(q)) : ℂ) * f (R(q)) := rfl

/-- The local half-twist multiplies the norm-coordinate representative by the square root of its argument. -/
theorem quotientHalfTwistFun_apply (f : ℝ → ℂ) (q : J) :
    quotientHalfTwistFun f q = (Real.sqrt (R(q)) : ℂ) * f (R(q)) :=
  quotientHalfTwistFun_eq_sqrt_mul f q

/-- The squared integral of a measurable half-twisted representative transforms by
the norm-one Haar mass at every real Sobolev exponent. -/
theorem integral_sq_quotientHalfTwistFun (s : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    (∫ q : J, ‖quotientHalfTwistFun f q‖ ^ 2 ∂ν(s)) =
      c₀ * ∫ x, ‖f x‖ ^ 2 ∂positiveRayLogMeasure s :=
  halfTwist_sq_integral s f hf

end RiemannMasullo.AnnularBand

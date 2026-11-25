import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalOrderZeroHeatTrace
import RiemannMasullo.Ch12_TraceGeometric.Sec4_RatEmptyAveragedTraceFinitePart
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped CompactlySupported NumberField.AdeleRing NNReal ENNReal Topology

namespace RiemannMasullo.AnnularBand
open RatEmptyRealLevelBridge

set_option maxSynthPendingDepth 8
set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν₀" => (μ).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (Real.log (R(g)))))
local notation "Hq" => Lp ℂ 2 ν₀
local notation "ν₊" => volume.restrict (Ioi (0 : ℝ))
local notation "H₊" => Lp ℂ 2 ν₊
local notation "posR(" g ")" => NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)

local instance : BorelSpace J := ⟨rfl⟩
local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : SecondCountableTopology J := by
  let (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) : ProperSpace (v.val.adicCompletion ℚ) :=
    properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing ℚ ∅) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ)))
  let : SecondCountableTopology (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).1.secondCountableTopology
  infer_instance
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
local instance : (μ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1

/-- At order zero the translation in the Chapter 9 action is precisely the quotient Haar translation used by the interval operator. -/
theorem translation_eq_intervalTranslation (g : J) :
    hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl g = ratEmptyTranslation g := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  exact ((withDensity_absolutelyContinuous μ _).ae_eq
    (hardySobolevTranslation_apply μ m 0 0 0 le_rfl le_rfl g v)).trans
      (coeFn_ratEmptyTranslation g v).symm

/-- All radii of quotient idèles are positive, so the native window with floor zero is the sharp upper cutoff. -/
theorem cutoff_eq_intervalCutoff (L : ℝ) :
    modulatedAbsoluteCutoffOperator m ν₀ (Ioc 0 L) measurableSet_Ioc = ratEmptyCutoff L := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [modulatedAbsoluteCutoffOperator_apply m ν₀ (Ioc 0 L) measurableSet_Ioc v,
    coeFn_lpIndicatorCLM ν₀ (measurableSet_ratEmptyNormLE L) v] with q hm hc
  change _ = ratEmptyCutoff L v q
  change (ratEmptyCutoff L v) q = _ at hc
  rw [hm, hc]
  by_cases h : R(q) ≤ L
  · rw [Set.indicator_of_mem (show q ∈ {j : J | (((sIdeleQuotientNorm ℚ ∅ j).val : ℝ)) ≤ L} from h)]
    simp [modulatedAbsoluteCutoff, h, posR(q)]
  · rw [Set.indicator_of_notMem (show q ∉ {j : J | (((sIdeleQuotientNorm ℚ ∅ j).val : ℝ)) ≤ L} from h)]
    simp [modulatedAbsoluteCutoff, h]

private theorem logRadiusEmbedding : MeasurableEmbedding (fun q : J ↦ Real.log (R(q))) := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (a : ℝ≥0ˣ) : E.symm a = Real.log (a.val : ℝ) := by
    obtain ⟨t, rfl⟩ := E.surjective a
    rw [E.symm_apply_apply]
    exact (Real.log_exp t).symm
  have h := E.symm.isClosedEmbedding.measurableEmbedding.comp RatEmptyMeasureCoordinate.normEquiv.measurableEmbedding
  convert h using 1
  funext q
  exact (he _).symm

set_option maxHeartbeats 1500000 in
/-- The arithmetic Chapter 9 action is the prescribed Haar interval action at every vector when its true test is supported in the interval. -/
theorem testAction_eq_realHaarInterval (ψ : BruhatCompactSupport J) (w : ℝ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hψ : ∀ q : J, ψ.val q = (w (R(q)) : ℂ))
    (hs : ∀ r : ℝ, r ∉ Icc a b → w r = 0) (v : Hq) :
    hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl ψ v =
      ∫ g in a..b, ((w g / g : ℝ) : ℂ) • ratEmptyTranslation (realHaarNormClass g) v := by
  have hc : Continuous ψ.val := continuous_of_bruhatSmooth
    ((mem_bruhatSmoothSubmodule_iff ψ.val).1 ψ.property.1)
  have hact := hardySobolev_eq_integral_translation_of_convolution μ m 0 0 0 le_rfl le_rfl
    (hc.integrable_of_hasCompactSupport ψ.property.2) ψ.property.2 _
    (hardySobolevTestAction_apply μ m 0 0 0 le_rfl le_rfl ψ) v
  let f (t : ℝ) := (w (Real.exp t) : ℂ) • ratEmptyTranslation (realHaarNormClass (Real.exp t)) v
  have class_r (q : J) : realHaarNormClass (R(q)) = q := by
    apply sIdeleQuotientNorm_ratEmpty_injective
    exact Units.ext (NNReal.eq (realHaarNormClass_norm (posR(q))))
  have pos (q : J) : 0 < R(q) := posR(q)
  refine hact.trans ?_
  calc
    _ = ∫ q : J, f (Real.log (R(q))) ∂μ := by
      apply integral_congr_ae
      exact .of_forall fun q ↦ by simp [f, Real.exp_log (pos q), hψ, class_r, translation_eq_intervalTranslation]
    _ = ∫ t : ℝ, f t := quotientLogNorm_measurePreserving.integral_comp logRadiusEmbedding f
    _ = ∫ g in Ioi (0 : ℝ), g⁻¹ • f (Real.log g) := (integral_comp_log_Ioi_zero f).symm
    _ = ∫ g in Ioi (0 : ℝ), (Ioc a b).indicator
          (fun z : ℝ ↦ ((w z / z : ℝ) : ℂ) • ratEmptyTranslation (realHaarNormClass z) v) g := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi,
        ae_restrict_of_ae ((volume : Measure ℝ).ae_ne a)] with g hg hga
      change 0 < g at hg
      rw [show f (Real.log g) = (w g : ℂ) • ratEmptyTranslation (realHaarNormClass g) v by simp [f, Real.exp_log hg]]
      by_cases hin : g ∈ Ioc a b
      · rw [indicator_of_mem hin]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
        congr 1
        push_cast
        exact mul_comm _ _ |>.trans (div_eq_mul_inv _ _).symm
      · rw [indicator_of_notMem hin]
        have hout : g ∉ Icc a b := fun h ↦ hin ⟨lt_of_le_of_ne h.1 hga.symm, h.2⟩
        simp [hs _ hout]
    _ = _ := by
      have hsub : Ioc a b ⊆ Ioi 0 := fun _ hr ↦ ha.trans hr.1
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset hsub,
        intervalIntegral.integral_of_le hab]

open scoped ContDiff

/-- All ordinary smooth profiles supported in a compact positive window are actual rational
quotient Bruhat tests, also when the window contains the identity. -/
theorem exists_bruhatTest_of_smooth_radialWindow (w : ℝ → ℝ) (hw : ContDiff ℝ (∞) w)
    {a b : ℝ} (ha : 0 < a) (hs : ∀ r : ℝ, r ∉ Icc a b → w r = 0) :
    ∃ ψ : BruhatCompactSupport J, ∀ q : J, ψ.val q = (w (R(q)) : ℂ) := by
  let H : ℝ → ℂ := fun t ↦ (w (Real.exp t) : ℂ)
  have hHs : ContDiff ℝ (∞) H := Complex.ofRealCLM.contDiff.comp (hw.comp Real.contDiff_exp)
  have hHc : HasCompactSupport H := by
    apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    exact closure_minimal (t := Icc (Real.log a) (Real.log b)) (fun t ht ↦ by
      by_contra hout
      have he : Real.exp t ∉ Icc a b := fun hg ↦ hout
        ⟨by simpa using Real.log_le_log ha hg.1, by simpa using Real.log_le_log (Real.exp_pos t) hg.2⟩
      exact ht (by simp [H, hs _ he])) isClosed_Icc
  let φ : Multiplicative ℝ → ℂ := fun t ↦ H t.toAdd
  have hφ : φ ∈ bruhatCompactSupportSubmodule (Multiplicative ℝ) :=
    (mem_bruhatCompactSupportSubmodule_real_iff φ).2 ⟨hHs, hHc⟩
  let π : J →ₜ* Multiplicative ℝ := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m
  have hp : HasCompactSupport (φ ∘ π) := hφ.2.comp_homeomorph
    (RatEmptyMeasureCoordinate.normHomeomorph.trans positiveRealLogEquiv.toHomeomorph)
  refine ⟨⟨φ ∘ π, (mem_bruhatSmoothSubmodule_iff _).2
    (isBruhatSmooth_comp_continuousMonoidHom π ((mem_bruhatSmoothSubmodule_iff _).1 hφ.1)), hp⟩, ?_⟩
  intro q
  change (w (Real.exp (positiveRealLogEquiv (m q)).toAdd) : ℂ) = _
  rw [positiveRealLogEquiv_apply, Real.exp_log (posR(q))]
set_option maxHeartbeats 1300000 in
/-- For a compact quotient Bruhat test with the indicated real profile across norm one,
the finite part of its Chapter 9 compression is the sharp reciprocal-window finite part. -/
theorem tendsto_quotientBruhatLevel_cold_centralFinitePart
    {δ C : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C) {w : ℝ → ℝ}
    (hw : Continuous w)
    (hw1 : ∀ g ∈ Icc (centralDilation δ) (centralDilation (-δ)), |w g - w 1| ≤ C * |g - 1|)
    (ψ : BruhatCompactSupport J) (hψ : ∀ q : J, ψ.val q = (w (R(q)) : ℂ))
    (hs : ∀ r : ℝ, r ∉ Icc (centralDilation δ) (centralDilation (-δ)) → w r = 0)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {B L : ι → ℝ}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 < L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ hilbertTrace (quotientBruhatLevelCompressionNuclear (hB i) 0 (L i) ψ) -
        ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l (𝓝 (actualCentralTraceFinitePart δ w : ℂ)) := by
  have ha : 0 < centralDilation δ := by
    change 0 < (1 + δ)⁻¹
    positivity
  have hab : centralDilation δ ≤ centralDilation (-δ) := by
    change (1 + δ)⁻¹ ≤ (1 + -δ)⁻¹
    exact inv_anti₀ (by linarith : 0 < 1 + -δ) (by linarith)
  obtain ⟨A, hA, hn, hT⟩ :=
    tendsto_actualHaarAveragedCompressionTrace_centralFinitePart 1 hδ0 hδ1 hC hw hw1 hB hL hBL
  have hAct (i : ι) : A i = hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl ψ := by
    apply ContinuousLinearMap.ext
    intro v
    exact (hA i v).trans (testAction_eq_realHaarInterval ψ w ha hab hψ hs v).symm
  refine hT.congr fun i ↦ ?_
  congr 2
  apply Subtype.ext
  change ((orderZeroLevelProjection (B i)).comp
    ((ratEmptyCutoff (L i)).comp ((A i).comp (orderZeroLevelProjection (B i))))) =
    quotientBruhatLevelCompression (B i) 0 (L i) ψ
  rw [quotientBruhatLevelCompression, cutoff_eq_intervalCutoff (L i), hAct i]

/-- A single native quotient test realizes each smooth physical profile on the reciprocal
window and gives its zero-heat, zero-floor centered trace on every exhausting schedule. -/
theorem exists_bruhatTest_cold_centralFinitePart {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {w : ℝ → ℝ} (hw : ContDiff ℝ (∞) w)
    (hs : ∀ r : ℝ, r ∉ Icc (centralDilation δ) (centralDilation (-δ)) → w r = 0) :
    ∃ ψ : BruhatCompactSupport J, (∀ q : J, ψ.val q = (w (R(q)) : ℂ)) ∧
      ∀ {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {B L : ι → ℝ}
        (hB : ∀ i, 0 < B i) (_hL : ∀ i, 0 < L i),
        Tendsto (fun i ↦ B i * L i) l atTop →
        Tendsto (fun i ↦ hilbertTrace (quotientBruhatLevelCompressionNuclear (hB i) 0 (L i) ψ) -
          ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l (𝓝 (actualCentralTraceFinitePart δ w : ℂ)) := by
  have ha : 0 < centralDilation δ := by
    change 0 < (1 + δ)⁻¹
    positivity
  have h1 : (1 : ℝ) ∈ Icc (centralDilation δ) (centralDilation (-δ)) := by
    change (1 + δ)⁻¹ ≤ 1 ∧ 1 ≤ (1 + -δ)⁻¹
    exact ⟨(inv_le_one₀ (by linarith)).2 (by linarith), (one_le_inv₀ (by linarith)).2 (by linarith)⟩
  obtain ⟨ψ, hψ⟩ := exists_bruhatTest_of_smooth_radialWindow w hw ha hs
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (centralDilation δ) (centralDilation (-δ))) (hw.continuous_deriv (by simp)).continuousOn
  have hC0 := (norm_nonneg _).trans (hC 1 h1)
  refine ⟨ψ, hψ, ?_⟩
  intro ι l hl B L hB hL hBL
  apply tendsto_quotientBruhatLevel_cold_centralFinitePart hδ0 hδ1 hC0 hw.continuous _ ψ hψ hs hB hL hBL
  intro g hg
  simpa [Real.norm_eq_abs] using (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ hw.differentiable (by simp) x) hC h1 hg

#print axioms exists_bruhatTest_cold_centralFinitePart

#print axioms exists_bruhatTest_of_smooth_radialWindow
#print axioms translation_eq_intervalTranslation
#print axioms cutoff_eq_intervalCutoff
#print axioms testAction_eq_realHaarInterval
#print axioms tendsto_quotientBruhatLevel_cold_centralFinitePart

end RiemannMasullo.AnnularBand

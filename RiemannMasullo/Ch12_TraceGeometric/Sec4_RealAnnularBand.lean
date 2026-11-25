module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import Mathlib.Analysis.Fourier.LpSpace
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Fourier coordinates on the rational invariant weighted band

For the empty finite stage over the rationals, the quotient norm gives the
positive real coordinate. A theta generator untwists to the even sign sum of
its real Schwartz profile, with the angular Haar mass retained. Plancherel
and the generator bound extend the Fourier coordinates to the closed level
and its orthogonal projection.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing FourierTransform SchwartzMap Topology
  ComplexInnerProductSpace ComplexConjugate

namespace RiemannMasullo.AnnularBand

set_option maxSynthPendingDepth 8
set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "η" => sLocalNormOneQuotientMeasure ℚ ∅
local notation "c₀" => (η).real univ
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "Z" => sAdelePolarSubspace ℚ ∅
local notation "X" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))
local notation "ω₀" => (1 : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
local notation "hh" => (show (0:ℝ) < 1/2 by norm_num)
local notation "ν(" s ")" => (μ).withDensity (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (R(g)))))
local notation "H(" s ")" => Lp ℂ 2 ν(s)
local notation "Band(" B ")" => Lp ℂ 2 (volume.restrict (Icc (-B) B))
local notation "coord" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

local notation "V(" hs "," B ")" => sLocalInvariantPWSobolev (F := ℚ) (S := ∅) hs hh ω₀ B
local notation "μB(" B ")" => volume.restrict (Icc (-B) B)

/-- The test submodule indexing precisely the generators in the actual local Sobolev level. -/
def tests (B : ℝ) : Submodule ℂ Z :=
  (sLocalPWTests (F := ℚ) (S := ∅) (T := ∅) le_rfl (sLocalPWProductRegion ∅ B)).comap (Z).subtype

/-- The actual local half-twisted theta lift on banded polar tests, as a linear map. -/
def thetaLift (s B : ℝ) : tests B →ₗ[ℂ] H(s) where
  toFun f := sLocalPWThetaSobolevMap (F := ℚ) (S := ∅) (s := s) hh ω₀ f.val
  map_add' f g := by
    let L : Z →ₗ[ℂ] (J → ℂ) := (modulationWeight m (1/2)).comp
      ((ContinuousMap.coeFnLinearMap ℂ).comp ((sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω₀).comp (Z).subtype))
    change MemLp.toLp (L (f.val + g.val)) _ =
      MemLp.toLp (L f.val) _ + MemLp.toLp (L g.val) _
    simp only [map_add]
    rfl
  map_smul' a f := by
    let L : Z →ₗ[ℂ] (J → ℂ) := (modulationWeight m (1/2)).comp
      ((ContinuousMap.coeFnLinearMap ℂ).comp ((sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω₀).comp (Z).subtype))
    change MemLp.toLp (L (a • f.val)) _ = a • MemLp.toLp (L f.val) _
    simp only [map_smul]
    rfl

theorem actualLevel {s : ℝ} (hs : 0 ≤ s) (B : ℝ) :
    V(hs,B) = (LinearMap.range (thetaLift s B)).topologicalClosure := by
  change (Submodule.span ℂ (range (thetaLift s B))).topologicalClosure = _
  exact congrArg (fun P : Submodule ℂ H(s) ↦ P.topologicalClosure)
    (Submodule.span_eq (LinearMap.range (thetaLift s B)))

/-- A bounded assignment on the generators first extends to the closed weighted level and
then composes with its actual orthogonal projection. -/
private theorem projectedExtension {s : ℝ} (hs : 0 ≤ s) (B C : ℝ) (hC : 0 ≤ C)
    (d : tests B →ₗ[ℂ] Band(B)) (bound : ∀ f, ‖d f‖ ≤ C * ‖thetaLift s B f‖) :
    ∃ (T : V(hs,B) →L[ℂ] Band(B)) (A : H(s) →L[ℂ] Band(B)),
      ‖A‖ ≤ C ∧ ‖T‖ ≤ C ∧
      (letI : IsClosed (V(hs,B) : Set H(s)) := by rw [actualLevel]; exact Submodule.isClosed_topologicalClosure _
       A = T.comp (V(hs,B)).orthogonalProjectionOnto) ∧
      ∀ f, A (thetaLift s B f) = d f := by
  let V := V(hs,B)
  have hVr : V = (LinearMap.range (thetaLift s B)).topologicalClosure := actualLevel hs B
  let : IsClosed (V : Set H(s)) := hVr ▸ Submodule.isClosed_topologicalClosure _
  let e := (thetaLift s B).codRestrict V fun f ↦ hVr ▸
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ f)
  have dense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff, ← range_comp]
    change (V : Set H(s)) ⊆ closure (range (thetaLift s B))
    rw [hVr]
    exact subset_rfl
  let T := d.extendOfNorm e
  let Q := V.orthogonalProjectionOnto
  have tnorm : ‖T‖ ≤ C := LinearMap.opNorm_extendOfNorm_le dense hC bound
  refine ⟨T, T.comp Q, (T.opNorm_comp_le Q).trans ?_, tnorm, rfl, fun f ↦ ?_⟩
  · calc ‖T‖ * ‖Q‖ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left V.orthogonalProjectionOnto_norm_le (norm_nonneg _)
         _ ≤ C := (mul_one _).le.trans tnorm
  · change T (V.orthogonalProjectionOnto (e f : H(s))) = _
    exact (congrArg T (V.orthogonalProjectionOnto_mem_subspace_eq_self (e f))).trans
      (LinearMap.extendOfNorm_eq dense ⟨C, bound⟩ f)

def realCoordinates : 𝓢(ℝ, ℂ) ≃L[ℂ] X := ratTrivialHomogeneousTheta_quotient_realEquiv.choose

private theorem inCoordinates (f : X) (x : SAdeleRing ℚ ∅) :
    f (Multiplicative.ofAdd x) = realCoordinates.symm f (coord (x.1 Rat.infinitePlace)) := by
  rw [← ratTrivialHomogeneousTheta_quotient_realEquiv.choose_spec (realCoordinates.symm f) x]
  exact congrArg (fun h : X ↦ h (Multiplicative.ofAdd x)) (realCoordinates.apply_symm_apply f).symm

def sumSigns : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := ContinuousLinearMap.id ℂ _ +
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv

/-- The unitarily *unnormalized* positive-ray profile is the sign sum times angular mass.
For an even input the sum is twice that input. -/
def profile : X →L[ℂ] 𝓢(ℝ, ℂ) := (c₀ : ℂ) • sumSigns.comp realCoordinates.symm.toContinuousLinearMap

theorem profile_apply (f : X) (x : ℝ) :
    profile f x = (c₀ : ℂ) * (realCoordinates.symm f x + realCoordinates.symm f (-x)) := rfl

theorem profile_even (f : X) : Function.Even (profile f) := by
  intro x
  simp only [profile_apply, neg_neg, add_comm (realCoordinates.symm f (-x))]

/-- This equality concerns the actual weighted generator, at every quotient point of the
continuous representative and at almost every point of its Hilbert-space class. -/
theorem weightedTheta_eq (f : X) (g : J) :
    modulationWeight m (1/2) (sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω₀ f) g =
      ((Real.sqrt (R(g)) : ℝ) : ℂ) * profile f (R(g)) := by
  change ((R(g) ^ (1/2 : ℝ) : ℝ) : ℂ) * _ = _
  rw [← Real.sqrt_eq_rpow, sLocalHomogeneousTheta_ratEmpty_eq_evenProfile
    ω₀ f (realCoordinates.symm f) (inCoordinates f) g, profile_apply]
  rfl

theorem thetaLift_ae_haar (s B : ℝ) (f : tests B) :
    (thetaLift s B f : J → ℂ) =ᵐ[μ] fun g ↦ (Real.sqrt (R(g)) : ℂ) * profile f.val.val (R(g)) :=
  (sLocalPWThetaSobolevMap_apply (F := ℚ) (S := ∅) (s := s) hh ω₀ f.val).trans
    (.of_forall (weightedTheta_eq f.val.val))

private theorem normPush :
    (μ).map (sIdeleQuotientNorm ℚ ∅) = ((η) univ) • positiveRealHaar := by
  let : BorelSpace J := ⟨rfl⟩
  let : MeasurableSpace (sIdeleQuotientNorm ℚ ∅).ker := borel _
  let : BorelSpace (sIdeleQuotientNorm ℚ ∅).ker := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace (sIdeleQuotientNorm ℚ ∅).ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ ∅).isCompact_preimage isCompact_singleton)
  let : (η).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  let : IsFiniteMeasure (η) := CompactSpace.isFiniteMeasure
  let π := Units.map (adeleProjection ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))).toMonoidHom
  have hπ : Continuous π := (continuous_fst.prodMk (continuous_pi fun w : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
    (RestrictedProduct.continuous_eval w.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* (SAdeleRing ℚ ∅)ˣ := ⟨π.comp (canonicalIdeleNormSection ℚ),
    hπ.comp (canonicalIdeleNormSection_continuous ℚ)⟩
  have hτ : RightInverse τ (sIdeleNorm ℚ ∅) := sIdeleNorm_project_canonicalSection ℚ ∅
  let j (p : (sIdeleQuotientNorm ℚ ∅).ker × ℝ≥0ˣ) := p.1.val * (QuotientGroup.mk (τ p.2) : J)
  have hj : Measurable j :=
    ((continuous_subtype_val.comp continuous_fst).mul
      ((show Continuous (QuotientGroup.mk : (SAdeleRing ℚ ∅)ˣ → J) from continuous_quotient_mk').comp
        (τ.continuous.comp continuous_snd))).measurable
  have hjm : (sIdeleQuotientNorm ℚ ∅) ∘ j = Prod.snd := by
    funext p
    change sIdeleQuotientNorm ℚ ∅ (p.1.val * QuotientGroup.mk (τ p.2)) = p.2
    rw [map_mul, MonoidHom.mem_ker.mp p.1.property, one_mul]
    exact (sIdeleQuotientNorm_mk ℚ ∅ (τ p.2)).trans (hτ p.2)
  have hp : ((η).prod positiveRealHaar).map j = μ :=
    (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).2 τ hτ
  rw [← hp, Measure.map_map (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous.measurable hj,
    hjm, Measure.map_snd_prod]

/-- The theta half-twist exactly cancels the reciprocal Jacobian of `dx/x`.
The Haar constant is retained on both sides of the chart. -/
theorem rayIntegral (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ q : J, R(q) * g (R(q)) ∂μ) = c₀ * ∫ x in Ioi (0 : ℝ), g x := by
  let : BorelSpace J := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let d (t : ℝ≥0ˣ) := (t.val : ℝ) * g (t.val : ℝ)
  have hm : Measurable (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) := (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hd : Measurable d := hm.mul (hg.comp hm)
  let e (u : ℝ) := Units.mk0 (Real.exp u).toNNReal (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos u)))
  have he : Measurable e := measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  change (∫ q : J, d (sIdeleQuotientNorm ℚ ∅ q) ∂μ) = _
  rw [← integral_map (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous.measurable.aemeasurable hd.aestronglyMeasurable,
    normPush, integral_smul_measure]
  change _ * (∫ t : ℝ≥0ˣ, d t ∂volume.map e) = _
  rw [integral_map he.aemeasurable hd.aestronglyMeasurable]
  congr 1
  simpa only [d, e, Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos _).le, smul_eq_mul]
    using MeasureTheory.integral_comp_exp g

private theorem sqLp {α : Type*} [MeasurableSpace α] {ν : Measure α} (f : α → ℂ) (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, inv_eq_one_div, ← Real.sqrt_eq_rpow]
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))]

/-- The nonnegative Sobolev exponent gives a weighted measure dominating quotient Haar. -/
theorem weight_ge_one (s : ℝ) (hs : 0 ≤ s) : μ ≤ ν(s) := by
  calc μ = (μ).withDensity 1 := withDensity_one.symm
       _ ≤ _ := withDensity_mono (.of_forall fun q ↦ ?_)
  change 1 ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (R(q))))
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  simp only [intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
  exact Real.one_le_rpow (by nlinarith [sq_nonneg (Real.log (R(q)))]) (by positivity)

/-- On the true weighted level each full-line even profile has L²-norm at most
`sqrt(2 / angular mass)` times the weighted norm. -/
theorem profileBound (s B : ℝ) (hs : 0 ≤ s) (f : tests B) :
    ‖(profile f.val.val).toLp 2‖ ≤ Real.sqrt (2 / c₀) * ‖thetaLift s B f‖ := by
  let P := profile f.val.val
  let Fq (q : J) := modulationWeight m (1/2) (sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω₀ f.val.val) q
  have hF : MemLp Fq 2 ν(s) := sLocalPWTheta_memLp (F := ℚ) (S := ∅) (s := s) hh ω₀ f.val
  have hQ : (∫ x : J, ‖Fq x‖ ^ 2 ∂μ) ≤ ‖thetaLift s B f‖ ^ 2 :=
    (integral_mono_measure (weight_ge_one s hs) (.of_forall fun _ ↦ sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF)).trans_eq (sqLp Fq hF).symm
  have hEq (q : J) : ‖Fq q‖ ^ 2 = R(q) * ‖P (R(q))‖^2 := by
    dsimp only [Fq]
    rw [weightedTheta_eq, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hRay := rayIntegral (fun x ↦ ‖P x‖^2) ((P.continuous.norm.pow 2).measurable)
  simp_rw [hEq] at hQ
  rw [hRay] at hQ
  have hEven (t : ℝ) : ‖P |t|‖ ^ 2 = ‖P t‖ ^ 2 := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, profile_even _]
  have hLine : ‖P.toLp 2‖^2 = 2 * ∫ x in Ioi (0:ℝ), ‖P x‖^2 := by
    calc _ = ∫ t : ℝ, ‖P t‖^2 := sqLp _ (P.memLp 2 volume)
         _ = ∫ t : ℝ, ‖P |t|‖^2 := integral_congr_ae (.of_forall fun x ↦ (hEven x).symm)
         _ = _ := integral_comp_abs (f := fun t : ℝ ↦ ‖P t‖^2)
  have hc := sLocalNormOneQuotientMeasure_ratEmpty_mass_pos
  have htwo : 0 ≤ 2 / c₀ := by positivity
  have result : ‖P.toLp 2‖^2 ≤ (Real.sqrt (2 / c₀) * ‖thetaLift s B f‖)^2 := by
    rw [hLine, mul_pow, Real.sq_sqrt htwo, div_mul_eq_mul_div, le_div_iff₀ hc]
    calc 2 * (∫ x in Ioi (0:ℝ), ‖P x‖^2) * c₀ = 2 * (c₀ * (∫ x in Ioi (0:ℝ), ‖P x‖^2)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hQ zero_le_two
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 result

private theorem transition (f : X) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) f = f := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) f
    (Multiplicative.ofAdd (Multiplicative.toAdd x)) = f x
  rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w ↦ absurd w.2 (Finset.notMem_empty _))]
  rfl

private theorem coord_abs (z : Rat.infinitePlace.Completion) : |coord z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z, ← map_zero coord]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem coord_supp (B : ℝ) (f : tests B) :
    tsupport (𝓕 (realCoordinates.symm f.val.val) : 𝓢(ℝ,ℂ)) ⊆ Icc (-B) B := by
  classical
  obtain ⟨g, hg, -, hsupp⟩ := (mem_sLocalPWTests (F := ℚ) (S := ∅) (T := ∅) le_rfl
    (sLocalPWProductRegion ∅ B) f.val.val).mp f.property
  rw [transition] at hg
  refine closure_minimal (fun t ht ↦ ?_) isClosed_Icc
  let y : SAdeleRing ℚ ∅ := ⟨Pi.single Rat.infinitePlace ((coord).symm t), 0⟩
  have hy : coord (y.1 Rat.infinitePlace) = t := by
    change coord ((Pi.single Rat.infinitePlace ((coord).symm t)) Rat.infinitePlace) = t
    rw [Pi.single_eq_same, RingEquiv.apply_symm_apply]
  have hF := sAdeleSchwartzFourier_ratEmpty_apply (realCoordinates.symm f.val.val) f.val.val
    (inCoordinates f.val.val) y
  rw [hy] at hF
  have hm : Multiplicative.ofAdd y ∈ tsupport (sAdeleSchwartzFourier g).val := by
    apply subset_tsupport
    change sAdeleSchwartzFourier g (Multiplicative.ofAdd y) ≠ 0
    rw [hg, hF]
    exact ht
  have hb := hsupp hm
  change y ∈ sLocalPWProductRegion ∅ B at hb
  have hn : ‖y.1 Rat.infinitePlace‖ ≤ B := by
    simpa [sLocalPWProductRegion, ← Unique.eq_default Rat.infinitePlace] using hb
  rw [← coord_abs, hy] at hn
  exact abs_le.mp hn

private theorem fourier_signs (f : 𝓢(ℝ,ℂ)) : 𝓕 (sumSigns f) = sumSigns (𝓕 f) := by
  let R := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv (F := ℂ)
  change 𝓕 (f + R f) = sumSigns (𝓕 f)
  rw [FourierTransform.fourier_add]
  ext t
  change 𝓕 f t + 𝓕 (R f) t = 𝓕 f t + 𝓕 f (-t)
  apply congrArg (fun z : ℂ ↦ 𝓕 f t + z)
  change 𝓕 ((f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ) t = 𝓕 (f : ℝ → ℂ) (-t)
  exact Real.fourier_comp_linearIsometry _ _ _

theorem fourier_profile_apply (f : X) (t : ℝ) :
    𝓕 (profile f) t = (c₀ : ℂ) *
      (𝓕 (realCoordinates.symm f) t + 𝓕 (realCoordinates.symm f) (-t)) := by
  change (𝓕 ((c₀ : ℂ) • sumSigns (realCoordinates.symm f)) : 𝓢(ℝ,ℂ)) t = _
  rw [FourierTransform.fourier_smul, fourier_signs]
  rfl

theorem fourier_profile_support (B : ℝ) (f : tests B) :
    tsupport (𝓕 (profile f.val.val) : 𝓢(ℝ,ℂ)) ⊆ Icc (-B) B := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra h
  have hn : -t ∉ Icc (-B) B := by
    intro hn
    exact h ⟨by linarith [hn.2], by linarith [hn.1]⟩
  have hbound := coord_supp B f
  have h₁ := image_eq_zero_of_notMem_tsupport (fun ht ↦ h (hbound ht))
  have h₂ := image_eq_zero_of_notMem_tsupport (fun ht ↦ hn (hbound ht))
  exact ht (by simp only [fourier_profile_apply, h₁, h₂, add_zero, mul_zero])

/-- The signed and half-untwisted real profile transformed by Mathlib's unitary Fourier operator
and restricted to Lebesgue measure on the given interval. -/
def bandData (B : ℝ) : tests B →ₗ[ℂ] Band(B) :=
  (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-B) B)).toLinearMap.comp
    ((Lp.fourierTransformₗᵢ ℝ ℂ).toLinearMap.comp
      ((SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 volume).toLinearMap.comp
        (profile.toLinearMap.comp ((Z).subtype.comp (tests B).subtype))))

theorem bandData_coe (B : ℝ) (f : tests B) :
    (bandData B f : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-B) B)] (𝓕 (profile f.val.val) : 𝓢(ℝ,ℂ)) := by
  change ⇑(LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-B) B)
    (𝓕 ((profile f.val.val).toLp 2))) =ᵐ[_] _
  rw [SchwartzMap.toLp_fourier_eq]
  exact (LpToLpRestrictCLM_coeFn ℂ _ _).trans
    (ae_restrict_of_ae (SchwartzMap.coeFn_toLp (𝓕 (profile f.val.val) : 𝓢(ℝ,ℂ)) 2 volume))

private theorem restriction_norm (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-B) B) u‖ ≤ ‖u‖ :=
  norm_Lp_toLp_restrict_le (Icc (-B) B) u

theorem bandData_bound (s B : ℝ) (hs : 0 ≤ s) (f : tests B) :
    ‖bandData B f‖ ≤ Real.sqrt (2/c₀) * ‖thetaLift s B f‖ := by
  let p := (profile f.val.val).toLp 2 volume
  have h₁ : ‖bandData B f‖ ≤ ‖(𝓕 p : Lp ℂ 2 (volume : Measure ℝ))‖ := restriction_norm B (𝓕 p)
  exact h₁.trans ((Lp.norm_fourier_eq p).le.trans (profileBound s B hs f))

/-- The concrete, bounded positive-ray half-untwisting and Plancherel coefficient operator
on the actual rational level, with the ambient orthogonal projection included. -/
theorem existsBandOperator (s B : ℝ) (hs : 0 ≤ s) :
    ∃ (T : V(hs,B) →L[ℂ] Band(B)) (A : H(s) →L[ℂ] Band(B)),
      ‖A‖ ≤ Real.sqrt (2/c₀) ∧ ‖T‖ ≤ Real.sqrt (2/c₀) ∧
      (letI : IsClosed (V(hs,B) : Set H(s)) := by rw [actualLevel]; exact Submodule.isClosed_topologicalClosure _
       A = T.comp (V(hs,B)).orthogonalProjectionOnto) ∧
      ∀ f, A (thetaLift s B f) = bandData B f :=
  projectedExtension hs B _ (Real.sqrt_nonneg _) (bandData B) (bandData_bound s B hs)

theorem inversion_on_generators (B : ℝ) (f : tests B) (x : ℝ) :
    (∫ t in Icc (-B) B, Real.fourierChar (t*x) • (bandData B f : ℝ → ℂ) t) = profile f.val.val x := by
  have hb := bandData_coe B f
  calc
    _ = ∫ t in Icc (-B) B, Real.fourierChar (t*x) • (𝓕 (profile f.val.val) : 𝓢(ℝ,ℂ)) t :=
      integral_congr_ae (hb.mono fun t h ↦ congrArg (fun z : ℂ ↦ Real.fourierChar (t*x) • z) h)
    _ = ∫ t, Real.fourierChar (t*x) • (𝓕 (profile f.val.val) : 𝓢(ℝ,ℂ)) t := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      rw [image_eq_zero_of_notMem_tsupport (fun hm ↦ ht (fourier_profile_support B f hm)), smul_zero]
    _ = 𝓕⁻ (𝓕 (profile f.val.val) : 𝓢(ℝ,ℂ)) x := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq]
      simp only [mul_neg, neg_neg]
    _ = _ := congrArg (fun h : 𝓢(ℝ,ℂ) ↦ h x) (FourierTransform.fourierInv_fourier_eq _)

def inversePhase (x t : ℝ) : ℂ := conj (Real.fourierChar (t*x) : ℂ)

/-- The inverse Fourier phase has unit norm at every frequency. -/
theorem inversePhase_memLp (B x : ℝ) : MemLp (inversePhase x) 2 μB(B) := by
  let : IsFiniteMeasure μB(B) := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top
  have hc : Continuous (inversePhase x) := (continuous_star.comp
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))))
  exact MemLp.of_bound hc.aestronglyMeasurable 1 (.of_forall fun t ↦ by simp [inversePhase])

/-- With Lean's linear-in-the-second-slot convention, the inverse Fourier evaluation is the
inner product against the conjugate phase on the band. -/
def bandEval (B x : ℝ) : Band(B) →L[ℂ] ℂ :=
  innerSL ℂ ((inversePhase_memLp B x).toLp (inversePhase x))

theorem bandEval_integral (B x : ℝ) (u : Band(B)) :
    bandEval B x u = ∫ t in Icc (-B) B, Real.fourierChar (t*x) • u t := by
  rw [bandEval, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (inversePhase_memLp B x)] with t ht
  rw [ht, RCLike.inner_apply', inversePhase]
  simp [Circle.smul_def]

theorem bandEval_generator (B x : ℝ) (f : tests B) :
    bandEval B x (bandData B f) = profile f.val.val x :=
  (bandEval_integral B x _).trans (inversion_on_generators B f x)

/-- The continuous inverse-band representative is even at every point, for every
member of the completed local quotient level. -/
theorem bandEval_even_on_level (s B : ℝ) (hs : 0 ≤ s) (A : H(s) →L[ℂ] Band(B))
    (hA : ∀ f, A (thetaLift s B f) = bandData B f) (u : V(hs,B)) (x : ℝ) :
    bandEval B (-x) (A u.val) = bandEval B x (A u.val) := by
  have hu : u.val ∈ closure (range (thetaLift s B)) := (actualLevel hs B).le u.property
  have hc : IsClosed {h : H(s) | bandEval B (-x) (A h) = bandEval B x (A h)} :=
    isClosed_eq ((bandEval B (-x)).continuous.comp A.continuous) ((bandEval B x).continuous.comp A.continuous)
  apply closure_minimal (t := {h : H(s) | bandEval B (-x) (A h) = bandEval B x (A h)}) _ hc hu
  rintro _ ⟨f,rfl⟩
  change bandEval B (-x) (A (thetaLift s B f)) = bandEval B x (A (thetaLift s B f))
  rw [hA, bandEval_generator, bandEval_generator]
  exact profile_even _ x

def levelProjection (s B : ℝ) (hs : 0 ≤ s) : H(s) →L[ℂ] V(hs,B) := by
  letI : IsClosed (V(hs,B) : Set H(s)) := by rw [actualLevel]; exact Submodule.isClosed_topologicalClosure _
  exact (V(hs,B)).orthogonalProjectionOnto

theorem bandEval_even_after_projection (s B : ℝ) (hs : 0 ≤ s)
    (A : H(s) →L[ℂ] Band(B)) (T : V(hs,B) →L[ℂ] Band(B))
    (hA : ∀ f, A (thetaLift s B f) = bandData B f)
    (hproj : A = T.comp (levelProjection s B hs)) (u : H(s)) (x : ℝ) :
    bandEval B (-x) (A u) = bandEval B x (A u) := by
  let : IsClosed (V(hs,B) : Set H(s)) := by rw [actualLevel]; exact Submodule.isClosed_topologicalClosure _
  let v := levelProjection s B hs u
  have huv : A (v : H(s)) = A u := by
    rw [hproj]
    change T ((V(hs,B)).orthogonalProjectionOnto (v : H(s))) = T v
    exact congrArg T ((V(hs,B)).orthogonalProjectionOnto_mem_subspace_eq_self v)
  simpa only [huv] using bandEval_even_on_level s B hs A hA v x

theorem bandEval_norm (B x : ℝ) (hB : 0 ≤ B) : ‖bandEval B x‖ = Real.sqrt (2*B) := by
  rw [bandEval, innerSL_apply_norm, Lp.norm_toLp,
      (inversePhase_memLp B x).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [inversePhase, Complex.norm_conj, Circle.norm_coe, Real.one_rpow, integral_const, smul_eq_mul,
    mul_one, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal
      (show 0 ≤ B - -B by linarith), ENNReal.toReal_ofNat, inv_eq_one_div, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  congr 1
  ring

private theorem extend_representation {Y D : Type*} [MeasurableSpace Y] (δ : Measure Y)
    (j : D → Lp ℂ 2 δ) (u : Lp ℂ 2 δ) (hu : u ∈ closure (range j))
    (L : Y → Lp ℂ 2 δ →L[ℂ] ℂ) (hL : ∀ f, ∀ᵐ q ∂δ, (j f) q = L q (j f)) :
    ∀ᵐ q ∂δ, u q = L q u := by
  obtain ⟨v, hvmem, hv⟩ := mem_closure_iff_seq_limit.mp hu
  choose f hf using hvmem
  obtain ⟨k, hk, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae'
  let Rep (z : Lp ℂ 2 δ) := ∀ᵐ q ∂δ, z q = L q z
  have hgens (n : ℕ) : Rep (v (k n)) := (congrArg Rep (hf (k n))).mp (hL (f (k n)))
  filter_upwards [hAE, ae_all_iff.2 hgens] with q hq hgen
  have hp := (L q).continuous.continuousAt.tendsto.comp (hv.comp hk)
  exact tendsto_nhds_unique hq (hp.congr' (.of_forall fun n ↦ (hgen n).symm))

/-- For every member of the *completed actual* level, the inverse band integral represents
its half-untwisted class almost everywhere for the weighted quotient measure. -/
theorem allLevel_inversion (s B : ℝ) (hs : 0 ≤ s) (A : H(s) →L[ℂ] Band(B))
    (hA : ∀ f, A (thetaLift s B f) = bandData B f)
    (u : V(hs,B)) :
    (u.val : J → ℂ) =ᵐ[ν(s)] fun q ↦ (Real.sqrt (R(q)) : ℂ) * bandEval B (R(q)) (A u.val) := by
  have hu : u.val ∈ closure (range (thetaLift s B)) := (actualLevel hs B).le u.property
  let L (q : J) := (Real.sqrt (R(q)) : ℂ) • ((bandEval B (R(q))).comp A)
  apply extend_representation ν(s) (thetaLift s B) u.val hu L
  intro f
  have hac : ν(s) ≪ μ := withDensity_absolutelyContinuous _ _
  have hbase := hac.ae_le (thetaLift_ae_haar s B f)
  filter_upwards [hbase] with q hq
  change _ = (Real.sqrt (R(q)) : ℂ) * bandEval B (R(q)) (A (thetaLift s B f))
  rw [hA f, bandEval_generator]
  exact hq

/-- Every even real Schwartz function flat at zero is the actual untwisted homogeneous
theta profile of a flat rational-place test. Sign summation and angular averaging give
the factor `2*c₀`, and taking its inverse supplies an explicit preimage. -/
theorem exists_flat_profile_preimage (p : realSchwartzFlatAtOrigin) (hp : Function.Even p.val) :
    ∃ g : X, realCoordinates.symm g ∈ realSchwartzFlatAtOrigin ∧ profile g = p.val := by
  let k : ℂ := ((2:ℂ) * (c₀ : ℂ))⁻¹
  let g := realCoordinates (k • p.val)
  have hg : realCoordinates.symm g = k • p.val := realCoordinates.symm_apply_apply _
  refine ⟨g, hg ▸ realSchwartzFlatAtOrigin.smul_mem k p.property, ?_⟩
  have hc : (c₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr sLocalNormOneQuotientMeasure_ratEmpty_mass_pos.ne'
  ext x
  rw [profile_apply, hg]
  change (c₀ : ℂ) * (k * p.val x + k * p.val (-x)) = _
  rw [hp x]
  dsimp only [k]
  field_simp
  ring

end RiemannMasullo.AnnularBand

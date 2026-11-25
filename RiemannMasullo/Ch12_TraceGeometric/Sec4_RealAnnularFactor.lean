module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularFlat
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularRay
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularMoments
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.InfiniteSum

/-!
# Nuclear factor of the annular rational real-place dilation

Theorem 12.4.1.1, pp. 514–517, at fixed cutoffs. The reconstruction by
dyknapp (issue #7354) uses a smooth mask supported away from zero. Its
normalized even monomials are bounded in every Schwartz seminorm, and the
corresponding coefficient rows carry an absolutely summable factorial weight.
-/

public noncomputable section

open Bornology Filter MeasureTheory Set Topology
open scoped SchwartzMap

namespace RiemannMasullo

open RealAnnularMoments
open scoped ContDiff FourierTransform

private theorem annularNuclearSeries {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y] [CompleteSpace Y]
    (c : ℕ → ℂ) (lin : ℕ → H →L[ℂ] ℂ) (v : ℕ → Y)
    (hc : Summable (fun n ↦ ‖c n‖)) (hlin : ∃ K : ℝ, ∀ n, ‖lin n‖ ≤ K)
    (hdisc : ∃ B : Set Y, IsBanachDisc B ∧ ∀ n, v n ∈ B) :
    ∃ T : H →L[ℂ] Y, IsNuclearOperator T ∧
      ∀ h, HasSum (fun n ↦ (c n * lin n h) • v n) (T h) := by
  obtain ⟨B, hB, hmem⟩ := hdisc
  obtain ⟨K, hK⟩ := hlin
  have hK0 : 0 ≤ K := (norm_nonneg (lin 0)).trans (hK 0)
  let terms (h : H) (n : ℕ) := (c n * lin n h) • v n
  let seminorms := PolynormableSpace.withSeminorms ℂ Y
  have vector_bound (p : {q : Seminorm ℂ Y // Continuous q}) :
      ∃ M > (0 : ℝ), ∀ n, p.val (v n) ≤ M := by
    obtain ⟨M, hM, h⟩ := seminorms.isVonNBounded_iff_seminorm_bounded.mp hB.bounded p
    exact ⟨M, hM, fun n ↦ (h (v n) (hmem n)).le⟩
  have row_bound (h : H) (n : ℕ) : ‖lin n h‖ ≤ K * ‖h‖ :=
    ((lin n).le_opNorm h).trans (mul_le_mul_of_nonneg_right (hK n) (norm_nonneg h))
  have majorant (p : Seminorm ℂ Y) (M : ℝ) (hM : ∀ n, p (v n) ≤ M) (h : H) (n : ℕ) :
      p (terms h n) ≤ ‖c n‖ * (K * ‖h‖ * M) := by
    rw [show p (terms h n) = ‖c n‖ * ‖lin n h‖ * p (v n) by simp only [terms, map_smul_eq_mul, norm_mul]]
    calc
      _ ≤ (‖c n‖ * (K * ‖h‖)) * M := by gcongr <;> first | exact row_bound h n | exact hM n
      _ = _ := by ring
  have hs (h : H) : Summable (terms h) := by
    apply summable_of_summable_seminorms seminorms
    intro p
    obtain ⟨M, hM, hv⟩ := vector_bound p
    exact Summable.of_nonneg_of_le (fun n ↦ apply_nonneg p.val _) (majorant p.val M hv h)
      (hc.mul_right (K * ‖h‖ * M))
  let S : H →ₗ[ℂ] Y :=
    { toFun h := ∑' n, terms h n
      map_add' h k := by simpa [terms, mul_add, add_smul] using (hs h).tsum_add (hs k)
      map_smul' a h := by
        change (∑' n, terms (a • h) n) = a • ∑' n, terms h n
        exact ((hs (a • h)).hasSum.unique (((hs h).hasSum.const_smul a).congr_fun
          fun n ↦ by simp only [terms, map_smul, smul_eq_mul, smul_smul]; ring_nf)) }
  have hcont : Continuous S := by
    apply seminorms.continuous_of_continuous_comp S
    intro p
    obtain ⟨M, hM, hv⟩ := vector_bound p
    let C := (∑' n, ‖c n‖) * (K * M)
    apply Seminorm.continuous' (r := C)
    refine mem_of_superset (Metric.ball_mem_nhds (0 : H) one_pos) fun h hh ↦ ?_
    rw [Metric.mem_ball, dist_zero_right] at hh
    apply (p.val.comp S).mem_closedBall_zero.mpr
    change p.val (∑' n, terms h n) ≤ C
    have hl := p.property.continuousAt.tendsto.comp (hs h).hasSum
    have hr := hc.hasSum.mul_right (K * ‖h‖ * M)
    calc
      _ ≤ (∑' n, ‖c n‖) * (K * ‖h‖ * M) := le_of_tendsto_of_tendsto' hl hr fun F ↦ by
        exact (Finset.le_sum_of_subadditive p.val (map_zero _).le
          (map_add_le_add _) F _).trans (Finset.sum_le_sum fun n _ ↦ majorant p.val M hv h n)
      _ ≤ C := by
        dsimp only [C]
        gcongr
        exact (mul_le_of_le_one_right hK0 hh.le)
  let T : H →L[ℂ] Y := ⟨S, hcont⟩
  have eqc : EquicontinuousAt (fun n h ↦ lin n h) 0 := by
    apply Metric.equicontinuousAt_of_continuity_modulus (fun h : H ↦ K * ‖h‖)
    · simpa using ((continuous_norm : Continuous (norm : H → ℝ)).tendsto (0 : H)).const_mul K
    · exact Eventually.of_forall fun h n ↦ by simpa using row_bound h n
  refine ⟨T, (isNuclearOperator_iff_nonempty_presentation T).mpr ⟨?_⟩, fun h ↦ (hs h).hasSum⟩
  exact
    { coeff := c, functional := lin, disc := B, isBanachDisc := hB
      vector := fun n ↦ ⟨v n, Submodule.subset_span (hmem n)⟩
      vector_mem := hmem, summable_coeff := hc, equicontinuous := eqc
      hasSum := fun h ↦ (hs h).hasSum }

private theorem annularFlatSeries_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ 𝓢(ℝ, ℂ)) (hS : IsClosed (S : Set 𝓢(ℝ, ℂ)))
    (c : ℕ → ℂ) (lin : ℕ → H →L[ℂ] ℂ) (v : ℕ → S)
    (hc : Summable (fun n ↦ ‖c n‖)) (hlin : ∃ K : ℝ, ∀ n, ‖lin n‖ ≤ K)
    (hvB : IsVonNBounded ℂ (range v))
    (f : H → ℝ → ℂ)
    (hf : ∀ h x, HasSum (fun n ↦ (c n * lin n h) * (v n).val x) (f h x)) :
    ∃ T : H →L[ℂ] S, IsNuclearOperator T ∧ ∀ h x, (T h).val x = f h x := by
  let : PolynormableSpace ℂ S :=
    (LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ) S.subtype).toPolynormableSpace
  let : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
  let : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨T, hT, hseries⟩ := annularNuclearSeries c lin v hc hlin
    (exists_isBanachDisc_of_isVonNBounded_range v hvB)
  refine ⟨T, hT, fun h x ↦ ?_⟩
  let eval : S →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ x).comp
      ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).comp S.subtypeL)
  exact ((hseries h).mapL eval).unique (hf h x)

private theorem flatPowers_bounded_of_image (S : Submodule ℂ 𝓢(ℝ, ℂ))
    (u : ℕ → ↥realSchwartzFlatAtOrigin) (h : IsVonNBounded ℂ (range u))
    (hm : ∀ n, (u n).val ∈ S) :
    IsVonNBounded ℂ (range (fun n ↦ (⟨(u n).val, hm n⟩ : S))) := by
  have flat := LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)
    realSchwartzFlatAtOrigin.subtype
  have target := LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ) S.subtype
  apply target.isVonNBounded_iff_seminorm_bddAbove.mpr
  intro i
  obtain ⟨M, hM⟩ := flat.isVonNBounded_iff_seminorm_bddAbove.mp h i
  refine ⟨M, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact hM ⟨_, ⟨n, rfl⟩, rfl⟩

/-- The subspace has the seminorms induced from the Schwartz space. -/
instance : PolynormableSpace ℂ ↥evenFlatRealSchwartz :=
  (LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)
    evenFlatRealSchwartz.subtype).toPolynormableSpace

instance : IsUniformAddGroup ↥evenFlatRealSchwartz :=
  evenFlatRealSchwartz.toAddSubgroup.isUniformAddGroup

/-- Paper: Theorem 12.4.1.1, pp. 514–517.
The masked positive dilation lifts to a nuclear operator with values in the
even flat real Schwartz space. The frequency input is an arbitrary bounded
map into the finite band. The formula gives the full output at every real point.
Reconstruction: This is the factorial expansion of the annular repair in issue #7354. -/
theorem exists_realAnnularNuclearDilation {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    {φ : ℝ → ℂ} (hφ : IntegrableOn (dilationDensity φ) (Icc c d))
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (he : Function.Even ρ)
    (P : H →L[ℂ] Lp ℂ 2 (volume.restrict (Icc (-B) B))) :
    ∃ T : H →L[ℂ] ↥evenFlatRealSchwartz, IsNuclearOperator T ∧
      ∀ h x, (T h).val x = ρ x * dilationEvaluation B c d φ (P h) x := by
  obtain ⟨u, hu, hb, hel⟩ := exists_even_realAnnularFlatPowers ρ A hA hρ hK h0 he
  have hm (n : ℕ) : (u n).val ∈ evenFlatRealSchwartz :=
    (mem_evenFlatRealSchwartz_iff _).2 ⟨(u n).property, (hel n).1⟩
  let v (n : ℕ) : ↥evenFlatRealSchwartz := ⟨(u n).val, hm n⟩
  let t := 4 * Real.pi * A * B / c
  let row (n : ℕ) := (coefficientRow B hB c d φ n).comp P
  apply annularFlatSeries_apply evenFlatRealSchwartz evenFlatRealSchwartz_isClosed
    (fun n ↦ (evenScalar t n : ℂ)) row v
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using summable_abs_evenScalar t
  · refine ⟨(∫ g in Icc c d, ‖dilationDensity φ g‖) * Real.sqrt (2 * B) * ‖P‖, fun n ↦ ?_⟩
    exact ((coefficientRow B hB c d φ n).opNorm_comp_le P).trans
      (mul_le_mul_of_nonneg_right (norm_coefficientRow_le hB hc hφ n) (norm_nonneg P))
  · exact flatPowers_bounded_of_image _ u hb hm
  · intro h x
    simpa only [v, hu, Complex.ofReal_pow, t, row, ContinuousLinearMap.comp_apply] using
      hasSum_maskedDilation hA hB hc hφ ρ (P h) x

/-- For an even compact-band Fourier representative the nuclear lift is exactly
the positive-ray dilation of its inverse Fourier transform, including the half twist. -/
theorem exists_realAnnularNuclearFourierInv {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Icc c d)) (hφsupp : Function.support φ ⊆ Icc c d)
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (he : Function.Even ρ)
    (P : H →L[ℂ] Lp ℂ 2 (volume.restrict (Icc (-B) B))) :
    ∃ T : H →L[ℂ] ↥evenFlatRealSchwartz, IsNuclearOperator T ∧
      ∀ h (b : ℝ → ℂ), Integrable b →
        (∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ Icc (-B) B → b ξ = 0) →
        ((P h : ℝ → ℂ) =ᵐ[volume.restrict (Icc (-B) B)] b) →
        ((fun ξ ↦ b (-ξ)) =ᵐ[volume] b) →
        ∀ x, (T h).val x = ρ x *
          ∫ g in Ioi (0 : ℝ), (φ g * (g ^ (-(3 / 2) : ℝ) : ℝ)) * 𝓕⁻ b (x / g) := by
  obtain ⟨T, hT, hval⟩ := exists_realAnnularNuclearDilation hA hB hc
    (integrableOn_dilationDensity hc hφ) ρ hρ hK h0 he P
  refine ⟨T, hT, fun h b hb hband hrep hev x ↦ ?_⟩
  have hcos := funext (cosineEvaluation_eq_fourierInv_of_even B (P h) b hb hband hrep hev)
  rw [hval, dilationEvaluation_eq_positiveRay hc φ hφsupp, hcos]
  rfl

/-- Paper: Lemma C.3.2.2, p. 695, applied in the untwisted rational ray chart.
The inclusion of the flat output into the weighted ray is injective. The
two induced endomorphisms are nuclear, and the Hilbert output agrees almost
everywhere with the same uncompressed masked integral. -/
theorem exists_realAnnularNuclearRayFactor (s : ℝ) (hs : 0 ≤ s)
    {A B c d : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    {φ : ℝ → ℂ} (hφ : IntegrableOn (dilationDensity φ) (Icc c d))
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hK : tsupport ρ ⊆ Icc (-A) A)
    (h0 : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (he : Function.Even ρ)
    (P : Lp ℂ 2 (positiveRayLogMeasure s) →L[ℂ] Lp ℂ 2 (volume.restrict (Icc (-B) B))) :
    ∃ T : Lp ℂ 2 (positiveRayLogMeasure s) →L[ℂ] ↥evenFlatRealSchwartz,
      IsNuclearOperator T ∧ IsNuclearOperator (T.comp (evenFlatToPositiveRayLp s hs)) ∧
      IsNuclearOperator ((evenFlatToPositiveRayLp s hs).comp T) ∧
      ∀ h, ((evenFlatToPositiveRayLp s hs (T h)) : ℝ → ℂ) =ᵐ[positiveRayLogMeasure s]
        fun x ↦ ρ x * dilationEvaluation B c d φ (P h) x := by
  obtain ⟨T, hT, hval⟩ := exists_realAnnularNuclearDilation hA hB hc hφ ρ hρ hK h0 he P
  have hj := isNuclearOperator_factor_comps _ (evenFlatToPositiveRayLp_injective s hs) T hT
  refine ⟨T, hT, hj.1, hj.2, fun h ↦ ?_⟩
  exact (evenFlatToPositiveRayLp_coeFn s hs (T h)).trans (.of_forall (hval h))

end RiemannMasullo

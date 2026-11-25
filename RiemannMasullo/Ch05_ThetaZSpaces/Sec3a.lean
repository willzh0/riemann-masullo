module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import RiemannMasullo.ForMathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b_IsotypicAverages
public import RiemannMasullo.Ch03_IdelicZeta.Sec4
public import Mathlib.Analysis.Distribution.Support

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import RiemannMasullo.AppD_SchwartzBruhat.Sec2b
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
public import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import RiemannMasullo.ForMathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Geometry.Manifold.PartitionOfUnity
import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction.CoordinatePlane
import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction.Schwartz
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion
import Mathlib.LinearAlgebra.Dual.Lemmas
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import RiemannMasullo.ForMathlib.Topology.MetricSpace.CompactQuotient

/-! # Non-archimedean principal values and distributions supported at the origin

Masullo, §5.3.1–5.3.2, pp. 240–249.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions NNReal NumberField.AdeleRing SchwartzMap TensorProduct

namespace RiemannMasullo

/-- A series whose terms are dominated, seminorm by seminorm, by summable real sequences is
summable in a complete space whose topology is given by those seminorms, and each seminorm of
its sum is at most the sum of the dominating sequence. -/
private theorem realSchwartzFlatQuotient_strongDual_summable {𝕜 E ι : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (x : ℕ → E) (u : ι → ℕ → ℝ)
    (hu : ∀ i, Summable (u i)) (hx : ∀ i n, p i (x n) ≤ u i n) :
    Summable x ∧ ∀ i, p i (∑' n, x n) ≤ ∑' n, u i n := by
  have hu0 (i : ι) (n : ℕ) : 0 ≤ u i n := (apply_nonneg _ _).trans (hx i n)
  have hsum : Summable x := by
    rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
    intro e he
    obtain ⟨⟨I, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp he
    have hv (i : ι) : ∃ s : Finset ℕ, ∀ t : Finset ℕ, Disjoint t s → ∑ n ∈ t, u i n < r := by
      obtain ⟨s, hs⟩ := (hu i).vanishing (Metric.ball_mem_nhds (0 : ℝ) hr)
      refine ⟨s, fun t ht ↦ ?_⟩
      have := hs t ht
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans_lt this
    choose s hs using hv
    refine ⟨I.biUnion s, fun t ht ↦ hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    refine Seminorm.finset_sup_apply_lt hr fun i hi ↦ ?_
    calc p i (∑ n ∈ t, x n) ≤ ∑ n ∈ t, p i (x n) :=
          Finset.le_sum_of_subadditive (p i) (map_zero _).le (map_add_le_add _) _ _
      _ ≤ ∑ n ∈ t, u i n := Finset.sum_le_sum fun n _ ↦ hx i n
      _ < r := hs i t (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem s hi) ht)
  refine ⟨hsum, fun i ↦ ?_⟩
  have ht := ((hp.continuous_seminorm i).tendsto _).comp hsum.hasSum
  refine le_of_tendsto' ht fun t ↦ ?_
  calc p i (∑ n ∈ t, x n) ≤ ∑ n ∈ t, p i (x n) :=
        Finset.le_sum_of_subadditive (p i) (map_zero _).le (map_add_le_add _) _ _
    _ ≤ ∑ n ∈ t, u i n := Finset.sum_le_sum fun n _ ↦ hx i n
    _ ≤ ∑' n, u i n := (hu i).sum_le_tsum t fun n _ ↦ hu0 i n

/-- The derivatives at zero of a real power, viewed as a complex function. -/
private theorem realSchwartzFlatQuotient_strongDual_pow (n j : ℕ) :
    iteratedDeriv j (fun x : ℝ ↦ (x : ℂ) ^ n) 0 = if j = n then (n.factorial : ℂ) else 0 := by
  have h : ∀ j, iteratedDeriv j (fun x : ℝ ↦ (x : ℂ) ^ n) =
      fun x : ℝ ↦ (n.descFactorial j : ℂ) * (x : ℂ) ^ (n - j) := by
    intro j
    induction j with
    | zero => funext x; simp
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have := (h1.pow (n - j)).const_mul (n.descFactorial j : ℂ)
      rw [show (fun x : ℝ ↦ (n.descFactorial j : ℂ) * (x : ℂ) ^ (n - j)) =
        fun y ↦ (n.descFactorial j : ℂ) * ((fun y : ℝ ↦ (y : ℂ)) ^ (n - j)) y from rfl,
        this.deriv, Nat.descFactorial_succ, Nat.sub_sub, mul_one]
      push_cast
      ring
  rw [h j]
  rcases lt_trichotomy j n with hj | rfl | hj
  · simp [hj.ne, Nat.sub_ne_zero_of_lt hj]
  · simp [Nat.descFactorial_self]
  · simp [hj.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hj]

/-- `y ↦ yⁿ χ(y)` is a Schwartz function. -/
private theorem realSchwartzFlatQuotient_strongDual_exists_bump (χ : ContDiffBump (0 : ℝ))
    (n : ℕ) : ∃ G : 𝓢(ℝ, ℂ), ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ) := by
  have hc : HasCompactSupport (fun y : ℝ ↦ (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) :=
    (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left
  exact ⟨hc.toSchwartzMap ((Complex.ofRealCLM.contDiff.pow n).mul
    (Complex.ofRealCLM.contDiff.comp χ.contDiff)), fun _ ↦ rfl⟩

/-- `y ↦ yⁿ χ(y)` vanishes outside `[-1, 1]` when `χ` does. -/
private theorem realSchwartzFlatQuotient_strongDual_bump_tsupport (χ : ContDiffBump (0 : ℝ))
    (hχ : χ.rOut ≤ 1) (n : ℕ) (G : 𝓢(ℝ, ℂ)) (hG : ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) :
    tsupport (G : ℝ → ℂ) ⊆ Metric.closedBall 0 1 := by
  rw [show (G : ℝ → ℂ) = fun y : ℝ ↦ (y : ℂ) ^ n * ((χ y : ℝ) : ℂ) from funext hG]
  refine tsupport_mul_subset_right.trans ((tsupport_comp_subset Complex.ofReal_zero _).trans ?_)
  rw [χ.tsupport_eq]
  exact Metric.closedBall_subset_closedBall hχ

/-- `x ↦ εⁿ G(x / ε)` is a Schwartz function when `G` has compact support. -/
private theorem realSchwartzFlatQuotient_strongDual_exists_scaled (G : 𝓢(ℝ, ℂ))
    (hG : HasCompactSupport (G : ℝ → ℂ)) (n : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    ∃ ψ : 𝓢(ℝ, ℂ), ∀ x, ψ x = (ε : ℂ) ^ n * G (ε⁻¹ * x) :=
  ⟨HasCompactSupport.toSchwartzMap (f := fun x ↦ (ε : ℂ) ^ n * G (ε⁻¹ * x))
    ((hG.comp_smul (inv_ne_zero hε)).mul_left (f := fun _ ↦ (ε : ℂ) ^ n))
    (contDiff_const.mul ((G.smooth ⊤).comp (contDiff_const.mul contDiff_id))), fun _ ↦ rfl⟩

/-- For `m < n` and `ε ≤ 1`, every seminorm of order `m` of `x ↦ xⁿ χ(x / ε)` is at most `ε`
times a bound that does not depend on `ε`. -/
private theorem realSchwartzFlatQuotient_strongDual_scaled_seminorm (χ : ContDiffBump (0 : ℝ))
    (hχ : χ.rOut ≤ 1) (n m k : ℕ) (hmn : m < n) (G ψ : 𝓢(ℝ, ℂ))
    (hG : ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hψ : ∀ x, ψ x = (ε : ℂ) ^ n * G (ε⁻¹ * x)) :
    SchwartzMap.seminorm ℂ k m ψ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by
  have hGb (y : ℝ) : ‖iteratedDeriv m (G : ℝ → ℂ) y‖ ≤ SchwartzMap.seminorm ℂ 0 m G := by
    have h := SchwartzMap.le_seminorm' ℂ 0 m G y
    rwa [pow_zero, one_mul] at h
  have hC : 0 ≤ SchwartzMap.seminorm ℂ 0 m G := apply_nonneg _ _
  refine SchwartzMap.seminorm_le_bound' ℂ k m _ (by positivity) fun x ↦ ?_
  have hd : iteratedDeriv m (ψ : ℝ → ℂ) x =
      (ε : ℂ) ^ n * ((ε⁻¹) ^ m • iteratedDeriv m (G : ℝ → ℂ) (ε⁻¹ * x)) := by
    rw [show (ψ : ℝ → ℂ) = fun x ↦ (ε : ℂ) ^ n * G (ε⁻¹ * x) from funext hψ,
      iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_smul ((G.smooth ⊤).of_le (mod_cast le_top))]
  have hpow : ε ^ n * (ε⁻¹) ^ m ≤ ε := by
    rw [← pow_sub_mul_pow ε hmn.le, mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow,
      mul_one]
    calc ε ^ (n - m) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by omega)
      _ = ε := pow_one ε
  rw [hd, norm_mul, norm_smul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hε, abs_of_pos (inv_pos.mpr hε)]
  by_cases hx : |x| ≤ 1
  · calc |x| ^ k * (ε ^ n * ((ε⁻¹) ^ m * ‖iteratedDeriv m (G : ℝ → ℂ) (ε⁻¹ * x)‖))
        ≤ 1 * ((ε ^ n * (ε⁻¹) ^ m) * SchwartzMap.seminorm ℂ 0 m G) := by
          rw [← mul_assoc (ε ^ n)]
          gcongr
          · exact pow_le_one₀ (abs_nonneg x) hx
          · exact hGb _
      _ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by
          rw [one_mul]
          gcongr
  · have hout : ε⁻¹ * x ∉ tsupport (G : ℝ → ℂ) := by
      intro h
      have := realSchwartzFlatQuotient_strongDual_bump_tsupport χ hχ n G hG h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
        inv_mul_le_iff₀ hε] at this
      exact hx (by nlinarith [abs_nonneg x])
    have h0 : iteratedDeriv m (G : ℝ → ℂ) (ε⁻¹ * x) = 0 := by
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_eq_zero]
      by_contra hne
      exact hout (support_iteratedFDeriv_subset m hne)
    rw [h0, norm_zero, mul_zero, mul_zero, mul_zero]
    positivity


set_option quotPrecheck false

open scoped UniformConvergence in
/-- Pulling back the strong dual of a quotient is an embedding when every bounded set of the
quotient is the image of a bounded set. -/
private theorem realSchwartzFlatQuotient_strongDual_isEmbedding {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] (K : Submodule 𝕜 E)
    (h : ∀ B : Set (E ⧸ K), Bornology.IsVonNBounded 𝕜 B →
      ∃ S : Set E, Bornology.IsVonNBounded 𝕜 S ∧ B ⊆ K.mkQ '' S) :
    IsEmbedding (fun T : StrongDual 𝕜 (E ⧸ K) ↦ T.comp K.mkQL) := by
  let A := {s : Set E | Bornology.IsVonNBounded 𝕜 s}
  let B := {s : Set (E ⧸ K) | Bornology.IsVonNBounded 𝕜 s}
  let R (f : (E ⧸ K) →ᵤ[B] 𝕜) : E →ᵤ[A] 𝕜 :=
    UniformOnFun.ofFun A (UniformOnFun.toFun B f ∘ K.mkQL)
  have hRc : UniformContinuous R :=
    UniformOnFun.precomp_uniformContinuous (f := K.mkQL) (𝔖 := B) (𝔗 := A)
      (fun _ hs ↦ hs.image K.mkQL)
  have hR : IsUniformInducing R := by
    refine isUniformInducing_iff'.mpr ⟨hRc, ?_⟩
    conv_rhs => rw [UniformOnFun.uniformity_eq]
    refine le_iInf₂ fun s hs ↦ le_iInf₂ fun V hV ↦ ?_
    obtain ⟨S, hS, hsS⟩ := h s hs
    rw [le_principal_iff]
    refine ⟨_, UniformOnFun.gen_mem_uniformity (α := E) (β := 𝕜) (𝔖 := A) (hs := hS) (hV := hV),
      fun fg hfg y hy ↦ ?_⟩
    obtain ⟨x, hx, rfl⟩ := hsS hy
    exact hfg x hx
  let ie := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 A
  let iq := UniformConvergenceCLM.isUniformInducing_coeFn (RingHom.id 𝕜) 𝕜 B
  have hpull : IsUniformInducing (fun T : StrongDual 𝕜 (E ⧸ K) ↦ T.comp K.mkQL) :=
    (IsUniformInducing.of_comp_iff ie).mp (hR.comp iq)
  refine ⟨hpull.isInducing, fun T T' hT ↦ ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := K.mkQ_surjective y
  exact congrArg (fun L : StrongDual 𝕜 E ↦ L x) hT

section FinitePlace

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Fᵥ(" v ")" => HeightOneSpectrum.adicCompletion F v
local notation "Uᵥ(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "vval(" v ")" => (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ)))

/-- Paper: Lemma 5.3.1.1, p. 240.
The difference of a local test function and its inverse-unit pullback is linear. -/
theorem finitePlaceDifference_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ f - schwartzBruhatUnitTranslate π f) := by
  have hT : IsLinearMap ℂ (fun f : ℬ(Fᵥ(v)) ↦ schwartzBruhatUnitTranslate π f) := by
    refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
    · exact Subtype.ext (funext fun x ↦ rfl)
    · exact Subtype.ext (funext fun x ↦ rfl)
  exact (LinearMap.id - hT.mk' _).isLinear

/-- Paper: Lemma 5.3.1.1, p. 240.
The local difference subtracts pullback by multiplication by the inverse of the chosen unit
in the local field. The lemma applies this definition to uniformizers. -/
def finitePlaceDifference (v : V) (π : Fᵥ(v)ˣ) : ℬ(Fᵥ(v)) →ₗ[ℂ] ℬ(Fᵥ(v)) :=
  (finitePlaceDifference_isLinear v π).mk' _

/-- Paper: Lemma 5.3.1.1, p. 240.
The difference of the integer-ring indicator at a uniformizer is the integer-unit indicator.
Deviation: The integer-ring indicator is represented by the trivial standard Gaussian of §3.4. -/
theorem finitePlaceDifference_integerIndicator (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (x : Fᵥ(v)) :
    finitePlaceDifference v π (finiteStandardGaussian v 1) (Multiplicative.ofAdd x) =
      (Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ)).indicator (fun _ ↦ (1 : ℂ)) x := by
  classical
  have hG (y : Fᵥ(v)) : finiteStandardGaussian v 1 (Multiplicative.ofAdd y) =
      (v.adicCompletionIntegers F : Set Fᵥ(v)).indicator (fun _ ↦ (1 : ℂ)) y := by
    change finiteStandardGaussianValue v 1 y = _
    unfold finiteStandardGaussianValue
    exact ite_eq_left fun u _ ↦ rfl
  have hval : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hmem (y : Fᵥ(v)) : y ∈ Units.val '' (Uᵥ(v) : Set Fᵥ(v)ˣ) ↔ vval(v) y = 1 := by
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨u, hu, rfl⟩
      exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
    · have hy0 : y ≠ 0 := fun h0 ↦ by simp [h0] at hy
      exact ⟨Units.mk0 y hy0,
        HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩
  have hπx : vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) = WithZero.exp (1 : ℤ) * vval(v) x := by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval, ← WithZero.exp_neg, neg_neg]
  change finiteStandardGaussian v 1 (Multiplicative.ofAdd x) -
    finiteStandardGaussian v 1 (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) = _
  rw [hG, hG]
  rcases lt_trichotomy (vval(v) x) 1 with h | h | h
  · have h1 : vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      have h2 := (WithZero.lt_mul_exp_iff_le (x := vval(v) x * WithZero.exp (1 : ℤ)) (y := 1)
        one_ne_zero).mp
      rw [one_mul] at h2
      rw [hπx, mul_comm]
      exact h2 (mul_lt_mul_of_pos_right h (by simp))
    rw [indicator_of_mem (show x ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.le),
      indicator_of_mem (show _ ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_notMem fun hx ↦ h.ne ((hmem x).mp hx), sub_self]
  · have h1 : ¬ vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      rw [hπx, h, mul_one]
      simp
    rw [indicator_of_mem (show x ∈ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.le),
      indicator_of_notMem (show _ ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_mem ((hmem x).mpr h), sub_zero]
  · have h1 : ¬ vval(v) ((↑π⁻¹ : Fᵥ(v)) * x) ≤ 1 := by
      rw [hπx, not_le]
      exact h.trans_le (le_mul_of_one_le_left zero_le (by simp))
    rw [indicator_of_notMem (show x ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h.not_ge),
      indicator_of_notMem (show _ ∉ (v.adicCompletionIntegers F : Set Fᵥ(v)) from h1),
      indicator_of_notMem fun hx ↦ h.ne' ((hmem x).mp hx), sub_zero]

private theorem finitePlaceDifference_injective_aux (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (g : Fᵥ(v) → ℂ) (hlc : IsLocallyConstant g)
    (hcs : HasCompactSupport g) (hg : ∀ x, g x = g ((↑π⁻¹ : Fᵥ(v)) * x)) : g = 0 := by
  have hval : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hv1 : vval(v) π.val < 1 := by
    rw [hval, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hpow (n : ℕ) (x : Fᵥ(v)) : g ((π : Fᵥ(v)) ^ n * x) = g x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, ih, hg (π * x), Units.inv_mul_cancel_left]
  let := Valued.toNontriviallyNormedField (Fᵥ(v)) _
  have hn : ‖(π : Fᵥ(v))‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hv1
  have hconst (x : Fᵥ(v)) : g x = g 0 := by
    have ht : Tendsto (fun n : ℕ ↦ (π : Fᵥ(v)) ^ n * x) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).mul_const x
    have h := (hlc.continuous.tendsto 0).comp ht
    simp only [Function.comp_def, hpow] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  funext x
  by_contra hx
  have hc : support g = univ := eq_univ_of_forall fun y ↦ by
    rw [mem_support, hconst y, ← hconst x]; exact hx
  have hK : IsCompact (univ : Set Fᵥ(v)) := by
    have := hcs.isCompact
    rwa [tsupport, hc, closure_univ] at this
  exact noncompact_univ _ hK

private theorem finitePlaceDifference_injective (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) : Function.Injective (finitePlaceDifference v π) := by
  intro f f' hf
  have hg (x : Fᵥ(v)) : f (Multiplicative.ofAdd x) - f' (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) -
        f' (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) := by
    have h := congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd x)) hf
    change f (Multiplicative.ofAdd x) - f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) =
      f' (Multiplicative.ofAdd x) - f' (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) at h
    linear_combination h
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff F v
    (fun x ↦ f (Multiplicative.ofAdd x))).1 ⟨f, fun _ ↦ rfl⟩
  obtain ⟨hlc', hcs'⟩ := (mem_finitePlaceSchwartz_iff F v
    (fun x ↦ f' (Multiplicative.ofAdd x))).1 ⟨f', fun _ ↦ rfl⟩
  have h0 := finitePlaceDifference_injective_aux v π hπ
    (fun x ↦ f (Multiplicative.ofAdd x) - f' (Multiplicative.ofAdd x)) (hlc.sub hlc')
    (hcs.sub hcs') hg
  refine Subtype.ext (funext fun y ↦ ?_)
  have hy := congrFun h0 (Multiplicative.toAdd y)
  exact sub_eq_zero.mp hy

private theorem finestLocallyConvex_isEmbedding_of_injective {E : Type*} [AddCommGroup E]
    [Module ℂ E] (D : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex E)
    (hD : Function.Injective D) : IsEmbedding D := by
  have : T2Space (FinestLocallyConvex E) := finestLocallyConvex_t2 E
  obtain ⟨L, hL⟩ := D.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hD)
  have hLD : Function.LeftInverse L D := fun f ↦ LinearMap.congr_fun hL f
  exact Topology.IsEmbedding.of_leftInverse hLD
    (continuous_of_finestLocallyConvex E L) (continuous_of_finestLocallyConvex E D)

/-- Paper: Lemma 5.3.1.1, p. 240.
For each fixed uniformizer the local difference is a topological embedding. -/
theorem finitePlaceDifference_isEmbedding (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    IsEmbedding (finitePlaceDifference v π) := by
  have heq := finitePlaceSchwartz_finestTopology F v
  have h := finestLocallyConvex_isEmbedding_of_injective (E := ℬ(Fᵥ(v)))
    (finitePlaceDifference v π) (finitePlaceDifference_injective v π hπ)
  exact (congrArg (fun t ↦ @IsEmbedding ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t
    (fun f ↦ finitePlaceDifference v π f)) heq).mpr h

/-- Paper: Lemma 5.3.1.1, pp. 240–241.
The range of the difference for a fixed uniformizer is closed on the full test space. -/
theorem finitePlaceDifference_isClosed_range (v : V) (π : Fᵥ(v)ˣ)
    (_hπ : vval(v).IsUniformizer π.val) :
    IsClosed (Set.range (finitePlaceDifference v π)) := by
  have heq := finitePlaceSchwartz_finestTopology F v
  have h := finestLocallyConvex_submodule_isClosed (E := ℬ(Fᵥ(v)))
    (LinearMap.range (finitePlaceDifference v π))
  exact (congrArg (fun t ↦ @IsClosed ℬ(Fᵥ(v)) t (Set.range (finitePlaceDifference v π)))
    heq).mpr h

-- TODO(paper-gap): ERRATA R7 gives the failure of independence and range on the whole space.

/-- Paper: Lemma 5.3.1.1, p. 240.
The local difference on integer-unit-invariant functions is independent of the uniformizer.
Deviation: The independence claim is restricted to integer-unit invariants by ERRATA R7. -/
theorem finitePlaceDifference_eq_of_unitInvariant (v : V) (π π' : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (hπ' : vval(v).IsUniformizer π'.val) (f : ℬ(Fᵥ(v)))
    (hf : ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) :
    finitePlaceDifference v π f = finitePlaceDifference v π' f := by
  have hu : π * π'⁻¹ ∈ Uᵥ(v) :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ.val, ← hπ'.val]
      exact mul_inv_cancel₀ hπ'.val_ne_zero)
  refine Subtype.ext (funext fun x ↦ ?_)
  have h : f (Multiplicative.ofAdd ((↑(π * π'⁻¹)⁻¹ : Fᵥ(v)) * ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))) =
      f (Multiplicative.ofAdd ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd)) :=
    congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))) (hf _ hu)
  rw [← mul_assoc, ← Units.val_mul, show (π * π'⁻¹)⁻¹ * π'⁻¹ = π⁻¹ by
    rw [mul_inv_rev, inv_inv, mul_right_comm, mul_inv_cancel, one_mul]] at h
  exact congrArg (fun a ↦ f x - a) h

/-- A test vanishing at zero meets only finitely many valuation shells in its support. -/
private theorem finitePlaceDifference_range_on_unitInvariants_finite (v : V) (f : ℬ(Fᵥ(v)))
    (h₀ : f (Multiplicative.ofAdd 0) = 0) :
    ∃ I : Finset ℤ, ∀ x : Fᵥ(v), f (Multiplicative.ofAdd x) ≠ 0 → (vval(v) x).log ∈ I := by
  classical
  let k (x : Fᵥ(v)) := f (Multiplicative.ofAdd x)
  obtain ⟨hl, hc⟩ := (mem_finitePlaceSchwartz_iff F v k).1 ⟨f, fun _ ↦ rfl⟩
  have hclosed : IsClosed (support k) := (hl.isClopen_fiber 0).isOpen.isClosed_compl
  have hcomp : IsCompact (support k) := hclosed.closure_eq ▸ hc
  let : CompactSpace (support k) := isCompact_iff_compactSpace.mp hcomp
  let a (x : support k) := (vval(v) x.val).log
  have ha : IsLocallyConstant a := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hx : x.val ≠ 0 := fun h ↦ x.property (h ▸ h₀)
    have hv := Valued.locally_const ((Valuation.ne_zero_iff vval(v)).mpr hx)
    filter_upwards [continuous_subtype_val.continuousAt hv] with y hy
    exact congrArg WithZero.log hy
  exact ⟨ha.range_finite.toFinset, fun x hx ↦ ha.range_finite.mem_toFinset.mpr ⟨⟨x, hx⟩, rfl⟩⟩

private theorem finitePlaceDifference_range_on_unitInvariants_radial (v : V) (f : ℬ(Fᵥ(v)))
    (hf : ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) (x y : Fᵥ(v))
    (hx : x ≠ 0) (hy : y ≠ 0) (he : vval(v) x = vval(v) y) :
    f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd y) := by
  let u := Units.mk0 x hx / Units.mk0 y hy
  have hu : u ∈ Uᵥ(v) := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    (show vval(v) (x / y) = 1 by rw [map_div₀, he, div_self ((Valuation.ne_zero_iff _).mpr hy)])
  have h := congrArg (fun g : ℬ(Fᵥ(v)) ↦ g (Multiplicative.ofAdd y)) (hf u⁻¹ (Uᵥ(v).inv_mem hu))
  simpa only [schwartzBruhatUnitTranslate_apply, inv_inv, Units.val_div_eq_div_val,
    Units.val_mk0, div_mul_cancel₀ _ hy, u] using h

private theorem finitePlaceDifference_range_on_unitInvariants_ball (v : V) (n : ℤ) (c : ℂ) :
    ∃ g : ℬ(Fᵥ(v)), ∀ x : Fᵥ(v), g (Multiplicative.ofAdd x) =
      if vval(v) x ≤ WithZero.exp n then c else 0 := by
  classical
  obtain ⟨t, ht⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp n)
  have ht₀ : t ≠ 0 := fun h ↦ WithZero.exp_ne_zero (ht.symm.trans (h ▸ map_zero _))
  refine ⟨c • schwartzBruhatUnitTranslate (Units.mk0 t ht₀) (finiteStandardGaussian v 1), fun x ↦ ?_⟩
  have hx : t⁻¹ * x ∈ v.adicCompletionIntegers F ↔ vval(v) x ≤ WithZero.exp n := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, ht, inv_mul_le_one₀]
    exact zero_lt_iff.mpr WithZero.exp_ne_zero
  change c * finiteStandardGaussianValue v 1 (t⁻¹ * x) = _
  unfold finiteStandardGaussianValue
  rw [ite_eq_left (show ∀ u ∈ Uᵥ(v), (1 : QuasiCharacter Fᵥ(v)ˣ) u = 1 from fun _ _ ↦ rfl)]
  by_cases h : t⁻¹ * x ∈ v.adicCompletionIntegers F
  · rw [indicator_of_mem h, mul_one, ite_eq_left (hx.mp h)]
  · rw [indicator_of_notMem h, mul_zero, ite_eq_right (fun hv ↦ h (hx.mpr hv))]

private theorem finitePlaceDifference_range_on_unitInvariants_step (m n : ℤ) (c : ℂ) :
    (if WithZero.exp m ≤ WithZero.exp n then c else 0) -
      (if WithZero.exp 1 * WithZero.exp m ≤ WithZero.exp n then c else 0) =
      if n = m then c else 0 := by
  simp only [← WithZero.exp_add, WithZero.exp_le_exp]
  split_ifs <;> first | omega | simp_all

/-- Paper: Lemma 5.3.1.1, p. 240.
The image of the integer-unit-invariant subspace under the local difference consists of the
integer-unit-invariant functions vanishing at zero.
Deviation: The domain and the evaluation kernel are restricted by ERRATA R7. -/
theorem finitePlaceDifference_range_on_unitInvariants (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    finitePlaceDifference v π '' {f | ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f} =
      {f | (∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) ∧
        f (Multiplicative.ofAdd 0) = 0} := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩
    have h (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) (y : Fᵥ(v)) :
        f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y)) = f (Multiplicative.ofAdd y) :=
      congrArg (fun k : ℬ(Fᵥ(v)) ↦ k (Multiplicative.ofAdd y)) (hf u hu)
    constructor
    · intro u hu
      apply Subtype.ext
      funext x
      change f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) -
        f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd))) = _
      exact congrArg₂ (· - ·) (h u hu x.toAdd)
        ((congrArg (fun z ↦ f (Multiplicative.ofAdd z))
          (mul_left_comm (↑π⁻¹ : Fᵥ(v)) (↑u⁻¹ : Fᵥ(v)) x.toAdd)).trans
            (h u hu ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
    · change f (Multiplicative.ofAdd 0) - f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * 0)) = 0
      simp
  · rintro f ⟨hf, h₀⟩
    have H := finitePlaceDifference_range_on_unitInvariants_finite (F := F) v f h₀
    let I := H.choose
    have hI := H.choose_spec
    choose t ht using fun n : ℤ ↦ v.valuedAdicCompletion_surjective F (WithZero.exp n)
    let c (n : ℤ) := f (Multiplicative.ofAdd (t n))
    choose b hb using fun n : ℤ ↦ finitePlaceDifference_range_on_unitInvariants_ball (F := F) v n (c n)
    -- Each weighted ball contributes its boundary shell under the difference.
    let g := ∑ n ∈ I, b n
    have hg (x : Fᵥ(v)) : g (Multiplicative.ofAdd x) =
        ∑ n ∈ I, if vval(v) x ≤ WithZero.exp n then c n else 0 := by
      calc
        _ = ∑ n ∈ I, b n (Multiplicative.ofAdd x) :=
          map_sum ((LinearMap.proj (Multiplicative.ofAdd x)).comp
            (schwartzBruhatSubmodule (Multiplicative Fᵥ(v))).subtype) b I
        _ = _ := Finset.sum_congr rfl fun i _ ↦ hb i x
    refine ⟨g, ?_, ?_⟩
    · intro u hu
      have hu₁ := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (Uᵥ(v).inv_mem hu)
      apply Subtype.ext
      funext x
      change g (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) = g (Multiplicative.ofAdd x.toAdd)
      rw [hg, hg, map_mul, hu₁, one_mul]
    · have hπv : vval(v) π.val = WithZero.exp (-1 : ℤ) := hπ.trans
        (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
          (v.valuedAdicCompletion_surjective F)))
      have hπi : vval(v) (↑π⁻¹ : Fᵥ(v)) = WithZero.exp 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hπv, ← WithZero.exp_neg, neg_neg]
      apply Subtype.ext
      funext x
      change g (Multiplicative.ofAdd x.toAdd) -
        g (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)) = f (Multiplicative.ofAdd x.toAdd)
      by_cases hx : x.toAdd = 0
      · simp only [hx, mul_zero, sub_self, h₀]
      let m := (vval(v) x.toAdd).log
      have hm : WithZero.exp m = vval(v) x.toAdd :=
        WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)
      rw [hg, hg, map_mul, hπi, ← hm, ← Finset.sum_sub_distrib]
      simp only [finitePlaceDifference_range_on_unitInvariants_step, Finset.sum_ite_eq']
      by_cases hi : m ∈ I
      · rw [ite_eq_left hi]
        have htm : t m ≠ 0 := fun e ↦ WithZero.exp_ne_zero ((ht m).symm.trans (e ▸ map_zero _))
        exact finitePlaceDifference_range_on_unitInvariants_radial (F := F) v f hf _ _ htm hx ((ht m).trans hm)
      · exact (ite_eq_right hi).trans (not_ne_iff.mp (fun h ↦ hi (hI _ h))).symm

-- TODO(paper-gap): At the trivial quasi-character, the eigendistribution in (5.3.1.3)
-- is a multiple of Dirac evaluation and vanishes on the integer-unit indicator.
-- For a nontrivial unramified character the unit-shell and integer-ring
-- normalizations differ by the following factor.

/-- Paper: (5.3.1.3), p. 240.
An eigendistribution normalized on the integer ring as in §3.4 takes the value
one minus the weight of the uniformizer on the unit shell.
Deviation: The shell normalization requires dividing by this factor when it is nonzero. -/
theorem finiteEigendistribution_unitShell (v : V) (π : Fᵥ(v)ˣ)
    (_hπ : vval(v).IsUniformizer π.val) (c : QuasiCharacter Fᵥ(v)ˣ)
    (T : StrongDual ℂ ℬ(Fᵥ(v))) (hT : T ∈ schwartzBruhatEigendistributions (R := Fᵥ(v)) c)
    (hnorm : T (finiteStandardGaussian v 1) = 1) :
    T (finitePlaceDifference v π (finiteStandardGaussian v 1)) = 1 - c π := by
  let f : ℬ(Fᵥ(v)) := finiteStandardGaussian v 1
  change T (f - schwartzBruhatUnitTranslate π f) = 1 - c π
  have heigen : ∀ (g : Fᵥ(v)ˣ) (h : ℬ(Fᵥ(v))),
      T (schwartzBruhatUnitTranslate g h) = c g * T h := hT
  calc
    _ = T f - T (schwartzBruhatUnitTranslate π f) := map_sub T _ _
    _ = T f - c π * T f := congrArg (fun a ↦ T f - a) (heigen π f)
    _ = 1 - c π := by rw [show T f = 1 from hnorm, mul_one]

local instance instMeasurableSpaceAdicUnitsSec3a (v : V) : MeasurableSpace Fᵥ(v)ˣ :=
  borel _

local notation "μᵥ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
Weil's local principal value subtracts the uniformizer translate of the normalized
integer-unit average. -/
def finitePlacePrincipalValueFun (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) : ℂ :=
  f x - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
    ∫ u in Uᵥ(v), f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
      ∂μᵥ(v)

/-- Paper: Lemma 5.3.1.3, p. 241.
The local Haar mass on integer units is positive and finite, and the scalar orbit integrals
defining the principal value exist. -/
theorem finitePlacePrincipalValue_integrable (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) :
    0 < μᵥ(v).real Uᵥ(v) ∧
      IntegrableOn
        (fun u : Fᵥ(v)ˣ ↦
          f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))))
        Uᵥ(v) μᵥ(v) := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : (μᵥ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hO : IsOpen (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  refine ⟨ENNReal.toReal_pos (hO.measure_pos _ ⟨1, Uᵥ(v).one_mem⟩).ne' hK.measure_lt_top.ne, ?_⟩
  refine ContinuousOn.integrableOn_compact hK (Continuous.continuousOn ?_)
  exact (schwartzBruhat_continuous f).comp (continuous_ofAdd.comp
    ((Units.continuous_val.comp continuous_inv).mul continuous_const))

/-- The unit average of a locally constant compactly supported function, after scaling by a
fixed unit, is again locally constant with compact support. -/
private theorem finitePlacePrincipalValue_mem_average {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [MeasurableSpace Kˣ] [OpensMeasurableSpace Kˣ]
    (μ : Measure Kˣ) (U : Set Kˣ) (hO : IsOpen U) (hK : IsCompact U) (c : Kˣ) (F0 : K → ℂ)
    (hlc : IsLocallyConstant F0) (hcs : HasCompactSupport F0) :
    IsLocallyConstant (fun y : K ↦ ∫ u in U, F0 ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * y)) ∂μ) ∧
      HasCompactSupport (fun y : K ↦ ∫ u in U, F0 ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * y)) ∂μ) := by
  have hinv : Continuous fun u : Kˣ ↦ (↑u⁻¹ : K) := Units.continuous_val.comp continuous_inv
  refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_, ?_⟩
  · have hΦ : IsLocallyConstant fun p : K × Kˣ ↦
        (F0 ((↑p.2⁻¹ : K) * ((↑c⁻¹ : K) * p.1)), F0 ((↑p.2⁻¹ : K) * ((↑c⁻¹ : K) * x))) :=
      (hlc.comp_continuous ((hinv.comp continuous_snd).mul
        (continuous_const.mul continuous_fst))).prodMk
        (hlc.comp_continuous ((hinv.comp continuous_snd).mul continuous_const))
    obtain ⟨A, B, hA, -, hxA, hUB, hAB⟩ := generalized_tube_lemma isCompact_singleton hK
      (hΦ {q | q.1 = q.2}) (fun p hp ↦ by
        obtain ⟨hp1, -⟩ := hp
        change F0 _ = F0 _
        rw [Set.mem_singleton_iff.mp hp1])
    exact ⟨A, hA, hxA rfl, fun x' hx' ↦
      setIntegral_congr_fun hO.measurableSet fun u hu ↦
        hAB (show ((x', u) : K × Kˣ) ∈ A ×ˢ B from ⟨hx', hUB hu⟩)⟩
  · refine HasCompactSupport.intro
      ((hK.prod hcs.isCompact).image (f := fun p : Kˣ × K ↦ (↑c : K) * ((↑p.1 : K) * p.2))
        (continuous_const.mul ((Units.continuous_val.comp continuous_fst).mul continuous_snd)))
      fun x hx ↦ setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
    by_contra hne
    refine hx ⟨(u, (↑u⁻¹ : K) * ((↑c⁻¹ : K) * x)), ⟨hu, subset_tsupport _ hne⟩, ?_⟩
    change (↑c : K) * ((↑u : K) * ((↑u⁻¹ : K) * ((↑c⁻¹ : K) * x))) = x
    rw [Units.mul_inv_cancel_left, Units.mul_inv_cancel_left]

/-- Paper: Lemma 5.3.1.3, p. 241.
The formula for the local principal value produces a Schwartz–Bruhat test function. -/
theorem finitePlacePrincipalValue_mem (v : V) (π : Fᵥ(v)ˣ) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValueFun v π f ∈ schwartzBruhatSubmodule (Multiplicative Fᵥ(v)) :=
  by
  have hlc := (mem_finitePlaceSchwartz_iff F v (fun y ↦ f (Multiplicative.ofAdd y))).mp
    ⟨f, fun _ ↦ rfl⟩
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have hO : IsOpen (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v))
  have h := finitePlacePrincipalValue_mem_average μᵥ(v) _ hO hK π _ hlc.1 hlc.2
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v _).mpr h
  have heq : finitePlacePrincipalValueFun v π f =
      (f : Multiplicative Fᵥ(v) → ℂ) -
        (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ • (g : Multiplicative Fᵥ(v) → ℂ) :=
    funext fun x ↦ by
      change _ = f x - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ * g (Multiplicative.ofAdd x.toAdd)
      rw [hg]
      rfl
  rw [heq]
  exact Submodule.sub_mem _ (show schwartzBruhatSubmodule _ from f).property
    (Submodule.smul_mem _ _ (show schwartzBruhatSubmodule _ from g).property)

local notation "pvBundle(" v ", " π ")" =>
  (fun f : ℬ(Fᵥ(v)) ↦
    (⟨finitePlacePrincipalValueFun v π f, finitePlacePrincipalValue_mem v π f⟩ : ℬ(Fᵥ(v))))

/-- Paper: Lemma 5.3.1.3, p. 241.
The bundled local averaging formula is linear. -/
theorem finitePlacePrincipalValue_isLinear (v : V) (π : Fᵥ(v)ˣ) :
    IsLinearMap ℂ (pvBundle(v, π)) := by
  refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
  · refine Subtype.ext (funext fun x ↦ ?_)
    have hf := (finitePlacePrincipalValue_integrable v π f x).2
    have hg := (finitePlacePrincipalValue_integrable v π g x).2
    change finitePlacePrincipalValueFun v π (f + g) x =
      finitePlacePrincipalValueFun v π f x + finitePlacePrincipalValueFun v π g x
    unfold finitePlacePrincipalValueFun
    simp only [show ∀ y, (f + g) y = f y + g y from fun _ ↦ rfl]
    rw [integral_add hf hg]
    ring
  · refine Subtype.ext (funext fun x ↦ ?_)
    change finitePlacePrincipalValueFun v π (c • f) x = c * finitePlacePrincipalValueFun v π f x
    unfold finitePlacePrincipalValueFun
    simp only [show ∀ y, (c • f) y = c * f y from fun _ ↦ rfl]
    rw [integral_const_mul]
    ring

/-- Paper: Lemma 5.3.1.3, p. 241.
The local principal value formula is continuous. -/
theorem finitePlacePrincipalValue_continuous (v : V) (π : Fᵥ(v)ˣ) :
    @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) _ _
      ((finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))).toFun := by
  let E := FinestLocallyConvex ℬ(Fᵥ(v))
  let L : E →ₗ[ℂ] E := (finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π))
  apply (congrArg (fun t ↦ @Continuous ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t L.toFun)
    (finitePlaceSchwartz_finestTopology F v)).mpr
  have h := finestLocallyConvex_withSeminorms ℬ(Fᵥ(v))
  haveI : IsTopologicalAddGroup E := h.isTopologicalAddGroup
  exact h.continuous_of_continuous_comp L fun p ↦ h.continuous_seminorm (p.comp L)

/-- Paper: Definition 5.3.1.2, p. 241.
The principal value is the identity minus the uniformizer pullback of the trivial-isotype
projection. A uniformizer is chosen from the discrete local valuation. -/
def finitePlacePrincipalValue (v : V) : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) :=
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  ⟨(finitePlacePrincipalValue_isLinear v π).mk' (pvBundle(v, π)),
    finitePlacePrincipalValue_continuous v π⟩

/-- A left-invariant set integral is unchanged by left translation by an element that
preserves the set. -/
private theorem finitePlacePrincipalValue_spec_setIntegral_mul_left {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Set G)
    (hS : MeasurableSet S) (g : G → ℂ) (w : G) (hw : ∀ u, w * u ∈ S ↔ u ∈ S) :
    ∫ u in S, g (w * u) ∂μ = ∫ u in S, g u ∂μ := by
  rw [← integral_indicator hS, ← integral_indicator hS,
    ← integral_mul_left_eq_self (S.indicator g) w]
  congr 1
  funext u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((hw u).mpr hu)]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h ↦ hu ((hw u).mp h))]

/-- The scalar principal-value formula does not depend on the choice of uniformizer, by left
invariance of the multiplicative Haar measure on the integer units. -/
private theorem finitePlacePrincipalValue_spec_indep (v : V) (π π' : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (hπ' : vval(v).IsUniformizer π'.val) (f : ℬ(Fᵥ(v)))
    (x : Multiplicative Fᵥ(v)) :
    finitePlacePrincipalValueFun v π f x = finitePlacePrincipalValueFun v π' f x := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsMulLeftInvariant := by
    unfold finiteLocalMultiplicativeTamagawaMeasure
    infer_instance
  have hu : π * π'⁻¹ ∈ Uᵥ(v) :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hπ.val, ← hπ'.val]
      exact mul_inv_cancel₀ hπ'.val_ne_zero)
  have hw : π'⁻¹ * π ∈ Uᵥ(v) := mul_comm π π'⁻¹ ▸ hu
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  unfold finitePlacePrincipalValueFun
  congr 2
  refine Eq.trans ?_ (finitePlacePrincipalValue_spec_setIntegral_mul_left μᵥ(v) _ hU
    (fun u : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π'⁻¹ : Fᵥ(v)) * x.toAdd))))
    (π'⁻¹ * π) (fun u ↦ Subgroup.mul_mem_cancel_left _ hw))
  congr 1
  funext u
  rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  group

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
The scalar formula for the operator works with every choice of uniformizer. -/
theorem finitePlacePrincipalValue_spec (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    ∀ (f : ℬ(Fᵥ(v))) (x : Multiplicative Fᵥ(v)),
      finitePlacePrincipalValue v f x = finitePlacePrincipalValueFun v π f x := by
  intro f x
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact finitePlacePrincipalValue_spec_indep v (Units.mk0 (h.choose : Fᵥ(v))
    h.choose_spec.ne_zero) π h.choose_spec hπ f x

open Classical in
/-- The principal value acts as the local difference on unit-invariant tests and as the
identity on the other integer-unit isotypes. -/
private theorem finitePlacePrincipalValue_unique_obeys (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val)
    (χ : PontryaginDual Uᵥ(v)) (f : ℬ(Fᵥ(v)))
    (hf : ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val f = (χ u : ℂ) • f) :
    finitePlacePrincipalValue v f = if χ = 1 then finitePlaceDifference v π f else f := by
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsMulLeftInvariant := by
    unfold finiteLocalMultiplicativeTamagawaMeasure
    infer_instance
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hpt : ∀ (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) (y : Fᵥ(v)),
      f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y)) =
        (χ ⟨u, hu⟩ : ℂ) * f (Multiplicative.ofAdd y) := by
    intro u hu y
    have h := congrArg (fun g : ℬ(Fᵥ(v)) ↦ g (Multiplicative.ofAdd y)) (hf ⟨u, hu⟩)
    simp only at h
    rw [schwartzBruhatUnitTranslate_apply] at h
    exact h
  have hm : (μᵥ(v).real Uᵥ(v) : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v π f 1).1.ne'
  refine SchwartzBruhat.ext fun x ↦ ?_
  rw [finitePlacePrincipalValue_spec v π hπ]
  unfold finitePlacePrincipalValueFun
  split_ifs with h1
  · subst h1
    rw [setIntegral_congr_fun hU
      (g := fun _ ↦ f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
      (fun u hu ↦ by rw [hpt u hu]; simp), setIntegral_const, Complex.real_smul]
    change _ = f x - f (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))
    field_simp
  · obtain ⟨u0, hu0⟩ : ∃ u0 : Uᵥ(v), χ u0 ≠ 1 := by
      by_contra! h
      exact h1 (ContinuousMonoidHom.ext fun u ↦ h u)
    have hI : ∫ u in Uᵥ(v), f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) *
        ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))) ∂μᵥ(v) = 0 := by
      set y := (↑π⁻¹ : Fᵥ(v)) * x.toAdd
      set I := ∫ u in Uᵥ(v), f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y)) ∂μᵥ(v) with hIdef
      have hII : I = (χ u0 : ℂ) * I := by
        conv_lhs => rw [hIdef, ← finitePlacePrincipalValue_spec_setIntegral_mul_left μᵥ(v) _ hU
          (fun u : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y))) u0.val
          (fun u ↦ Subgroup.mul_mem_cancel_left _ u0.property)]
        rw [hIdef, ← integral_const_mul]
        refine setIntegral_congr_fun hU fun u hu ↦ ?_
        simp only
        rw [mul_inv_rev, Units.val_mul, mul_assoc, ← hpt u0.val u0.property]
        rw [mul_left_comm (↑u⁻¹ : Fᵥ(v)) (↑(u0.val)⁻¹ : Fᵥ(v)) y]
      have h2 : (1 - (χ u0 : ℂ)) * I = 0 := by rw [sub_mul, one_mul, ← hII, sub_self]
      have h3 : (1 - (χ u0 : ℂ)) ≠ 0 := by
        intro h0
        apply hu0
        exact Circle.ext (by rw [Circle.coe_one]; linear_combination -h0)
      exact (mul_eq_zero.mp h2).resolve_left h3
    rw [hI, mul_zero, sub_zero]

/-- Every local test is fixed by an open subgroup of the integer units. -/
private theorem finitePlacePrincipalValue_unique_stab (v : V) (f : ℬ(Fᵥ(v))) :
    ∃ N : Subgroup Uᵥ(v), IsOpen (N : Set Uᵥ(v)) ∧
      ∀ n ∈ N, schwartzBruhatUnitTranslate (n : Uᵥ(v)).val f = f := by
  let φ0 : Fᵥ(v) → ℂ := fun y ↦ f (Multiplicative.ofAdd y)
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff F v φ0).mp ⟨f, fun _ ↦ rfl⟩
  have hinv : Continuous fun u : Fᵥ(v)ˣ ↦ (↑u⁻¹ : Fᵥ(v)) := Units.continuous_val.comp continuous_inv
  have hΦ : IsLocallyConstant fun p : Fᵥ(v)ˣ × Fᵥ(v) ↦ (φ0 ((↑p.1⁻¹ : Fᵥ(v)) * p.2), φ0 p.2) :=
    (hlc.comp_continuous ((hinv.comp continuous_fst).mul continuous_snd)).prodMk
      (hlc.comp_continuous continuous_snd)
  obtain ⟨B, A, hB, -, h1B, hA, hBA⟩ := generalized_tube_lemma isCompact_singleton
    hcs.isCompact (hΦ {q | q.1 = q.2}) (fun p hp ↦ by
      obtain ⟨hp1, -⟩ := hp
      rw [Set.mem_singleton_iff] at hp1
      change φ0 _ = φ0 _
      rw [hp1, inv_one, Units.val_one, one_mul])
  have hkey : ∀ u : Fᵥ(v)ˣ, u ∈ B → u⁻¹ ∈ B → ∀ y, φ0 ((↑u⁻¹ : Fᵥ(v)) * y) = φ0 y := by
    intro u hu hu' y
    by_cases hy : y ∈ tsupport φ0
    · have h := hBA (Set.mk_mem_prod hu (hA hy))
      rw [Set.mem_preimage, Set.mem_ofPred_eq] at h
      exact h
    · by_cases hy' : (↑u⁻¹ : Fᵥ(v)) * y ∈ tsupport φ0
      · have h := hBA (Set.mk_mem_prod hu' (hA hy'))
        rw [Set.mem_preimage, Set.mem_ofPred_eq] at h
        simp only [inv_inv, Units.mul_inv_cancel_left] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']
  let N : Subgroup Uᵥ(v) :=
    { carrier := {n | ∀ y, φ0 (((n.val⁻¹ : Fᵥ(v)ˣ) : Fᵥ(v)) * y) = φ0 y}
      one_mem' := fun y ↦ by
        change φ0 (((1 : Fᵥ(v)ˣ)⁻¹ : Fᵥ(v)ˣ) * y) = φ0 y
        rw [inv_one, Units.val_one, one_mul]
      mul_mem' := fun {a b} ha hb y ↦ by
        change φ0 ((((a.val * b.val)⁻¹ : Fᵥ(v)ˣ) : Fᵥ(v)) * y) = φ0 y
        rw [mul_inv_rev, Units.val_mul, mul_assoc, hb, ha]
      inv_mem' := fun {a} ha y ↦ by
        change φ0 (((a.val⁻¹⁻¹ : Fᵥ(v)ˣ) : Fᵥ(v)) * y) = φ0 y
        have h := ha ((a.val : Fᵥ(v)) * y)
        rw [Units.inv_mul_cancel_left] at h
        rw [inv_inv]
        exact h.symm }
  have hsub : {n : Uᵥ(v) | n.val ∈ B ∧ n.val⁻¹ ∈ B} ⊆ (N : Set Uᵥ(v)) := by
    rintro n ⟨hn, hn'⟩
    exact fun y ↦ hkey n.val hn hn' y
  have hopen : IsOpen {n : Uᵥ(v) | n.val ∈ B ∧ n.val⁻¹ ∈ B} :=
    (hB.preimage continuous_subtype_val).inter
      (hB.preimage (continuous_inv.comp continuous_subtype_val))
  have h1 : (1 : Uᵥ(v)) ∈ {n : Uᵥ(v) | n.val ∈ B ∧ n.val⁻¹ ∈ B} := by
    refine ⟨h1B rfl, ?_⟩
    rw [OneMemClass.coe_one, inv_one]
    exact h1B rfl
  refine ⟨N, Subgroup.isOpen_of_mem_nhds N (Filter.mem_of_superset (hopen.mem_nhds h1) hsub),
    fun n hn ↦ ?_⟩
  refine SchwartzBruhat.ext fun x ↦ ?_
  rw [← ofAdd_toAdd x, schwartzBruhatUnitTranslate_apply]
  exact hn x.toAdd

open Classical in
/-- The integer-unit isotypic tests span the local test space: average over the finite
quotient of the units by the stabilizer, with its characters. -/
private theorem finitePlacePrincipalValue_unique_span (v : V) (f : ℬ(Fᵥ(v))) :
    f ∈ Submodule.span ℂ {g : ℬ(Fᵥ(v)) | ∃ χ : PontryaginDual Uᵥ(v),
      ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val g = (χ u : ℂ) • g} := by
  obtain ⟨N, hNo, hN⟩ := finitePlacePrincipalValue_unique_stab v f
  have : CompactSpace Uᵥ(v) := isCompact_iff_compactSpace.mp (Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  have : Finite (Uᵥ(v) ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  have : DiscreteTopology (Uᵥ(v) ⧸ N) := QuotientGroup.discreteTopology hNo
  have : Fintype (Additive (Uᵥ(v) ⧸ N)) := Fintype.ofFinite _
  let L : Uᵥ(v) → ℬ(Fᵥ(v)) →ₗ[ℂ] ℬ(Fᵥ(v)) := fun u ↦
    { toFun := schwartzBruhatUnitTranslate u.val
      map_add' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ rfl)
      map_smul' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ rfl) }
  have hcomp : ∀ (a b : Uᵥ(v)) (g : ℬ(Fᵥ(v))), schwartzBruhatUnitTranslate a.val
      (schwartzBruhatUnitTranslate b.val g) = schwartzBruhatUnitTranslate (a * b).val g := by
    intro a b g
    refine SchwartzBruhat.ext fun x ↦ ?_
    rw [← ofAdd_toAdd x]
    simp only [schwartzBruhatUnitTranslate_apply]
    rw [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]
  let T : Uᵥ(v) → ℬ(Fᵥ(v)) := fun u ↦ schwartzBruhatUnitTranslate u.val f
  have hT : ∀ (u : Uᵥ(v)) (n : N), T (u * n) = T u := by
    intro u n
    simp only [T]
    rw [← hcomp, hN n n.property]
  let r : Uᵥ(v) ⧸ N → Uᵥ(v) := fun g ↦ g.out
  have hr : ∀ u : Uᵥ(v), T (r (QuotientGroup.mk u)) = T u := by
    intro u
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N u
    simp only [r]
    rw [hn, hT]
  have hrmk : ∀ g : Uᵥ(v) ⧸ N, (QuotientGroup.mk (r g) : Uᵥ(v) ⧸ N) = g :=
    fun g ↦ QuotientGroup.out_eq' g
  let S : Additive (Uᵥ(v) ⧸ N) → ℬ(Fᵥ(v)) := fun a ↦ T (r (Additive.toMul a))
  have hS : ∀ (u : Uᵥ(v)) (a : Additive (Uᵥ(v) ⧸ N)), schwartzBruhatUnitTranslate u.val (S a) =
      S (Additive.ofMul (QuotientGroup.mk u) + a) := by
    intro u a
    simp only [S, T]
    rw [hcomp]
    change T (u * r (Additive.toMul a)) =
      T (r (Additive.toMul (Additive.ofMul (QuotientGroup.mk u) + a)))
    rw [← hr (u * r (Additive.toMul a)), toMul_add, toMul_ofMul, QuotientGroup.mk_mul, hrmk]
  let comp : AddChar (Additive (Uᵥ(v) ⧸ N)) ℂ → ℬ(Fᵥ(v)) := fun ψ ↦ ∑ a, ψ (-a) • S a
  have hiso : ∀ ψ : AddChar (Additive (Uᵥ(v) ⧸ N)) ℂ, ∃ χ : PontryaginDual Uᵥ(v),
      ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val (comp ψ) = (χ u : ℂ) • comp ψ := by
    intro ψ
    let ψc : Uᵥ(v) ⧸ N → Circle := fun g ↦
      ⟨ψ (Additive.ofMul g), mem_sphere_zero_iff_norm.2 (ψ.norm_apply _)⟩
    let χm : Uᵥ(v) →* Circle :=
      { toFun := fun u ↦ ψc (QuotientGroup.mk u)
        map_one' := by
          apply Circle.ext
          change ψ (Additive.ofMul (QuotientGroup.mk 1)) = 1
          rw [QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]
        map_mul' := fun a b ↦ by
          apply Circle.ext
          change ψ (Additive.ofMul (QuotientGroup.mk (a * b))) =
            ψ (Additive.ofMul (QuotientGroup.mk a)) * ψ (Additive.ofMul (QuotientGroup.mk b))
          rw [QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul] }
    have hχc : Continuous χm :=
      (continuous_of_discreteTopology (f := ψc)).comp QuotientGroup.continuous_mk
    refine ⟨⟨χm, hχc⟩, fun u ↦ ?_⟩
    set c := Additive.ofMul (QuotientGroup.mk u : Uᵥ(v) ⧸ N)
    change L u (comp ψ) = ψ c • comp ψ
    simp only [comp, map_sum, map_smul]
    change ∑ a, ψ (-a) • schwartzBruhatUnitTranslate u.val (S a) = _
    simp only [hS]
    rw [Fintype.sum_equiv (Equiv.addLeft c) (fun a ↦ ψ (-a) • S (c + a))
      (fun b ↦ ψ (c + -b) • S b) (fun a ↦ by
        simp only [Equiv.coe_addLeft]
        rw [show c + -(c + a) = -a by abel]), Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [AddChar.map_add_eq_mul, mul_smul]
  have hsum : ∑ ψ : AddChar (Additive (Uᵥ(v) ⧸ N)) ℂ, comp ψ =
      (Fintype.card (Additive (Uᵥ(v) ⧸ N)) : ℂ) • f := by
    simp only [comp]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    change T (r (Additive.toMul 0)) = f
    rw [toMul_zero, ← QuotientGroup.mk_one, hr]
    change schwartzBruhatUnitTranslate (1 : Uᵥ(v)).val f = f
    refine SchwartzBruhat.ext fun x ↦ ?_
    rw [← ofAdd_toAdd x, schwartzBruhatUnitTranslate_apply, OneMemClass.coe_one, inv_one,
      Units.val_one, one_mul]
  have hc : (Fintype.card (Additive (Uᵥ(v) ⧸ N)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hf : f = (Fintype.card (Additive (Uᵥ(v) ⧸ N)) : ℂ)⁻¹ •
      ∑ ψ : AddChar (Additive (Uᵥ(v) ⧸ N)) ℂ, comp ψ := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hf]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun ψ _ ↦ Submodule.subset_span (hiso ψ))

open Classical in
/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
Weil's operator is uniquely specified by acting as the local difference on the trivial isotype
and as the identity on every nontrivial integer-unit isotype. Both formulas preserve the
corresponding isotype. -/
theorem finitePlacePrincipalValue_unique (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) :
    let obeys := fun P : ℬ(Fᵥ(v)) →L[ℂ] ℬ(Fᵥ(v)) ↦
      ∀ (χ : PontryaginDual Uᵥ(v)) (f : ℬ(Fᵥ(v))),
        (∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val f = (χ u : ℂ) • f) →
        P f = if χ = 1 then finitePlaceDifference v π f else f
    obeys (finitePlacePrincipalValue v) ∧
      ∀ P, obeys P → P = finitePlacePrincipalValue v := by
  intro obeys
  have hobeys : obeys (finitePlacePrincipalValue v) := fun χ f hf ↦
    finitePlacePrincipalValue_unique_obeys v π hπ χ f hf
  refine ⟨hobeys, fun P hP ↦ ?_⟩
  have heq : Set.EqOn P.toLinearMap (finitePlacePrincipalValue v).toLinearMap
      {g : ℬ(Fᵥ(v)) | ∃ χ : PontryaginDual Uᵥ(v),
        ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val g = (χ u : ℂ) • g} := by
    rintro g ⟨χ, hχ⟩
    change P g = finitePlacePrincipalValue v g
    rw [hP χ g hχ, hobeys χ g hχ]
  ext1 f
  exact LinearMap.eqOn_span' heq (finitePlacePrincipalValue_unique_span v f)

/-- The principal value is injective: a test in its kernel is invariant under the integer
units and under the uniformizer, so it vanishes. -/
private theorem finitePlacePrincipalValue_isClosedEmbedding_injective (v : V) :
    Function.Injective (finitePlacePrincipalValue v) := by
  let h := vval(v).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  have hπ : vval(v).IsUniformizer π.val := h.choose_spec
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsMulLeftInvariant := by
    unfold finiteLocalMultiplicativeTamagawaMeasure
    infer_instance
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  intro f f' hff'
  set k := f - f' with hk
  have hP : ∀ x, k x = (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd)))
        ∂μᵥ(v) := by
    intro x
    have h0 : finitePlacePrincipalValue v k = 0 := by rw [hk, map_sub, hff', sub_self]
    have h1 := finitePlacePrincipalValue_spec v π hπ k x
    rw [h0] at h1
    unfold finitePlacePrincipalValueFun at h1
    exact (sub_eq_zero.mp h1.symm)
  have hpos := (finitePlacePrincipalValue_integrable v π k 1).1
  have hm : (μᵥ(v).real Uᵥ(v) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  -- invariance of the average
  have hI : ∀ (w : Fᵥ(v)ˣ), w ∈ Uᵥ(v) → ∀ y : Fᵥ(v),
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((w : Fᵥ(v)) * y))) ∂μᵥ(v) =
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y)) ∂μᵥ(v) := by
    intro w hw y
    have hw' : w⁻¹ ∈ Uᵥ(v) := Subgroup.inv_mem _ hw
    rw [← finitePlacePrincipalValue_spec_setIntegral_mul_left μᵥ(v) _ hU
      (fun u : Fᵥ(v)ˣ ↦ k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * y))) w⁻¹
      (fun u ↦ Subgroup.mul_mem_cancel_left _ hw')]
    congr 1
    funext u
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    ring_nf
  have hinv : ∀ (w : Fᵥ(v)ˣ), w ∈ Uᵥ(v) → ∀ y : Fᵥ(v),
      k (Multiplicative.ofAdd ((w : Fᵥ(v)) * y)) = k (Multiplicative.ofAdd y) := by
    intro w hw y
    rw [hP, hP]
    congr 1
    change ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) *
      ((↑π⁻¹ : Fᵥ(v)) * ((w : Fᵥ(v)) * y)))) ∂μᵥ(v) =
      ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * y))) ∂μᵥ(v)
    rw [mul_left_comm, hI w hw]
  have hstep : ∀ x : Fᵥ(v), k (Multiplicative.ofAdd x) =
      k (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)) := by
    intro x
    rw [hP]
    change (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ * ∫ u in Uᵥ(v), k (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) *
      ((↑π⁻¹ : Fᵥ(v)) * x))) ∂μᵥ(v) = _
    rw [setIntegral_congr_fun hU (g := fun _ ↦ k (Multiplicative.ofAdd ((↑π⁻¹ : Fᵥ(v)) * x)))
      fun u hu ↦ hinv u⁻¹ (Subgroup.inv_mem _ hu) _, setIntegral_const, Complex.real_smul]
    field_simp
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff F v
    (fun x ↦ k (Multiplicative.ofAdd x))).1 ⟨k, fun _ ↦ rfl⟩
  have h0 := finitePlaceDifference_injective_aux v π hπ _ hlc hcs hstep
  refine sub_eq_zero.mp (SchwartzBruhat.ext fun y ↦ ?_)
  exact congrFun h0 (Multiplicative.toAdd y)

/-- Paper: Lemma 5.3.1.3, p. 241.
Weil's local principal value is a topological embedding with closed range. -/
theorem finitePlacePrincipalValue_isClosedEmbedding (v : V) :
    IsClosedEmbedding (finitePlacePrincipalValue v) := by
  have heq := finitePlaceSchwartz_finestTopology F v
  have h := finestLocallyConvex_isEmbedding_of_injective (E := ℬ(Fᵥ(v)))
    (finitePlacePrincipalValue v).toLinearMap
    (finitePlacePrincipalValue_isClosedEmbedding_injective v)
  have hemb : IsEmbedding (finitePlacePrincipalValue v) :=
    (congrArg (fun t ↦ @IsEmbedding ℬ(Fᵥ(v)) ℬ(Fᵥ(v)) t t
      (fun f ↦ finitePlacePrincipalValue v f)) heq).mpr h
  have hc := finestLocallyConvex_submodule_isClosed (E := ℬ(Fᵥ(v)))
    (LinearMap.range (finitePlacePrincipalValue v).toLinearMap)
  have hcl : IsClosed (Set.range (finitePlacePrincipalValue v)) :=
    (congrArg (fun t ↦ @IsClosed ℬ(Fᵥ(v)) t (Set.range (finitePlacePrincipalValue v)))
      heq).mpr hc
  exact ⟨hemb, hcl⟩

private theorem finitePlacePrincipalValue_range_integral {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (K : Subgroup G) (a : G) (ha : a ∈ K) (f : G → ℂ) :
    ∫ x in K, f (a * x) ∂μ = ∫ x in K, f x ∂μ := by
  have he : (fun x : G ↦ a * x) ⁻¹' (K : Set G) = K := by
    ext x
    simp only [mem_preimage]
    constructor
    · intro h
      have := K.mul_mem (K.inv_mem ha) h
      simpa using this
    · exact K.mul_mem ha
  have hp := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding f (K : Set G)
  rw [he] at hp
  exact hp

private theorem finitePlacePrincipalValue_range_zero (v : V) (f : ℬ(Fᵥ(v))) :
    finitePlacePrincipalValue v f (Multiplicative.ofAdd 0) = 0 := by
  let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  rw [finitePlacePrincipalValue_spec v π h.choose_spec]
  unfold finitePlacePrincipalValueFun
  simp only [show (Multiplicative.ofAdd (0 : Fᵥ(v))).toAdd = 0 from rfl, mul_zero,
    setIntegral_const, Complex.real_smul]
  have hm : (μᵥ(v).real Uᵥ(v) : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v π f (Multiplicative.ofAdd 0)).1.ne'
  field_simp
  ring

private theorem finitePlacePrincipalValue_range_invariant (v : V) (f : ℬ(Fᵥ(v))) :
    ∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u (f - finitePlacePrincipalValue v f) =
      f - finitePlacePrincipalValue v f := by
  intro u hu
  let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
  letI : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  let : (μᵥ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  apply Subtype.ext
  funext x
  change (f - finitePlacePrincipalValue v f) (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) = _
  change f _ - finitePlacePrincipalValue v f _ = f x - finitePlacePrincipalValue v f x
  have hp1 := finitePlacePrincipalValue_spec v π h.choose_spec f
    (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd))
  have hp2 := finitePlacePrincipalValue_spec v π h.choose_spec f x
  apply (congrArg₂ (fun a b : ℂ ↦
    f (Multiplicative.ofAdd ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)) - a = f x - b) hp1 hp2).mpr
  unfold finitePlacePrincipalValueFun
  have hi := finitePlacePrincipalValue_range_integral (μᵥ(v)) Uᵥ(v) u hu
    (fun a : Fᵥ(v)ˣ ↦ f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))))
  have hi' : (∫ a : Fᵥ(v)ˣ in Uᵥ(v),
      f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)))) ∂μᵥ(v)) =
      ∫ a : Fᵥ(v)ˣ in Uᵥ(v), f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))) ∂μᵥ(v) := by
    convert hi using 1
    congr 1
    funext a
    simp only [mul_inv_rev, Units.val_mul]
    ring
  change _ - (_ - (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹ *
      (∫ a : Fᵥ(v)ˣ in Uᵥ(v), f (Multiplicative.ofAdd ((↑a⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * ((↑u⁻¹ : Fᵥ(v)) * x.toAdd)))) ∂μᵥ(v))) = _
  rw [hi']
  ring

/-- Paper: Lemmas 5.3.1.1 and 5.3.1.3, pp. 240–241.
Weil's operator maps onto all tests vanishing at zero.
Deviation: The full evaluation kernel belongs to the averaged operator from (5.3.1.5). -/
theorem finitePlacePrincipalValue_range (v : V) :
    Set.range (finitePlacePrincipalValue v) =
      {f : ℬ(Fᵥ(v)) | f (Multiplicative.ofAdd 0) = 0} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact finitePlacePrincipalValue_range_zero v g
  · intro hf
    let h := (Valued.v : Valuation Fᵥ(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π := Units.mk0 (h.choose : Fᵥ(v)) h.choose_spec.ne_zero
    have hb : (f - finitePlacePrincipalValue v f) ∈
        {f | (∀ u ∈ Uᵥ(v), schwartzBruhatUnitTranslate u f = f) ∧ f (Multiplicative.ofAdd 0) = 0} := by
      refine ⟨finitePlacePrincipalValue_range_invariant v f, ?_⟩
      change f (Multiplicative.ofAdd 0) - finitePlacePrincipalValue v f (Multiplicative.ofAdd 0) = 0
      exact sub_eq_zero.mpr (hf.trans (finitePlacePrincipalValue_range_zero v f).symm)
    have hb' := (Set.ext_iff.mp (finitePlaceDifference_range_on_unitInvariants v π h.choose_spec)
      (f - finitePlacePrincipalValue v f)).mpr hb
    obtain ⟨g, hg, hge⟩ := hb'
    have hP : finitePlacePrincipalValue v g = finitePlaceDifference v π g := by
      have huniq := (finitePlacePrincipalValue_unique v π h.choose_spec).1 1 g
      have hh : ∀ u : Uᵥ(v), schwartzBruhatUnitTranslate u.val g = ((1 : PontryaginDual Uᵥ(v)) u : ℂ) • g := by
        intro u
        simpa using hg u.val u.property
      simpa only [if_pos rfl, ite_true] using huniq hh
    refine ⟨f + g, ?_⟩
    calc
      finitePlacePrincipalValue v (f + g) = finitePlacePrincipalValue v f + finitePlacePrincipalValue v g := map_add _ _ _
      _ = finitePlacePrincipalValue v f + (f - finitePlacePrincipalValue v f) := congrArg (finitePlacePrincipalValue v f + ·) (hP.trans hge)
      _ = f := by abel

section

/-- Tests for which a scalar functional intertwines an operator with a weighted
average of translates form a submodule, including integrability in the predicate. -/
private def principalValueAverageSubmodule {A G : Type*} [AddCommGroup A] [Module ℂ A]
    [MeasurableSpace G] (μ : Measure G) (K : ℂ) (P : A →ₗ[ℂ] A)
    (T : G → A →ₗ[ℂ] A) (L : A →ₗ[ℂ] ℂ) : Submodule ℂ A where
  carrier := {f | Integrable (fun u ↦ L (T u f)) μ ∧ L (P f) = L f - K * ∫ u, L (T u f) ∂μ}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf, ef⟩ ⟨hg, eg⟩
    simp only [Set.mem_ofPred_eq, map_add]
    exact ⟨hf.add hg, by rw [integral_add hf hg, ef, eg]; ring⟩
  smul_mem' := by
    rintro c f ⟨hf, ef⟩
    simp only [Set.mem_ofPred_eq, map_smul, smul_eq_mul]
    exact ⟨hf.const_mul c, by rw [integral_const_mul, ef]; ring⟩

/-- Transport the scalar averaging identity along a linear insertion on a single orbit. -/
private theorem principalValueAverageSubmodule_insert {A B G : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [MeasurableSpace G]
    (μ : Measure G) (K : ℂ) (p : A →ₗ[ℂ] A) (P : B →ₗ[ℂ] B)
    (u : G → A →ₗ[ℂ] A) (T : G → B →ₗ[ℂ] B) (L : B →ₗ[ℂ] ℂ)
    (I : A →ₗ[ℂ] B) (a : A) (b : B) (hi : I a = b)
    (hp : P b = I (p a)) (ht : ∀ g, T g b = I (u g a))
    (ha : a ∈ principalValueAverageSubmodule μ K p u (L.comp I)) :
    b ∈ principalValueAverageSubmodule μ K P T L := by
  change Integrable (fun g ↦ L (T g b)) μ ∧ L (P b) = L b - K * ∫ g, L (T g b) ∂μ
  simp only [ht, hp]
  rw [← hi]
  exact ha

/-- Translation of tests as a linear map. -/
private def principalValueTranslate {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (c : Rˣ) :
    SchwartzBruhat (Multiplicative R) →ₗ[ℂ] SchwartzBruhat (Multiplicative R) where
  toFun := schwartzBruhatUnitTranslate c
  map_add' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ rfl)
  map_smul' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ rfl)

/-- A linear functional commutes with the local principal-value average. On each unit
isotype the orbit integral is the integral of a scalar character times a single test. -/
private theorem finitePlacePrincipalValue_average_functional (v : V) (π : Fᵥ(v)ˣ)
    (hπ : vval(v).IsUniformizer π.val) (L : ℬ(Fᵥ(v)) →ₗ[ℂ] ℂ) (f : ℬ(Fᵥ(v))) :
    f ∈ principalValueAverageSubmodule (μᵥ(v).restrict Uᵥ(v)) (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹
      (finitePlacePrincipalValue v).toLinearMap (fun u ↦ principalValueTranslate (π * u)) L := by
  classical
  have : BorelSpace Fᵥ(v)ˣ := ⟨rfl⟩
  have : μᵥ(v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hU : MeasurableSet (Uᵥ(v) : Set Fᵥ(v)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hK : IsCompact (Uᵥ(v) : Set Fᵥ(v)ˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  refine Submodule.span_le.mpr ?_ (finitePlacePrincipalValue_unique_span v f)
  rintro g ⟨χ, hχ⟩
  let ψ (u : Fᵥ(v)ˣ) : ℂ := if h : u ∈ Uᵥ(v) then χ ⟨u, h⟩ else 0
  have hc : ContinuousOn ψ (Uᵥ(v) : Set Fᵥ(v)ˣ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp χ.continuous).congr fun u ↦ by
      change (χ u : ℂ) = ψ u.val
      simp only [ψ, dite_eq_left u.2]
  let b := principalValueTranslate π g
  have trans (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) :
      principalValueTranslate (π * u) g = ψ u • b := by
    rw [show ψ u = (χ ⟨u, hu⟩ : ℂ) by simp [ψ, hu]]
    calc principalValueTranslate (π * u) g =
          principalValueTranslate π (schwartzBruhatUnitTranslate u g) := by
            apply SchwartzBruhat.ext
            intro x
            change g (Multiplicative.ofAdd ((↑(π * u)⁻¹ : Fᵥ(v)) * x.toAdd)) = _
            rw [mul_inv_rev, Units.val_mul, mul_assoc]
            rfl
      _ = _ := by rw [hχ ⟨u, hu⟩, map_smul]
  let k : ℂ := (μᵥ(v).real Uᵥ(v) : ℂ)⁻¹
  have hPV : finitePlacePrincipalValue v g = g - (k * ∫ u in Uᵥ(v), ψ u ∂μᵥ(v)) • b := by
    apply SchwartzBruhat.ext
    intro x
    rw [finitePlacePrincipalValue_spec v π hπ]
    unfold finitePlacePrincipalValueFun
    have he (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) := congrArg (fun t : ℬ(Fᵥ(v)) ↦ t x) (trans u hu)
    have point (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) : g (Multiplicative.ofAdd
        ((↑u⁻¹ : Fᵥ(v)) * ((↑π⁻¹ : Fᵥ(v)) * x.toAdd))) = ψ u * b x := by
      have eq := he u hu
      change g (Multiplicative.ofAdd ((↑(π * u)⁻¹ : Fᵥ(v)) * x.toAdd)) = _ at eq
      rwa [mul_inv_rev, Units.val_mul, mul_assoc] at eq
    rw [setIntegral_congr_fun hU point, integral_mul_const]
    change g x - k * (_ * b x) = g x - (k * _) * b x
    rw [mul_assoc]
  have hval (u : Fᵥ(v)ˣ) (hu : u ∈ Uᵥ(v)) :
      L (principalValueTranslate (π * u) g) = ψ u * L b := by rw [trans u hu, map_smul, smul_eq_mul]
  change IntegrableOn _ _ _ ∧ L (finitePlacePrincipalValue v g) = _
  refine ⟨((hc.mul continuousOn_const).congr (fun u hu ↦ hval u hu)).integrableOn_compact hK, ?_⟩
  rw [hPV, map_sub, map_smul, smul_eq_mul, setIntegral_congr_fun hU hval, integral_mul_const]
  change L g - (k * _) * L b = L g - k * (_ * L b)
  rw [mul_assoc]

end

end FinitePlace

section AdelicPrincipalValue

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬₛ(" S ")" => ℬ(SAdeleRing F S)
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)

open Classical in
variable (F) in
/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value applies the local operators in the selected finite factors.
Deviation: The tensor decomposition is the one from the Lean version of Proposition 2.1.4.1. -/
def sAdelePrincipalValue {S S₀ : Finset V} (_h₀ : S₀ ⊆ S) : ℬₛ(S) →ₗ[ℂ] ℬₛ(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] w : S, ℬ(w.val.adicCompletion F))
  let P : W →ₗ[ℂ] W := PiTensorProduct.map (R := ℂ) fun w : S ↦
    if w.val ∈ S₀ then (finitePlacePrincipalValue w.val).toLinearMap else LinearMap.id
  let idArch : ℬ(InfiniteAdeleRing F) →ₗ[ℂ] ℬ(InfiniteAdeleRing F) := LinearMap.id
  e.toLinearMap.comp ((TensorProduct.map idArch P).comp e.symm.toLinearMap)

variable (F) in
/-- Paper: Definition 5.3.1.4(2), p. 242.
The global principal value acts in the S₀-local factor and leaves the complementary factor
unchanged. -/
def adelePrincipalValue (S₀ : Finset V) : ℬ(𝔸[F]) →ₗ[ℂ] ℬ(𝔸[F]) :=
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose
  let idTail : ℬ(FiniteAdeleTail F S₀) →ₗ[ℂ] ℬ(FiniteAdeleTail F S₀) := LinearMap.id
  e.toLinearMap.comp
    ((TensorProduct.map (sAdelePrincipalValue F (Finset.Subset.refl S₀)) idTail).comp
      e.symm.toLinearMap)

private theorem sAdelePrincipalValue_tmul_aux {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (p : ι → Prop) [DecidablePred p] (T : ∀ i, D i →L[ℂ] D i) (f : A) (g : ∀ i, D i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map fun i ↦
      if p i then (T i).toLinearMap else LinearMap.id
    let I : A →ₗ[ℂ] A := LinearMap.id
    (e.toLinearMap.comp ((TensorProduct.map I P).comp e.symm.toLinearMap))
      (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) = e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, if p i then T i (g i) else g i)) := by
  intro W P I
  change e (TensorProduct.map I P (e.symm (e _))) = e _
  erw [e.symm_apply_apply, TensorProduct.map_tmul]
  apply congrArg e
  apply congrArg (TensorProduct.tmul ℂ f)
  exact (PiTensorProduct.map_tprod _ g).trans (congrArg (PiTensorProduct.tprod ℂ)
    (funext fun i ↦ DFunLike.ite_apply (P := p i) (T i).toLinearMap LinearMap.id (g i)))

open Classical in
/-- Paper: Definition 5.3.1.4(1), p. 242.
On pure tensors the S-local operator acts by the local principal value in each selected factor. -/
theorem sAdelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePrincipalValue F h₀ (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) =
      e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w)) := by
  intro e
  unfold sAdelePrincipalValue
  with_reducible
    exact sAdelePrincipalValue_tmul_aux e (fun w : S ↦ w.val ∈ S₀)
      (fun w ↦ finitePlacePrincipalValue w.val) f g

/-- Slicing an algebraic tensor against a functional on the tail commutes with any
linear operator on the first factor. -/
private theorem adelePrincipalValue_tensor_slice {A B X : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (e : InductiveTensor A B ≃L[ℂ] X) (l : B →ₗ[ℂ] ℂ) (P : A →ₗ[ℂ] A) :
    let T := e.toLinearMap.comp ((TensorProduct.map P (LinearMap.id (M := B))).comp e.symm.toLinearMap)
    ∃ r : X →ₗ[ℂ] A, (∀ a b, r (e (a ⊗ₜ[ℂ] b)) = l b • a) ∧ r.comp T = P.comp r := by
  intro T
  let m : A ⊗[ℂ] B →ₗ[ℂ] A :=
    (TensorProduct.rid ℂ A).toLinearMap.comp (TensorProduct.map LinearMap.id l)
  let r := m.comp e.symm.toLinearMap
  have hr (a : A) (b : B) : r (e (a ⊗ₜ[ℂ] b)) = l b • a := by
    change m (e.symm (e _)) = _
    erw [e.symm_apply_apply]
    exact TensorProduct.rid_tmul a (l b)
  refine ⟨r, hr, (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp ?_⟩
  apply TensorProduct.ext'
  intro a b
  change r (e (TensorProduct.map P LinearMap.id (e.symm (e (a ⊗ₜ[ℂ] b))))) =
    P (r (e (a ⊗ₜ[ℂ] b)))
  erw [e.symm_apply_apply, TensorProduct.map_tmul, hr, hr, map_smul]
  rfl

/-- The slice at the tail of an adele is evaluated by varying its stage coordinates.
Applying the global principal value before slicing applies the stage principal value to the slice. -/
private theorem adelePrincipalValue_slice (S : Finset V) (x : 𝔸[F]) :
    ∃ (z : SAdeleRing F S → 𝔸[F]) (r : ℬ(𝔸[F]) →ₗ[ℂ] ℬₛ(S)),
      (∀ p, (z p).1 = p.1) ∧ (∀ p (w : S), (z p).2 w.val = p.2 w) ∧
      (∀ p w, w ∉ S → (z p).2 w = x.2 w) ∧ z (adeleProjection F S x) = x ∧
      (∀ h p, r h (Multiplicative.ofAdd p) = h (Multiplicative.ofAdd (z p))) ∧
      r.comp (adelePrincipalValue F S) = (sAdelePrincipalValue F (Finset.Subset.refl S)).comp r := by
  classical
  let patch (p : SAdeleRing F S) (w : V) : w.adicCompletion F :=
    if h : w ∈ S then p.2 ⟨w, h⟩ else x.2 w
  let z (p : SAdeleRing F S) : 𝔸[F] := (p.1, ⟨patch p, by
    filter_upwards [S.eventually_cofinite_notMem, x.2.2] with w hw hx
    rw [show patch p w = x.2 w from dite_eq_right hw]
    exact hx⟩)
  have hstage (p : SAdeleRing F S) : adeleProjection F S (z p) = p :=
    Prod.ext rfl (funext fun w ↦ (dite_eq_left w.2 : patch p w.val = p.2 w))
  let tail := finiteAdeleTailProjection F S x.2
  have htail (p : SAdeleRing F S) : finiteAdeleTailProjection F S (z p).2 = tail := by
    apply RestrictedProduct.ext
    intro w
    exact dite_eq_right w.2
  let ev : ℬ(FiniteAdeleTail F S) →ₗ[ℂ] ℂ :=
    { toFun := fun g ↦ g (Multiplicative.ofAdd tail), map_add' := fun _ _ ↦ rfl,
      map_smul' := fun _ _ ↦ rfl }
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
  obtain ⟨r, hr, hP⟩ := adelePrincipalValue_tensor_slice e ev (sAdelePrincipalValue F (Finset.Subset.refl S))
  refine ⟨z, r, fun _ ↦ rfl, fun p w ↦ dite_eq_left w.2, fun p w hw ↦ dite_eq_right hw, ?_, ?_, hP⟩
  · refine Prod.ext rfl ?_
    apply RestrictedProduct.ext
    intro w
    change patch _ w = _
    simp only [patch]
    split <;> rfl
  · intro h p
    let L : ℬₛ(S) →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f (Multiplicative.ofAdd p), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    let R : ℬ(𝔸[F]) →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f (Multiplicative.ofAdd (z p)), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    suffices heq : (L.comp r).comp e.toLinearMap = R.comp e.toLinearMap from
      LinearMap.congr_fun ((LinearMap.cancel_right e.surjective).mp heq) h
    apply TensorProduct.ext'
    intro a b
    change r (e (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd p) = e (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd (z p))
    erw [hr, (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose_spec a b (z p), hstage, htail]
    exact mul_comm _ _

open Classical in
/-- Split a product on a stage into factors on the selected stage and its complement. -/
private theorem adelePrincipalValue_prod_stage {ι : Type*} {S₀ S : Finset ι} (h₀ : S₀ ⊆ S)
    (f : S → ℂ) : (∏ w : S, f w) =
      (∏ w : S₀, f ⟨w.val, h₀ w.2⟩) * ∏ w : {w : S // w.val ∉ S₀}, f w.val := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : S ↦ w.val ∈ S₀)]
  congr 1
  exact Fintype.prod_equiv
    (⟨fun w ↦ ⟨w.val.val, w.2⟩, fun w ↦ ⟨⟨w.val, h₀ w.2⟩, w.2⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩ : {w : S // w.val ∈ S₀} ≃ S₀) _ _ fun _ ↦ rfl

private theorem sLocalThetaPrincipalValue_transition_ext {ι A X Y : Type*} {M : ι → Type*}
    [TopologicalSpace A] [AddCommGroup A] [Module ℂ A] [TopologicalSpace X]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] X)
    (i : X →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X) (q : Y →ₗ[ℂ] Y)
    (h : ∀ (a : A) (g : ∀ i, M i),
      i (p (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)))) = q (i (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))) :
    i.comp p = q.comp i := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top (h a)

/-- Paper: Definition 5.3.1.4(2), p. 242.
Through any stage containing S₀ the global operator acts as the S-local operator on the stage
factor and as the identity on the tail. -/
theorem adelePrincipalValue_tmul {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬₛ(S)) (g : ℬ(FiniteAdeleTail F S)) :
    let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
    adelePrincipalValue F S₀ (e (f ⊗ₜ[ℂ] g)) = e (sAdelePrincipalValue F h₀ f ⊗ₜ[ℂ] g) := by
  classical
  intro e
  let i : ℬₛ(S) →ₗ[ℂ] ℬ(𝔸[F]) :=
    e.toLinearMap.comp ((TensorProduct.mk ℂ ℬₛ(S) ℬ(FiniteAdeleTail F S)).flip g)
  let P := sAdelePrincipalValue F h₀
  let Q := adelePrincipalValue F S₀
  suffices eq : i.comp P = Q.comp i from (LinearMap.congr_fun eq f).symm
  apply sLocalThetaPrincipalValue_transition_ext (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  intro a b
  let pure (T : Finset V) (d : ∀ w : T, ℬ(w.val.adicCompletion F)) : ℬₛ(T) :=
    (sAdeleSchwartz_inductiveTensor_equiv F T).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, d w))
  let op (T : Finset V) (d : ∀ w : T, ℬ(w.val.adicCompletion F)) (w : T) :=
    if w.val ∈ S₀ then finitePlacePrincipalValue w.val (d w) else d w
  let res (d : ∀ w : S, ℬ(w.val.adicCompletion F)) (w : S₀) := d ⟨w.val, h₀ w.2⟩
  have hPV (T : Finset V) (hT : S₀ ⊆ T) (d : ∀ w : T, ℬ(w.val.adicCompletion F)) :
      sAdelePrincipalValue F hT (pure T d) = pure T (op T d) := by
    with_reducible exact sAdelePrincipalValue_tmul hT a d
  change i (P (pure S b)) = Q (i (pure S b))
  apply SchwartzBruhat.ext
  intro y
  let x := y.toAdd
  obtain ⟨z, r, hz₁, hzS, hzout, hzx, hr, hrQ⟩ := adelePrincipalValue_slice S₀ x
  let C (d : ∀ w : S, ℬ(w.val.adicCompletion F)) : ℂ :=
    (∏ w : {w : S // w.val ∉ S₀}, d w.val (Multiplicative.ofAdd (x.2 w.val.val))) *
      g (Multiplicative.ofAdd (finiteAdeleTailProjection F S x.2))
  have slice (d : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      r (i (pure S d)) = C d • pure S₀ (res d) := by
    apply SchwartzBruhat.ext
    intro t
    let p := t.toAdd
    change r (i (pure S d)) (Multiplicative.ofAdd p) = C d * pure S₀ (res d) (Multiplicative.ofAdd p)
    erw [hr, (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose_spec (pure S d) g (z p)]
    have ht : finiteAdeleTailProjection F S (z p).2 = finiteAdeleTailProjection F S x.2 := by
      apply RestrictedProduct.ext
      intro w
      exact hzout p w.val fun h ↦ w.2 (h₀ h)
    erw [ht, (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a d (adeleProjection F S (z p)),
      (sAdeleSchwartz_inductiveTensor_equiv F S₀).choose_spec a (res d) p]
    change (a (Multiplicative.ofAdd (z p).1) *
      ∏ w : S, d w (Multiplicative.ofAdd ((z p).2 w.val))) * _ = _
    rw [hz₁, adelePrincipalValue_prod_stage h₀]
    have hout (w : {w : S // w.val ∉ S₀}) : (z p).2 w.val.val = x.2 w.val.val :=
      hzout p w.val.val w.2
    simp only [hzS p, hout, C, res]
    ring
  have hC : C (op S b) = C b := by
    apply congrArg (· * _)
    exact Finset.prod_congr rfl fun w _ ↦ by simp only [op, ite_eq_right w.2]
  have eq : r (i (P (pure S b))) = r (Q (i (pure S b))) := by
    change r (i (sAdelePrincipalValue F h₀ (pure S b))) = _
    have hq : r (Q (i (pure S b))) = sAdelePrincipalValue F (Finset.Subset.refl S₀) (r (i (pure S b))) :=
      LinearMap.congr_fun hrQ _
    rw [hPV S h₀, slice, hC, hq, slice, map_smul, hPV]
  have atx := congrArg (fun k : ℬₛ(S₀) ↦ k (Multiplicative.ofAdd (adeleProjection F S₀ x))) eq
  change i (P (pure S b)) (Multiplicative.ofAdd x) = Q (i (pure S b)) (Multiplicative.ofAdd x)
  simpa only [hr, hzx] using atx

section PrincipalValueInjectivity

/-- A tensor product of injective endomorphisms of finitely many factors is injective: an
injective linear map over a field has a left inverse, and a left inverse of each factor composes
to a left inverse of the tensor product. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_injective_piTensor {ι : Type*}
    [Fintype ι] {D : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (T : ∀ i, D i →ₗ[ℂ] D i) (hT : ∀ i, Function.Injective (T i)) :
    Function.Injective (PiTensorProduct.map (R := ℂ) T) := by
  classical
  choose g hg using fun i ↦
    LinearMap.exists_leftInverse_of_injective (T i) (LinearMap.ker_eq_bot.mpr (hT i))
  have hcomp : (PiTensorProduct.map (R := ℂ) g) ∘ₗ (PiTensorProduct.map (R := ℂ) T) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp (f := T) (g := g), funext hg, PiTensorProduct.map_id]
  intro x y hxy
  have hx : (PiTensorProduct.map (R := ℂ) g) ((PiTensorProduct.map (R := ℂ) T) x) = x := by
    simpa using congrArg (fun L => L x) hcomp
  have hy : (PiTensorProduct.map (R := ℂ) g) ((PiTensorProduct.map (R := ℂ) T) y) = y := by
    simpa using congrArg (fun L => L y) hcomp
  rw [← hx, ← hy, hxy]

/-- A tensor product of two injective linear maps over a field is injective, by the left inverse
of each factor. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_injective_tensorProduct
    {A A' B B' : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup B] [Module ℂ B] [AddCommGroup B'] [Module ℂ B']
    (f : A →ₗ[ℂ] A') (g : B →ₗ[ℂ] B') (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (TensorProduct.map f g) := by
  obtain ⟨f', hf'⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective g (LinearMap.ker_eq_bot.mpr hg)
  have hcomp : TensorProduct.map f' g' ∘ₗ TensorProduct.map f g = LinearMap.id := by
    rw [← TensorProduct.map_comp f' g' f g, hf', hg', TensorProduct.map_id]
  intro x y hxy
  have hx : TensorProduct.map f' g' (TensorProduct.map f g x) = x := by
    simpa using congrArg (fun L => L x) hcomp
  have hy : TensorProduct.map f' g' (TensorProduct.map f g y) = y := by
    simpa using congrArg (fun L => L y) hcomp
  rw [← hx, ← hy, hxy]

/-- An operator given by the identity on the archimedean factor and by a tensor product of
endomorphisms of the finite factors, conjugated by a linear homeomorphism, is injective as soon
as those endomorphisms are. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_injective_aux {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} [Fintype ι] {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (p : ι → Prop) [DecidablePred p] (T : ∀ i, D i →L[ℂ] D i)
    (hT : ∀ i, Function.Injective (T i)) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map fun i ↦
      if p i then (T i).toLinearMap else LinearMap.id
    let I : A →ₗ[ℂ] A := LinearMap.id
    Function.Injective (e.toLinearMap.comp ((TensorProduct.map I P).comp e.symm.toLinearMap)) := by
  classical
  intro W P I
  have hP : Function.Injective P := by
    refine sAdelePrincipalValue_isClosedEmbedding_injective_piTensor
      (fun i => if p i then (T i).toLinearMap else LinearMap.id) ?_
    intro i
    by_cases h : p i
    · simpa [h] using hT i
    · simpa [h] using (show Function.Injective (LinearMap.id : D i →ₗ[ℂ] D i)
        from fun a b hab => hab)
  have hI : Function.Injective I := fun a b hab => hab
  have hTens : Function.Injective (TensorProduct.map I P) :=
    sAdelePrincipalValue_isClosedEmbedding_injective_tensorProduct I P hI hP
  intro x y hxy
  have hxy' : e (TensorProduct.map I P (e.symm x)) =
      e (TensorProduct.map I P (e.symm y)) := hxy
  exact e.symm.injective (hTens (e.injective hxy'))

end PrincipalValueInjectivity

/-- Paper: Definition 5.3.1.4(1) and Lemma 5.3.1.3, p. 242.
The S-local principal value has trivial kernel: on a selected finite place it is the local
principal value of Lemma 5.3.1.3, whose kernel is trivial, and on every other factor of the
tensor decomposition it is the identity. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_injective {S S₀ : Finset V}
    (h₀ : S₀ ⊆ S) : Function.Injective (sAdelePrincipalValue F h₀) := by
  classical
  unfold sAdelePrincipalValue
  with_reducible
    exact sAdelePrincipalValue_isClosedEmbedding_injective_aux
      (sAdeleSchwartz_inductiveTensor_equiv F S).choose (fun w : S ↦ w.val ∈ S₀)
      (fun w ↦ finitePlacePrincipalValue w.val)
      (fun w ↦ (finitePlacePrincipalValue_isClosedEmbedding w.val).injective)

/-- Finite-place principal values admit algebraic left inverses. On the finite
tensor factor these are continuous for the finest locally convex topology. -/
private theorem sAdelePrincipalValue_tensorFamily_leftInverse {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [T2Space B]
    {ι : Type*} {D : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (T : ∀ i, D i →ₗ[ℂ] D i) (hinj : ∀ i, Function.Injective (T i)) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map T
    let f := e.toLinearMap.comp ((TensorProduct.map
      (LinearMap.id (R := ℂ) (M := A)) P).comp e.symm.toLinearMap)
    ∃ j : B →L[ℂ] B, LeftInverse j f ∧ Continuous f := by
  classical
  intro W P _
  choose L hL using fun i ↦ (T i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hinj i))
  let J : W →ₗ[ℂ] W := PiTensorProduct.map L
  have hJP : J.comp P = LinearMap.id :=
    (PiTensorProduct.map_comp L T).symm.trans ((congrArg (PiTensorProduct.map (R := ℂ))
      (funext hL)).trans PiTensorProduct.map_id)
  let : T2Space W := finestLocallyConvex_t2 _
  let lift (p : W →ₗ[ℂ] W) : InductiveTensor A W →L[ℂ] InductiveTensor A W :=
    ⟨inductiveTensorMap LinearMap.id p, inductiveTensorMap_continuous (ContinuousLinearMap.id ℂ A)
      (⟨p, continuous_of_finestLocallyConvex _ p⟩ : W →L[ℂ] W)⟩
  let f := e.toContinuousLinearMap.comp ((lift P).comp e.symm.toContinuousLinearMap)
  let j := e.toContinuousLinearMap.comp ((lift J).comp e.symm.toContinuousLinearMap)
  have hleft : Function.LeftInverse j f := by
    intro x
    change e (lift J (e.symm (e (lift P (e.symm x))))) = x
    rw [e.symm_apply_apply]
    have hmaps (z : A ⊗[ℂ] W) :
        TensorProduct.map (LinearMap.id (M := A)) J (TensorProduct.map LinearMap.id P z) = z := by
      rw [TensorProduct.map_map, hJP, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
    exact (congrArg e (hmaps (e.symm x))).trans (e.apply_symm_apply x)
  exact ⟨j, hleft, f.continuous⟩

private theorem sAdelePrincipalValue_isClosedEmbedding_tensorFamily {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [T2Space B]
    {ι : Type*} {D : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (T : ∀ i, D i →ₗ[ℂ] D i) (hinj : ∀ i, Function.Injective (T i)) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map T
    IsClosedEmbedding (e.toLinearMap.comp ((TensorProduct.map
      (LinearMap.id (R := ℂ) (M := A)) P).comp e.symm.toLinearMap)) := by
  obtain ⟨j, hj, hc⟩ := sAdelePrincipalValue_tensorFamily_leftInverse e T hinj
  exact hj.isClosedEmbedding j.continuous hc

/-- Transport the split injection through the S-adelic tensor presentation. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_tensor {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    IsClosedEmbedding (sAdelePrincipalValue F h₀) := by
  classical
  let : T2Space (ℬ(InfiniteAdeleRing F)) := schwartzBruhat_eval_t2
  let : T2Space (ℬₛ(S)) := schwartzBruhat_eval_t2
  unfold sAdelePrincipalValue
  with_reducible_and_instances
    apply sAdelePrincipalValue_isClosedEmbedding_tensorFamily
  intro w
  split
  · exact fun _ _ h ↦ (finitePlacePrincipalValue_isClosedEmbedding w.val).injective h
  · exact Function.injective_id

/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value induces the topology of the S-local test space: it is the identity
on the archimedean factor and a tensor product of endomorphisms of the finite factors, so it is
a linear self-map of a space whose topology is transported from that tensor decomposition. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_isInducing {S S₀ : Finset V}
    (h₀ : S₀ ⊆ S) : IsInducing (sAdelePrincipalValue F h₀) :=
  (sAdelePrincipalValue_isClosedEmbedding_tensor (F := F) h₀).isEmbedding.isInducing

/-- Paper: Definition 5.3.1.4(1) and Lemma 5.3.1.3, p. 242.
The image of the S-local principal value is closed: it is the image of the whole archimedean
factor and of the image of the local principal value in each selected finite place, that is, of
tests vanishing at the origin there, which is the zero set of a continuous functional. -/
private theorem sAdelePrincipalValue_isClosedEmbedding_isClosed {S S₀ : Finset V}
    (h₀ : S₀ ⊆ S) : IsClosed (Set.range (sAdelePrincipalValue F h₀)) :=
  (sAdelePrincipalValue_isClosedEmbedding_tensor (F := F) h₀).isClosed_range

/-- Paper: Definition 5.3.1.4(1), p. 242.
The S-local principal value is a topological embedding with closed range. -/
theorem sAdelePrincipalValue_isClosedEmbedding {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    IsClosedEmbedding (sAdelePrincipalValue F h₀) :=
  ⟨⟨sAdelePrincipalValue_isClosedEmbedding_isInducing h₀,
    sAdelePrincipalValue_isClosedEmbedding_injective h₀⟩,
    sAdelePrincipalValue_isClosedEmbedding_isClosed h₀⟩

/-- A continuous linear left inverse on the stage tensors with the identity on the tail. -/
private theorem adelePrincipalValue_isClosedEmbedding_tensor {A B X : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [T2Space X]
    (e : InductiveTensor A B ≃L[ℂ] X) (p : A →ₗ[ℂ] A)
    (hs : ∃ j : A →L[ℂ] A, LeftInverse j p ∧ Continuous p) :
    IsClosedEmbedding (e.toLinearMap.comp ((TensorProduct.map p
      (LinearMap.id (R := ℂ) (M := B))).comp e.symm.toLinearMap)) := by
  obtain ⟨j, hj, hp⟩ := hs
  let lift (t : A →L[ℂ] A) : X →L[ℂ] X := e.toContinuousLinearMap.comp
    ((⟨inductiveTensorMap t.toLinearMap LinearMap.id,
       inductiveTensorMap_continuous t (ContinuousLinearMap.id ℂ B)⟩ :
      InductiveTensor A B →L[ℂ] InductiveTensor A B).comp e.symm.toContinuousLinearMap)
  have hcomp : j.toLinearMap.comp p = LinearMap.id := LinearMap.ext hj
  have hleft : LeftInverse (lift j) (lift ⟨p, hp⟩) := by
    intro x
    change e (TensorProduct.map j.toLinearMap LinearMap.id
      (e.symm (e (TensorProduct.map p LinearMap.id (e.symm x))))) = x
    have hm (t : A ⊗[ℂ] B) :
        TensorProduct.map j.toLinearMap (LinearMap.id (M := B)) (TensorProduct.map p LinearMap.id t) = t := by
      rw [TensorProduct.map_map, hcomp, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
    erw [e.symm_apply_apply]
    exact (congrArg e (hm (e.symm x))).trans (e.apply_symm_apply x)
  exact hleft.isClosedEmbedding (lift j).continuous (lift ⟨p, hp⟩).continuous

/-- Paper: Definition 5.3.1.4(2), p. 242.
The global principal value is a topological embedding with closed range. -/
theorem adelePrincipalValue_isClosedEmbedding (S₀ : Finset V) :
    IsClosedEmbedding (adelePrincipalValue F S₀) := by
  classical
  let : T2Space (ℬ(InfiniteAdeleRing F)) := schwartzBruhat_eval_t2
  let : T2Space (ℬₛ(S₀)) := schwartzBruhat_eval_t2
  let : T2Space (ℬ(FiniteAdeleTail F S₀)) := schwartzBruhat_eval_t2
  let : T2Space (ℬ(𝔸[F])) := schwartzBruhat_eval_t2
  unfold adelePrincipalValue
  with_reducible apply adelePrincipalValue_isClosedEmbedding_tensor
  unfold sAdelePrincipalValue
  with_reducible_and_instances apply sAdelePrincipalValue_tensorFamily_leftInverse
  intro w
  rw [ite_eq_left w.property]
  exact (finitePlacePrincipalValue_isClosedEmbedding w.val).injective

local instance instMeasurableSpaceAdicUnitsSec3aKernel (v : V) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

/-- The unit of the S-local adele ring that is the given local unit at `v` and `1` at every
other place of `S`; translating by it rescales only the `v`-coordinate of the argument. -/
private def adelicPrincipalValueLocalUnit {S : Finset V} (v : S)
    (c : (v.val.adicCompletion F)ˣ) : (SAdeleRing F S)ˣ := by
  classical
  refine Units.mk (1, Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.val)
    (1, Function.update (fun w : S => (1 : w.val.adicCompletion F)) v c.inv) ?_ ?_
  · refine Prod.ext (by simp) (funext fun w => ?_)
    by_cases h : w = v
    · subst h
      simp [Function.update_apply, Units.mul_inv]
    · simp [Function.update_apply, h]
  · refine Prod.ext (by simp) (funext fun w => ?_)
    by_cases h : w = v
    · subst h
      simp [Function.update_apply, Units.inv_mul]
    · simp [Function.update_apply, h]

/-- S-local theta of a translate is S-local theta evaluated at the inverse-translated idele. -/
private theorem sAdelePrincipalValue_preserves_thetaKernel_translate
    {S : Finset V} (g x : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x =
      sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp
    (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t => congrArg (fun y => f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (d t).val x.val)

/-- Inserting a single local test in a fixed pure tensor is linear in that test. -/
private theorem principalValue_tensor_insert {ι A B : Type*} [DecidableEq ι] {M : ι → Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] B)
    (a : A) (b : ∀ i, M i) (v : ι) :
    ∃ I : M v →ₗ[ℂ] B, (∀ h, I h = e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, (Function.update b v h) w))) ∧
      I (b v) = e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) := by
  let W := FinestLocallyConvex (⨂[ℂ] i, M i)
  refine ⟨e.toLinearMap.comp (((TensorProduct.mk ℂ A W) a).comp
    ((PiTensorProduct.tprod ℂ).toLinearMap b v)), fun _ ↦ rfl, ?_⟩
  exact congrArg (fun d : ∀ i, M i ↦ e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, d w))) (Function.update_eq_self v b)

/-- Paper: (5.3.1.9), p. 242.
The single-place operator at `v` is `1` minus the normalized average over the integer units at
`v` of the translates by the reciprocal uniformizer times the unit, and S-local theta turns this
into the same recipe on the theta function: theta of the principal value at one place is theta of
the test minus the normalized average, over the integer units at that place, of theta of its
translates. This is the analytic content of (5.3.1.9): the theta sum over the S-units is exchanged
with the integral over the compact group of integer units, as in the proof of the formula for the
global theta function in one place in `Ch11_ShellStructure.Sec2a`. -/
private theorem sLocalAdelicTheta_sAdelePrincipalValue_singleton {S : Finset V} (v : S)
    (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F))
    (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
    sLocalAdelicTheta F S
        (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f) x =
      sLocalAdelicTheta F S f x -
        ((finiteLocalMultiplicativeTamagawaMeasure F v.val).real
          ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
            Set (v.val.adicCompletion F)ˣ) : ℂ)⁻¹ *
          ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v.val).units :
              Set (v.val.adicCompletion F)ˣ),
            sLocalAdelicTheta F S
              (schwartzBruhatUnitTranslate
                (adelicPrincipalValueLocalUnit v (π * (u : (v.val.adicCompletion F)ˣ))) f) x
            ∂(finiteLocalMultiplicativeTamagawaMeasure F v.val) := by
  classical
  let U : Set (v.val.adicCompletion F)ˣ := (v.val.adicCompletionIntegers F).units
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
  let L : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ sLocalAdelicTheta F S h x
      map_add' := fun a b ↦ congrArg (fun t : C((SAdeleRing F S)ˣ, ℂ) ↦ t x)
        (map_add (sLocalAdelicTheta F S) a b)
      map_smul' := fun c a ↦ congrArg (fun t : C((SAdeleRing F S)ˣ, ℂ) ↦ t x)
        (map_smul (sLocalAdelicTheta F S) c a) }
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
  let T (u : (v.val.adicCompletion F)ˣ) := principalValueTranslate (adelicPrincipalValueLocalUnit v (π * u))
  let D := principalValueAverageSubmodule (μ.restrict U) (μ.real U : ℂ)⁻¹ P T L
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have hpure (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ∈ D := by
    let t := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
    have insertion := principalValue_tensor_insert (A := ℬ(InfiniteAdeleRing F)) (B := ℬₛ(S))
      (M := fun w : S ↦ ℬ(w.val.adicCompletion F)) e a b v
    let I := insertion.choose
    have ins := insertion.choose_spec.1
    have hid := insertion.choose_spec.2
    have hPV : P t = I (finitePlacePrincipalValue v.val (b v)) := by
      refine (sAdelePrincipalValue_tmul (Finset.singleton_subset_iff.mpr v.2) a b).trans ?_
      refine Eq.trans ?_ (ins _).symm
      apply congrArg (fun d : ∀ w : S, ℬ(w.val.adicCompletion F) ↦ e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, d w)))
      funext w
      by_cases h : w = v
      · subst w; simp
      · simp only [Finset.mem_singleton, ite_eq_right (fun he ↦ h (Subtype.ext he)),
          Function.update_of_ne h]
    have htrans (u : (v.val.adicCompletion F)ˣ) : T u t = I (principalValueTranslate (π * u) (b v)) := by
      apply SchwartzBruhat.ext
      intro y
      let z := y.toAdd
      let c := π * u
      let k := adelicPrincipalValueLocalUnit v c
      change t (Multiplicative.ofAdd ((↑k⁻¹ : SAdeleRing F S) * z)) = _
      have hh := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
      refine (hh a b _).trans ?_
      refine Eq.trans ?_ ((hh a _ z).symm.trans (congrArg (fun φ : ℬₛ(S) ↦ φ y) (ins _).symm))
      have harch : ((↑k⁻¹ : SAdeleRing F S) * z).1 = z.1 := one_mul _
      rw [harch]
      apply congrArg (_ * ·)
      apply Finset.prod_congr rfl
      intro w _
      change b w (Multiplicative.ofAdd ((Function.update (fun j : S ↦ (1 : j.val.adicCompletion F)) v c.inv w) * z.2 w)) = _
      by_cases h : w = v
      · subst w
        simp only [Function.update_self]
        rfl
      · simp only [Function.update_of_ne h, one_mul]
    exact principalValueAverageSubmodule_insert (μ.restrict U) (μ.real U : ℂ)⁻¹
        (finitePlacePrincipalValue v.val).toLinearMap P (fun u ↦ principalValueTranslate (π * u))
        T L I (b v) t hid hPV htrans (finitePlacePrincipalValue_average_functional v.val π hπ (L.comp I) (b v))
  have hQ : D.mkQ.comp LinearMap.id = (0 : (ℬₛ(S) ⧸ D) →ₗ[ℂ] _).comp D.mkQ :=
    sLocalThetaPrincipalValue_transition_ext e D.mkQ LinearMap.id 0 fun a b ↦
      (Submodule.Quotient.mk_eq_zero D).mpr (hpure a b)
  have hf : f ∈ D := (Submodule.Quotient.mk_eq_zero D).mp (LinearMap.congr_fun hQ f)
  exact hf.2

/-- Paper: (5.3.1.9), p. 242.
The single-place principal value at `v` maps the theta kernel into itself: theta of the average
of the translates vanishes because theta of every translate is theta of the test at another
idele, and theta of the test is zero. -/
private theorem sAdelePrincipalValue_preserves_thetaKernel_singleton {S : Finset V} (v : S)
    (f : ℬₛ(S)) (hf : sLocalAdelicTheta F S f = 0) :
    sLocalAdelicTheta F S
      (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f) = 0 := by
  let hunif := (Valued.v :
    Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ :=
    Units.mk0 (hunif.choose : v.val.adicCompletion F) hunif.choose_spec.ne_zero
  have hπ : (Valued.v :
      Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
        (π : v.val.adicCompletion F) := hunif.choose_spec
  refine ContinuousMap.ext fun y => ?_
  refine (sLocalAdelicTheta_sAdelePrincipalValue_singleton v π hπ f y).trans ?_
  have hzero : ∀ (u : (v.val.adicCompletion F)ˣ) (z : (SAdeleRing F S)ˣ), sLocalAdelicTheta F S
        (schwartzBruhatUnitTranslate (R := SAdeleRing F S)
          (adelicPrincipalValueLocalUnit v (π * u)) f) z = 0 := by
    intro u z
    rw [sAdelePrincipalValue_preserves_thetaKernel_translate]
    exact DFunLike.congr_fun hf _
  have hfun : (fun u : (v.val.adicCompletion F)ˣ => sLocalAdelicTheta F S
        (schwartzBruhatUnitTranslate (R := SAdeleRing F S)
          (adelicPrincipalValueLocalUnit v (π * u)) f) y) = fun _ => 0 :=
    funext fun u => hzero u y
  have hf0 : sLocalAdelicTheta F S f y = 0 := DFunLike.congr_fun hf y
  rw [hfun, integral_zero, mul_zero, sub_zero]
  exact hf0

private theorem sAdelePrincipalValue_list_comp {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (φ ψ : ∀ i, D i →ₗ[ℂ] D i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let I : A →ₗ[ℂ] A := LinearMap.id
    let Q : (∀ i, D i →ₗ[ℂ] D i) → (B →ₗ[ℂ] B) := fun χ ↦
      e.toLinearMap.comp ((TensorProduct.map I (PiTensorProduct.map χ : W →ₗ[ℂ] W)).comp
        e.symm.toLinearMap)
    Q φ * Q ψ = Q (fun i ↦ φ i ∘ₗ ψ i) := by
  intro W I Q
  apply LinearMap.ext
  intro x
  change e (TensorProduct.map I _ (e.symm (e _))) = e _
  erw [e.symm_apply_apply]
  apply congrArg e
  have h : (TensorProduct.map I (PiTensorProduct.map φ : W →ₗ[ℂ] W)) ∘ₗ
      (TensorProduct.map I (PiTensorProduct.map ψ : W →ₗ[ℂ] W)) =
        TensorProduct.map I (PiTensorProduct.map (fun i ↦ φ i ∘ₗ ψ i) : W →ₗ[ℂ] W) := by
    rw [← TensorProduct.map_comp, PiTensorProduct.map_comp]
    rfl
  exact LinearMap.congr_fun h (e.symm x)

private theorem sAdelePrincipalValue_list_one {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)] [∀ i, TopologicalSpace (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let I : A →ₗ[ℂ] A := LinearMap.id
    e.toLinearMap.comp ((TensorProduct.map I
      (PiTensorProduct.map (fun i ↦ (LinearMap.id : D i →ₗ[ℂ] D i)) : W →ₗ[ℂ] W)).comp
        e.symm.toLinearMap) = (1 : B →ₗ[ℂ] B) := by
  intro W I
  apply LinearMap.ext
  intro x
  show e (TensorProduct.map I
    (PiTensorProduct.map (fun i ↦ (LinearMap.id : D i →ₗ[ℂ] D i)) : W →ₗ[ℂ] W) (e.symm x)) = x
  rw [PiTensorProduct.map_id]
  erw [TensorProduct.map_id]
  exact e.apply_symm_apply x

open Classical in
/-- Paper: (5.3.1.9), p. 242.
The S-local principal value is the composition, over the selected places, of its single-place
versions: each factor acts in its own coordinate of the tensor decomposition of the S-local test
space, so the operators commute and compose to the operator attached to the whole set. The
composite is written as a product over a list so that it can be peeled one place at a time. -/
private theorem sAdelePrincipalValue_preserves_thetaKernel_list {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (f : ℬₛ(S)) :
    sAdelePrincipalValue F h₀ f =
      (S₀.val.toList.map fun v => if h : v ∈ S then
        sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1).prod f := by
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] w : S, ℬ(w.val.adicCompletion F))
  let I : ℬ(InfiniteAdeleRing F) →ₗ[ℂ] ℬ(InfiniteAdeleRing F) := LinearMap.id
  let Q : (∀ w : S, ℬ(w.val.adicCompletion F) →ₗ[ℂ] ℬ(w.val.adicCompletion F)) →
      (ℬₛ(S) →ₗ[ℂ] ℬₛ(S)) := fun χ ↦
    e.toLinearMap.comp ((TensorProduct.map I (PiTensorProduct.map χ : W →ₗ[ℂ] W)).comp
      e.symm.toLinearMap)
  let T : ∀ w : S, ℬ(w.val.adicCompletion F) →ₗ[ℂ] ℬ(w.val.adicCompletion F) :=
    fun w ↦ (finitePlacePrincipalValue w.val).toLinearMap
  have hcomp : ∀ φ ψ, Q φ * Q ψ = Q (fun i ↦ φ i ∘ₗ ψ i) := fun φ ψ ↦
    sAdelePrincipalValue_list_comp e φ ψ
  have hone : Q (fun _ ↦ LinearMap.id) = 1 := sAdelePrincipalValue_list_one e
  have hPV : ∀ {S₁ : Finset V} (h : S₁ ⊆ S),
      sAdelePrincipalValue F h = Q (fun w ↦ if w.val ∈ S₁ then T w else LinearMap.id) :=
    fun _ ↦ rfl
  have hg : ∀ v : V, (if h : v ∈ S then
      sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1) =
        Q (fun w ↦ if w.val = v then T w else LinearMap.id) := by
    intro v
    by_cases hv : v ∈ S
    · rw [dite_eq_left_of_eq_true (eq_true hv), hPV]
      congr 1
      funext w
      simp only [Finset.mem_singleton]
    · rw [dite_eq_right_of_eq_false (eq_false hv), ← hone]
      congr 1
      funext w
      have hw : ¬(w.val = v) := fun hw ↦ hv (hw ▸ w.property)
      simp [hw]
  have hL : ∀ L : List V, L.Nodup → (L.map fun v ↦ if h : v ∈ S then
      sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1).prod =
        Q (fun w ↦ if w.val ∈ L then T w else LinearMap.id) := by
    intro L
    induction L with
    | nil =>
      intro _
      rw [List.map_nil, List.prod_nil, ← hone]
      congr 1
    | cons a L ih =>
      intro hnd
      have ha : a ∉ L := (List.nodup_cons.mp hnd).1
      rw [List.map_cons, List.prod_cons, hg a, ih (List.nodup_cons.mp hnd).2, hcomp]
      congr 1
      funext w
      by_cases hw : w.val = a
      · simp [hw, ha]
      · simp [hw]
  refine LinearMap.congr_fun ?_ f
  have hnd : S₀.val.toList.Nodup := by
    rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact S₀.nodup
  rw [hL _ hnd, hPV h₀]
  congr 1
  funext w
  simp only [Multiset.mem_toList, Finset.mem_val]

/-- Paper: (5.3.1.9), p. 242.
The S-local principal value preserves the kernel of theta averaging. -/
theorem sAdelePrincipalValue_preserves_thetaKernel {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    Kₛ(S) ≤ (Kₛ(S)).comap (sAdelePrincipalValue F h₀) := by
  classical
  have key : ∀ (l : List V), (∀ v ∈ l, v ∈ S) → ∀ g : ℬₛ(S), sLocalAdelicTheta F S g = 0 →
      sLocalAdelicTheta F S ((l.map fun v => if h : v ∈ S then
        sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1).prod g) = 0 := by
    intro l
    induction l with
    | nil =>
      intro _ g hg
      simpa using hg
    | cons a l ih =>
      intro hmem g hg
      have ha : a ∈ S := hmem a List.mem_cons_self
      have hta : ∀ v ∈ l, v ∈ S := fun v hv => hmem v (List.mem_cons_of_mem a hv)
      have htail := ih hta g hg
      have hQa : (if h : a ∈ S then
          sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1) =
          sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr ha) := dif_pos ha
      rw [List.map_cons, List.prod_cons, hQa]
      exact sAdelePrincipalValue_preserves_thetaKernel_singleton ⟨a, ha⟩ _ htail
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_comap]
  rw [sAdelePrincipalValue_preserves_thetaKernel_list h₀]
  exact key S₀.val.toList (fun v hv => h₀ (Multiset.mem_toList.mp hv)) f hf

open Classical in
/-- Through a stage containing the selected places, the global principal value of an
inserted test is the insertion of the S-local principal value. The integer tail indicator
is obtained by slicing the inserted test `k₀` at a point `p` where its value is one. -/
private theorem sLocalThetaPrincipalValue_toGlobal_slice {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (k₀ : ℬₛ(S)) (p : SAdeleRing F S)
    (hk₀ : k₀ (Multiplicative.ofAdd p) = 1) (k : ℬₛ(S)) :
    adelePrincipalValue F S₀ (sAdeleSchwartzToGlobal F S k) =
      sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F h₀ k) := by
  let Tl := ℬ(FiniteAdeleTail F S)
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose_spec
  let ev : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun a ↦ a (Multiplicative.ofAdd p)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : ℬₛ(S) ⊗[ℂ] Tl →ₗ[ℂ] Tl := TensorProduct.lift ((LinearMap.lsmul ℂ Tl).comp ev)
  let c : Tl := L (e.symm (sAdeleSchwartzToGlobal F S k₀))
  have hc (y : FiniteAdeleTail F S) : c (Multiplicative.ofAdd y) =
      if ∀ w, y w ∈ w.val.adicCompletionIntegers F then 1 else 0 := by
    let f : ∀ w : V, w.adicCompletion F := fun w ↦ if h : w ∈ S then p.2 ⟨w, h⟩ else y ⟨w, h⟩
    have hf : ∀ᶠ w in Filter.cofinite, f w ∈ w.adicCompletionIntegers F := by
      filter_upwards [S.eventually_cofinite_notMem, Filter.eventually_comap.mp
        (y.2.filter_mono (Filter.comap_cofinite_le Subtype.val))] with w hw h
      simp only [f, dite_eq_right hw]
      exact h ⟨w, hw⟩ rfl
    let z : FiniteAdeleRing (𝓞 F) F := ⟨f, hf⟩
    let x : AdeleRing (𝓞 F) F := (p.1, z)
    have hx (w : V) (hw : w ∉ S) : x.2 w = y ⟨w, hw⟩ := dite_eq_right hw
    have hp : adeleProjection F S x = p :=
      Prod.ext rfl (funext fun w ↦ (dite_eq_left w.2 : f w.val = p.2 w))
    have ht : finiteAdeleTailProjection F S x.2 = y := by
      apply RestrictedProduct.ext
      intro w
      exact dite_eq_right w.2
    let evy : Tl →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd y)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let evx : ℬ(AdeleRing (𝓞 F) F) →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd x)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have key : evy ∘ₗ L = evx ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S) Tl →ₗ[ℂ] _) := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change (a (Multiplicative.ofAdd p) • b) (Multiplicative.ofAdd y) =
        e (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x)
      rw [he a b x, hp, ht]
      rfl
    have h2 : c (Multiplicative.ofAdd y) =
        sAdeleSchwartzToGlobal F S k₀ (Multiplicative.ofAdd x) :=
      (LinearMap.congr_fun key (e.symm (sAdeleSchwartzToGlobal F S k₀))).trans
        (congrArg (fun φ : ℬ(AdeleRing (𝓞 F) F) ↦
          φ (Multiplicative.ofAdd x)) (e.apply_symm_apply _))
    rw [h2, sAdeleSchwartzToGlobal_apply, hp, hk₀]
    by_cases hy : ∀ w, y w ∈ w.val.adicCompletionIntegers F
    · rw [ite_eq_left hy, ite_eq_left fun w hw ↦ by rw [hx w hw]; exact hy ⟨w, hw⟩]
    · rw [ite_eq_right hy, ite_eq_right fun h ↦ hy fun w ↦ by rw [← hx w.val w.2]; exact h w.val w.2]
  have hslice (a : ℬₛ(S)) : e (a ⊗ₜ[ℂ] c) = sAdeleSchwartzToGlobal F S a := by
    apply Subtype.ext
    funext x
    change e (a ⊗ₜ[ℂ] c) (Multiplicative.ofAdd x.toAdd) =
      sAdeleSchwartzToGlobal F S a (Multiplicative.ofAdd x.toAdd)
    rw [he a c x.toAdd, hc, sAdeleSchwartzToGlobal_apply]
    by_cases hx : ∀ w : V, w ∉ S → x.toAdd.2 w ∈ w.adicCompletionIntegers F
    · rw [ite_eq_left hx, ite_eq_left (show ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun w ↦ hx w.val w.2), mul_one]
    · rw [ite_eq_right hx, ite_eq_right (show ¬ ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun h ↦ hx fun w hw ↦ h ⟨w, hw⟩), mul_zero]
  rw [← hslice k, ← hslice (sAdelePrincipalValue F h₀ k)]
  exact adelePrincipalValue_tmul h₀ k c

/-- On test functions, insertion of an S-local stage intertwines the S-local and the
global principal values. A nonzero test, normalized at a point where it does not vanish,
supplies the slice that identifies the integer tail indicator. -/
private theorem sLocalThetaPrincipalValue_toGlobal_tests {S₀ S : Finset V} (h₀ : S₀ ⊆ S) :
    (sAdeleSchwartzToGlobal F S).comp (sAdelePrincipalValue F h₀) =
      (adelePrincipalValue F S₀).comp (sAdeleSchwartzToGlobal F S) := by
  apply LinearMap.ext
  intro k
  by_cases hk : k = 0
  · rw [hk, map_zero, map_zero]
  · obtain ⟨x, hx⟩ : ∃ x : Multiplicative (SAdeleRing F S), k x ≠ 0 := by
      by_contra h
      apply hk
      apply Subtype.ext
      funext x
      exact not_not.mp fun hx ↦ h ⟨x, hx⟩
    have hk₀ : ((k x)⁻¹ • k) (Multiplicative.ofAdd x.toAdd) = 1 := inv_mul_cancel₀ hx
    exact (sLocalThetaPrincipalValue_toGlobal_slice h₀ _ x.toAdd hk₀ k).symm

/-- Paper: (5.3.1.10), p. 242.
The global principal value preserves the kernel of theta averaging. -/
theorem adelePrincipalValue_preserves_thetaKernel (S₀ : Finset V) :
    K𝔽 ≤ (K𝔽).comap (adelePrincipalValue F S₀) := by
  classical
  intro f hf
  change adelePrincipalValue F S₀ f ∈ K𝔽
  obtain ⟨U, g, hg⟩ := sAdeleSchwartzToGlobal_exhaustive F f
  let T := U ∪ S₀
  have hu : U ⊆ T := Finset.subset_union_left
  have h₀ : S₀ ⊆ T := Finset.subset_union_right
  let k := sAdeleSchwartzTransition F hu g
  have hk : sAdeleSchwartzToGlobal F T k = f :=
    (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hu) g).trans hg
  have hlocal : k ∈ Kₛ(T) := by
    apply sLocalThetaToGlobal_reflects_kernel (F := F) (S := T)
    change sAdeleSchwartzToGlobal F T k ∈ K𝔽
    rwa [hk]
  have hcomm : sAdeleSchwartzToGlobal F T (sAdelePrincipalValue F h₀ k) =
      adelePrincipalValue F S₀ (sAdeleSchwartzToGlobal F T k) :=
    LinearMap.congr_fun (sLocalThetaPrincipalValue_toGlobal_tests h₀) k
  rw [← hk, ← hcomm]
  exact sLocalThetaToGlobal_preserves_kernel (F := F) (S := T)
    (sAdelePrincipalValue_preserves_thetaKernel h₀ hlocal)

variable (F) in
/-- Paper: (5.3.1.9), p. 242.
The S-local principal value acts on the S-local theta quotient by descent. -/
def sLocalThetaPrincipalValue {S S₀ : Finset V} (h₀ : S₀ ⊆ S) : Θₛ(S) →ₗ[ℂ] Θₛ(S) :=
  (Kₛ(S)).mapQ (Kₛ(S)) (sAdelePrincipalValue F h₀)
    (sAdelePrincipalValue_preserves_thetaKernel h₀)

variable (F) in
/-- Paper: (5.3.1.10), p. 242.
The global principal value acts on the global theta quotient by descent. -/
def globalThetaPrincipalValue (S₀ : Finset V) : Θ𝔽 →ₗ[ℂ] Θ𝔽 :=
  (K𝔽).mapQ K𝔽 (adelePrincipalValue F S₀) (adelePrincipalValue_preserves_thetaKernel S₀)

/-- Paper: (5.3.1.9), p. 242.
On a class represented by a test function the S-local operator gives the class of its image. -/
theorem sLocalThetaPrincipalValue_mk {S S₀ : Finset V} (h₀ : S₀ ⊆ S) (f : ℬₛ(S)) :
    sLocalThetaPrincipalValue F h₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F h₀ f) := by
  rfl

/-- Paper: (5.3.1.10), p. 242.
On a class represented by a test function the global operator gives the class of its image. -/
theorem globalThetaPrincipalValue_mk (S₀ : Finset V) (f : ℬ(𝔸[F])) :
    globalThetaPrincipalValue F S₀ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (adelePrincipalValue F S₀ f) := by
  rfl

/-- Paper: (5.3.1.9), p. 242.
The S-local operator descends continuously for every set of selected places. -/
theorem sLocalThetaPrincipalValue_continuous {S S₀ : Finset V} (h₀ : S₀ ⊆ S) :
    Continuous (sLocalThetaPrincipalValue F h₀) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (Kₛ(S)).isQuotientMap_mkQ.continuous.comp
    (sAdelePrincipalValue_isClosedEmbedding h₀).continuous

/-- Paper: (5.3.1.10), p. 242.
The global operator descends continuously for every set of selected places. -/
theorem globalThetaPrincipalValue_continuous (S₀ : Finset V) :
    Continuous (globalThetaPrincipalValue F S₀) := by
  apply (K𝔽).isQuotientMap_mkQ.continuous_iff.mpr
  exact (K𝔽).isQuotientMap_mkQ.continuous.comp
    (adelePrincipalValue_isClosedEmbedding S₀).continuous

-- TODO(paper-gap): Let K be the theta kernel and P the operator on tests.
-- On the quotient the preimage of the range is range P + K. Closedness of
-- range P and injectivity after descent do not establish closedness of this
-- sum or continuity of the inverse on its image. This affects both quotients.

private theorem sLocalThetaPrincipalValue_isClosedEmbedding_localUnit_mul {S : Finset V} (v : S)
    (a b : (v.val.adicCompletion F)ˣ) :
    adelicPrincipalValueLocalUnit v (a * b) =
      adelicPrincipalValueLocalUnit v a * adelicPrincipalValueLocalUnit v b := by
  classical
  apply Units.ext
  refine Prod.ext (one_mul 1).symm (funext fun w ↦ ?_)
  by_cases hw : w = v
  · subst w
    simp [adelicPrincipalValueLocalUnit]
  · simp [adelicPrincipalValueLocalUnit, Function.update_of_ne hw]

/-- Theta of the part removed by a single principal value is the translated unit average.
Changing the uniformizer by a unit leaves this average unchanged. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_average {S : Finset V} (v : S)
    (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
    let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
    let U := (HeightOneSpectrum.adicCompletionIntegers F v.val).units
    let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
    sLocalAdelicTheta F S (f - P f) x = (μ.real U : ℂ)⁻¹ *
      ∫ u in U, sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v (π * u))⁻¹ * x) ∂μ := by
  intro P U μ
  rw [map_sub, ContinuousMap.sub_apply, sLocalAdelicTheta_sAdelePrincipalValue_singleton v π hπ,
    sub_sub_cancel]
  simp only [U, μ, sAdelePrincipalValue_preserves_thetaKernel_translate]

/-- Translating the removed part by an integer unit has the same effect in the averaging
formula as making another choice of uniformizer. Its theta function is therefore invariant. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_unitInvariant {S : Finset V} (v : S)
    (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) (f : ℬₛ(S))
    (a : (HeightOneSpectrum.adicCompletionIntegers F v.val).units) (x : (SAdeleRing F S)ˣ) :
    let g := f - sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f
    sLocalAdelicTheta F S g ((adelicPrincipalValueLocalUnit v a.val)⁻¹ * x) =
      sLocalAdelicTheta F S g x := by
  have ha := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp a.property
  have hπa : (Valued.v : Valuation (v.val.adicCompletion F) _).IsUniformizer
      ((a.val * π : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) := by
    rw [Valuation.IsUniformizer.iff, Units.val_mul, map_mul, ha, one_mul]
    exact hπ.val
  dsimp only
  rw [sLocalThetaPrincipalValue_isClosedEmbedding_average v π hπ,
    sLocalThetaPrincipalValue_isClosedEmbedding_average v (a.val * π) hπa]
  congr 1
  apply congrArg (fun g : (v.val.adicCompletion F)ˣ → ℂ ↦ ∫ u in _, g u ∂_)
  funext u
  simp only [sLocalThetaPrincipalValue_isClosedEmbedding_localUnit_mul, mul_inv_rev, mul_assoc]

/-- Removing the value at zero times a fixed test of value one gives a local
principal value. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_local
    (v : V) (b φ : ℬ(v.adicCompletion F)) (hφ : φ (Multiplicative.ofAdd 0) = 1) :
    ∃ t, finitePlacePrincipalValue v t = b - b (Multiplicative.ofAdd 0) • φ := by
  apply (Set.ext_iff.mp (finitePlacePrincipalValue_range v) _).mpr
  change b (Multiplicative.ofAdd 0) - b (Multiplicative.ofAdd 0) * φ (Multiplicative.ofAdd 0) = 0
  rw [hφ, mul_one, sub_self]

/-- On a pure tensor, removing its value on the face times `φ` amounts to
performing the same subtraction on the single local factor. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_pure
    {S : Finset V} [DecidableEq (↥S)] (v : S) (φ : ℬ(v.val.adicCompletion F))
    (hφ : φ (Multiplicative.ofAdd 0) = 1)
    (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.2)
    let z (x : SAdeleRing F S) : SAdeleRing F S := (x.1, Function.update x.2 v 0)
    let f := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
    (∀ x : SAdeleRing F S, x.2 v = 0 → P f (Multiplicative.ofAdd x) = 0) ∧
      ∃ h, ∀ x : SAdeleRing F S, P h (Multiplicative.ofAdd x) =
        f (Multiplicative.ofAdd x) - f (Multiplicative.ofAdd (z x)) * φ (Multiplicative.ofAdd (x.2 v)) := by
  classical
  intro e P z f
  let pack (b : ∀ w : S, ℬ(w.val.adicCompletion F)) := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
  have pv (c : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      P (pack c) = pack (Function.update c v (finitePlacePrincipalValue v.val (c v))) := by
    refine (sAdelePrincipalValue_tmul (Finset.singleton_subset_iff.mpr v.2) a c).trans ?_
    apply congrArg pack
    funext w
    by_cases h : w = v
    · subst w; simp
    · simp [Function.update_of_ne h, show w.val ≠ v.val from fun he ↦ h (Subtype.ext he)]
  let other := fun (x : SAdeleRing F S) ↦
    a (Multiplicative.ofAdd x.1) * ∏ w ∈ Finset.univ.erase v, b w (Multiplicative.ofAdd (x.2 w))
  have val (c : ℬ(v.val.adicCompletion F)) (x : SAdeleRing F S) :
      pack (Function.update b v c) (Multiplicative.ofAdd x) =
        other x * c (Multiplicative.ofAdd (x.2 v)) := by
    rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v), ← mul_assoc, Function.update_self]
    congr 2
    exact Finset.prod_congr rfl fun w hw ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have vo (x : SAdeleRing F S) : other (z x) = other x := by
    apply congrArg (_ * ·)
    exact Finset.prod_congr rfl fun w hw ↦ by
      change b w (Multiplicative.ofAdd (Function.update x.2 v 0 w)) = _
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have vb (x : SAdeleRing F S) : pack b (Multiplicative.ofAdd x) =
      other x * b v (Multiplicative.ofAdd (x.2 v)) := by
    simpa only [Function.update_eq_self] using val (b v) x
  have hv (c : ℬ(v.val.adicCompletion F)) : finitePlacePrincipalValue v.val c
      (Multiplicative.ofAdd 0) = 0 :=
    (Set.ext_iff.mp (finitePlacePrincipalValue_range v.val) _).mp ⟨c, rfl⟩
  obtain ⟨t, ht⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_local (F := F)
    v.val (b v) φ hφ
  refine ⟨fun x hx ↦ ?_, pack (Function.update b v t), fun x ↦ ?_⟩
  · change P (pack b) _ = 0
    rw [pv, val, hx, hv, mul_zero]
  · change P (pack (Function.update b v t)) _ = pack b _ - pack b _ * _
    rw [pv, Function.update_self, ht, Function.update_idem, val, vb, vb, vo]
    change _ * (b v _ - b v _ * φ _) = _ - (_ * b v (Multiplicative.ofAdd (Function.update x.2 v 0 v))) * _
    rw [Function.update_self]
    ring

/-- On a single finite factor the principal-value range is the kernel of evaluation
at zero. Tensoring gives exactly the tests that vanish on the face `x_v = 0`. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_face
    {S : Finset V} (v : S) (f : ℬₛ(S)) :
    f ∈ (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.2)).range ↔
      ∀ x : SAdeleRing F S, x.2 v = 0 → f (Multiplicative.ofAdd x) = 0 := by
  classical
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.2)
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let φ := finiteStandardGaussian v.val 1
  have hφ : φ (Multiplicative.ofAdd 0) = 1 := by
    change finiteStandardGaussianValue v.val 1 0 = 1
    simp [finiteStandardGaussianValue]
  let z (x : SAdeleRing F S) : SAdeleRing F S := (x.1, Function.update x.2 v 0)
  let D : Submodule ℂ ℬₛ(S) :=
    { carrier := {t | (∀ x : SAdeleRing F S, x.2 v = 0 → P t (Multiplicative.ofAdd x) = 0) ∧
        ∃ h, ∀ x : SAdeleRing F S, P h (Multiplicative.ofAdd x) =
          t (Multiplicative.ofAdd x) - t (Multiplicative.ofAdd (z x)) * φ (Multiplicative.ofAdd (x.2 v))}
      zero_mem' := ⟨fun x _ ↦ by simp, 0, fun x ↦ by simp⟩
      add_mem' := by
        rintro a b ⟨ha, j, hj⟩ ⟨hb, k, hk⟩
        refine ⟨fun x hx ↦ ?_, j + k, fun x ↦ ?_⟩
        · rw [map_add]; exact (congrArg₂ (· + ·) (ha x hx) (hb x hx)).trans (add_zero 0)
        · rw [map_add]
          change P j _ + P k _ = (_ + _) - (_ + _) * _
          rw [hj, hk]
          ring
      smul_mem' := by
        rintro c a ⟨ha, j, hj⟩
        refine ⟨fun x hx ↦ ?_, c • j, fun x ↦ ?_⟩
        · rw [map_smul]; exact mul_eq_zero_of_right c (ha x hx)
        · rw [map_smul]
          change c * P j _ = c * _ - c * _ * _
          rw [hj]
          ring }
  have pure (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ∈ D :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_pure v φ hφ a b
  have all_mem (t : ℬₛ(S)) : t ∈ D := by
    have heq := sLocalThetaPrincipalValue_transition_ext e D.mkQ LinearMap.id 0
      (fun a b ↦ (Submodule.Quotient.mk_eq_zero D).mpr (pure a b))
    exact (Submodule.Quotient.mk_eq_zero D).mp (LinearMap.congr_fun heq t)
  constructor
  · rintro ⟨t, rfl⟩
    exact (all_mem t).1
  · intro hf
    obtain ⟨t, ht⟩ := (all_mem f).2
    refine ⟨t, SchwartzBruhat.ext fun y ↦ ?_⟩
    change P t (Multiplicative.ofAdd y.toAdd) = f (Multiplicative.ofAdd y.toAdd)
    rw [ht, hf (z y.toAdd) (Function.update_self ..), zero_mul, sub_zero]

/-- The inverse one-place uniformizer has norm greater than one, since its norm is
the residue cardinality. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_norm
    {S : Finset V} (v : S) (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) :
    1 < ((sIdeleNorm F S (adelicPrincipalValueLocalUnit v π)⁻¹).val : ℝ) := by
  classical
  have h : ((sIdeleNorm F S (adelicPrincipalValueLocalUnit v π)).val : ℝ) = ‖π.val‖ := by
    simp [sIdeleNorm, adelicPrincipalValueLocalUnit]
    change (∏ w : InfinitePlace F, ‖(1 : w.Completion)‖ ^ w.mult) *
      (∏ w : S, ‖Function.update (fun j : S ↦ (1 : j.val.adicCompletion F)) v π.val w‖) = _
    simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single v, Function.update_self]
    · intro w _ hw
      rw [Function.update_of_ne hw, norm_one]
    · simp
  rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, h,
    norm_uniformizer_adicCompletion v.val _ hπ, inv_inv]
  exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val

/-- An S-local theta function invariant under an idele of norm greater than one vanishes.
Its values on the forward orbit are constant and tend to zero by the large-norm estimate. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_periodic
    {S : Finset V} (a : (SAdeleRing F S)ˣ) (ha : 1 < ((sIdeleNorm F S a).val : ℝ))
    (f : ℬₛ(S)) (hf : ∀ x, sLocalAdelicTheta F S f (a * x) = sLocalAdelicTheta F S f x) :
    f ∈ Kₛ(S) := by
  apply LinearMap.mem_ker.mpr
  ext x
  obtain ⟨C, T, _, _, h⟩ := sLocalAdelicTheta_decay_large F S f 1 le_rfl
  let m (y : (SAdeleRing F S)ˣ) : ℝ := (sIdeleNorm F S y).val
  have hm (n : ℕ) : m (a ^ n * x) = m a ^ n * m x := by simp [m]
  have ht : Tendsto (fun n : ℕ ↦ m (a ^ n * x)) atTop atTop := by
    simp_rw [hm]
    exact (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const
      (NNReal.coe_pos.mpr (Units.zero_lt _))
  have he (n : ℕ) : sLocalAdelicTheta F S f (a ^ n * x) = sLocalAdelicTheta F S f x := by
    induction n with
    | zero => simp
    | succ n ih => rwa [pow_succ', mul_assoc, hf]
  have hle : ∀ᶠ n : ℕ in atTop, ‖sLocalAdelicTheta F S f x‖ ≤ C * (m (a ^ n * x))⁻¹ := by
    filter_upwards [ht.eventually_gt_atTop T] with n hn
    simpa only [he, pow_one, m] using h (a ^ n * x) hn
  have hzero := le_of_tendsto_of_tendsto tendsto_const_nhds
    ((tendsto_const_nhds (x := C)).mul (tendsto_inv_atTop_zero.comp ht)) hle
  exact norm_le_zero_iff.mp (by simpa only [mul_zero] using hzero)

/-- To descend an embedding on tests it suffices to lift small boundary values of
kernel elements to small kernel elements. Subtracting such a lift gives a small test
in the range of the embedding, where the inverse is continuous. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_descend
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (K : Submodule ℂ E) (P : E →ₗ[ℂ] E) (T : (E ⧸ K) →ₗ[ℂ] E ⧸ K)
    (hP : IsInducing P) (hT : Continuous T) (hi : Injective T)
    (hcomm : ∀ f, T (K.mkQ f) = K.mkQ (P f))
    (htrace : IsOpenMap (P.range.mkQ.comp K.subtype).rangeRestrict) :
    IsInducing T := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (by simpa only [map_zero] using (hT.tendsto 0).le_comap) (fun U hU ↦ ?_)
  have hpre : K.mkQ ⁻¹' U ∈ 𝓝 (0 : E) := by
    simpa only [map_zero] using K.isQuotientMap_mkQ.continuous.continuousAt.preimage_mem_nhds hU
  obtain ⟨A, hA, hsub⟩ := (hP.nhds_eq_comap 0 ▸ hpre : K.mkQ ⁻¹' U ∈ comap P (𝓝 (P 0)))
  rw [map_zero] at hA
  obtain ⟨B, hB, C, hC, hBC⟩ := mem_prod_iff.mp
    (show (fun z : E × E ↦ z.1 - z.2) ⁻¹' A ∈ 𝓝 0 ×ˢ 𝓝 0 by
      rw [← nhds_prod_eq]
      exact (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds (by simpa using hA))
  let b := P.range.mkQ
  let r := (b.comp K.subtype).rangeRestrict
  have hCr : r '' (Subtype.val ⁻¹' C) ∈ 𝓝 (0 : (b.comp K.subtype).range) := by
    simpa only [map_zero] using htrace.image_mem_nhds
      (continuous_subtype_val.continuousAt (x := (0 : K)).preimage_mem_nhds hC)
  rw [nhds_subtype_eq_comap] at hCr
  obtain ⟨D, hD, hDC⟩ := hCr
  have hW : B ∩ b ⁻¹' D ∈ 𝓝 (0 : E) :=
    inter_mem hB (P.range.isQuotientMap_mkQ.continuous.continuousAt.preimage_mem_nhds
      (by simpa [b] using hD))
  refine ⟨K.mkQ '' (B ∩ b ⁻¹' D), ?_, ?_⟩
  · simpa only [map_zero] using K.isOpenMap_mkQ.image_mem_nhds hW
  · rintro x ⟨g, ⟨hg, hDg⟩, he⟩
    obtain ⟨f, rfl⟩ := K.mkQ_surjective x
    rw [hcomm] at he
    have hk : g - P f ∈ K := (Submodule.Quotient.eq K).mp he
    have hb : b (g - P f) = b g := by
      rw [map_sub, show b (P f) = 0 from (Submodule.Quotient.mk_eq_zero P.range).mpr ⟨f, rfl⟩,
        sub_zero]
    have hmem : b (g - P f) ∈ D := hb.symm ▸ hDg
    obtain ⟨k, hkC, hkD⟩ := hDC (a := r ⟨g - P f, hk⟩) hmem
    have hz : b k.val = b g := (congrArg Subtype.val hkD).trans hb
    obtain ⟨z, hez⟩ := (Submodule.Quotient.eq P.range).mp hz.symm
    have hsmall : P z ∈ A := hez ▸ hBC (show (g, k.val) ∈ B ×ˢ C from ⟨hg, hkC⟩)
    have heq : K.mkQ z = K.mkQ f := hi (by
      rw [hcomm, hcomm, hez, map_sub, show K.mkQ k.val = 0 from
        (Submodule.Quotient.mk_eq_zero K).mpr k.property, sub_zero, he])
    exact heq ▸ hsub hsmall

/-- On a unit-invariant theta function, the term removed by the principal value is the
uniformizer translate. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_removed
    {S : Finset V} (v : S) (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) (f : ℬₛ(S))
    (hf : ∀ (u : (HeightOneSpectrum.adicCompletionIntegers F v.val).units) (x : (SAdeleRing F S)ˣ),
      sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v u.val)⁻¹ * x) =
        sLocalAdelicTheta F S f x) (x : (SAdeleRing F S)ˣ) :
    sLocalAdelicTheta F S (f - sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.2) f) x =
      sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v π)⁻¹ * x) := by
  rw [sLocalThetaPrincipalValue_isClosedEmbedding_average v π hπ]
  let U := (HeightOneSpectrum.adicCompletionIntegers F v.val).units
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
  let : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  have hm : (μ.real U : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v.val π 0 1).1.ne'
  have hU : MeasurableSet (U : Set (v.val.adicCompletion F)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  rw [setIntegral_congr_fun hU (g := fun _ ↦
    sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v π)⁻¹ * x)) (fun u hu ↦ by
      rw [sLocalThetaPrincipalValue_isClosedEmbedding_localUnit_mul, mul_inv_rev, mul_assoc]
      exact hf ⟨u, hu⟩ _), setIntegral_const, Complex.real_smul, inv_mul_cancel_left₀ hm]

/-- If the one-place principal value kills a theta class, its theta function equals the
removed unit-invariant term. It is then periodic under the uniformizer and hence zero. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_injective
    {S : Finset V} (v : S) (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) :
    Injective (sLocalThetaPrincipalValue F (Finset.singleton_subset_iff.mpr v.2)) := by
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.2)
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective t
  have hPf : P f ∈ Kₛ(S) := (Submodule.Quotient.mk_eq_zero _).mp ht
  have he : sLocalAdelicTheta F S (f - P f) = sLocalAdelicTheta F S f := by
    rw [map_sub, LinearMap.mem_ker.mp hPf, sub_zero]
  have hu := sLocalThetaPrincipalValue_isClosedEmbedding_unitInvariant v π hπ f
  change ∀ u x, sLocalAdelicTheta F S (f - P f) _ = sLocalAdelicTheta F S (f - P f) x at hu
  rw [he] at hu
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_periodic _
    (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_norm v π hπ) f
  intro x
  exact (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_removed v π hπ f hu x).symm.trans
    (DFunLike.congr_fun he x)

/-- Contract the new tensor factor against evaluation at zero. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_tensor
    {A B E : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [PolynormableSpace ℂ A] [T2Space A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (e : InductiveTensor A B ≃L[ℂ] E) (l : B →L[ℂ] ℂ) :
    ∃ r : E →L[ℂ] A, ∀ a b, r (e (a ⊗ₜ[ℂ] b)) = l b • a := by
  let L : InductiveTensor A B →ₗ[ℂ] A :=
    (TensorProduct.rid ℂ A).toLinearMap.comp (TensorProduct.map LinearMap.id l.toLinearMap)
  have hp (a : A) (b : B) : L (a ⊗ₜ[ℂ] b) = l b • a := TensorProduct.rid_tmul a (l b)
  have hc : Continuous L := (continuous_inductiveTensor_iff L).mpr
    ⟨fun a ↦ (l.continuous.smul continuous_const).congr fun b ↦ (hp a b).symm,
     fun b ↦ (continuous_const.smul continuous_id).congr fun a ↦ (hp a b).symm⟩
  refine ⟨(⟨L, hc⟩ : _ →L[ℂ] A).comp e.symm.toContinuousLinearMap, fun a b ↦ ?_⟩
  change L (e.symm (e _)) = _
  erw [e.symm_apply_apply, hp]

/-- Restriction to the face is continuous. Inserting the integer indicator in the
missing coordinate gives a continuous section. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_restrict
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (Z : Submodule ℂ ℬₛ(S))
    (hZ : ∀ f, f ∈ Z ↔ ∀ x : SAdeleRing F S, x.2 v = 0 → f (Multiplicative.ofAdd x) = 0) :
    ∃ r : ℬₛ(S) →L[ℂ] ℬₛ(T), r.ker = Z ∧
      (∀ f, r (sAdeleSchwartzTransition F i f) = f) ∧
      ∀ f (x : SAdeleRing F S), x.2 v = 0 →
        r f (Multiplicative.ofAdd (x.1, fun w : T ↦ x.2 ⟨w.val, i w.property⟩)) =
          f (Multiplicative.ofAdd x) := by
  classical
  obtain ⟨e, he⟩ := sAdeleDifferenceSchwartz_inductiveTensor_equiv F i
  let B := ℬ(FinitePlaceProduct F (S \ T))
  let ev : B →ₗ[ℂ] ℂ := (LinearMap.proj (Multiplicative.ofAdd 0)).comp
    (schwartzBruhatSubmodule _).subtype
  have ht := (finiteProduct_tailSchwartz_finestTopology F (S \ T) ∅).1
  let l : B →L[ℂ] ℂ := ⟨ev, Eq.mpr (congrArg (fun t ↦ @Continuous B ℂ t _ ev) ht)
    (continuous_of_finestLocallyConvex B ev)⟩
  let : PolynormableSpace ℂ ℬₛ(T) := (sAdeleSchwartz_nuclear.{_,0} F T).2.1
  let : T2Space ℬₛ(T) := (sAdeleSchwartz_nuclear.{_,0} F T).1
  let : PolynormableSpace ℂ B := (finiteProduct_tailSchwartz_nuclear.{_,0} F (S \ T) ∅).1.2.1
  let : T2Space B := (finiteProduct_tailSchwartz_nuclear.{_,0} F (S \ T) ∅).1.1
  obtain ⟨r, hr⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_tensor e l
  let old (x : SAdeleRing F S) : SAdeleRing F T := (x.1, fun w ↦ x.2 ⟨w.val, i w.property⟩)
  let z (y : SAdeleRing F T) : SAdeleRing F S :=
    (y.1, fun w ↦ if h : w.val ∈ T then y.2 ⟨w.val, h⟩ else 0)
  have hz (y : SAdeleRing F T) : (z y).2 v = 0 := dite_eq_right ((hv v).mpr rfl)
  have hold (y : SAdeleRing F T) : old (z y) = y :=
    Prod.ext rfl (funext fun w ↦ dite_eq_left w.property)
  have face (f : ℬₛ(S)) (x : SAdeleRing F S) (hx : x.2 v = 0) :
      r f (Multiplicative.ofAdd (old x)) = f (Multiplicative.ofAdd x) := by
    obtain ⟨t, rfl⟩ := e.surjective f
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [hr, he]
      have h0 : (fun w : ↥(S \ T) ↦ x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) = 0 := by
        funext w
        let w₀ : S := ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩
        change x.2 w₀ = 0
        rw [(hv w₀).mp (Finset.mem_sdiff.mp w.property).2, hx]
      rw [h0]
      exact mul_comm _ _
    | add t s ht hs =>
      erw [e.map_add, r.map_add]
      exact congrArg₂ (· + ·) ht hs
  refine ⟨r, ?_, fun f ↦ ?_, face⟩
  · ext f
    rw [hZ, LinearMap.mem_ker]
    exact ⟨fun h x hx ↦ (face f x hx).symm.trans (congrArg
      (fun g : ℬₛ(T) ↦ g (Multiplicative.ofAdd (old x))) h), fun h ↦
      SchwartzBruhat.ext fun y ↦ by
        have e := face f (z y.toAdd) (hz _)
        rw [hold] at e
        exact e.trans (h _ (hz _))⟩
  · apply SchwartzBruhat.ext
    intro y
    have hh := face (sAdeleSchwartzTransition F i f) (z y.toAdd) (hz _)
    rw [hold, sAdeleSchwartzTransition_apply, ite_eq_left] at hh
    · exact hh.trans (congrArg (fun t ↦ f (Multiplicative.ofAdd t)) (hold _))
    · intro w hw
      rw [(hv w).mp hw, hz]
      exact Subring.zero_mem _

/-- An open parameter map gives small parameters for all nearby compatible traces.
Evaluating a continuous lift at such a parameter gives openness on the kernel. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_lift
    {A B E X : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Submodule ℂ E) (m : E →ₗ[ℂ] X)
    (t : (m.comp K.subtype).range →L[ℂ] B) (D : A →L[ℂ] B) (hD : IsOpenMap D)
    (l : ((m.comp K.subtype).range × A) →L[ℂ] E)
    (hl : ∀ y a, t y = D a → l (y, a) ∈ K ∧ m (l (y, a)) = y.val) :
    IsOpenMap (m.comp K.subtype).rangeRestrict := by
  let f := (m.comp K.subtype).rangeRestrict
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  intro U hU
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : K) := hU
  rw [nhds_subtype] at hpre
  obtain ⟨W, hW, hsub⟩ := Filter.mem_comap.mp hpre
  have hsmall : l ⁻¹' W ∈ 𝓝 ((0, 0) : (m.comp K.subtype).range × A) :=
    l.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (l 0); rwa [l.map_zero])
  obtain ⟨N, hN, C, hC, hNC⟩ := mem_nhds_prod_iff.mp hsmall
  have hDC : D '' C ∈ 𝓝 (0 : B) := by
    rw [← D.map_zero]
    exact hD.image_mem_nhds hC
  have ht : t ⁻¹' (D '' C) ∈ 𝓝 0 :=
    t.continuous.continuousAt.preimage_mem_nhds (by simpa using hDC)
  refine mem_of_superset (inter_mem hN ht) ?_
  rintro y ⟨hy, a, ha, hay⟩
  obtain ⟨hk, he⟩ := hl y a hay.symm
  have hkW := hNC (show (y, a) ∈ N ×ˢ C from ⟨hy, ha⟩)
  have hyU := hsub (a := (⟨l (y, a), hk⟩ : K)) hkW
  exact (show f ⟨l (y, a), hk⟩ = y from Subtype.ext he) ▸ hyU

/-- A principal power of the prime at the selected place gives an S-unit with
nonzero valuation there. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_nonzero
    {S : Finset V} (v : S) :
    ∃ x : (S : Set V).unit F, v.val.valuation F (x.val : F) ≠ 1 := by
  classical
  let n := classNumber F
  have hv := mem_nonZeroDivisors_iff_ne_zero.mpr v.val.ne_bot
  have hpow : (ClassGroup.mk0 ⟨v.val.asIdeal, hv⟩) ^ n = 1 := pow_card_eq_one
  have hp : (v.val.asIdeal ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hv n), ← hpow, ← map_pow]
    rfl
  obtain ⟨a, ha⟩ := hp
  change v.val.asIdeal ^ n = Ideal.span {a} at ha
  have ha₀ : a ≠ 0 := fun h ↦ (pow_ne_zero n v.val.ne_bot) (by simpa [h] using ha)
  let x := Units.mk0 (algebraMap (𝓞 F) F a) (fun h ↦ ha₀ (IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm)))
  have hdiv (w : V) (hw : a ∈ w.asIdeal) : w = v.val := by
    have hle := w.isPrime.le_of_pow_le (n := n) (ha.trans_le ((Ideal.span_singleton_le_iff_mem _).mpr hw))
    exact HeightOneSpectrum.ext (v.val.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
  refine ⟨⟨x, fun w hw ↦ ?_⟩, ?_⟩
  · change w.valuation F (algebraMap (𝓞 F) F a) = 1
    rw [w.valuation_of_algebraMap, w.intValuation_eq_one_iff]
    exact fun h ↦ hw (hdiv w h ▸ v.property)
  · change v.val.valuation F (algebraMap (𝓞 F) F a) ≠ 1
    rw [v.val.valuation_of_algebraMap, ne_eq, v.val.intValuation_eq_one_iff, not_not]
    apply (Ideal.span_singleton_le_iff_mem _).mp
    rw [← ha]
    exact Ideal.pow_le_self (classNumber_ne_zero F)

/-- The positive generator of the valuation image divides the order of every S-unit. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_generator
    {S : Finset V} (v : S) (w : Fˣ →* Multiplicative ℤ)
    (hw : ∀ t, WithZero.exp (w t).toAdd = v.val.valuation F (t : F)) :
    ∃ u : (S : Set V).unit F,
      let ord (t : (S : Set V).unit F) := -(w t.val).toAdd
      0 < ord u ∧ ∀ t, ord u ∣ ord t := by
  let f : Additive ((S : Set V).unit F) →+ ℤ := (w.comp
    ((S : Set V).unit F).subtype).toAdditive
  obtain ⟨z, hz⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq f.range).mp
    (AddSubgroup.isAddCyclic f.range)
  have hz' := (Int.zmultiples_natAbs z).trans hz
  obtain ⟨x, hx⟩ := show -(z.natAbs : ℤ) ∈ f.range by
    rw [← hz']
    exact AddSubgroup.neg_mem _ (AddSubgroup.mem_zmultiples _)
  have hn : z ≠ 0 := by
    obtain ⟨y, hy⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_nonzero v
    intro h
    have hm : f (.ofMul y) ∈ f.range := ⟨_, rfl⟩
    rw [← hz, h, Int.mem_zmultiples_iff, zero_dvd_iff] at hm
    exact hy ((hw y.val).symm.trans (by change WithZero.exp (f (.ofMul y)) = 1; rw [hm, WithZero.exp_zero]))
  refine ⟨x.toMul, ?_⟩
  change 0 < -f x ∧ ∀ t : (S : Set V).unit F, -f x ∣ -f (.ofMul t)
  rw [hx, neg_neg]
  refine ⟨by positivity, fun t ↦ ?_⟩
  rw [dvd_neg, ← Int.mem_zmultiples_iff, hz']
  exact ⟨_, rfl⟩

/-- Factor a product over the enlarged stage into its old coordinates and the
factor at the added place. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_prod
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    {M : Type*} [CommMonoid M] (b : S → M) :
    (∏ w : S, b w) = (∏ w : T, b ⟨w.val, i w.property⟩) * b v := by
  classical
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
  congr 1
  exact Finset.prod_bij' (fun w hw ↦ (⟨w.val, by
    by_contra h
    exact Finset.ne_of_mem_erase hw ((hv w).mp h)⟩ : T))
    (fun w _ ↦ (⟨w.val, i w.property⟩ : S)) (fun _ _ ↦ Finset.mem_univ _)
    (fun w _ ↦ Finset.mem_erase.mpr ⟨fun h ↦ ((hv _).mpr h) w.property, Finset.mem_univ _⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Removing the selected place from the product formula leaves a norm different
from one whenever the S-unit has positive order there. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_norm
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (u : ((S : Set V).integer F)ˣ) (hu : 0 < -WithZero.log (Valued.v ((sUnitEmbedding F S u).val.2 v))) :
    let g := Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
      (Units.map (integralAdeleDiagonal F S).toMonoidHom u)
    sIdeleNorm F T g ≠ 1 := by
  classical
  intro g
  let a := sUnitEmbedding F S u
  have he : sIdeleNorm F S a = 1 := (sIdeleNorm_spec F S).2 ⟨u, rfl⟩
  have hp : (∏ w : S, ‖a.val.2 w‖) = (∏ w : T, ‖g.val.2 w‖) * ‖a.val.2 v‖ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_prod v i hv (fun w ↦ ‖a.val.2 w‖)
  intro hg
  have valS := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) he
  have valT := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
  simp [sIdeleNorm] at valS valT
  change (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) * (∏ w : T, ‖g.val.2 w‖) = 1 at valT
  change (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) * (∏ w : S, ‖a.val.2 w‖) = 1 at valS
  rw [hp, ← mul_assoc, valT, one_mul] at valS
  have h := Valued.toNormedField.norm_eq_one_iff.mp valS
  change 0 < -WithZero.log (Valued.v (a.val.2 v)) at hu
  simp [h] at hu

/-- Radial local tests are spanned by valuation balls. After removing the value at
zero times the unit ball, only finitely many shells remain. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_radial
    (v : V) (f : ℬ(v.adicCompletion F))
    (hf : ∀ u ∈ (v.adicCompletionIntegers F).units, schwartzBruhatUnitTranslate u f = f)
    (D : Submodule ℂ (v.adicCompletion F → ℂ))
    (hD : ∀ n : ℤ, (fun x : v.adicCompletion F ↦
      if Valued.v x ≤ WithZero.exp n then (1 : ℂ) else 0) ∈ D) :
    (fun x ↦ f (Multiplicative.ofAdd x)) ∈ D := by
  classical
  let ball (n : ℤ) (x : v.adicCompletion F) : ℂ := if Valued.v x ≤ WithZero.exp n then 1 else 0
  obtain ⟨b, hb⟩ := finitePlaceDifference_range_on_unitInvariants_ball (F := F) v 0 1
  let c := f (Multiplicative.ofAdd 0)
  let h := f - c • b
  have he (x : v.adicCompletion F) :
      h (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd x) - c * ball 0 x := by
    change _ - _ * b _ = _
    rw [hb]
  have h0 : h (Multiplicative.ofAdd 0) = 0 := by rw [he 0]; simp [ball, c]
  obtain ⟨I, hI⟩ := finitePlaceDifference_range_on_unitInvariants_finite (F := F) v h h0
  choose t ht using fun m : ℤ ↦ v.valuedAdicCompletion_surjective F (WithZero.exp m)
  let shell (m : ℤ) := ball m - ball (m - 1)
  have shell_val (m : ℤ) (x : v.adicCompletion F) (hx : x ≠ 0) :
      shell m x = if m = (Valued.v x).log then 1 else 0 := by
    have hh := WithZero.exp_log ((Valuation.ne_zero_iff Valued.v).mpr hx)
    simp only [shell, Pi.sub_apply, ball]
    conv_lhs => rw [← hh]
    simp only [WithZero.exp_le_exp]
    split_ifs <;> first | omega | simp_all
  have rep : (fun x ↦ f (Multiplicative.ofAdd x)) =
      c • ball 0 + ∑ m ∈ I, h (Multiplicative.ofAdd (t m)) • shell m := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    apply (eq_add_of_sub_eq' (he x).symm).trans
    congr 1
    by_cases hx : x = 0
    · subst x
      rw [h0]
      simp [shell, ball]
    simp only [shell_val _ x hx, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    split_ifs with hm
    · let m := (Valued.v x).log
      have hv : Valued.v (t m) = Valued.v x :=
        (ht m).trans (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx))
      have hn : t m ≠ 0 := fun e ↦ hx ((Valuation.zero_iff _).mp (by rw [← hv, e, map_zero]))
      have hfx := finitePlaceDifference_range_on_unitInvariants_radial (F := F) v f hf x (t m) hx hn hv.symm
      change h (Multiplicative.ofAdd x) = h (Multiplicative.ofAdd (t m))
      rw [he x, he (t m), hfx]
      simp only [ball, hv]
    · exact not_ne_iff.mp fun hne ↦ hm (hI x hne)
  rw [rep]
  exact D.add_mem (D.smul_mem _ (hD 0))
    (D.sum_mem fun m _ ↦ D.smul_mem _ (D.sub_mem (hD m) (hD (m - 1))))

/-- The unit-invariant part of a test has a finite expansion in valuation balls
with test functions on the old stage as coefficients. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_expand
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (k : ℬₛ(S)) :
    let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
    ∃ (I : Finset ℤ) (a : ℤ → ℬₛ(T)), ∀ x : SAdeleRing F S,
      (k - P k) (Multiplicative.ofAdd x) = ∑ n ∈ I,
        if Valued.v (x.2 v) ≤ WithZero.exp (-n) then
          a n (Multiplicative.ofAdd (x.1, fun w : T ↦ x.2 ⟨w.val, i w.property⟩)) else 0 := by
  classical
  intro P
  let old (x : SAdeleRing F S) : SAdeleRing F T := (x.1, fun w ↦ x.2 ⟨w.val, i w.property⟩)
  let ev (y : SAdeleRing F T) : ℬₛ(T) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd y)).comp (schwartzBruhatSubmodule _).subtype
  let B (n : ℤ) : ℬₛ(T) →ₗ[ℂ] (SAdeleRing F S → ℂ) :=
    LinearMap.pi fun x ↦ if Valued.v (x.2 v) ≤ WithZero.exp (-n) then ev (old x) else 0
  let L := Finsupp.lsum ℂ B
  let valS : ℬₛ(S) →ₗ[ℂ] (SAdeleRing F S → ℂ) := LinearMap.pi fun x ↦
    (LinearMap.proj (Multiplicative.ofAdd x)).comp (schwartzBruhatSubmodule _).subtype
  let D := L.range.comap (valS.comp (LinearMap.id - P))
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have pure (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ∈ D := by
    let f := (sAdeleSchwartz_inductiveTensor_equiv F T).choose
      (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w : T, b ⟨w.val, i w.property⟩))
    let ins (h : ℬ(v.val.adicCompletion F)) := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, Function.update b v h w))
    let pack := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
    have hin : ins (b v) = pack := congrArg (fun b ↦ e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)))
      (Function.update_eq_self v b)
    have hP : P pack = ins (finitePlacePrincipalValue v.val (b v)) := by
      refine (sAdelePrincipalValue_tmul (Finset.singleton_subset_iff.mpr v.property) a b).trans ?_
      apply congrArg (fun b : ∀ w : S, ℬ(w.val.adicCompletion F) ↦ e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)))
      funext w
      by_cases h : w = v
      · subst w; simp
      · simp [Function.update_of_ne h, show w.val ≠ v.val from fun he ↦ h (Subtype.ext he)]
    have hins (h : ℬ(v.val.adicCompletion F)) (x : SAdeleRing F S) :
        ins h (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd (old x)) * h (Multiplicative.ofAdd (x.2 v)) := by
      rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec,
        (sAdeleSchwartz_inductiveTensor_equiv F T).choose_spec,
        sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_prod v i hv,
        Function.update_self, ← mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [Function.update_of_ne (show (⟨w.val, i w.property⟩ : S) ≠ v from
        fun he ↦ ((hv _).mpr he) w.property)]
    let M : (v.val.adicCompletion F → ℂ) →ₗ[ℂ] (SAdeleRing F S → ℂ) :=
      LinearMap.pi fun x ↦ f (Multiplicative.ofAdd (old x)) • LinearMap.proj (x.2 v)
    have hm := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_radial v.val
      (b v - finitePlacePrincipalValue v.val (b v))
      (finitePlacePrincipalValue_range_invariant v.val (b v)) (L.range.comap M) (fun n ↦ by
        refine ⟨Finsupp.single (-n) f, ?_⟩
        rw [show L (Finsupp.single (-n) f) = B (-n) f from Finsupp.lsum_single ..]
        funext x
        by_cases hx : Valued.v (x.2 v) ≤ WithZero.exp n <;> simp [B, M, hx, ev]
        rfl)
    change valS (pack - P pack) ∈ L.range
    suffices hval : valS (pack - P pack) = M (fun x ↦
        (b v - finitePlacePrincipalValue v.val (b v)) (Multiplicative.ofAdd x)) by rw [hval]; exact hm
    funext x
    change pack _ - P pack _ = f _ * ((b v) _ - finitePlacePrincipalValue v.val (b v) _)
    rw [hP, ← hin, hins, hins, mul_sub]
  have heq := sLocalThetaPrincipalValue_transition_ext e D.mkQ LinearMap.id 0
    (fun a b ↦ (Submodule.Quotient.mk_eq_zero D).mpr (pure a b))
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero D).mp (LinearMap.congr_fun heq k)
  refine ⟨a.support, a, fun x ↦ (congrFun ha x).symm.trans ?_⟩
  change (∑ n ∈ a.support, B n (a n)) x = _
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hx : Valued.v (x.2 v) ≤ WithZero.exp (-n) <;> simp [B, hx, ev, old]
  rfl

/-- Summing on a valuation fiber is summing on its translate of the old unit
group. The terms extended by zero have the same sum. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_fiber
    {G A : Type*} [CommGroup G] [Group A] [DecidableEq A] (H J : Subgroup G) (w : G →* A)
    (hH : ∀ t, t ∈ H ↔ t ∈ J ∧ w t = 1)
    (b : J) (f : G → ℂ) (z : ℂ) (hz : HasSum (fun t : H ↦ f (b.val * t.val)) z) :
    HasSum (fun t : J ↦ if w t.val = w b.val then f t.val else 0) z := by
  classical
  let inc (t : H) : J := ⟨b.val * t.val, J.mul_mem b.property ((hH _).mp t.property).1⟩
  have hi : Injective inc := fun x y h ↦ Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
  have hw (t : H) : w (inc t).val = w b.val := by
    change w (b.val * t.val) = _
    rw [map_mul, ((hH _).mp t.property).2, mul_one]
  refine (hi.hasSum_iff (fun t ht ↦ ite_eq_right (fun he ↦ ht ?_))).mp ?_
  · have hm : b.val⁻¹ * t.val ∈ H := (hH _).mpr ⟨J.mul_mem (J.inv_mem b.property) t.property,
      by rw [map_mul, map_inv, he, inv_mul_cancel]⟩
    exact ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel_left ..)⟩
  · exact hz.congr_fun fun t ↦ ite_eq_left (hw t)

/-- The two shells of orders `d - 1` and `-1` select a single valuation fiber
for each ball, including balls with a negative index. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_select
    (d j n : ℤ) (hd : 0 < d) (c : ℂ) :
    (if n ≤ j * d + d - 1 then c else 0) - (if n ≤ j * d - 1 then c else 0) =
      if j = n / d then c else 0 := by
  have h := Int.ediv_eq_iff_of_pos (x := n) (y := j) hd
  split_ifs <;> first | omega | simp_all

/-- The theta series indexed by the subgroup of field units has the same sum
as the series indexed by the units of the ring of S-integers. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_series
    (S : Finset V) (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
    let diag := Units.map ((adeleProjection F S).comp (algebraMap F 𝔸[F])).toMonoidHom
    HasSum (fun t : (S : Set V).unit F ↦ f (Multiplicative.ofAdd ((diag t.val * x).val)))
      (sLocalAdelicTheta F S f x) := by
  intro diag
  let e := Set.unitEquivUnitsInteger (S : Set V) F
  exact e.toEquiv.hasSum_iff.mpr
    ((sLocalAdelicTheta_hasSumUniformlyOn F S f {x} isCompact_singleton).hasSum rfl)

/-- Lift an old idele with any prescribed valuation at the added place. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_idele
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : v.val ∉ T) (p : ℤ) (y : (SAdeleRing F T)ˣ) :
    ∃ x : (SAdeleRing F S)ˣ,
      (x.val.1, fun w : T ↦ x.val.2 ⟨w.val, i w.property⟩) = y.val ∧
      Valued.v (x.val.2 v) = WithZero.exp p := by
  classical
  choose b hb using fun w : S ↦ w.val.valuedAdicCompletion_surjective F (WithZero.exp p)
  let c (w : S) : (w.val.adicCompletion F)ˣ := if h : w.val ∈ T then
    Units.map ((Pi.evalRingHom _ (⟨w.val, h⟩ : T)).comp (RingHom.snd _ _)).toMonoidHom y
    else Units.mk0 (b w) (fun hz ↦ WithZero.exp_ne_zero ((hb w).symm.trans (hz ▸ map_zero _)))
  let x : (SAdeleRing F S)ˣ :=
    ⟨(y.val.1, fun w ↦ (c w).val), (y.inv.1, fun w ↦ (c w).inv),
      Prod.ext (congrArg (fun t : SAdeleRing F T ↦ t.1) y.val_inv) (funext fun w ↦ (c w).val_inv),
      Prod.ext (congrArg (fun t : SAdeleRing F T ↦ t.1) y.inv_val) (funext fun w ↦ (c w).inv_val)⟩
  refine ⟨x, Prod.ext rfl (funext fun w ↦ ?_), ?_⟩
  · change (c ⟨w.val, i w.property⟩).val = _
    simp only [c, dite_eq_left w.property]
    rfl
  · change Valued.v (c v).val = _
    simp only [c, dite_eq_right hv, Units.val_mk0, hb]

/-- Evaluating the difference of two theta series a full valuation period apart
extracts one translate of each ball coefficient. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_sum
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (w : Fˣ →* Multiplicative ℤ) (hw : ∀ t, WithZero.exp (w t).toAdd = v.val.valuation F (t : F))
    (u : (S : Set V).unit F) (d : ℤ) (hd : 0 < d)
    (hu : (w u.val).toAdd = -d)
    (hdiv : ∀ t : (S : Set V).unit F, d ∣ -(w t.val).toAdd)
    (f : ℬₛ(S)) (hf : f ∈ Kₛ(S)) (I : Finset ℤ) (a : ℤ → ℬₛ(T))
    (ha : ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) = ∑ n ∈ I,
      if Valued.v (x.2 v) ≤ WithZero.exp (-n) then
        a n (Multiplicative.ofAdd (x.1, fun w : T ↦ x.2 ⟨w.val, i w.property⟩)) else 0) :
    let diag := Units.map ((adeleProjection F T).comp (algebraMap F 𝔸[F])).toMonoidHom
    (∑ n ∈ I, unitTranslateEnd (diag u.val ^ (-(n / d))) (a n)) ∈ Kₛ(T) := by
  classical
  intro diag
  have hH (t : Fˣ) : t ∈ (T : Set V).unit F ↔ t ∈ (S : Set V).unit F ∧ w t = 1 := by
    have h1 : w t = 1 ↔ v.val.valuation F t.val = 1 := by
      rw [← hw t]
      change w t = 1 ↔ (↑(w t) : WithZero (Multiplicative ℤ)) = 1
      exact WithZero.coe_inj.symm
    rw [h1]
    refine ⟨fun h ↦ ⟨fun z hz ↦ h z (fun ht ↦ hz (i ht)), h _ ((hv v).mpr rfl)⟩, ?_⟩
    rintro ⟨h, he⟩ z hz
    by_cases hs : z ∈ S
    · have eq := congrArg Subtype.val ((hv ⟨z, hs⟩).mp hz)
      rwa [show z = v.val from eq]
    · exact h z hs
  let old : SAdeleRing F S →* SAdeleRing F T :=
    ⟨⟨fun x ↦ (x.1, fun z ↦ x.2 ⟨z.val, i z.property⟩), rfl⟩, fun _ _ ↦ rfl⟩
  let newDiag := Units.map ((adeleProjection F S).comp (algebraMap F 𝔸[F])).toMonoidHom
  let tr (n : ℤ) := unitTranslateEnd (diag u.val ^ (-(n / d))) (a n)
  apply LinearMap.mem_ker.mpr
  ext y
  let val (n : ℤ) (t : Fˣ) := a n (Multiplicative.ofAdd ((diag t * y).val))
  let term (n : ℤ) (t : (S : Set V).unit F) :=
    if w t.val = w (u.val ^ (n / d)) then val n t.val else 0
  have row (n : ℤ) : HasSum (term n) (sLocalAdelicTheta F T (tr n) y) := by
    apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_fiber
      _ _ w hH (u ^ (n / d)) (val n)
    refine (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_series T (tr n) y).congr_fun
      fun t ↦ ?_
    symm
    change a n (Multiplicative.ofAdd (((diag u.val ^ (-(n / d)))⁻¹ * (diag t.val * y)).val)) =
      a n (Multiplicative.ofAdd ((diag (u.val ^ (n / d) * t.val) * y).val))
    rw [map_mul, map_zpow, zpow_neg, inv_inv, mul_assoc]
  have read (p : ℤ) : HasSum (fun t : (S : Set V).unit F ↦ ∑ n ∈ I,
      if (w t.val).toAdd + p ≤ -n then val n t.val else 0) 0 := by
    obtain ⟨x, hx, hp⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_idele
      v i ((hv v).mpr rfl) p y
    have hs := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_series S f x
    rw [LinearMap.mem_ker.mp hf] at hs
    refine hs.congr_fun fun t ↦ ((ha _).trans (Finset.sum_congr rfl fun n _ ↦ ?_)).symm
    have he : old ((newDiag t.val * x).val) = (diag t.val * y).val := by
      rw [Units.val_mul, map_mul, show old x.val = y.val from hx]
      rfl
    have hlocal : Valued.v ((newDiag t.val).val.2 v) = WithZero.exp (w t.val).toAdd := by
      change Valued.v ((t.val : F) : v.val.adicCompletion F) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (hw t.val).symm
    change (if Valued.v ((newDiag t.val).val.2 v * x.val.2 v) ≤ WithZero.exp (-n)
      then a n (Multiplicative.ofAdd (old ((newDiag t.val * x).val))) else 0) = _
    simp only [map_mul, hlocal, hp, ← WithZero.exp_add, WithZero.exp_le_exp, he, val]
  have hdif := (read (1 - d)).sub (read 1)
  rw [sub_zero] at hdif
  have hzero : HasSum (fun t ↦ ∑ n ∈ I, term n t) 0 := by
    refine hdif.congr_fun fun t ↦ ?_
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    obtain ⟨j, hj⟩ := hdiv t
    have hj' : (w t.val).toAdd = -(j * d) := by
      change -((w t.val).toAdd) = d * j at hj
      rw [mul_comm d j] at hj
      omega
    have heq : w t.val = w (u.val ^ (n / d)) ↔ j = n / d := by
      rw [map_zpow]
      change (w t.val).toAdd = (n / d) • (w u.val).toAdd ↔ _
      rw [hj', show (w u.val).toAdd = -d from hu, zsmul_eq_mul, mul_neg, neg_inj]
      exact mul_left_inj' hd.ne'
    symm
    unfold term
    simp only [heq, hj', show -(j * d) + (1 - d) ≤ -n ↔ n ≤ j * d + d - 1 by omega,
      show -(j * d) + 1 ≤ -n ↔ n ≤ j * d - 1 by omega]
    exact sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_select d j n hd _
  change sLocalAdelicTheta F T (∑ n ∈ I, tr n) y = 0
  rw [map_sum, ContinuousMap.sum_apply]
  exact (hasSum_sum (s := I) fun n _ ↦ row n).unique hzero

/-- Group the radial ball coefficients of a theta-null test by their indices modulo
the positive valuation generator `d` of the S-units. Subtracting consecutive theta
values on the local shells and summing over residues gives an old-stage theta-null
sum after translating the coefficient at `n` by the power `-(n / d)` of the generator.
The sum of the untranslated coefficients is the trace at zero. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (r : ℬₛ(S) →L[ℂ] ℬₛ(T))
    (hr : ∀ f (x : SAdeleRing F S), x.2 v = 0 →
      r f (Multiplicative.ofAdd (x.1, fun w : T ↦ x.2 ⟨w.val, i w.property⟩)) =
        f (Multiplicative.ofAdd x)) :
    ∃ u : ((S : Set V).integer F)ˣ,
      let g := Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
        (Units.map (integralAdeleDiagonal F S).toMonoidHom u)
      let d := -WithZero.log (Valued.v ((sUnitEmbedding F S u).val.2 v))
      sIdeleNorm F T g ≠ 1 ∧ ∀ k ∈ Kₛ(S), ∃ (I : Finset ℤ) (a : ℤ → ℬₛ(T)),
        r k = ∑ n ∈ I, a n ∧
          (∑ n ∈ I, unitTranslateEnd (g ^ (-(n / d))) (a n)) ∈ Kₛ(T) := by
  classical
  let w : Fˣ →* Multiplicative ℤ := WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v.val.valuation F).toMonoidHom)
  have hw (t : Fˣ) : WithZero.exp (w t).toAdd = v.val.valuation F (t : F) :=
    WithZero.coe_unitsWithZeroEquiv_eq_units_val (Units.map (v.val.valuation F).toMonoidHom t)
  obtain ⟨u, hd, hdiv⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_generator v w hw
  let e := Set.unitEquivUnitsInteger (S : Set V) F
  let d := -(w u.val).toAdd
  have he : -WithZero.log (Valued.v ((sUnitEmbedding F S (e u)).val.2 v)) = d := by
    change -WithZero.log (Valued.v ((u.val : F) : v.val.adicCompletion F)) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hw u.val, WithZero.log_exp]
  refine ⟨e u, sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_norm
    v i hv (e u) (he ▸ hd), fun k hk ↦ ?_⟩
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
  obtain ⟨I, a, ha⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_expand v i hv k
  refine ⟨I, a, ?_, ?_⟩
  · apply SchwartzBruhat.ext
    intro y
    let x : SAdeleRing F S := (y.toAdd.1, fun w ↦ if h : w.val ∈ T then y.toAdd.2 ⟨w.val, h⟩ else 0)
    have hx : x.2 v = 0 := dite_eq_right ((hv v).mpr rfl)
    have hy : (x.1, fun w : T ↦ x.2 ⟨w.val, i w.property⟩) = y.toAdd :=
      Prod.ext rfl (funext fun w ↦ dite_eq_left w.property)
    have hz := (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_face v (P k)).mp ⟨k, rfl⟩ x hx
    have hh := ha x
    change k _ - P k _ = _ at hh
    rw [hz, sub_zero, hx, hy, map_zero] at hh
    simp only [zero_le, ite_true] at hh
    let ev : ℬₛ(T) →ₗ[ℂ] ℂ := (LinearMap.proj y).comp (schwartzBruhatSubmodule _).subtype
    exact ((congrArg (fun t ↦ r k (Multiplicative.ofAdd t)) hy.symm).trans (hr k x hx)).trans
      (hh.trans (map_sum ev a I).symm)
  · have hPk : P k ∈ Kₛ(S) :=
      sAdelePrincipalValue_preserves_thetaKernel (F := F) (Finset.singleton_subset_iff.mpr v.property) hk
    have hf : k - P k ∈ Kₛ(S) := (Kₛ(S)).sub_mem hk hPk
    let diag := Units.map ((adeleProjection F T).comp (algebraMap F 𝔸[F])).toMonoidHom
    have hg : Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
        (Units.map (integralAdeleDiagonal F S).toMonoidHom (e u)) = diag u.val := Units.ext rfl
    rw [he, hg]
    exact sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells_sum v i hv w hw u d hd
      (neg_neg _).symm hdiv (k - P k) hf I a ha

/-- Modulo differences for one generator, each translated shell coefficient has
the same class as the original coefficient, for positive and negative powers alike. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_telescope
    {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E] (A : G →* Module.End ℂ E)
    (g : G) (K : Submodule ℂ E) (I : Finset ℤ) (a : ℤ → E) (j : ℤ → ℤ)
    (hk : (∑ n ∈ I, A (g ^ j n) (a n)) ∈ K) :
    ∃ c : E, (∑ n ∈ I, a n) - (c - A g c) ∈ K := by
  let D := LinearMap.id - A g
  let q := D.range.mkQ
  have step (x : E) : q x = q (A g x) :=
    (Submodule.Quotient.eq D.range).mpr ⟨x, rfl⟩
  have pow (n : ℤ) : ∀ x : E, q (A (g ^ n) x) = q x := by
    apply zpow_induction_left (P := fun b ↦ ∀ x : E, q (A b x) = q x)
    · intro x
      rw [map_one]
      rfl
    · intro b h x
      exact (congrArg (fun L : Module.End ℂ E ↦ q (L x)) (map_mul A g b)).trans
        ((step (A b x)).symm.trans (h x))
    · intro b h x
      calc q (A (g⁻¹ * b) x) = q (A g (A (g⁻¹ * b) x)) := step _
           _ = q (A (g * (g⁻¹ * b)) x) := congrArg (fun L : Module.End ℂ E ↦ q (L x)) (A.map_mul _ _).symm
           _ = q x := by rw [mul_inv_cancel_left, h]
  have he : q (∑ n ∈ I, a n) = q (∑ n ∈ I, A (g ^ j n) (a n)) := by
    simp only [map_sum, pow]
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq D.range).mp he
  refine ⟨c, ?_⟩
  change c - A g c = _ at hc
  rwa [hc, sub_sub_cancel]

/-- The normalized Haar average projects onto the fixed vectors. It commutes with
every continuous linear operator commuting with the subgroup action. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_average
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
    (hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    ∃ A : E →L[ℂ] E,
      (∀ x h, h ∈ H → ρ h (A x) = A x) ∧
      (∀ x, (∀ h ∈ H, ρ h x = x) → A x = x) ∧
      ∀ B : E →L[ℂ] E, (∀ h ∈ H, ∀ x, B (ρ h x) = ρ h (B x)) →
        ∀ x, B (A x) = A (B x) := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  let : MeasurableSpace H := borel _
  let : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  obtain ⟨A, hA⟩ := (existsUnique_globalThetaIsotypicAverage_of_compact H hc μ ρ hρ 1).exists
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : SeparatingDual ℂ E := by
    refine ⟨fun x hx ↦ ?_⟩
    obtain ⟨φ, hφ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) hx
    exact ⟨φ, fun he ↦ by simp [he] at hφ⟩
  have dual (x : E) (φ : StrongDual ℂ E) : φ (A x) = ∫ h : H, φ (ρ h.val x) ∂μ := by
    have eq := congrArg (fun z : PettisWeakCompletion E ↦
      (show Module.Dual ℂ (StrongDual ℂ E) from z) φ) (hA x).2
    change φ (A x) = ∫ h : H, φ (star (((1 : PontryaginDual H) h) : ℂ) • ρ h.val x) ∂μ.restrict univ at eq
    simpa only [Measure.restrict_univ, PontryaginDual.one_apply, Circle.coe_one, star_one, one_smul] using eq
  refine ⟨A, ?_, ?_, ?_⟩
  · have hr := compactActionAverage_range μ (ρ.comp H.subtype)
      (hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) 1 A hA
    intro x h hh
    have hx := hr ▸ (show A x ∈ A.toLinearMap.range from ⟨x, rfl⟩)
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, PontryaginDual.one_apply,
      Circle.coe_one, one_smul] using (mem_actionIsotype _ _ _).mp hx ⟨h, hh⟩
  · intro x hx
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    simp [dual, hx]
  · intro B hB x
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro φ
    exact (dual x (φ.comp B)).trans ((integral_congr_ae (ae_of_all μ fun h ↦
      congrArg φ (hB h.val h.property x))).trans (dual (B x) φ).symm)

/-- A closed subspace contained in a Fréchet subspace is Fréchet in the induced
topology. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_subspace
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (L M : Submodule ℂ E) (h : L ≤ M) (hc : IsClosed (L : Set E)) (hM : IsFrechetTVS M) :
    IsFrechetTVS L := by
  obtain ⟨a, p, m, c⟩ := hM
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace M := c
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  let : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let i := Submodule.inclusion h
  have hi : IsEmbedding i := IsEmbedding.inclusion h
  have hr : range i = Subtype.val ⁻¹' (L : Set E) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := i.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i, hi.metrizableSpace,
    hu.completeSpace (hr ▸ hc.preimage continuous_subtype_val).isComplete⟩

/-- Successive compact averages telescope. Their differences are idempotent, since
a finer average fixes the coarser range and all the averages commute. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_difference
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
    (hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2)
    (H : ℕ → Subgroup G) (hcpt : ∀ n, IsCompact (H n : Set G)) (hm : Antitone H)
    (hcover : ∀ x, ∃ n, ∀ g ∈ H n, ρ g x = x)
    (hstage : ∀ n, ∃ M : Submodule ℂ E, IsFrechetTVS M ∧ ∀ x, (∀ g ∈ H n, ρ g x = x) → x ∈ M) :
    ∃ P : ℕ → E →L[ℂ] E,
      (∀ x, ∃ I : Finset ℕ, (∑ n ∈ I, P n x) = x ∧ ∀ n ∉ I, P n x = 0) ∧
      (∀ n, IsFrechetTVS (P n).toLinearMap.range) ∧
      (∀ n x, P n (P n x) = P n x) ∧
      ∀ n a x, P n (ρ a x) = ρ a (P n x) := by
  choose A hinv hfix hcomm using fun n ↦
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_average hc ρ hρ (H n) (hcpt n)
  have commute (n : ℕ) (a : G) (x : E) : A n (ρ a x) = ρ a (A n x) := by
    refine (hcomm n (ρ a) (fun g _ y ↦ ?_) x).symm
    exact DFunLike.congr_fun ((ρ.map_mul a g).symm.trans ((mul_comm a g) ▸ ρ.map_mul g a)) y
  have nested {i j : ℕ} (hij : i ≤ j) (x : E) : A j (A i x) = A i x :=
    hfix j _ fun g hg ↦ hinv i x g (hm hij hg)
  have rev (n : ℕ) (x : E) : A n (A (n+1) x) = A n x :=
    (hcomm (n+1) (A n) (fun g _ y ↦ commute n g y) x).trans (nested n.le_succ x)
  let P : ℕ → E →L[ℂ] E
    | 0 => A 0
    | n+1 => A (n+1) - A n
  have proj (n : ℕ) (x : E) : P n (P n x) = P n x := by
    cases n with
    | zero => exact nested le_rfl x
    | succ n =>
      change A (n+1) (A (n+1) x - A n x) - A n (A (n+1) x - A n x) = _
      rw [map_sub, map_sub, nested le_rfl, nested n.le_succ, rev, nested le_rfl, sub_self, sub_zero]
      rfl
  refine ⟨P, ?_, ?_, proj, ?_⟩
  · intro x
    obtain ⟨m, hx⟩ := hcover x
    have stable {k : ℕ} (hk : m ≤ k) : A k x = x := hfix k x fun g hg ↦ hx g (hm hk hg)
    have partialSum (k : ℕ) : ∑ n ∈ Finset.range (k+1), P n x = A k x := by
      induction k with
      | zero => simp [P]
      | succ k ih => rw [Finset.sum_range_succ, ih]; exact add_sub_cancel _ _
    refine ⟨Finset.range (m+1), (partialSum m).trans (stable le_rfl), ?_⟩
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    cases k with
    | zero => omega
    | succ k =>
      change A (k+1) x - A k x = 0
      rw [stable (by omega), stable (by omega), sub_self]
  · intro n
    obtain ⟨M, hM, hmem⟩ := hstage n
    apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_subspace
      _ M ?_ ?_ hM
    · rintro _ ⟨x, rfl⟩
      apply hmem
      intro g hg
      cases n with
      | zero => exact hinv 0 x g hg
      | succ n =>
        change ρ g (A (n+1) x - A n x) = _
        rw [map_sub, hinv _ x g hg, hinv _ x g (hm n.le_succ hg)]
        rfl
    · have eq : ((P n).toLinearMap.range : Set E) = {x | P n x = x} :=
        Set.ext fun x ↦ ⟨fun ⟨y, hy⟩ ↦ hy ▸ proj n y, fun hx ↦ ⟨x, hx⟩⟩
      exact eq ▸ isClosed_eq (P n).continuous continuous_id
  · intro n a x
    cases n with
    | zero => exact commute 0 a x
    | succ n =>
      change A (n+1) (ρ a x) - A n (ρ a x) = ρ a (A (n+1) x - A n x)
      rw [map_sub, commute, commute]

/-- The principal congruence conditions define compact subgroups of the S-ideles.
Their archimedean component is one. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_groups
    (T : Finset V) : ∃ H : ℕ → Subgroup (SAdeleRing F T)ˣ,
      (∀ n, IsCompact (H n : Set (SAdeleRing F T)ˣ)) ∧ Antitone H ∧
      ∀ n (h : (SAdeleRing F T)ˣ), h ∈ H n ↔ h.val.1 = 1 ∧
        ∀ w : T, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) := by
  let B (n : ℕ) (w : T) : Set (w.val.adicCompletion F) :=
    {x | Valued.v (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))}
  have val_one {n : ℕ} {w : T} {x : w.val.adicCompletion F} (hx : x ∈ B n w) :
      Valued.v x = 1 := by
    have he : WithZero.exp (-(n + 1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    simpa only [add_sub_cancel] using Valued.v.map_one_add_of_lt (lt_of_le_of_lt hx he)
  have mul_iff {n : ℕ} {w : T} {x : w.val.adicCompletion F} (hx : x ∈ B n w) (y) :
      x * y ∈ B n w ↔ y ∈ B n w := by
    have he : x * (y - 1) = (x * y - 1) - (x - 1) := by ring
    have hv := val_one hx
    change Valued.v (x * y - 1) ≤ _ ↔ Valued.v (y - 1) ≤ _
    constructor
    · intro h
      have hh := (Valued.v.map_sub (x * y - 1) (x - 1)).trans (max_le h hx)
      rwa [← he, map_mul, hv, one_mul] at hh
    · intro h
      rw [← sub_add_cancel (x * y - 1) (x - 1), ← he]
      apply (Valued.v.map_add _ _).trans (max_le _ hx)
      rwa [map_mul, hv, one_mul]
  have one_mem' (n : ℕ) (w : T) : 1 ∈ B n w := by
    change Valued.v (1 - 1 : w.val.adicCompletion F) ≤ _
    rw [sub_self, map_zero]
    exact zero_le
  let M (n : ℕ) : Submonoid (SAdeleRing F T) :=
    { carrier := {x | x.1 = 1 ∧ ∀ w, x.2 w ∈ B n w}
      one_mem' := ⟨rfl, one_mem' n⟩
      mul_mem' := fun {x y} hx hy ↦ ⟨(congrArg₂ (· * ·) hx.1 hy.1).trans (one_mul _),
        fun w ↦ (mul_iff (hx.2 w) _).mpr (hy.2 w)⟩ }
  have mem (n) (h : (SAdeleRing F T)ˣ) : h ∈ (M n).units ↔ h.val ∈ M n := by
    refine ⟨fun hh ↦ hh.1, fun hh ↦ ⟨hh, ?_⟩⟩
    have eq := congrArg (fun a : (SAdeleRing F T)ˣ ↦ a.val) (mul_inv_cancel h)
    have eq₁ := congrArg Prod.fst eq
    change h.val.1 * h⁻¹.val.1 = 1 at eq₁
    rw [hh.1, one_mul] at eq₁
    refine ⟨eq₁, fun w ↦ (mul_iff (hh.2 w) _).mp ?_⟩
    have ew : h.val.2 w * h⁻¹.val.2 w = 1 := congrArg (fun a : SAdeleRing F T ↦ a.2 w) eq
    exact (congrArg (· ∈ B n w) ew).mpr (one_mem' n w)
  refine ⟨fun n ↦ (M n).units, ?_, ?_, mem⟩
  · intro n
    let : T2Space (SAdeleRing F T) := inferInstanceAs
      (T2Space (((v : InfinitePlace F) → v.Completion) × ((w : T) → w.val.adicCompletion F)))
    apply Submonoid.units_isCompact
    have eq : (M n : Set (SAdeleRing F T)) = ({1} : Set (InfiniteAdeleRing F)) ×ˢ Set.univ.pi (B n) := by
      ext x
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ_pi]
      rfl
    rw [eq]
    apply isCompact_singleton.prod (isCompact_univ_pi fun w ↦ ?_)
    obtain ⟨z, hz⟩ := w.val.valuedAdicCompletion_surjective F (WithZero.exp (-(n + 1 : ℤ)))
    have hclosed : IsClosed (B n w) := by
      have eq : B n w = {x | ‖x - 1‖ ≤ ‖z‖} := by
        ext x
        exact (Valued.toNormedField.norm_le_iff.trans (hz ▸ Iff.rfl)).symm
      exact eq ▸ isClosed_le (continuous_id.sub continuous_const).norm continuous_const
    exact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w.val)).of_isClosed_subset
      hclosed fun x hx ↦ (val_one hx).le
  · intro n m hnm h hh
    obtain ⟨h₁, hw⟩ := (mem m h).mp hh
    exact (mem n h).mpr ⟨h₁, fun w ↦ (hw w).trans (WithZero.exp_le_exp.mpr (by omega))⟩

/-- Each level is contained in a Fréchet stage as soon as it has finitely many
archimedean Schwartz generators. Each generator map factors through one stage
of the strict LF presentation, so a single stage contains their finite sum. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_stage
    (T : Finset V) (d : ℕ) (p : Fin d → ℬ(InfiniteAdeleRing F) →L[ℂ] ℬₛ(T)) :
    ∃ M : Submodule ℂ (Θₛ(T)), IsFrechetTVS M ∧
      ∀ a : Fin d → ℬ(InfiniteAdeleRing F), (Kₛ(T)).mkQ (∑ j, p j (a j)) ∈ M := by
  classical
  obtain ⟨hT, L, hmono, hL, hcov, _⟩ := sLocalAdelicThetaSpace_strictLF (F := F) (S := T)
  let X := SchwartzMap (mixedEmbedding.mixedSpace F) ℂ
  obtain ⟨J, -⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  have hX : IsFrechetTVS X := by
    have : (uniformity X).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero]
      infer_instance
    refine ⟨inferInstance, (schwartz_withSeminorms ℂ _ _).toPolynormableSpace,
      UniformSpace.metrizableSpace, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact completeSpace_schwartzMap
  let u (j : Fin d) := ((Kₛ(T)).mkQL.comp (p j)).comp J.toContinuousLinearMap
  have fac (j : Fin d) : ∃ k, ∀ a, (Kₛ(T)).mkQ (p j a) ∈ L k := by
    obtain ⟨k, v, hv⟩ := frechet_factorization hL (fun k ↦ (L k).subtypeL)
      (fun _ ↦ Subtype.val_injective)
      (fun k _ ⟨z, hz⟩ ↦ ⟨⟨z.val, hmono k.le_succ z.property⟩, hz⟩)
      (fun x ↦ (hcov x).imp fun k hk ↦ ⟨⟨x, hk⟩, rfl⟩) hX (u j)
    refine ⟨k, fun a ↦ ?_⟩
    obtain ⟨x, rfl⟩ := J.surjective a
    exact (DFunLike.congr_fun hv x) ▸ (v x).property
  choose k hk using fac
  refine ⟨L (Finset.univ.sup k), hL _, fun a ↦ ?_⟩
  rw [map_sum]
  exact Submodule.sum_mem _ fun j hj ↦ hmono (Finset.le_sup hj) (hk j (a j))

/-- Local constancy of the dilation orbit at the identity gives one principal
congruence subgroup fixing a local test. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_local
    (v : V) (f : ℬ(v.adicCompletion F)) :
    ∃ n : ℕ, ∀ u : (v.adicCompletion F)ˣ,
      Valued.v (u.val - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) → schwartzBruhatUnitTranslate u f = f := by
  let K := v.adicCompletion F
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  have hnear : ∀ᶠ u : Kˣ in 𝓝 1, schwartzBruhatUnitTranslate u f = f := by
    exact ((finiteTest_translate_locallyConstant v f).eventually_eq 1).mono
      fun u hu ↦ hu.trans (DFunLike.congr_fun (unitTranslateEnd (R := K)).map_one f)
  have hind : IsInducing (Units.val : Kˣ → K) := Units.isEmbedding_val₀.isInducing
  rw [hind.nhds_eq_comap 1] at hnear
  obtain ⟨U, hU, hu⟩ := Filter.mem_comap.mp hnear
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  let r := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hr : r ≠ 0 := by simp [r]
  refine ⟨(-WithZero.log r).toNat, fun u h ↦ hu (hγ ?_)⟩
  apply ν.restrict_lt_iff_lt_embedding.mpr
  refine lt_of_le_of_lt h ?_
  change _ < r
  exact lt_of_lt_of_eq ((WithZero.exp_lt_exp (b := WithZero.log r)).mpr (by
    have := Int.self_le_toNat (-WithZero.log r)
    omega)) (WithZero.exp_log hr)

/-- A pure adelic tensor is fixed at the maximum of the levels of its finite
factors. Tests fixed at some level form a subspace and pure tensors span. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_cover
    (T : Finset V) (H : ℕ → Subgroup (SAdeleRing F T)ˣ) (hm : Antitone H)
    (hmem : ∀ n (h : (SAdeleRing F T)ˣ), h ∈ H n → h.val.1 = 1 ∧
      ∀ w : T, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) (f : ℬₛ(T)) :
    ∃ n, ∀ h ∈ H n, unitTranslateEnd h f = f := by
  classical
  let D : Submodule ℂ (ℬₛ(T)) :=
    { carrier := {b | ∃ n, ∀ h ∈ H n, unitTranslateEnd h b = b}
      zero_mem' := ⟨0, fun _ _ ↦ map_zero _⟩
      add_mem' := by
        rintro x y ⟨m, hx⟩ ⟨n, hy⟩
        exact ⟨max m n, fun h hh ↦ (map_add _ _ _).trans
          (congrArg₂ (· + ·) (hx h (hm (le_max_left _ _) hh)) (hy h (hm (le_max_right _ _) hh)))⟩
      smul_mem' := by
        rintro c x ⟨n, hx⟩
        exact ⟨n, fun h hh ↦ (map_smul _ c x).trans (congrArg (c • ·) (hx h hh))⟩ }
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F T
  have pure (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : T, ℬ(w.val.adicCompletion F)) :
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ∈ D := by
    choose k hk using fun w : T ↦
      sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_local w.val (b w)
    refine ⟨Finset.univ.sup k, fun h hh ↦ ?_⟩
    let t := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
    have h₁ := (hmem (Finset.univ.sup k) h⁻¹ ((H (Finset.univ.sup k)).inv_mem hh)).1
    apply SchwartzBruhat.ext
    intro x
    refine (schwartzBruhatUnitTranslate_apply h t x.toAdd).trans ((he a b _).trans
      (Eq.trans ?_ (he a b x.toAdd).symm))
    rw [Prod.fst_mul, h₁, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    let u : (w.val.adicCompletion F)ˣ := Units.map ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).toMonoidHom h
    have hu := hk w u ((hmem _ h (hm (Finset.le_sup (Finset.mem_univ w)) hh)).2 w)
    exact (schwartzBruhatUnitTranslate_apply u (b w) (x.toAdd.2 w)).symm.trans
      (congrArg (fun z : ℬ(w.val.adicCompletion F) ↦ z (Multiplicative.ofAdd (x.toAdd.2 w))) hu)
  have heq := sLocalThetaPrincipalValue_transition_ext e D.mkQ LinearMap.id 0
    (fun a b ↦ (Submodule.Quotient.mk_eq_zero D).mpr (pure a b))
  exact (Submodule.Quotient.mk_eq_zero D).mp (LinearMap.congr_fun heq f)

/-- At a fixed principal congruence level, finitely many archimedean Schwartz
families represent all invariant theta functions. This is the finite-generation
step of Theorem 5.2.1.1(1), p. 230, proved as
`sLocalAdelicThetaSpace_strictLF_level_generators` in Sec2. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_generators
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
    ∃ (d : ℕ) (p : Fin d →
        (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ] ℬₛ(S))),
      ∀ f : ℬₛ(S),
        (∀ h g : (SAdeleRing F S)ˣ, h.val.1 = 1 →
          (∀ w : S, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
          sLocalAdelicTheta F S f (h * g) = sLocalAdelicTheta F S f g) →
        ∃ a : Fin d → SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
          sLocalAdelicTheta F S (∑ j, p j (a j)) = sLocalAdelicTheta F S f :=
  sLocalAdelicThetaSpace_strictLF_level_generators (F := F) S n

/-- Decompose theta classes by their finite unit conductors. Differences of the normalized
averages over successive principal congruence subgroups give commuting projections. Each
range lies in a single congruence level, which has a finite family of archimedean Schwartz
generators as in the proof of Theorem 5.2.1.1(1), and is Fréchet. Each test has finite level. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels
    (T : Finset V) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    ∃ P : ℕ → Θₛ(T) →L[ℂ] Θₛ(T),
      (∀ x, ∃ I : Finset ℕ, (∑ n ∈ I, P n x) = x ∧ ∀ n ∉ I, P n x = 0) ∧
      (∀ n, IsFrechetTVS (P n).toLinearMap.range) ∧
      (∀ n x, P n (P n x) = P n x) ∧
      ∀ n a x, P n (ρ a x) = ρ a (P n x) := by
  classical
  intro ρ
  let π : (SAdeleRing F T)ˣ →* SIdeleQuotient F T := QuotientGroup.mk' _
  let θ := sLocalAdelicTheta F T
  let q := θ.ker.mkQ
  have eq (f g : ℬₛ(T)) : q f = q g ↔ θ f = θ g := by
    change Submodule.Quotient.mk f = (Submodule.Quotient.mk g : Θₛ(T)) ↔ _
    rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  have invariant (h : (SAdeleRing F T)ˣ) (f : ℬₛ(T)) (hf : ρ (π h) (q f) = q f)
      (g : (SAdeleRing F T)ˣ) : θ f (h * g) = θ f g := by
    have he := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 h f
    have ht := (eq _ _).mp (he.symm.trans hf)
    exact ((sAdelePrincipalValue_preserves_thetaKernel_translate h (h * g) f).symm.trans
      (DFunLike.congr_fun ht (h * g))).symm.trans (congrArg (θ f) (inv_mul_cancel_left h g))
  obtain ⟨H, hcompact, hmono, hmem⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_groups (F := F) T
  let : T2Space (Θₛ(T)) := (sLocalAdelicThetaSpace_strictLF (F := F) (S := T)).1
  let : PolynormableSpace ℂ (Θₛ(T)) := sLocalAdelicThetaSpace_polynormable (F := F) (S := T)
  have := isClosed_sProjectedDiagonal (F := F) (S := T)
  let : T2Space (SIdeleQuotient F T) := inferInstanceAs (T2Space (_ ⧸ _))
  apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_difference
    sLocalAdelicThetaSpace_complete ρ (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.1
    (fun n ↦ (H n).map π) (fun n ↦ (hcompact n).image continuous_quotient_mk')
    (fun _ _ hij ↦ Subgroup.map_mono (hmono hij))
  · intro x
    obtain ⟨f, rfl⟩ := θ.ker.mkQ_surjective x
    obtain ⟨n, hn⟩ :=
      sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_cover
        T H hmono (fun n h ↦ (hmem n h).mp) f
    refine ⟨n, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact ((existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 h f).trans
      (congrArg q (hn h hh))
  · intro n
    obtain ⟨d, p, hp⟩ :=
      sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_generators (F := F) T n
    obtain ⟨M, hM, ha⟩ :=
      sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_stage T d p
    refine ⟨M, hM, fun x hx ↦ ?_⟩
    obtain ⟨f, rfl⟩ := θ.ker.mkQ_surjective x
    obtain ⟨a, hfa⟩ := hp f fun h g h₁ hw ↦
      invariant h f (hx (π h) ⟨h, (hmem n h).mpr ⟨h₁, hw⟩, rfl⟩) g
    exact (eq _ _).2 hfa ▸ ha a

/-- The open mapping theorem on one Fréchet summand turns sequential closedness of the
range into an inducing map. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_frechet
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechetTVS E) (D : E →L[ℂ] E) (hi : Injective D)
    (hs : IsSeqClosed (Set.range D)) : IsInducing D := by
  obtain ⟨hadd, hpoly, hmetr, hcomp⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomp
  let R := D.toLinearMap.range
  have hc : IsClosed (R : Set E) := isSeqClosed_iff_isClosed.mp hs
  have hR : IsFrechetTVS R := by
    let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
    let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
    have hi : IsInducing R.subtypeL := IsInducing.subtypeVal
    have hu := AddMonoidHom.isUniformInducing_of_isInducing
      (f := R.subtype.toAddMonoidHom) hi
    have hr : range R.subtype.toAddMonoidHom = (R : Set E) :=
      Set.ext fun x ↦ ⟨fun ⟨z, hz⟩ ↦ hz ▸ z.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
    exact ⟨inferInstance, inferInstance, IsEmbedding.subtypeVal.metrizableSpace,
      hu.completeSpace (hr ▸ hc.isComplete)⟩
  have ho := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hR)
    (X := fun _ ↦ E) (fun _ ↦ ⟨hadd, hpoly, hmetr, hcomp⟩) (fun _ ↦ ContinuousLinearMap.id ℂ E)
    (fun _ ↦ Subset.rfl) (fun x ↦ ⟨0, x, rfl⟩) D.rangeRestrict D.toLinearMap.surjective_rangeRestrict
  have hh := isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨ho.isQuotientMap D.rangeRestrict.continuous D.toLinearMap.surjective_rangeRestrict,
     fun x y e ↦ hi (congrArg Subtype.val e)⟩
  exact IsInducing.subtypeVal.comp hh.isInducing

/-- Add the inverse seminorm estimates on the finite conductor summands. Their sum is
pointwise finite, so the supremum of its finite partial sums is continuous by barrelledness. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_sum
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [PolynormableSpace ℂ E] [BarrelledSpace ℂ E] (D : E →L[ℂ] E) (P : ℕ → E →L[ℂ] E)
    (hs : ∀ x, ∃ I : Finset ℕ, (∑ n ∈ I, P n x) = x ∧ ∀ n ∉ I, P n x = 0)
    (hF : ∀ n, IsFrechetTVS (P n).toLinearMap.range) (hproj : ∀ n x, P n (P n x) = P n x)
    (hi : Injective D) (hcomm : ∀ n x, P n (D x) = D (P n x))
    (hlim : ∀ n (z : ℕ → (P n).toLinearMap.range) (y : (P n).toLinearMap.range),
      Tendsto (fun j ↦ D (z j).val) atTop (𝓝 y.val) → y.val ∈ range D) :
    IsOpenMap D.toLinearMap.rangeRestrict := by
  classical
  have hstage (n : ℕ) : IsInducing (D.comp (P n).toLinearMap.range.subtypeL) := by
    let R := (P n).toLinearMap.range
    let d : R →L[ℂ] R := D.restrict (p := R) (q := R) fun _ ⟨x, hx⟩ ↦ ⟨D x, hx ▸ hcomm n x⟩
    have hd : IsInducing d := by
      apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_frechet (hF n) d
        (fun _ _ e ↦ Subtype.ext (hi (congrArg Subtype.val e)))
      intro seq y hseq hy
      choose z hz using hseq
      have hl : Tendsto (fun j ↦ d (z j)) atTop (𝓝 y) := by simpa only [hz] using hy
      obtain ⟨x, hx⟩ := hlim n z y ((continuous_subtype_val.tendsto y).comp hl)
      refine ⟨(P n).rangeRestrict x, Subtype.ext ?_⟩
      change D (P n x) = y.val
      rw [← hcomm, hx]
      obtain ⟨x', hx'⟩ := y.property
      exact hx' ▸ hproj n x'
    exact IsInducing.subtypeVal.comp hd
  have hind : IsInducing D := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm (by simpa only [map_zero] using (D.continuous.tendsto 0).le_comap) ?_
    intro U hU
    obtain ⟨p, hp, hball⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
    have hl (n : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ x, p (P n x) ≤ q (P n (D x)) := by
      obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing
        (p := p.comp (P n).toLinearMap.range.subtype) (hp.comp continuous_subtype_val)
        (f := (D.comp (P n).toLinearMap.range.subtypeL).toLinearMap) (hstage n)
      exact ⟨q, hq, fun x ↦ hcomm n x ▸ hle ((P n).rangeRestrict x)⟩
    choose q hq hle using hl
    let b (I : Finset ℕ) : Seminorm ℂ E := ∑ n ∈ I, (q n).comp (P n).toLinearMap
    have hb (I : Finset ℕ) (x : E) : b I x = ∑ n ∈ I, q n (P n x) := by
      induction I using Finset.induction_on with
      | empty => simp [b]
      | insert n I hn ih => simp [b, Finset.sum_insert hn] at ih ⊢
    have hbd : BddAbove (range b) := by
      apply Seminorm.bddAbove_range_iff.mpr
      intro x
      obtain ⟨I, -, hI⟩ := hs x
      refine ⟨b I x, forall_mem_range.mpr fun J ↦ ?_⟩
      rw [hb, hb]
      calc ∑ n ∈ J, q n (P n x) = ∑ n ∈ J ∩ I, q n (P n x) := by
            symm
            exact Finset.sum_subset Finset.inter_subset_left fun n hn hni ↦ by
              rw [hI n (fun hi ↦ hni (Finset.mem_inter.mpr ⟨hn, hi⟩)), map_zero]
           _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
             (fun _ _ _ ↦ apply_nonneg _ _)
    have hc := Seminorm.continuous_iSup b (fun I ↦ Seminorm.continuous_finsetSum
      (fun n _ ↦ (hq n).comp (P n).continuous)) hbd
    rw [← Seminorm.coe_iSup_eq hbd] at hc
    refine ⟨(⨆ I, b I).ball 0 1, Seminorm.ball_mem_nhds hc one_pos, fun x hx ↦ hball ?_⟩
    apply p.mem_ball_zero.mpr
    obtain ⟨I, hI, -⟩ := hs x
    calc p x = p (∑ n ∈ I, P n x) := congrArg p hI.symm
         _ ≤ ∑ n ∈ I, p (P n x) := Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
         _ ≤ b I (D x) := (Finset.sum_le_sum fun n _ ↦ hle n x).trans_eq (hb I _).symm
         _ ≤ (⨆ I, b I) (D x) := le_ciSup hbd I _
         _ < 1 := (Seminorm.mem_ball_zero _).mp hx
  have hr : IsInducing D.rangeRestrict :=
    IsInducing.of_comp (g := Subtype.val) D.rangeRestrict.continuous continuous_subtype_val hind
  have hs : Surjective D.rangeRestrict := D.toLinearMap.surjective_rangeRestrict
  exact hr.isOpenMap (hs.range_eq.symm ▸ isOpen_univ)

/-- A convergent sequence in the theta quotient has a subsequence represented by convergent
tests. Bounded lifting for nuclear strict LF quotients puts representatives in a bounded
set of one Fréchet test stage, where the Montel property gives a convergent subsequence. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_lift
    (T : Finset V) (z : ℕ → Θₛ(T)) (y : Θₛ(T)) (hz : Tendsto z atTop (𝓝 y)) :
    ∃ (φ : ℕ → ℕ) (a : ℕ → ℬₛ(T)) (f : ℬₛ(T)), StrictMono φ ∧ (∀ n, (Kₛ(T)).mkQ (a n) = z (φ n)) ∧
      Tendsto a atTop (𝓝 f) ∧ (Kₛ(T)).mkQ f = y := by
  let E := ℬₛ(T)
  let K := Kₛ(T)
  let : T2Space (Θₛ(T)) := sLocalAdelicThetaSpace_strictLF.1
  obtain ⟨_, L, hL, hF, he, ht⟩ := sAdeleSchwartz_strictLF F T
  let j (n : ℕ) := (L n).subtypeL.codRestrict (L (n + 1)) fun x ↦ hL n.le_succ x.property
  have hj (n : ℕ) : IsEmbedding (j n) :=
    IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal
  have hs : IsInjectiveLCLimit j (fun n ↦ (L n).subtypeL) :=
    ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ (he x).imp fun n hx ↦ ⟨⟨x, hx⟩, rfl⟩, ht⟩
  have hN : IsNuclearTVS.{0} ℬₛ(T) := sAdeleSchwartz_nuclear F T
  have hlift := (liftsBoundedSets_quotient_of_nuclear_strictLF hs hj hF
    (fun n ↦ isNuclearTVS_submodule hN (L n)) K sLocalAdelicTheta_ker_isClosed
    sLocalAdelicThetaSpace_strictLF sLocalAdelicThetaSpace_nuclear).1
  obtain ⟨A, hA, hcov⟩ := hlift _ (hz.isVonNBounded_range ℂ)
  let : ∀ n, PolynormableSpace ℂ (L n) := fun n ↦ (hF n).2.1
  let : ∀ n, TopologicalSpace.MetrizableSpace (L n) := fun n ↦ (hF n).2.2.1
  have hclosed (n : ℕ) : IsClosedEmbedding (j n) := by
    let : ∀ k, UniformSpace (L k) := fun k ↦ IsTopologicalAddGroup.rightUniformSpace _
    let : ∀ k, IsUniformAddGroup (L k) := fun k ↦ isUniformAddGroup_of_addCommGroup
    let : CompleteSpace (L n) := (hF n).2.2.2
    exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := (j n).toLinearMap.toAddMonoidHom)
      (hj n)).isClosedEmbedding
  obtain ⟨k, B, hB, hBA⟩ := (isVonNBounded_iff_bounded_stage hs hclosed A).mp hA
  have hpre (n : ℕ) : ∃ b ∈ B, K.mkQL (b : E) = z n := by
    obtain ⟨a, ha, hq⟩ := hcov (mem_range_self n)
    obtain ⟨b, hb, rfl⟩ := hBA.symm ▸ ha
    exact ⟨b, hb, hq⟩
  choose b hb heq using hpre
  let : UniformSpace (L k) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (L k) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (L k) := (hF k).2.2.2
  have hC := isCompact_closure_of_isNuclearTVS (L k) (isNuclearTVS_submodule hN (L k)) hB
  obtain ⟨w, -, φ, hφ, hw⟩ := hC.tendsto_subseq (fun n ↦ subset_closure (hb n))
  have ha := (continuous_subtype_val.tendsto w).comp hw
  refine ⟨φ, fun n ↦ (b (φ n)).val, w.val, hφ, fun n ↦ heq (φ n), ha, ?_⟩
  have hq := (K.mkQL.continuous.tendsto w.val).comp ha
  exact tendsto_nhds_unique hq (by simpa only [Function.comp_def, heq] using hz.comp hφ.tendsto_atTop)

/-- Fourier uniqueness for the integrable function obtained by multiplying theta by the
idele norm. Mellin evaluations on the single line of real part one separate theta classes. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_line
    (T : Finset V) :
    let c := fun χ : PontryaginDual (SIdeleQuotient F T) ↦
      quasiCharacterNormTwist (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) 1
    let Z := fun (x : Θₛ(T)) χ ↦ (sLocalThetaMellin x).val ⟨c χ, sLocalOrderBound_positive χ (by norm_num)⟩
    Injective Z := by
  intro c Z
  let : MeasurableSpace (SIdeleQuotient F T) := borel _
  let : BorelSpace (SIdeleQuotient F T) := ⟨rfl⟩
  let : LocallyCompactSpace (SAdeleRing F T)ˣ := (sIdeleGroup_description F T).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := T)
  let μ := sLocalQuotientTamagawaMeasure F T
  have : μ.IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := T)).1
  have : μ.Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := T)).2.1
  intro x y he
  apply sub_eq_zero.mp
  obtain ⟨f, hf⟩ := (Kₛ(T)).mkQ_surjective (x - y)
  rw [← hf]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hθ : sLocalAdelicThetaOnClasses F T f = 0 := by
    refine eq_zero_of_weighted_integrals μ _ (c 1)
      (sLocalThetaMellinIntegral_integrable f _ ⟨1, 1, by norm_num, rfl⟩) fun χ ↦ ?_
    have hz : sLocalIdelicZFunction f (c χ) = 0 := by
      change Z ((Kₛ(T)).mkQ f) χ = 0
      rw [hf]
      change (sLocalThetaMellin (x - y)).val _ = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun he χ)
    have hr : ∃ (ψ : PontryaginDual (SIdeleQuotient F T)) (s : ℂ), 0 < s.re ∧
        c χ = quasiCharacterNormTwist _ _ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) s :=
      ⟨χ, 1, by norm_num, rfl⟩
    rw [sLocalIdelicZFunction_eq_integral f hr, ← sLocalThetaMellinIntegral_eq_zeta f hr] at hz
    refine (integral_congr_ae (.of_forall fun a ↦ ?_)).trans hz
    change sLocalAdelicThetaOnClasses F T f a * (1 * _ ^ (1 : ℂ)) * (χ a : ℂ) =
      sLocalAdelicThetaOnClasses F T f a * ((χ a : ℂ) * _ ^ (1 : ℂ))
    rw [one_mul, mul_right_comm, mul_assoc]
  exact LinearMap.mem_ker.mpr (ContinuousMap.ext fun a ↦
    (sLocalAdelicThetaOnClasses_mk F T f a).symm.trans (DFunLike.congr_fun hθ _))

/-- At nonzero real weight the distance of the dilation multiplier from zero has
a positive lower bound independent of the unitary character. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_gap
    (T : Finset V) (g : (SAdeleRing F T)ˣ) (hg : sIdeleNorm F T g ≠ 1)
    (r : ℝ) (hr : r ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ : PontryaginDual (SIdeleQuotient F T),
      let c := quasiCharacterNormTwist (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) (r : ℂ)
      ε ≤ ‖1 - c (QuotientGroup.mk g)‖ := by
  let m : ℝ := (sIdeleNorm F T g).val
  refine ⟨|1 - m ^ r|, abs_pos.mpr (sub_ne_zero.mpr fun he ↦ hg ?_), ?_⟩
  · have hm : m ^ r = 1 ^ r := he.symm.trans (Real.one_rpow r).symm
    exact Units.ext (NNReal.eq ((Real.rpow_left_inj (NNReal.coe_nonneg _) zero_le_one hr).mp hm))
  · intro χ c
    have hm : ‖c (QuotientGroup.mk g)‖ = m ^ r := by
      change ‖(χ (QuotientGroup.mk g) : ℂ) * _ ^ (r : ℂ)‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)), Complex.ofReal_re]
    simpa only [norm_one, hm] using abs_norm_sub_norm_le (1 : ℂ) (c (QuotientGroup.mk g))

/-- Mellin evaluation of a dilation difference at any regular quasi-character. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_symbol
    (T : Finset V) (g : (SAdeleRing F T)ˣ) (f : ℬₛ(T))
    (d : {d : QuasiCharacter (SIdeleQuotient F T) // 0 ≤ sLocalIdelicOrderBound d}) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    let D := ContinuousLinearMap.id ℂ Θₛ(T) - ρ (QuotientGroup.mk g)
    (sLocalThetaMellin (D ((Kₛ(T)).mkQ f))).val d =
      (1 - d.val (QuotientGroup.mk g)) * sLocalIdelicZFunction f d.val := by
  intro ρ D
  change (sLocalThetaMellin ((Kₛ(T)).mkQ f - ρ _ ((Kₛ(T)).mkQ f))).val d = _
  rw [show ρ (QuotientGroup.mk g) ((Kₛ(T)).mkQ f) = (Kₛ(T)).mkQ (schwartzBruhatUnitTranslate g f) from
    (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 g f, map_sub]
  change (sLocalIdelicMellin f).val d - (sLocalIdelicMellin (schwartzBruhatUnitTranslate g f)).val d = _
  rw [sLocalIdelicMellin_unitTranslate, sub_mul, one_mul]
  rfl

section

local notation "chartₜ(" T ", " χ ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F T)
  (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F T))
  (ContinuousMonoidHom.comp (ContinuousMonoidHom.mk Circle.coeHom continuous_subtype_val : Circle →ₜ* ℂ) χ)

/-- Schwartz seminorms of the restrictions to one vertical line on the elementary
subgroup `H × ℝ` of the dual. The polynomials and derivatives act in the radial
variable, and group seminorms on the finitely generated group supply angular weights. -/
private def mellinSchwartzStage {D : Type*} [CommGroup D] (Z : ℕ → D → ℂ → ℂ)
    (a : ℝ) (H : Subgroup D) : Prop :=
  (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → Z n χ z = 0) ∧
    ∀ (p : GroupSeminorm H) (k m j : ℕ), ∃ M : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
      (1 + p χ) ^ k * ‖iteratedDeriv j (fun s ↦ s ^ m * Z n χ.val s) z‖ ≤ M

/-- The weighted Mellin transforms are bounded in the Bruhat–Schwartz space of the
unitary dual on each line of real part greater than one. -/
private def sLocalMellinSchwartzBounds (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (g : ℕ → ℬₛ(T))
    (Z : ℬₛ(T) → QuasiCharacter (SIdeleQuotient F T) → ℂ := sLocalIdelicZFunction) : Prop :=
  ∀ a : ℝ, 1 < a → ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
    mellinSchwartzStage (fun n χ z ↦ Z (g n) (chartₜ(T, χ.val) z)) a H

/-- Unfold the theta Mellin integral on the positive half-plane. Equality on a
neighborhood of each point also identifies all the derivatives in the Schwartz bounds. -/
private theorem sLocalMellinSchwartzBounds_unfold (T : Finset V)
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (v : ℕ → ℬₛ(T)) :
    sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral ↔ sLocalMellinSchwartzBounds T τ v := by
  have transfer (Z W : ℬₛ(T) → QuasiCharacter (SIdeleQuotient F T) → ℂ)
      (h : ∀ g χ (z : ℂ), 0 < z.re → Z g (chartₜ(T, χ) z) = W g (chartₜ(T, χ) z)) :
      sLocalMellinSchwartzBounds T τ v Z → sLocalMellinSchwartzBounds T τ v W := by
    intro hZ a ha
    obtain ⟨H, hH, hs, hb⟩ := hZ a ha
    refine ⟨H, hH, ?_, ?_⟩
    · intro χ hχ n z hz
      exact (h (v n) χ.val z (hz ▸ zero_lt_one.trans ha)).symm.trans (hs χ hχ n z hz)
    · intro p k m j
      obtain ⟨B, hB⟩ := hb p k m j
      refine ⟨B, fun χ n z hz ↦ ?_⟩
      have he : (fun s : ℂ ↦ s ^ m * Z (v n) (chartₜ(T, χ.val.val) s)) =ᶠ[𝓝 z]
          (fun s ↦ s ^ m * W (v n) (chartₜ(T, χ.val.val) s)) := by
        filter_upwards [((isOpen_Ioi (a := (0 : ℝ))).preimage Complex.continuous_re).mem_nhds
          (show 0 < z.re from hz ▸ zero_lt_one.trans ha)] with s hpos
        exact congrArg (s ^ m * ·) (h (v n) χ.val.val s hpos)
      exact (he.iteratedDeriv_eq j) ▸ hB χ n z hz
  have h (g : ℬₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ) (hz : 0 < z.re) :
      sLocalThetaMellinIntegral g (chartₜ(T, χ) z) = sLocalIdelicZFunction g (chartₜ(T, χ) z) :=
    (sLocalThetaMellinIntegral_eq_zeta g ⟨χ, z, hz, rfl⟩).trans
      (sLocalIdelicZFunction_eq_integral g ⟨χ, z, hz, rfl⟩).symm
  exact ⟨transfer _ _ h, transfer _ _ (fun g χ z hz ↦ (h g χ z hz).symm)⟩

/-- Absorb the imaginary part of a norm twist into its unitary character. -/
private theorem sLocalMellinSchwartzBounds_unitary
    (T : Finset V) (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ) :
    ∃ ψ : PontryaginDual (SIdeleQuotient F T), chartₜ(T, ψ) (z.re : ℂ) = chartₜ(T, χ) z := by
  let d := chartₜ(T, χ) ((z.im : ℂ) * Complex.I)
  have hp (g : SIdeleQuotient F T) : 0 < ((sIdeleQuotientNorm F T g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hd (g) : ‖d g‖ = 1 := by
    change ‖(χ g : ℂ) * _ ^ ((z.im : ℂ) * Complex.I)‖ = 1
    rw [norm_mul, Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos (hp g)]
    simp
  let ψ : PontryaginDual (SIdeleQuotient F T) :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Circle.ext d.map_one
      map_mul' := fun x y ↦ Circle.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨ψ, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change ((χ g : ℂ) * _ ^ ((z.im : ℂ) * Complex.I)) * _ ^ (z.re : ℂ) = _
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hp g).ne'),
    add_comm, Complex.re_add_im]
  rfl

/-- Meromorphic uniqueness extends the functional equation from the strip of convergence. -/
private theorem sLocalMellinSchwartzBounds_equation
    (T : Finset V) (χ : PontryaginDual (SIdeleQuotient F T)) (g : ℬₛ(T)) :
    ∀ᶠ z : ℂ in codiscrete ℂ,
      sLocalIdelicZFunction g (chartₜ(T, χ) z) = sLocalRhoFactor (chartₜ(T, χ) z) *
        sLocalIdelicZFunction (sAdeleSchwartzFourier g) (chartₜ(T, χ⁻¹) (1 - z)) := by
  let R (z : ℂ) := sLocalRhoFactor (chartₜ(T, χ) z)
  let Z (g : ℬₛ(T)) (η : PontryaginDual (SIdeleQuotient F T)) (z : ℂ) :=
    sLocalIdelicZFunction g (chartₜ(T, η) z)
  have hm (g : ℬₛ(T)) (η : PontryaginDual (SIdeleQuotient F T)) : Meromorphic (Z g η) :=
    fun z ↦ ((sLocalIdelicZFunction_meromorphic g η) (mem_univ z)).meromorphicAt
  have hR : Meromorphic R := sLocalRhoFactor_meromorphic χ
  let Δ (z : ℂ) := Z g χ z - R z * Z (sAdeleSchwartzFourier g) χ⁻¹ (1 - z)
  have hΔ : MeromorphicOn Δ univ := fun z _ ↦ (hm g χ z).sub ((hR z).mul
    ((hm _ _ (1 - z)).comp_analyticAt (g := fun s : ℂ ↦ 1 - s) (by fun_prop)))
  have htop : meromorphicOrderAt Δ (1 / 2) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hs : ∀ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
      nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by
        norm_num [mem_preimage, mem_Ioo]))
    filter_upwards [hs] with z hz
    have hdual : dualQuasiCharacter (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
        (chartₜ(T, χ) z) = chartₜ(T, χ⁻¹) (1 - z) := by
      exact sLocalNormTwistChart_dual χ z
    change Z g χ z - R z * Z _ _ _ = 0
    apply sub_eq_zero.mpr
    have hd : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
    exact (sLocalIdelicZFunction_eq_integral g ⟨χ, z, hz.1, rfl⟩).trans
      ((sLocalIdelicZetaIntegral_functionalEquation g χ z hz).trans (congrArg (R z * ·)
        ((congrArg (sLocalIdelicZetaIntegral (sAdeleSchwartzFourier g)) hdual).trans
          (sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹, 1 - z, hd, rfl⟩).symm)))
  have he : Δ =ᶠ[codiscrete ℂ] 0 := eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr
    fun z ↦ meromorphicOrderAt_eq_top_iff.mp (hΔ.meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ _) (mem_univ z) htop)
  exact he.mono fun z hz ↦ sub_eq_zero.mp hz

/-- Successive twists add their exponents. -/
private theorem sLocalMellinSchwartzBounds_twist
    {G : Type*} [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (c : QuasiCharacter G) (z w : ℂ) :
    quasiCharacterNormTwist m hm (quasiCharacterNormTwist m hm c z) w =
      quasiCharacterNormTwist m hm c (w + z) := by
  ext1 a
  let N : ℂ := (((m a : ℝ≥0) : ℝ) : ℂ)
  change (c a * N ^ z) * N ^ w = c a * N ^ (w + z)
  rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (m a).ne_zero)), mul_assoc]

/-- In a unitary chart the allowed order is nonnegative off a discrete set. -/
private theorem sLocalMellinSchwartzBounds_regular
    (T : Finset V) (χ : PontryaginDual (SIdeleQuotient F T)) :
    ∀ᶠ z : ℂ in codiscrete ℂ, 0 ≤ sLocalIdelicOrderBound (chartₜ(T, χ) z) := by
  let R (z : ℂ) := sLocalRhoFactor (chartₜ(T, χ) z)
  have hR : Meromorphic R := sLocalRhoFactor_meromorphic χ
  have hA := (meromorphicOn_univ.mpr hR).eventually_codiscreteWithin_analyticAt R
  apply hA.mono
  intro z hz
  simp only [sLocalIdelicOrderBound,
    sLocalMellinSchwartzBounds_twist]
  change 0 ≤ min 0 (meromorphicOrderAt (fun w ↦ R (w + z)) 0)
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add]
  exact le_min le_rfl hz.meromorphicOrderAt_nonneg

/-- Away from a discrete subset of a norm chart the functional equation is a pointwise
identity, the common factor is nonzero, and evaluation is allowed by the pole bound. -/
private theorem sLocalMellinSchwartzBounds_reflection
    (T : Finset V) (χ : PontryaginDual (SIdeleQuotient F T)) (g : ℬₛ(T)) :
    ∀ᶠ z : ℂ in codiscrete ℂ,
      0 ≤ sLocalIdelicOrderBound (chartₜ(T, χ) z) ∧ sLocalRhoFactor (chartₜ(T, χ) z) ≠ 0 ∧
      sLocalIdelicZFunction g (chartₜ(T, χ) z) = sLocalRhoFactor (chartₜ(T, χ) z) *
        sLocalIdelicZFunction (sAdeleSchwartzFourier g) (chartₜ(T, χ⁻¹) (1 - z)) := by
  filter_upwards [sLocalMellinSchwartzBounds_regular T χ,
    sLocalRhoFactor_mul_dual (F := F) (S := T) χ,
    sLocalMellinSchwartzBounds_equation T χ g] with z hr hp he
  exact ⟨hr, left_ne_zero_of_mul (hp.trans_ne ((Group.isUnit
    (QuotientGroup.mk (-1 : (SAdeleRing F T)ˣ) : SIdeleQuotient F T)).map (chartₜ(T, χ) z)).ne_zero), he⟩

/-- The convergent zeta integral is holomorphic on each positive half-plane chart. -/
private theorem sLocalMellinSchwartzBounds_holomorphic
    (T : Finset V) (g : ℬₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T)) :
    DifferentiableOn ℂ (fun z ↦ sLocalIdelicZFunction g (chartₜ(T, χ) z)) (Complex.re ⁻¹' Ioi 0) :=
  (sLocalIdelicZetaIntegral_analyticOn g χ).differentiableOn.congr fun z hz ↦
    sLocalIdelicZFunction_eq_integral g ⟨χ, z, hz, rfl⟩

/-- Cancel the common Tate factor on a punctured vertical line. Continuity of the
reflected integrals extends the bound across all exceptional points on that line. -/
private theorem sLocalMellinSchwartzBounds_fourier
    (T : Finset V) (b f : ℬₛ(T)) (r C : ℝ) (hr : 1 < r)
    (h : ∀ (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ), z.re = 1 - r →
      0 ≤ sLocalIdelicOrderBound (chartₜ(T, χ) z) →
      ‖sLocalIdelicZFunction f (chartₜ(T, χ) z)‖ ≤ C * ‖sLocalIdelicZFunction b (chartₜ(T, χ) z)‖)
    (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ) (hz : z.re = r) :
    ‖sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chartₜ(T, χ) z)‖ ≤
      C * ‖sLocalIdelicZFunction (sAdeleSchwartzFourier b) (chartₜ(T, χ) z)‖ := by
  let w (t : ℝ) := 1 - z + (t : ℂ) * Complex.I
  have hw : Tendsto w (𝓝[≠] 0) (𝓝[≠] (1 - z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous w := by fun_prop
      simpa [w] using (hc.tendsto 0).mono_left (y := 𝓝[≠] (0 : ℝ)) nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (s := ({0}ᶜ : Set ℝ)) (a := 0)] with t ht
      simpa [w] using (show t ≠ 0 from ht)
  have hlim : Tendsto (fun t ↦ 1 - w t) (𝓝[≠] 0) (𝓝 z) := by
    simpa only [sub_sub_cancel] using (tendsto_const_nhds (x := (1 : ℂ))).sub (hw.mono_right nhdsWithin_le_nhds)
  have hc (g : ℬₛ(T)) := (sLocalMellinSchwartzBounds_holomorphic
    T (sAdeleSchwartzFourier g) χ).continuousOn.continuousAt
    ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (show 0 < z.re by linarith))
  apply le_of_tendsto_of_tendsto (((hc f).tendsto.comp hlim).norm)
    (tendsto_const_nhds.mul (((hc b).tendsto.comp hlim).norm))
  have reg := sLocalMellinSchwartzBounds_reflection T χ⁻¹
  filter_upwards [hw.eventually (nhdsNE_le_codiscrete _ (reg f)),
    hw.eventually (nhdsNE_le_codiscrete _ (reg b))] with t hf hb
  have hh := h χ⁻¹ (w t) (by simp [w, hz]) hf.1
  rw [hf.2.2, hb.2.2, norm_mul, norm_mul, mul_left_comm C] at hh
  let comp (η : PontryaginDual (SIdeleQuotient F T)) :=
    ‖sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chartₜ(T, η) (1 - w t))‖ ≤
      C * ‖sLocalIdelicZFunction (sAdeleSchwartzFourier b) (chartₜ(T, η) (1 - w t))‖
  exact (congrArg comp (inv_inv χ)).mp (le_of_mul_le_mul_left hh (norm_pos_iff.mpr hf.2.1))

/-- Polynomially weighted edge bounds propagate across a strip by Phragmén–Lindelöf.
Rapid decay provides the preliminary unweighted bound for each individual test. -/
private theorem sLocalMellinSchwartzBounds_strip
    (T : Finset V) (g : ℬₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T)) (m : ℕ)
    (a b A M : ℝ) (ha : 1 < a) (hab : a < b) (hA : 0 ≤ A)
    (hedge : ∀ z : ℂ, z.re = a ∨ z.re = b →
      A * ‖z ^ m * sLocalIdelicZFunction g (chartₜ(T, χ) z)‖ ≤ M)
    (z : ℂ) (hz : z.re ∈ Icc a b) :
    A * ‖z ^ m * sLocalIdelicZFunction g (chartₜ(T, χ) z)‖ ≤ M := by
  let Z (s : ℂ) := sLocalIdelicZFunction g (chartₜ(T, χ) s)
  let W (s : ℂ) := (A : ℂ) * Z s
  have hW (s : ℂ) : ‖s ^ m * W s‖ = A * ‖s ^ m * Z s‖ := by
    simp only [W, mul_left_comm (s ^ m) (A : ℂ), norm_mul, Complex.norm_of_nonneg hA]
  have hD : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioi 0) :=
    (sLocalMellinSchwartzBounds_holomorphic T g χ).const_mul _
  obtain ⟨C, hC, htail⟩ := sLocalIdelicZFunction_rapid_decay_on_positive_strip g χ a b
    (zero_lt_one.trans ha) hab 1 (by decide)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (eventually_comap.mp htail)
  let R := max Y 1
  let K := Complex.reProdIm (Icc a b) (Icc (-R) R)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun s ↦ ‖W s‖) K :=
    (hD.continuousOn.norm).mono fun s hs ↦ (zero_lt_one.trans ha).trans_le hs.1.1
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc
  rw [← hW]
  apply norm_pow_mul_le_on_verticalStrip hab _ (M := max B (A * C)) _ m
    (fun s hs ↦ (hW s).le.trans (hedge s (.inl hs)))
    (fun s hs ↦ (hW s).le.trans (hedge s (.inr hs))) z hz
  · apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_preimage_re, closure_Ioo hab.ne]
    exact hD.mono fun s hs ↦ (zero_lt_one.trans ha).trans_le hs.1
  · intro s hs
    by_cases hy : |s.im| ≤ R
    · exact (hB (mem_image_of_mem _ (show s ∈ K from ⟨hs, abs_le.mp hy⟩))).trans (le_max_left _ _)
    · have hR := le_of_lt (lt_of_not_ge hy)
      have hdec := hY |s.im| ((le_max_left _ _).trans hR) s.im rfl s.re hs
      rw [Complex.re_add_im, pow_one] at hdec
      have hZ := hdec.trans (div_le_self hC.le ((le_max_right _ _).trans hR))
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hZ (norm_nonneg (A : ℂ))).trans
        (by rw [Complex.norm_of_nonneg hA]; exact le_max_right _ _))

/-- Cauchy's estimate on a circle between two neighboring weight lines bounds each
radial derivative, uniformly in the angular character and in the test index. -/
private theorem sLocalMellinSchwartzBounds_derivatives
    (T : Finset V) {ι : Type*} (g : ι → ℬₛ(T)) (χ : ι → PontryaginDual (SIdeleQuotient F T))
    (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) (m j : ℕ)
    (r d : ℝ) (hd : 0 < d) (hl : 1 < r - d)
    (h : ∀ a : ℝ, a = r - d ∨ a = r + d → ∃ M : ℝ, ∀ i (z : ℂ), z.re = a →
      A i * ‖z ^ m * sLocalIdelicZFunction (g i) (chartₜ(T, χ i) z)‖ ≤ M) :
    ∃ M : ℝ, ∀ i (z : ℂ), z.re = r → A i * ‖iteratedDeriv j
      (fun s ↦ s ^ m * sLocalIdelicZFunction (g i) (chartₜ(T, χ i) s)) z‖ ≤ M := by
  obtain ⟨L, hL⟩ := h (r - d) (.inl rfl)
  obtain ⟨R, hR⟩ := h (r + d) (.inr rfl)
  refine ⟨j.factorial * max L R / d ^ j, fun i z hz ↦ ?_⟩
  let Z (s : ℂ) := s ^ m * sLocalIdelicZFunction (g i) (chartₜ(T, χ i) s)
  let W (s : ℂ) := (A i : ℂ) * Z s
  have hball (w : ℂ) (hw : w ∈ Metric.closedBall z d) : w.re ∈ Icc (r - d) (r + d) := by
    have hdist : ‖w - z‖ ≤ d := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
    have he := (Complex.abs_re_le_norm (w - z)).trans hdist
    rw [Complex.sub_re, hz, abs_le] at he
    exact ⟨by linarith [he.1], by linarith [he.2]⟩
  have hdiff : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioi 0) := ((differentiableOn_id.pow m).mul
    (sLocalMellinSchwartzBounds_holomorphic T (g i) (χ i))).const_mul _
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := W) j hd
    (hdiff.diffContOnCl_ball (fun w hw ↦ (zero_lt_one.trans hl).trans_le (hball w hw).1)) (C := max L R) (by
      intro w hw
      change ‖(A i : ℂ) * Z w‖ ≤ _
      rw [norm_mul, Complex.norm_of_nonneg (hA i)]
      apply sLocalMellinSchwartzBounds_strip
        T (g i) (χ i) m (r - d) (r + d) (A i) _ hl (by linarith) (hA i) _ w
        (hball w (Metric.sphere_subset_closedBall hw))
      rintro u (hu | hu)
      · exact (hL i u hu).trans (le_max_left _ _)
      · exact (hR i u hu).trans (le_max_right _ _))
  simpa only [W, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_of_nonneg (hA i)] using hb

/-- A zeroth-order Schwartz bound extends to a larger angular subgroup by zero.
Pointwise comparison transfers that bound with its line constant. -/
private theorem sLocalMellinSchwartzBounds_edge
    {D : Type*} [CommGroup D] (H K : Subgroup D) (hi : H ≤ K) (U W : ℕ → D → ℂ → ℂ)
    (a C : ℝ) (hU : mellinSchwartzStage U a H)
    (h : ∀ n χ (z : ℂ), z.re = a → ‖W n χ z‖ ≤ C * ‖U n χ z‖)
    (p : GroupSeminorm K) (k m : ℕ) :
    ∃ M : ℝ, ∀ (χ : K) n (z : ℂ), z.re = a → (1 + p χ) ^ k * ‖z ^ m * W n χ.val z‖ ≤ M := by
  obtain ⟨B, hB⟩ := hU.2 (p.comp (Subgroup.inclusion hi)) k m 0
  refine ⟨max C 0 * max B 0, fun χ n z hz ↦ ?_⟩
  have hu : (1 + p χ) ^ k * ‖z ^ m * U n χ.val z‖ ≤ max B 0 := by
    by_cases hx : χ.val ∈ H
    · exact (hB ⟨χ.val, hx⟩ n z hz).trans (le_max_left _ _)
    · rw [hU.1 χ.val hx n z hz, mul_zero, norm_zero, mul_zero]
      exact le_max_right _ _
  have hV := (h n χ.val z hz).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))
  have hW : 0 ≤ (1 + p χ) ^ k := pow_nonneg (by linarith [apply_nonneg p χ]) _
  rw [norm_mul] at hu ⊢
  calc (1 + p χ) ^ k * (‖z ^ m‖ * ‖W n χ.val z‖) ≤
        (1 + p χ) ^ k * (‖z ^ m‖ * (max C 0 * ‖U n χ.val z‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV (norm_nonneg _)) hW
       _ = max C 0 * ((1 + p χ) ^ k * (‖z ^ m‖ * ‖U n χ.val z‖)) := by ring
       _ ≤ max C 0 * max B 0 := mul_le_mul_of_nonneg_left hu (le_max_right _ _)

/-- Choose a single elementary stage for the central line and both edges. The value
comparison controls angular support there, and Cauchy's estimate controls each radial
derivative on the central line. -/
private theorem sLocalMellinSchwartzBounds_transfer
    (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (b f : ℕ → ℬₛ(T))
    (hb : sLocalMellinSchwartzBounds T τ b)
    (h : ∀ r : ℝ, 1 < r → ∃ C : ℝ, ∀ n (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ), z.re = r →
      ‖sLocalIdelicZFunction (f n) (chartₜ(T, χ) z)‖ ≤ C * ‖sLocalIdelicZFunction (b n) (chartₜ(T, χ) z)‖) :
    sLocalMellinSchwartzBounds T τ f := by
  intro r hr
  let d := (r - 1) / 2
  have hd : 0 < d := half_pos (sub_pos.mpr hr)
  have hl : 1 < r - d := by dsimp [d]; linarith
  obtain ⟨H, hH, hc⟩ := hb r hr
  obtain ⟨L, hL, hleft⟩ := hb (r - d) hl
  have hr' : 1 < r + d := by linarith
  obtain ⟨R, hR, hright⟩ := hb (r + d) hr'
  let K := H ⊔ (L ⊔ R)
  have hHK : H ≤ K := le_sup_left
  have hLK : L ≤ K := le_sup_left.trans (le_sup_right (a := H))
  have hRK : R ≤ K := le_sup_right.trans (le_sup_right (a := H))
  refine ⟨K, hH.sup (hL.sup hR), ?_, ?_⟩
  · intro χ hχ n z hz
    obtain ⟨C, hC⟩ := h r hr
    have he := hC n χ.val z hz
    have heq : sLocalIdelicZFunction (b n) (chartₜ(T, χ.val) z) = 0 :=
      hc.1 χ (fun hx ↦ hχ (hHK hx)) n z hz
    rw [heq, norm_zero, mul_zero, norm_le_zero_iff] at he
    exact he
  · intro p k m j
    have edge (a : ℝ) (ha : 1 < a) (J : Subgroup (PontryaginDual.map τ).ker) (hi : J ≤ K)
        (hJ : mellinSchwartzStage (fun n χ z ↦ sLocalIdelicZFunction (b n) (chartₜ(T, χ.val) z)) a J) :
        ∃ M : ℝ, ∀ i : K × ℕ, ∀ z : ℂ, z.re = a →
          (1 + p i.1) ^ k * ‖z ^ m * sLocalIdelicZFunction (f i.2) (chartₜ(T, i.1.val.val) z)‖ ≤ M := by
      obtain ⟨C, hC⟩ := h a ha
      obtain ⟨M, hM⟩ := sLocalMellinSchwartzBounds_edge
        J K hi _ (fun n χ z ↦ sLocalIdelicZFunction (f n) (chartₜ(T, χ.val) z)) a C hJ
        (fun n χ ↦ hC n χ.val) p k m
      exact ⟨M, fun i ↦ hM i.1 i.2⟩
    obtain ⟨M, hM⟩ := sLocalMellinSchwartzBounds_derivatives
      T (fun i : K × ℕ ↦ f i.2) (fun i ↦ i.1.val.val) (fun i ↦ (1 + p i.1) ^ k)
      (fun i ↦ pow_nonneg (by linarith [apply_nonneg p i.1]) _) m j r d hd hl
      (by
        rintro a (rfl | rfl)
        · exact edge _ hl L hLK hleft
        · exact edge _ hr' R hRK hright)
    exact ⟨M, fun χ n ↦ hM (χ, n)⟩

/-- Vanishing on a vertical line extends to the entire positive half-plane. -/
private theorem sLocalMellinSchwartzBounds_meyer_line_support (p : ℂ → ℂ) (hp : AnalyticOnNhd ℂ p (Complex.re ⁻¹' Ioi 0))
    (a : ℝ) (ha : 0 < a) (hz : ∀ z : ℂ, z.re = a → p z = 0) :
    ∀ z : ℂ, 0 < z.re → p z = 0 := by
  have hc : Continuous (fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hf : Tendsto (fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * Complex.I) (𝓝[≠] 0) (𝓝[≠] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (a : ℂ) + (t : ℂ) * Complex.I ≠ (a : ℂ)
      simpa using (show t ≠ 0 from ht)
  apply hp.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := (a : ℂ)) (by simpa using ha)
  apply hf.frequently
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (fun t ↦ hz _ (by simp)))

/-- A single finitely generated subgroup supports every positive Mellin line. -/
private theorem sLocalMellinSchwartzBounds_meyer_one_angular_support (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (v : ℕ → ℬₛ(T)) (h : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      ∀ χ ∉ H, ∀ n (z : ℂ), 0 < z.re → sLocalThetaMellinIntegral (v n) (chartₜ(T, χ.val) z) = 0 := by
  obtain ⟨H,hH,hzero,_⟩ := h 2 (by norm_num)
  exact ⟨H,hH,fun χ hχ n ↦ sLocalMellinSchwartzBounds_meyer_line_support _ (sLocalThetaMellinIntegral_analyticOn (v n) χ.val)
    2 (by norm_num) (hzero χ hχ n)⟩

/-- A norm section factors every unitary character into an angular character and an imaginary norm power. -/
private theorem sLocalMellinSchwartzBounds_meyer_angular_normalization (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (χ : PontryaginDual (SIdeleQuotient F T)) :
    ∃ η : (PontryaginDual.map τ).ker, ∃ z : ℂ, z.re = 0 ∧ chartₜ(T, χ) 1 = chartₜ(T, η.val) (1+z) ∧
      ∀ x : SIdeleQuotient F T, sIdeleQuotientNorm F T x = 1 → χ x = η.val x := by
  let m : SIdeleQuotient F T →ₜ* ℝ≥0ˣ := ⟨sIdeleQuotientNorm F T, (isProperMap_sIdeleQuotientNorm F T).continuous⟩
  let b := χ.comp τ
  let f : PontryaginDual (SIdeleQuotient F T) := b.comp m
  let η : PontryaginDual (SIdeleQuotient F T) := χ / f
  have hη : η ∈ (PontryaginDual.map τ).ker := by
    apply PontryaginDual.ext
    intro x
    change χ (τ x) / χ (τ (sIdeleQuotientNorm F T (τ x))) = 1
    rw [hτ, div_self']
  let inc : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨z, ⟨hz, hb⟩, _⟩ := existsUnique_unitaryComplexPower (inc.comp b) (fun t ↦ Circle.norm_coe (b t))
  refine ⟨⟨η,hη⟩, z, hz, ?_, fun x hx ↦ ?_⟩
  · ext x
    let t : ℂ := ((sIdeleQuotientNorm F T x).val : ℝ)
    have ht : t ≠ 0 := by
      dsimp [t]
      exact_mod_cast (NNReal.coe_pos.mpr (sIdeleQuotientNorm F T x).zero_lt).ne'
    change (χ x : ℂ) * t ^ (1 : ℂ) = (χ x / b (m x) : Circle) * t ^ (1+z)
    rw [Circle.coe_div, Complex.cpow_add _ _ ht]
    have hbx : (b (m x) : ℂ) = t ^ z := hb _
    rw [← hbx]
    field_simp
  · change χ x = χ x / χ (τ (sIdeleQuotientNorm F T x))
    rw [hx, map_one, map_one, div_one]

/-- The finitely generated angular support detected on one Mellin line fixes every theta class under the norm-one annihilator of that support. -/
private theorem sLocalMellinSchwartzBounds_meyer_angular_annihilator (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (h : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      ∀ g : (SAdeleRing F T)ˣ, sIdeleQuotientNorm F T (QuotientGroup.mk g) = 1 →
        (∀ η ∈ H, η.val (QuotientGroup.mk g) = 1) → ∀ n, (sLocalAdelicTheta F T).ker.mkQ
          (schwartzBruhatUnitTranslate g (v n)) = (sLocalAdelicTheta F T).ker.mkQ (v n) := by
  obtain ⟨H,hH,hz⟩ := sLocalMellinSchwartzBounds_meyer_one_angular_support T τ v h
  refine ⟨H,hH,fun g hg hker n ↦ ?_⟩
  apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_line T
  funext χ
  let c := chartₜ(T,χ) 1
  have hc := sLocalOrderBound_positive χ (s := 1) (by norm_num)
  change (sLocalIdelicMellin (schwartzBruhatUnitTranslate g (v n))).val ⟨c,hc⟩ = (sLocalIdelicMellin (v n)).val ⟨c,hc⟩
  rw [sLocalIdelicMellin_unitTranslate]
  change c (QuotientGroup.mk g) * sLocalIdelicZFunction (v n) c = sLocalIdelicZFunction (v n) c
  obtain ⟨η,z,hzre,he, hχ⟩ := sLocalMellinSchwartzBounds_meyer_angular_normalization T τ hτ χ
  by_cases hη : η ∈ H
  · have hc1 : c (QuotientGroup.mk g) = 1 := by
      change (χ (QuotientGroup.mk g) : ℂ) * (((sIdeleQuotientNorm F T (QuotientGroup.mk g)).val : ℝ) : ℂ) ^ (1 : ℂ) = 1
      rw [hg, hχ _ hg, hker η hη]; norm_num
    rw [hc1,one_mul]
  · have hpos : 0 < (1+z).re := by simp [hzre]
    have hzeta : sLocalIdelicZFunction (v n) c = 0 := by
      change sLocalIdelicZFunction (v n) (chartₜ(T,χ) 1) = 0
      rw [he, sLocalIdelicZFunction_eq_integral (v n) ⟨η.val,1+z,hpos,rfl⟩,
        ← sLocalThetaMellinIntegral_eq_zeta (v n) ⟨η.val,1+z,hpos,rfl⟩]
      exact hz η hη n _ hpos
    rw [hzeta,mul_zero]


/-- Principal congruence subgroups of a finite product of nonarchimedean unit groups form a neighborhood base at one. -/
private theorem sLocalMellinSchwartzBounds_meyer_product_congruence (T : Finset V) (U : Set (∀ w : T, (w.val.adicCompletion F)ˣ))
    (hU : U ∈ 𝓝 1) : ∃ n : ℕ, ∀ u : (w : T) → (w.val.adicCompletion F)ˣ,
      (∀ w, Valued.v ((u w).val - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) → u ∈ U := by
  change U ∈ 𝓝 (fun w : T ↦ (1 : (w.val.adicCompletion F)ˣ)) at hU
  rw [nhds_pi] at hU
  obtain ⟨I,W,hW,hI⟩ := Filter.mem_pi'.mp hU
  have local_bound (w : T) : ∃ n : ℕ, ∀ x : (w.val.adicCompletion F)ˣ,
      Valued.v (x.val - 1) ≤ WithZero.exp (-(n+1 : ℤ)) → x ∈ W w := by
    let K := w.val.adicCompletion F
    let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
    have hind : IsInducing (Units.val : Kˣ → K) := Units.isEmbedding_val₀.isInducing
    have h := hW w
    rw [hind.nhds_eq_comap 1] at h
    obtain ⟨A,hA,ha⟩ := Filter.mem_comap.mp h
    obtain ⟨γ,hγ⟩ := Valued.mem_nhds.mp hA
    let r := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
    have hr : r ≠ 0 := by simp [r]
    refine ⟨(-WithZero.log r).toNat, fun x hx ↦ ha (hγ ?_)⟩
    apply ν.restrict_lt_iff_lt_embedding.mpr
    refine lt_of_le_of_lt hx ?_
    change _ < r
    exact lt_of_lt_of_eq ((WithZero.exp_lt_exp (b := WithZero.log r)).mpr (by
      have := Int.self_le_toNat (-WithZero.log r)
      omega)) (WithZero.exp_log hr)
  choose k hk using local_bound
  refine ⟨Finset.univ.sup k, fun u hu ↦ hI fun w hw ↦ hk w (u w) ((hu w).trans ?_)⟩
  exact WithZero.exp_le_exp.mpr (by have := Finset.le_sup (f := k) (Finset.mem_univ w); omega)

/-- A finitely generated group of angular characters kills one principal congruence subgroup of the S-local stage. -/
private theorem sLocalMellinSchwartzBounds_meyer_common_angular_conductor (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (H : Subgroup (PontryaginDual.map τ).ker) (hf : H.FG) :
    ∃ n : ℕ, ∀ g : (SAdeleRing F T)ˣ, g.val.1 = 1 →
      (∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(n+1 : ℤ))) →
      ∀ χ ∈ H, χ.val (QuotientGroup.mk g) = 1 := by
  classical
  let X := (w : T) → (w.val.adicCompletion F)ˣ
  let fin : X ≃ₜ* ((w : T) → w.val.adicCompletion F)ˣ := ContinuousMulEquiv.piUnits.symm
  let prod := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((w : T) → w.val.adicCompletion F)
  let raw : X →ₜ* (SAdeleRing F T)ˣ :=
    ⟨prod.symm.toMonoidHom.comp ((MonoidHom.inr _ _).comp fin.toMonoidHom),
      prod.symm.continuous.comp (continuous_const.prodMk fin.continuous)⟩
  let q : (SAdeleRing F T)ˣ →ₜ* SIdeleQuotient F T := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  obtain ⟨S,hS,hfin⟩ := H.fg_iff.mp hf
  let A := Circle.centeredArc (Real.pi / 2)
  have hA : A ∈ 𝓝 (1 : Circle) := by
    simpa [A] using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  have hnear : ∀ᶠ u : X in 𝓝 1, ∀ χ ∈ S, χ.val (q (raw u)) ∈ A :=
    hfin.eventually_all.mpr fun χ _ ↦
      (χ.val.comp (q.comp raw)).continuous.continuousAt.preimage_mem_nhds (x := (1 : X)) (by simpa using hA)
  obtain ⟨n,hn⟩ := sLocalMellinSchwartzBounds_meyer_product_congruence T _ hnear
  obtain ⟨L,_,_,hL⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_groups (F := F) T
  let eval (w : T) : (SAdeleRing F T)ˣ →* (w.val.adicCompletion F)ˣ :=
    Units.map ((Pi.evalRingHom (fun k : T ↦ k.val.adicCompletion F) w).comp (RingHom.snd _ _)).toMonoidHom
  have hsmall (g : (SAdeleRing F T)ˣ) (hg : g ∈ L n) (χ) (hχ : χ ∈ S) : χ.val (q g) ∈ A := by
    obtain ⟨ha,he⟩ := (hL n g).mp hg
    let u : X := fun w ↦ eval w g
    have hraw : raw u = g := Units.ext (Prod.ext ha.symm rfl)
    rw [← hraw]
    exact hn u he χ hχ
  refine ⟨n,fun g ha he ↦ ?_⟩
  have hgens (χ) (hχ : χ ∈ S) : χ.val (q g) = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro m _
    rw [← map_pow,← map_pow]
    exact hsmall (g^m) ((L n).pow_mem ((hL n g).mpr ⟨ha,he⟩) m) χ hχ
  intro χ hχ
  rw [← hS] at hχ
  induction hχ using Subgroup.closure_induction with
  | mem a ha => exact hgens a ha
  | one => rfl
  | mul a b ha hb ia ib =>
    change a.val (QuotientGroup.mk g) * b.val (QuotientGroup.mk g) = 1
    rw [ia,ib,one_mul]
  | inv a ha ia =>
    change (a.val (QuotientGroup.mk g))⁻¹ = 1
    rw [ia,inv_one]


/-- All tests in a single Fréchet subspace are fixed by one principal congruence level. -/
private theorem sLocalMellinSchwartzBounds_meyer_frechet_test_level (T : Finset V) (M : Submodule ℂ (ℬₛ(T))) (hM : IsFrechetTVS M)
    (H : ℕ → Subgroup (SAdeleRing F T)ˣ) (hm : Antitone H)
    (he : ∀ n (g : (SAdeleRing F T)ˣ), g ∈ H n → g.val.1 = 1 ∧
      ∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(n+1 : ℤ))) :
    ∃ k : ℕ, ∀ x : M, ∀ g ∈ H k, unitTranslateEnd g x.val = x.val := by
  let : T2Space ℬₛ(T) := (sAdeleSchwartz_strictLF F T).1
  obtain ⟨hadd,hpoly,hmetr,hcomp⟩ := hM
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace M := hcomp
  let : IsCountablyGenerated (uniformity M) := by
    rw [uniformity_eq_comap_nhds_zero]; infer_instance
  let : BaireSpace M := by
    let := UniformSpace.metricSpace M
    infer_instance
  let L (n : ℕ) : Submodule ℂ M :=
    ⨅ g : H n, ((unitTranslateEnd g.val - LinearMap.id).comp M.subtype).ker
  have hmem (n : ℕ) (x : M) :
      x ∈ L n ↔ ∀ g ∈ H n, unitTranslateEnd g x.val = x.val := by
    simp [L,Submodule.mem_iInf,LinearMap.mem_ker,sub_eq_zero]
  have hclosed (n : ℕ) : IsClosed (L n : Set M) := by
    have eq : (L n : Set M) = ⋂ g : H n, {x : M | unitTranslateEnd g.val x.val = x.val} := by
      ext x; simp [hmem]
    rw [eq]
    refine isClosed_iInter fun g ↦ isClosed_eq ?_ continuous_subtype_val
    exact continuous_sAdeleSchwartz_unitTranslate.comp (continuous_const.prodMk continuous_subtype_val)
  have hcover : (⋃ k : ℕ, (L k : Set M)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨k,hk⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_cover T H hm he x.val
    exact mem_iUnion.mpr ⟨k,(hmem k x).mpr hk⟩
  obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have htop := (L k).eq_top_of_nonempty_interior' hk
  exact ⟨k,fun x ↦ (hmem k x).mp (htop ▸ Submodule.mem_top)⟩

/-- Bounded representatives of a theta family have one common finite congruence level. -/
private theorem sLocalMellinSchwartzBounds_meyer_bounded_representatives_level (T : Finset V) (v : ℕ → ℬₛ(T))
    (h : ∃ A : Set ℬₛ(T), Bornology.IsVonNBounded ℂ A ∧
       (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) ⊆ (sLocalAdelicTheta F T).ker.mkQL '' A) :
    ∃ k : ℕ, ∀ g : (SAdeleRing F T)ˣ, g.val.1 = 1 →
      (∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(k+1 : ℤ))) →
      ∀ n, (sLocalAdelicTheta F T).ker.mkQ (schwartzBruhatUnitTranslate g (v n)) =
        (sLocalAdelicTheta F T).ker.mkQ (v n) := by
  obtain ⟨A,hA,hcov⟩ := h
  obtain ⟨_, L, hL, hF, he, ht⟩ := sAdeleSchwartz_strictLF F T
  let j (n : ℕ) := (L n).subtypeL.codRestrict (L (n + 1)) fun x ↦ hL n.le_succ x.property
  have hj (n : ℕ) : IsEmbedding (j n) :=
    IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal
  have hs : IsInjectiveLCLimit j (fun n ↦ (L n).subtypeL) :=
    ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ (he x).imp fun n hx ↦ ⟨⟨x,hx⟩,rfl⟩, ht⟩
  let : ∀ n, PolynormableSpace ℂ (L n) := fun n ↦ (hF n).2.1
  let : ∀ n, TopologicalSpace.MetrizableSpace (L n) := fun n ↦ (hF n).2.2.1
  have hclosed (n : ℕ) : IsClosedEmbedding (j n) := by
    let : ∀ m, UniformSpace (L m) := fun m ↦ IsTopologicalAddGroup.rightUniformSpace _
    let : ∀ m, IsUniformAddGroup (L m) := fun m ↦ isUniformAddGroup_of_addCommGroup
    let : CompleteSpace (L n) := (hF n).2.2.2
    exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := (j n).toLinearMap.toAddMonoidHom) (hj n)).isClosedEmbedding
  obtain ⟨m,B,hB,hBA⟩ := (isVonNBounded_iff_bounded_stage hs hclosed A).mp hA
  obtain ⟨H,_,hm,hmem⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_groups (F := F) T
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_frechet_test_level T (L m) (hF m) H hm (fun n g ↦ (hmem n g).mp)
  refine ⟨k,fun g ha hfin n ↦ ?_⟩
  obtain ⟨a,haA,heq⟩ := hcov (mem_range_self n)
  obtain ⟨b,hb,rfl⟩ := hBA.symm ▸ haA
  have action (f : ℬₛ(T)) := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 g f
  have hfixed : schwartzBruhatUnitTranslate g b.val = b.val := hk b g ((hmem k g).mpr ⟨ha,hfin⟩)
  change (sLocalAdelicTheta F T).ker.mkQ b.val = (sLocalAdelicTheta F T).ker.mkQ (v n) at heq
  exact (action (v n)).symm.trans
    ((congrArg ((existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose (QuotientGroup.mk g)) heq.symm).trans
      ((action b.val).trans ((congrArg (sLocalAdelicTheta F T).ker.mkQ hfixed).trans heq)))


/-- A common congruence level puts a whole sequence of theta classes in one Fréchet subspace, represented there by a fixed finite family of archimedean Schwartz maps. -/
private theorem sLocalMellinSchwartzBounds_meyer_conductor_stage (T : Finset V) (k : ℕ) (v : ℕ → ℬₛ(T))
    (hfixed : ∀ g : (SAdeleRing F T)ˣ, g.val.1 = 1 →
      (∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(k+1 : ℤ))) →
      ∀ n, (sLocalAdelicTheta F T).ker.mkQ (schwartzBruhatUnitTranslate g (v n)) =
        (sLocalAdelicTheta F T).ker.mkQ (v n)) :
    ∃ M : Submodule ℂ (SLocalAdelicThetaSpace F T), IsFrechetTVS M ∧
      (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) ⊆ M := by
  let θ := sLocalAdelicTheta F T
  let q := θ.ker.mkQ
  have eq (f g : ℬₛ(T)) : q f = q g ↔ θ f = θ g := by
    change Submodule.Quotient.mk f = (Submodule.Quotient.mk g : SLocalAdelicThetaSpace F T) ↔ _
    rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  obtain ⟨d, p, hp⟩ := sLocalAdelicThetaSpace_strictLF_level_generators (F := F) T k
  obtain ⟨M, hM, hstage⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_stage T d p
  refine ⟨M,hM,?_⟩
  rintro _ ⟨n,rfl⟩
  obtain ⟨a,ha⟩ := hp (v n) fun h g hi hfin ↦ by
    have ht := (eq _ _).mp (hfixed h hi hfin n)
    exact ((sAdelePrincipalValue_preserves_thetaKernel_translate h (h*g) (v n)).symm.trans
      (DFunLike.congr_fun ht (h*g))).symm.trans (congrArg (θ (v n)) (inv_mul_cancel_left h g))
  change q (v n) ∈ M
  rw [← (eq _ _).mpr ha]
  exact hstage a


/-- At a fixed angular character the polynomially weighted Mellin integral of a single
test stays bounded on each closed positive strip. -/
private theorem sLocalMellinSchwartzBounds_meyer_radial_strip_test (T : Finset V) (χ : PontryaginDual (SIdeleQuotient F T))
    (f : ℬₛ(T)) (a b : ℝ) (ha : 0 < a) (hab : a < b) (m : ℕ) :
    ∃ B : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖z ^ m * sLocalIdelicZFunction f (chartₜ(T,χ) z)‖ ≤ B := by
  let Z := fun z : ℂ ↦ sLocalIdelicZFunction f (chartₜ(T,χ) z)
  have hc : ContinuousOn Z (Complex.re ⁻¹' Ioi 0) := by
    refine (sLocalIdelicZetaIntegral_analyticOn f χ).continuousOn.congr fun z hz ↦ ?_
    exact sLocalIdelicZFunction_eq_integral f ⟨χ,z,hz,rfl⟩
  obtain ⟨C,hC,htail⟩ := sLocalIdelicZFunction_rapid_decay_on_positive_strip f χ a b ha hab (m+1) (by omega)
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (eventually_comap.mp htail)
  let L := max Y (max 1 b)
  let K := Complex.reProdIm (Icc a b) (Icc (-L) L)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B,hB⟩ := hK.bddAbove_image <| (((continuous_id.pow m).continuousOn).mul
    (hc.mono (show K ⊆ Complex.re ⁻¹' Ioi 0 from fun _ hz ↦ ha.trans_le hz.1.1))).norm
  refine ⟨max B (2 ^ m * C), fun z hz ↦ ?_⟩
  by_cases hy : |z.im| ≤ L
  · exact (hB (mem_image_of_mem _ (show z ∈ K from ⟨hz,abs_le.mp hy⟩))).trans (le_max_left _ _)
  have hL := (lt_of_not_ge hy).le
  have h1 : 1 ≤ |z.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hypos : 0 < |z.im| := zero_lt_one.trans_le h1
  have hdec := hY |z.im| ((le_max_left _ _).trans hL) z.im rfl z.re hz
  rw [Complex.re_add_im] at hdec
  have hnorm : ‖z‖ ≤ 2 * |z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_nonneg (ha.le.trans hz.1)]
    linarith [hz.2.trans ((le_max_right 1 b).trans ((le_max_right Y _).trans hL))]
  apply le_trans _ (le_max_right _ _)
  rw [norm_mul,norm_pow]
  calc
    _ ≤ (2 * |z.im|) ^ m * (C / |z.im| ^ m) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (hdec.trans
        (div_le_div_of_nonneg_left hC.le (pow_pos hypos _) (pow_le_pow_right₀ h1 (by omega))))
        (norm_nonneg _) (by positivity)
    _ = 2 ^ m * C := by rw [mul_pow]; field_simp

/-- Uniform boundedness upgrades every pointwise bounded family of weighted Mellin
evaluations to a simultaneous bound over the family and a bounded set of theta classes. -/
private theorem sLocalMellinSchwartzBounds_meyer_bounded_mellin_evaluations (T : Finset V) {ι : Type*}
    (χ : ι → PontryaginDual (SIdeleQuotient F T)) (z w : ι → ℂ) (hz : ∀ i, 0 < (z i).re)
    (pointwise : ∀ f : ℬₛ(T), ∃ B : ℝ, ∀ i,
      ‖w i * sLocalThetaMellinIntegral f (chartₜ(T,χ i) (z i))‖ ≤ B)
    (v : ℕ → ℬₛ(T))
    (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))) :
    ∃ B : ℝ, ∀ n i, ‖w i * sLocalThetaMellinIntegral (v n) (chartₜ(T,χ i) (z i))‖ ≤ B := by
  let Q := SLocalAdelicThetaSpace F T
  let : BarrelledSpace ℂ Q := sLocalAdelicThetaSpace_barrelled
  let : PolynormableSpace ℂ Q := sLocalAdelicThetaSpace_polynormable
  let c : Continuous (sLocalThetaMellin (F := F) (S := T)) :=
    (sLocalAdelicTheta F T).ker.isQuotientMap_mkQ.continuous_iff.mpr sLocalIdelicMellin_continuous
  let E (i : ι) : Q →L[ℂ] ℂ := w i • ((ContinuousMap.evalCLM ℂ
    ⟨chartₜ(T,χ i) (z i), sLocalOrderBound_positive (χ i) (hz i)⟩).comp
      ((Submodule.subtypeL _).comp ⟨sLocalThetaMellin,c⟩))
  have he (f : ℬₛ(T)) (i : ι) : E i ((sLocalAdelicTheta F T).ker.mkQ f) =
      w i * sLocalThetaMellinIntegral f (chartₜ(T,χ i) (z i)) := by
    change w i * sLocalIdelicZFunction f _ = _
    rw [sLocalThetaMellinIntegral_eq_zeta _ ⟨χ i,z i,hz i,rfl⟩,
      ← sLocalIdelicZFunction_eq_integral _ ⟨χ i,z i,hz i,rfl⟩]
  let p (i : ι) : Seminorm ℂ Q := (normSeminorm ℂ ℂ).comp (E i).toLinearMap
  have hp : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr fun x ↦ by
    obtain ⟨f,rfl⟩ := (sLocalAdelicTheta F T).ker.mkQ_surjective x
    obtain ⟨B,hB⟩ := pointwise f
    refine ⟨B,forall_mem_range.mpr fun i ↦ ?_⟩
    change ‖E i _‖ ≤ B
    exact (he f i).symm ▸ hB i
  let P : Seminorm ℂ Q := ⨆ i, p i
  have hP : Continuous P := by
    simpa only [P,Seminorm.coe_iSup_eq hp] using
      Seminorm.continuous_iSup p (fun i ↦ (E i).continuous.norm) hp
  obtain ⟨B,_,hB⟩ := (PolynormableSpace.withSeminorms ℂ Q).isVonNBounded_iff_seminorm_bounded.mp hv ⟨P,hP⟩
  refine ⟨B,fun n i ↦ ?_⟩
  rw [← he]
  exact ((le_ciSup hp i) ((sLocalAdelicTheta F T).ker.mkQ (v n))).trans (hB _ (mem_range_self n)).le

/-- At a fixed angular character the polynomially weighted vertical-strip estimates
are simultaneous over a bounded family of theta classes. -/
private theorem sLocalMellinSchwartzBounds_meyer_radial_strip (T : Finset V) (χ : PontryaginDual (SIdeleQuotient F T))
    (v : ℕ → ℬₛ(T))
    (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m : ℕ) :
    ∃ B : ℝ, ∀ n (z : ℂ), z.re ∈ Icc a b →
      ‖z ^ m * sLocalThetaMellinIntegral (v n) (chartₜ(T,χ) z)‖ ≤ B := by
  let J := {z : ℂ // z.re ∈ Icc a b}
  have pointwise (f : ℬₛ(T)) : ∃ B : ℝ, ∀ i : J,
      ‖i.val ^ m * sLocalThetaMellinIntegral f (chartₜ(T,χ) i.val)‖ ≤ B := by
    obtain ⟨B,hB⟩ := sLocalMellinSchwartzBounds_meyer_radial_strip_test T χ f a b ha hab m
    refine ⟨B,fun i ↦ ?_⟩
    rw [sLocalThetaMellinIntegral_eq_zeta _ ⟨χ,i.val,ha.trans_le i.property.1,rfl⟩,
      ← sLocalIdelicZFunction_eq_integral _ ⟨χ,i.val,ha.trans_le i.property.1,rfl⟩]
    exact hB i.val i.property
  obtain ⟨B,hB⟩ := sLocalMellinSchwartzBounds_meyer_bounded_mellin_evaluations T (fun _ : J ↦ χ) (fun i ↦ i.val) (fun i ↦ i.val ^ m)
    (fun i ↦ ha.trans_le i.property.1) pointwise v hv
  exact ⟨B,fun n z hz ↦ hB n ⟨z,hz⟩⟩

/-- At fixed weight a bounded theta family satisfies every polynomially weighted
Mellin estimate on each finite angular subgroup. Only the supremum across infinitely
many characters requires an estimate beyond the radial strip bounds. -/
private theorem sLocalMellinSchwartzBounds_meyer_finite_angular_estimates (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (v : ℕ → ℬₛ(T)) (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)))
    (a : ℝ) (ha : 0 < a) (H : Subgroup (PontryaginDual.map τ).ker) [Finite H]
    (p : GroupSeminorm H) (k m : ℕ) : ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
      (1 + p χ) ^ k * ‖z ^ m * sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val.val) z)‖ ≤ B := by
  classical
  let : Fintype H := Fintype.ofFinite H
  choose B hB using fun χ : H ↦ sLocalMellinSchwartzBounds_meyer_radial_strip T χ.val.val v hv a (a+1) ha (by linarith) m
  let W (χ : H) := (1 + p χ) ^ k * max (B χ) 0
  refine ⟨∑ χ : H, W χ, fun χ n z hz ↦ ?_⟩
  have hp : 0 ≤ (1 + p χ) ^ k := pow_nonneg (by linarith [apply_nonneg p χ]) _
  have h := hB χ n z (show z.re ∈ Icc a (a+1) from ⟨hz.ge,by linarith⟩)
  exact (mul_le_mul_of_nonneg_left (h.trans (le_max_left _ _)) hp).trans
    (Finset.single_le_sum (f := W) (fun η _ ↦ mul_nonneg
      (pow_nonneg (by linarith [apply_nonneg p η]) _) (le_max_right _ _)) (Finset.mem_univ χ))


/-- Extend weighted line estimates by zero from a subgroup to a larger subgroup. -/
private theorem sLocalMellinSchwartzBounds_meyer_enlarge_weights {D : Type*} [CommGroup D] (Z : ℕ → D → ℂ → ℂ)
    (J K : Subgroup D) (iJK : J ≤ K) (a : ℝ)
    (hs : ∀ χ ∉ J, ∀ n (z : ℂ), z.re = a → Z n χ z = 0)
    (hw : ∀ (p : GroupSeminorm J) (k m : ℕ), ∃ B : ℝ, ∀ (χ : J) n (z : ℂ), z.re = a →
      (1 + p χ) ^ k * ‖z ^ m * Z n χ.val z‖ ≤ B) (p : GroupSeminorm K) (k m : ℕ) :
    ∃ B : ℝ, ∀ i : K × ℕ, ∀ z : ℂ, z.re = a → (1+p i.1)^k * ‖z^m*Z i.2 i.1.val z‖ ≤ B := by
  obtain ⟨B,hB⟩ := hw (p.comp (Subgroup.inclusion iJK)) k m
  refine ⟨max B 0,fun i z hz ↦ ?_⟩
  by_cases hj : i.1.val ∈ J
  · exact (hB ⟨i.1.val,hj⟩ i.2 z hz).trans (le_max_left _ _)
  · rw [hs _ hj i.2 z hz,mul_zero,norm_zero,mul_zero]
    exact le_max_right _ _

/-- On the zeta chart, line estimates at the two neighboring weights imply Cauchy's
bound on each derivative at the middle weight. -/
private theorem sLocalMellinSchwartzBounds_meyer_zeroth_zeta (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (v : ℕ → ℬₛ(T))
    (h : ∀ a : ℝ, 1 < a → ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → sLocalIdelicZFunction (v n) (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalIdelicZFunction (v n) (chartₜ(T,χ.val.val) z)‖ ≤ B) :
    sLocalMellinSchwartzBounds T τ v := by
  intro a ha
  let d := (a-1)/2
  have hd : 0 < d := half_pos (sub_pos.mpr ha)
  have hl : 1 < a-d := by dsimp [d]; linarith
  have hr : 1 < a+d := by linarith
  obtain ⟨H,hH,hs,_⟩ := h a ha
  obtain ⟨L,hL,hls,hlw⟩ := h (a-d) hl
  obtain ⟨R,hR,hrs,hrw⟩ := h (a+d) hr
  let K := H ⊔ (L ⊔ R)
  let Z (n : ℕ) (χ : (PontryaginDual.map τ).ker) (z : ℂ) := sLocalIdelicZFunction (v n) (chartₜ(T,χ.val) z)
  have hHK : H ≤ K := le_sup_left
  have hLK : L ≤ K := le_sup_left.trans (le_sup_right (a := H))
  have hRK : R ≤ K := le_sup_right.trans (le_sup_right (a := H))
  refine ⟨K,hH.sup (hL.sup hR),fun χ hχ ↦ hs χ (fun hx ↦ hχ (hHK hx)),?_⟩
  intro p k m j
  obtain ⟨B,hB⟩ := sLocalMellinSchwartzBounds_derivatives T (fun i : K × ℕ ↦ v i.2)
    (fun i ↦ i.1.val.val) (fun i ↦ (1+p i.1)^k) (fun i ↦ pow_nonneg (by linarith [apply_nonneg p i.1]) _)
    m j a d hd hl (by
      rintro u (rfl | rfl)
      · exact sLocalMellinSchwartzBounds_meyer_enlarge_weights Z L K hLK _ hls hlw p k m
      · exact sLocalMellinSchwartzBounds_meyer_enlarge_weights Z R K hRK _ hrs hrw p k m)
  exact ⟨B,fun χ n ↦ hB (χ,n)⟩

/-- Zeroth-order angular estimates on a line depend only on the restriction to that line. -/
private theorem sLocalMellinSchwartzBounds_meyer_change_values {D : Type*} [CommGroup D] (Z W : ℕ → D → ℂ → ℂ) (a : ℝ)
    (he : ∀ n χ z, z.re = a → Z n χ z = W n χ z)
    (h : ∃ H : Subgroup D, H.FG ∧ (∀ χ ∉ H, ∀ n z, z.re = a → W n χ z = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n z, z.re = a → (1+p χ)^k * ‖z^m*W n χ.val z‖ ≤ B) :
    ∃ H : Subgroup D, H.FG ∧ (∀ χ ∉ H, ∀ n z, z.re = a → Z n χ z = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n z, z.re = a → (1+p χ)^k * ‖z^m*Z n χ.val z‖ ≤ B := by
  obtain ⟨H,hH,hs,hw⟩ := h
  refine ⟨H,hH,fun χ hχ n z hz ↦ (he n χ z hz).trans (hs χ hχ n z hz),fun p k m ↦ ?_⟩
  obtain ⟨B,hB⟩ := hw p k m
  refine ⟨B,fun χ n z hz ↦ ?_⟩
  rw [he n χ.val z hz]
  exact hB χ n z hz

/-- Unfolding the single-test zeta integral on a positive norm-twist chart. -/
private theorem sLocalMellinSchwartzBounds_meyer_zeta_equals_theta (T : Finset V) (f : ℬₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T))
    (z : ℂ) (hp : 0 < z.re) : sLocalIdelicZFunction f (chartₜ(T,χ) z) = sLocalThetaMellinIntegral f (chartₜ(T,χ) z) :=
  (sLocalIdelicZFunction_eq_integral _ ⟨χ,z,hp,rfl⟩).trans (sLocalThetaMellinIntegral_eq_zeta _ ⟨χ,z,hp,rfl⟩).symm

/-- Weighted Mellin values on all positive weight lines greater than one suffice for
the full Schwartz bounds, including all radial derivatives. -/
private theorem sLocalMellinSchwartzBounds_meyer_zeroth_iff (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (v : ℕ → ℬₛ(T)) :
    sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral ↔
    ∀ a : ℝ, 1 < a → ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
        (1 + p χ) ^ k * ‖z ^ m * sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val.val) z)‖ ≤ B := by
  constructor
  · intro h a ha
    obtain ⟨H,hH,hs,hp⟩ := h a ha
    refine ⟨H,hH,hs,fun p k m ↦ ?_⟩
    simpa only [iteratedDeriv_zero] using hp p k m 0
  intro h
  apply (sLocalMellinSchwartzBounds_unfold T τ v).mpr
  apply sLocalMellinSchwartzBounds_meyer_zeroth_zeta T τ v
  intro a ha
  let Z (n : ℕ) (χ : (PontryaginDual.map τ).ker) (z : ℂ) := sLocalIdelicZFunction (v n) (chartₜ(T,χ.val) z)
  let W (n : ℕ) (χ : (PontryaginDual.map τ).ker) (z : ℂ) := sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val) z)
  exact sLocalMellinSchwartzBounds_meyer_change_values Z W a (fun n χ z hz ↦ sLocalMellinSchwartzBounds_meyer_zeta_equals_theta T (v n) χ.val z
    (show 0 < z.re by rw [hz]; exact zero_lt_one.trans ha)) (h a ha)


/-- The angular support of a Mellin-bounded sequence implies invariance of all theta classes at one fixed principal congruence level. -/
private theorem sLocalMellinSchwartzBounds_meyer_mellin_bounds_level (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (h : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral) :
    ∃ k : ℕ, ∀ g : (SAdeleRing F T)ˣ, g.val.1 = 1 →
      (∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(k+1 : ℤ))) →
      ∀ n, (sLocalAdelicTheta F T).ker.mkQ (schwartzBruhatUnitTranslate g (v n)) =
        (sLocalAdelicTheta F T).ker.mkQ (v n) := by
  obtain ⟨H,hH,hfix⟩ := sLocalMellinSchwartzBounds_meyer_angular_annihilator T τ hτ v h
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_common_angular_conductor T τ H hH
  refine ⟨k,fun g ha hf ↦ hfix g ?_ (hk g ha hf)⟩
  apply Units.ext
  apply NNReal.coe_injective
  let ev : (((SAdeleRing F T)ˣ →* ℝ≥0ˣ) →* ℝ) := NNReal.toRealHom.toMonoidHom.comp
    ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g))
  change ev (sIdeleNorm F T) = 1
  simp only [sIdeleNorm, map_mul, map_prod]
  change (∏ v : InfinitePlace F, ‖g.val.1 v‖ ^ v.mult) * ∏ w : T, ‖g.val.2 w‖ = 1
  have hone (w : T) : ‖g.val.2 w‖ = 1 := by
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    have he : WithZero.exp (-(k+1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    simpa only [add_sub_cancel] using Valued.v.map_one_add_of_lt ((hf w).trans_lt he)
  have eone (w : InfinitePlace F) : (1 : InfiniteAdeleRing F) w = 1 := rfl
  simp [ha,hone,eone]

/-- The topological bornology of the theta quotient is exactly its bounded-lift bornology. -/
private theorem sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded (T : Finset V) (v : ℕ → ℬₛ(T)) :
    (∃ A : Set ℬₛ(T), Bornology.IsVonNBounded ℂ A ∧
      (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) ⊆ (sLocalAdelicTheta F T).ker.mkQL '' A) ↔
      Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) := by
  constructor
  · rintro ⟨A,hB,hcov⟩
    exact (hB.image (sLocalAdelicTheta F T).ker.mkQL).subset hcov
  · intro hb
    let : T2Space (SLocalAdelicThetaSpace F T) := sLocalAdelicThetaSpace_strictLF.1
    obtain ⟨_, L, hL, hF, he, ht⟩ := sAdeleSchwartz_strictLF F T
    let j (n : ℕ) := (L n).subtypeL.codRestrict (L (n + 1)) fun x ↦ hL n.le_succ x.property
    have hj (n : ℕ) : IsEmbedding (j n) :=
      IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal
    have hs : IsInjectiveLCLimit j (fun n ↦ (L n).subtypeL) :=
      ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ (he x).imp fun n hx ↦ ⟨⟨x,hx⟩,rfl⟩, ht⟩
    have hN : IsNuclearTVS.{0} ℬₛ(T) := sAdeleSchwartz_nuclear F T
    exact (liftsBoundedSets_quotient_of_nuclear_strictLF hs hj hF
      (fun n ↦ isNuclearTVS_submodule hN (L n)) (sLocalAdelicTheta F T).ker sLocalAdelicTheta_ker_isClosed
      sLocalAdelicThetaSpace_strictLF sLocalAdelicThetaSpace_nuclear).1 _ hb





/-- The Fourier classes of a bounded theta family are bounded. On the kernel, the
reflected Mellin comparison gives zero on a line, hence on the positive half-plane.
This uses the comparison already available in this file. -/
private theorem sLocalMellinSchwartzBounds_meyer_fourier_bounded (T : Finset V) (v : ℕ → ℬₛ(T))
    (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (sAdeleSchwartzFourier (v n))) := by
  let K := (sLocalAdelicTheta F T).ker
  obtain ⟨E,hE⟩ := sLocal_fourier_continuousLinear (F := F) (S := T)
  have hker : K ≤ (K.mkQ.comp E.toLinearMap).ker := by
    intro f hf
    have hq : K.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hf
    have hz (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ)
        (hr : 0 ≤ sLocalIdelicOrderBound (chartₜ(T,χ) z)) : sLocalIdelicZFunction f (chartₜ(T,χ) z) = 0 := by
      have e := congrArg (fun x : SLocalAdelicThetaSpace F T ↦ (sLocalThetaMellin x).val ⟨chartₜ(T,χ) z,hr⟩) hq
      change sLocalIdelicZFunction f (chartₜ(T,χ) z) = (sLocalThetaMellin 0).val _ at e
      rw [map_zero] at e
      exact e
    have hzF (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ) (hp : 0 < z.re) :
        sLocalThetaMellinIntegral (E f) (chartₜ(T,χ) z) = 0 := by
      refine sLocalMellinSchwartzBounds_meyer_line_support _ (sLocalThetaMellinIntegral_analyticOn (E f) χ) 2 (by norm_num) (fun s hs ↦ ?_) z hp
      have hpos : 0 < s.re := by rw [hs]; norm_num
      have H := sLocalMellinSchwartzBounds_fourier T 0 f 2 0 (by norm_num)
        (fun η w _ hw ↦ by rw [hz η w hw,norm_zero,zero_mul]) χ s hs
      have he : sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chartₜ(T,χ) s) = 0 := norm_le_zero_iff.mp (by simpa only [zero_mul] using H)
      rw [hE,sLocalThetaMellinIntegral_eq_zeta _ ⟨χ,s,hpos,rfl⟩,← sLocalIdelicZFunction_eq_integral _ ⟨χ,s,hpos,rfl⟩,he]
    change K.mkQ (E f) = 0
    apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_line T
    funext χ
    have hpos : 0 < (1 : ℂ).re := by norm_num
    change sLocalIdelicZFunction (E f) (chartₜ(T,χ) 1) = (sLocalThetaMellin 0).val _
    rw [map_zero]
    change _ = 0
    rw [sLocalIdelicZFunction_eq_integral _ ⟨χ,1,hpos,rfl⟩,← sLocalThetaMellinIntegral_eq_zeta _ ⟨χ,1,hpos,rfl⟩]
    exact hzF χ 1 hpos
  let D := K.liftQ (K.mkQ.comp E.toLinearMap) hker
  have hD : Continuous D := K.isQuotientMap_mkQ.continuous_iff.mpr (K.mkQL.continuous.comp E.continuous)
  refine (hv.image (ContinuousLinearMap.mk D hD)).subset ?_
  rintro _ ⟨n,rfl⟩
  exact ⟨_,mem_range_self n,congrArg K.mkQ (hE (v n))⟩

/-- Over a number field of degree one a principal congruence subgroup is open inside the norm-one
ideles. If its finite coordinates are near one, they have norm one. At the unique
real place, a positive coordinate of absolute value one equals one. -/
private theorem sLocalMellinSchwartzBounds_meyer_degree_one_level_open (T : Finset V) (hF : Module.finrank ℚ F = 1) (k : ℕ)
    (L : Subgroup (SAdeleRing F T)ˣ)
    (hL : ∀ g : (SAdeleRing F T)ˣ, g ∈ L ↔ g.val.1 = 1 ∧
      ∀ w : T, Valued.v (g.val.2 w-1) ≤ WithZero.exp (-(k+1 : ℤ))) :
    IsOpen ((L.comap (sIdeleNorm F T).ker.subtype : Subgroup (sIdeleNorm F T).ker) : Set (sIdeleNorm F T).ker) := by
  classical
  let P := (sIdeleNorm F T).ker
  have hdeg := (InfinitePlace.card_add_two_mul_card_eq_rank F).trans hF
  have hzero : InfinitePlace.nrComplexPlaces F = 0 := by omega
  let : Subsingleton (InfinitePlace F) := Fintype.card_le_one_iff_subsingleton.mp (by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega)
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hw : w.IsReal := (InfinitePlace.isReal_or_isComplex w).resolve_right fun h ↦ by
    have : 0 < InfinitePlace.nrComplexPlaces F := Fintype.card_pos_iff.mpr ⟨⟨w,h⟩⟩
    omega
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ei := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  have hcont : Continuous fun g : P ↦ e (g.val.val.1 w) :=
    ei.continuous.comp ((continuous_apply w).comp (continuous_fst.comp (Units.continuous_val.comp continuous_subtype_val)))
  have ha : ∀ᶠ g : P in 𝓝 1, 0 < e (g.val.val.1 w) := by
    exact (isOpen_lt continuous_const hcont).mem_nhds (by change 0 < e 1; rw [map_one]; exact zero_lt_one)
  have hfin (v : T) : ∀ᶠ g : P in 𝓝 1, Valued.v (g.val.val.2 v-1) ≤ WithZero.exp (-(k+1 : ℤ)) := by
    obtain ⟨z,hz⟩ := v.val.valuedAdicCompletion_surjective F (WithZero.exp (-(k+1 : ℤ)))
    have hz0 : z ≠ 0 := fun he ↦ by subst z; simp at hz
    have hc : Continuous fun g : P ↦ ‖g.val.val.2 v-1‖ :=
      (((continuous_apply v).comp (continuous_snd.comp (Units.continuous_val.comp continuous_subtype_val))).sub
        continuous_const).norm
    have h : ∀ᶠ g : P in 𝓝 1, ‖g.val.val.2 v-1‖ < ‖z‖ :=
      (isOpen_lt hc continuous_const).mem_nhds (by
        change ‖(1 : v.val.adicCompletion F) - 1‖ < ‖z‖
        rw [sub_self,norm_zero]
        exact norm_pos_iff.mpr hz0)
    exact h.mono fun g hg ↦ hz ▸ Valued.toNormedField.norm_le_iff.mp hg.le
  have hall : ∀ᶠ g : P in 𝓝 1, ∀ v : T, Valued.v (g.val.val.2 v-1) ≤ WithZero.exp (-(k+1 : ℤ)) :=
    Filter.eventually_all.mpr hfin
  apply Subgroup.isOpen_of_mem_nhds
  filter_upwards [ha,hall] with g hg hf
  apply (hL g.val).mpr
  refine ⟨?_,hf⟩
  have hone (v : T) : ‖g.val.val.2 v‖ = 1 := by
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    have hn : WithZero.exp (-(k+1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    simpa only [add_sub_cancel] using Valued.v.map_one_add_of_lt ((hf v).trans_lt hn)
  have hn := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (MonoidHom.mem_ker.mp g.property)
  let ev : (((SAdeleRing F T)ˣ →* ℝ≥0ˣ) →* ℝ) := NNReal.toRealHom.toMonoidHom.comp
    ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g.val))
  change ev (sIdeleNorm F T) = 1 at hn
  simp only [sIdeleNorm,map_mul,map_prod] at hn
  change (∏ v : InfinitePlace F, ‖g.val.val.1 v‖ ^ v.mult) * ∏ v : T, ‖g.val.val.2 v‖ = 1 at hn
  rw [Fintype.prod_subsingleton _ w,hw.mult_eq_one,pow_one] at hn
  simp only [hone,Finset.prod_const_one,mul_one] at hn
  have hnorm : ‖e (g.val.val.1 w)‖ = ‖g.val.val.1 w‖ := ei.isometry.norm_map_of_map_zero (map_zero e) _
  rw [hn,Real.norm_eq_abs,abs_of_pos hg] at hnorm
  funext v
  rw [Subsingleton.elim v w]
  exact e.injective (hnorm.trans (map_one e).symm)

/-- The image of the degree-one congruence subgroup in the norm-one quotient is
open. Members lift to actual principal congruence ideles of norm one. -/
private theorem sLocalMellinSchwartzBounds_meyer_degree_one_open_quotient (T : Finset V) (hF : Module.finrank ℚ F = 1) (k : ℕ) :
    ∃ D : Subgroup (sIdeleQuotientNorm F T).ker, IsOpen (D : Set (sIdeleQuotientNorm F T).ker) ∧
      ∀ d ∈ D, ∃ g : (SAdeleRing F T)ˣ, (QuotientGroup.mk g : SIdeleQuotient F T) = d.val ∧
        g.val.1 = 1 ∧ ∀ w : T, Valued.v (g.val.2 w-1) ≤ WithZero.exp (-(k+1 : ℤ)) := by
  obtain ⟨L,_,_,hL⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_groups (F := F) T
  let P := (sIdeleNorm F T).ker
  let N := (sIdeleQuotientNorm F T).ker
  let q : (SAdeleRing F T)ˣ →* SIdeleQuotient F T := QuotientGroup.mk' _
  let r : P →* N := {
    toFun g := ⟨q g.val,g.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let U := (L k).comap P.subtype
  have hopen : IsOpen (U : Set P) := sLocalMellinSchwartzBounds_meyer_degree_one_level_open T hF k (L k) (hL k)
  have hro : IsOpenMap r := (QuotientGroup.isOpenMap_coe (N := _)).restrictPreimage (N : Set (SIdeleQuotient F T))
  refine ⟨U.map r,hro _ hopen,?_⟩
  rintro _ ⟨g,hg,rfl⟩
  exact ⟨g.val,rfl,(hL k g.val).mp hg⟩


/-- The angular characters trivial on an open subgroup of the compact norm-one
group form a finite subgroup. Restriction embeds them in the character group of
the finite quotient, since an angular character is already trivial on the section. -/
private theorem sLocalMellinSchwartzBounds_meyer_finite_annihilator (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (D : Subgroup (sIdeleQuotientNorm F T).ker)
    (ho : IsOpen (D : Set (sIdeleQuotientNorm F T).ker)) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, Finite H ∧
      ∀ χ, χ ∈ H ↔ ∀ x ∈ D, χ.val x.val = 1 := by
  classical
  let N := (sIdeleQuotientNorm F T).ker
  let : IsMulCommutative N := .of_comm fun a b ↦ Subtype.ext (mul_comm a.val b.val)
  let A := (PontryaginDual.map τ).ker
  let H : Subgroup A := {
    carrier := {χ | ∀ x ∈ D, χ.val x.val = 1}
    one_mem' := fun _ _ ↦ rfl
    mul_mem' := fun {a b} ha hb x hx ↦ by
      change a.val x.val * b.val x.val = 1
      rw [ha x hx,hb x hx,one_mul]
    inv_mem' := fun {a} ha x hx ↦ by
      change (a.val x.val)⁻¹ = 1
      rw [ha x hx,inv_one] }
  have : CompactSpace N := isCompact_iff_compactSpace.mp
    (show IsCompact ((sIdeleQuotientNorm F T) ⁻¹' ({1} : Set ℝ≥0ˣ)) from
      (isProperMap_sIdeleQuotientNorm F T).isCompact_preimage isCompact_singleton)
  have : Finite (N ⧸ D) := Subgroup.quotient_finite_of_isOpen D ho
  let : Fintype (Additive (N ⧸ D)) := Fintype.ofFinite _
  let r (χ : H) := QuotientGroup.lift D (χ.val.val.toMonoidHom.comp N.subtype)
    (show D ≤ (χ.val.val.toMonoidHom.comp N.subtype).ker from fun x hx ↦ χ.property x hx)
  let c (χ : H) : AddChar (Additive (N ⧸ D)) ℂ :=
    AddChar.toMonoidHomEquiv.symm (Circle.coeHom.comp (r χ))
  have hs (χ : A) (t : ℝ≥0ˣ) : χ.val (τ t) = 1 :=
    DFunLike.congr_fun (MonoidHom.mem_ker.mp χ.property) t
  refine ⟨H,Finite.of_injective c ?_,fun _ ↦ Iff.rfl⟩
  intro χ ψ he
  apply Subtype.ext
  apply Subtype.ext
  apply PontryaginDual.ext
  intro x
  let t := sIdeleQuotientNorm F T x
  let y : N := ⟨x / τ t,by
    change sIdeleQuotientNorm F T (x / τ t) = 1
    rw [map_div,hτ t,div_self' (sIdeleQuotientNorm F T x)]⟩
  have hy : χ.val.val y.val = ψ.val.val y.val := Circle.ext
    (DFunLike.congr_fun he (Additive.ofMul (QuotientGroup.mk y)))
  change χ.val.val (x / τ t) = ψ.val.val (x / τ t) at hy
  simpa only [map_div,hs,div_one] using hy

/-- A bounded degree-one theta family has finite angular support for every finite set
of places: the level subgroup is open in the compact norm-one quotient. -/
private theorem sLocalMellinSchwartzBounds_meyer_degree_one_angular_support (T : Finset V) (hF : Module.finrank ℚ F = 1)
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
    (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, Finite H ∧
      ∀ χ ∉ H, ∀ n (z : ℂ), 0 < z.re →
        sLocalThetaMellinIntegral (v n) (quasiCharacterNormTwist (sIdeleQuotientNorm F T)
          (isProperMap_sIdeleQuotientNorm F T).continuous
          ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ.val) z) = 0 := by
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_bounded_representatives_level T v ((sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded T v).mpr hv)
  obtain ⟨D,ho,hd⟩ := sLocalMellinSchwartzBounds_meyer_degree_one_open_quotient T hF k
  obtain ⟨H,hF,hH⟩ := sLocalMellinSchwartzBounds_meyer_finite_annihilator T τ hτ D ho
  refine ⟨H,hF,fun χ hχ n z hz ↦ ?_⟩
  have hx := not_forall.mp (fun h ↦ hχ ((hH χ).mpr h))
  obtain ⟨d,hdh⟩ := hx
  obtain ⟨hmem,hne⟩ := not_imp.mp hdh
  obtain ⟨g,hg,ha,hf⟩ := hd d hmem
  let c := quasiCharacterNormTwist (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
    ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ.val) z
  have hnorm : sIdeleQuotientNorm F T (QuotientGroup.mk g) = 1 := by rw [hg]; exact d.property
  have hc : c (QuotientGroup.mk g) ≠ 1 := by
    change (χ.val (QuotientGroup.mk g) : ℂ) *
      (((sIdeleQuotientNorm F T (QuotientGroup.mk g)).val : ℝ) : ℂ) ^ z ≠ 1
    rw [hnorm,hg]
    simpa only [Units.val_one,NNReal.coe_one,Complex.ofReal_one,Complex.one_cpow,mul_one] using
      (show (χ.val d.val : ℂ) ≠ 1 from fun h ↦ hne (Circle.ext h))
  have hreg : 0 ≤ sLocalIdelicOrderBound c := sLocalOrderBound_positive χ.val hz
  have he := congrArg (fun x : SLocalAdelicThetaSpace F T ↦ (sLocalThetaMellin x).val ⟨c,hreg⟩)
    (hk g ha hf n)
  change (sLocalIdelicMellin (schwartzBruhatUnitTranslate g (v n))).val ⟨c,hreg⟩ =
    (sLocalIdelicMellin (v n)).val ⟨c,hreg⟩ at he
  rw [sLocalIdelicMellin_unitTranslate] at he
  change c (QuotientGroup.mk g) * sLocalIdelicZFunction (v n) c = sLocalIdelicZFunction (v n) c at he
  have hzero : sLocalIdelicZFunction (v n) c = 0 := by
    by_contra hn
    exact hc (mul_right_cancel₀ hn (he.trans (one_mul _).symm))
  rw [sLocalThetaMellinIntegral_eq_zeta _ ⟨χ.val,z,hz,rfl⟩,
    ← sLocalIdelicZFunction_eq_integral _ ⟨χ.val,z,hz,rfl⟩]
  exact hzero

/-- The forward half of Meyer's criterion holds over all number fields of degree one and every finite set of places. -/
private theorem sLocalMellinSchwartzBounds_meyer_degree_one_forward (T : Finset V) (hF : Module.finrank ℚ F = 1)
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
    (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))) :
    sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral ∧
      sLocalMellinSchwartzBounds T τ (fun n ↦ sAdeleSchwartzFourier (v n)) sLocalThetaMellinIntegral := by
  have forward (f : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
      (hf : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (f n))) :
      sLocalMellinSchwartzBounds T τ f sLocalThetaMellinIntegral := by
    obtain ⟨H,hfin,hs⟩ := sLocalMellinSchwartzBounds_meyer_degree_one_angular_support T hF τ hτ f hf
    apply (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ f).mpr
    intro a ha
    exact ⟨H,(Group.fg_iff_subgroup_fg H).mp (Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite),fun χ hχ n z hz ↦ hs χ hχ n z (hz ▸ zero_lt_one.trans ha),
      sLocalMellinSchwartzBounds_meyer_finite_angular_estimates T τ f hf a (zero_lt_one.trans ha) H⟩
  exact ⟨forward v hv,forward _ (sLocalMellinSchwartzBounds_meyer_fourier_bounded T v hv)⟩


/-- One angular Mellin line separates all theta classes. On a finite-dimensional
subspace, pointwise boundedness on this line already implies boundedness of the
original sequence. -/
private theorem sLocalMellinSchwartzBounds_meyer_finite_span_inverse (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (hspan : FiniteDimensional ℂ (Submodule.span ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))))
    (hval : ∀ (χ : (PontryaginDual.map τ).ker) (z : ℂ), z.re = 2 →
      ∃ B : ℝ, ∀ n, ‖sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val) z)‖ ≤ B) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) := by
  let Q := SLocalAdelicThetaSpace F T
  let q := (sLocalAdelicTheta F T).ker.mkQ
  let M := Submodule.span ℂ (range fun n ↦ q (v n))
  let x (n : ℕ) : M := ⟨q (v n),Submodule.subset_span (mem_range_self n)⟩
  let J := (PontryaginDual.map τ).ker × {z : ℂ // z.re = 2}
  let ev (i : J) : Q →ₗ[ℂ] ℂ := ((ContinuousMap.evalCLM ℂ
    ⟨chartₜ(T,i.1.val) i.2.val, sLocalOrderBound_positive i.1.val (by rw [i.2.property]; norm_num)⟩).toLinearMap.comp
      ((Submodule.subtype _).comp sLocalThetaMellin))
  let E : M →ₗ[ℂ] (J → ℂ) := LinearMap.pi fun i ↦ (ev i).comp M.subtype
  have he (f : ℬₛ(T)) (i : J) : ev i (q f) = sLocalThetaMellinIntegral f (chartₜ(T,i.1.val) i.2.val) := by
    change sLocalIdelicZFunction f _ = _
    have hp : 0 < i.2.val.re := by rw [i.2.property]; norm_num
    rw [sLocalThetaMellinIntegral_eq_zeta f ⟨i.1.val,i.2.val,hp,rfl⟩,
      sLocalIdelicZFunction_eq_integral f ⟨i.1.val,i.2.val,hp,rfl⟩]
  have hker : LinearMap.ker E = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro y hy
    apply Subtype.ext
    change y.val = 0
    obtain ⟨f,hf⟩ := (sLocalAdelicTheta F T).ker.mkQ_surjective y.val
    rw [← hf]
    apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_line T
    funext χ
    obtain ⟨η,z,hz,hc,_⟩ := sLocalMellinSchwartzBounds_meyer_angular_normalization T τ hτ χ
    have ha (s : ℂ) (hs : s.re = 2) : sLocalThetaMellinIntegral f (chartₜ(T,η.val) s) = 0 := by
      rw [← he f (η,⟨s,hs⟩),hf]
      exact congrFun hy (η,⟨s,hs⟩)
    have hp : 0 < (1+z).re := by simp [hz]
    have hv := sLocalMellinSchwartzBounds_meyer_line_support _ (sLocalThetaMellinIntegral_analyticOn f η.val) 2 (by norm_num) ha _ hp
    change sLocalIdelicZFunction f (chartₜ(T,χ) 1) = (sLocalThetaMellin 0).val _
    rw [map_zero]
    change _ = 0
    rw [hc,sLocalIdelicZFunction_eq_integral f ⟨η.val,1+z,hp,rfl⟩,
      ← sLocalThetaMellinIntegral_eq_zeta f ⟨η.val,1+z,hp,rfl⟩]
    exact hv
  let : T2Space Q := sLocalAdelicThetaSpace_strictLF.1
  let : FiniteDimensional ℂ M := hspan
  have hind := (LinearMap.isClosedEmbedding_of_injective hker).isEmbedding.isInducing
  have hB : Bornology.IsVonNBounded ℂ (range fun n ↦ E (x n)) := by
    apply Bornology.isVonNBounded_pi_iff.mpr
    intro i
    obtain ⟨B,hB⟩ := hval i.1 i.2.val i.2.property
    apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
    refine ⟨B,?_⟩
    rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
    change ‖ev i (q (v n))‖ ≤ B
    rw [he]
    exact hB n
  let ε (n : ℕ) : ℂ := (2⁻¹ : ℂ)^n
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hx : Bornology.IsVonNBounded ℂ (range x) := by
    apply Bornology.isVonNBounded_of_smul_tendsto_zero (ε := ε) (l := atTop) (Eventually.of_forall fun n ↦ by simp [ε])
    intro y hy
    apply hind.tendsto_nhds_iff.mpr
    have H := hB.smul_tendsto_zero (x := fun n ↦ E (y n)) (Eventually.of_forall fun n ↦ by
      obtain ⟨j,hj⟩ := hy n
      exact ⟨j,congrArg E hj⟩) hε
    change Tendsto (fun n ↦ E (ε n • y n)) atTop (𝓝 (E 0))
    simp only [map_smul,map_zero]
    exact H
  refine (hx.image M.subtypeL).subset ?_
  rintro _ ⟨n,rfl⟩
  exact ⟨x n,mem_range_self n,rfl⟩


/-- Finitely many active angular characters give every zeroth-order weighted
estimate on their generated subgroup, even when the characters have infinite
order and their generated subgroup is infinite. -/
private theorem sLocalMellinSchwartzBounds_meyer_finite_content (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (v : ℕ → ℬₛ(T)) (hb : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)))
    (a : ℝ) (ha : 0 < a) (S : Set (PontryaginDual.map τ).ker) (hS : S.Finite)
    (hs : ∀ χ ∉ S, ∀ n (z : ℂ), z.re = a → sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val) z) = 0) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val.val) z)‖ ≤ B := by
  classical
  let H := Subgroup.closure S
  refine ⟨H,H.fg_iff.mpr ⟨S,rfl,hS⟩,fun χ hχ ↦ hs χ (fun hx ↦ hχ (Subgroup.subset_closure hx)),?_⟩
  intro p k m
  choose B hB using fun χ : H ↦ sLocalMellinSchwartzBounds_meyer_radial_strip T χ.val.val v hb a (a+1) ha (by linarith) m
  let W (χ : H) := (1+p χ)^k * B χ
  have ht : (H.subtype ⁻¹' S).Finite := hS.preimage Subtype.val_injective.injOn
  obtain ⟨C,hC⟩ := (ht.image W).bddAbove
  refine ⟨max C 0,fun χ n z hz ↦ ?_⟩
  by_cases hχ : χ.val ∈ S
  · have hp : 0 ≤ (1+p χ)^k := pow_nonneg (by linarith [apply_nonneg p χ]) _
    exact (mul_le_mul_of_nonneg_left (hB χ n z (show z.re ∈ Icc a (a+1) from ⟨hz.ge,by linarith⟩)) hp).trans
      ((hC (mem_image_of_mem W (show χ ∈ H.subtype ⁻¹' S from hχ))).trans (le_max_left _ _))
  · rw [hs χ.val hχ n z hz,mul_zero,norm_zero,mul_zero]
    exact le_max_right _ _

/-- Continuous linear evaluations that are pointwise bounded on a nonmeagre set
are uniformly bounded on every bounded set, for an arbitrary index family. -/
private theorem sLocalMellinSchwartzBounds_meyer_nonmeagre_uniform {E I : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (S : Set E) (hS : ¬ IsMeagre S)
    (L : I → E →L[ℂ] ℂ) (hb : ∀ x ∈ S, ∃ B : ℝ, ∀ i, ‖L i x‖ ≤ B)
    (tests : Set E) (hV : Bornology.IsVonNBounded ℂ tests) :
    ∃ B : ℝ, ∀ x ∈ tests, ∀ i, ‖L i x‖ ≤ B := by
  let W (n : ℕ) : Set E := ⋂ i, {x : E | ‖L i x‖ ≤ (n : ℝ)}
  have hW (n : ℕ) : IsClosed (W n) := isClosed_iInter fun i ↦
    isClosed_le (L i).continuous.norm continuous_const
  have hcov : S ⊆ ⋃ n : ℕ, W n := by
    intro x hx
    obtain ⟨B,hB⟩ := hb x hx
    obtain ⟨n,hn⟩ := exists_nat_ge B
    exact mem_iUnion.mpr ⟨n,mem_iInter.mpr fun i ↦ (hB i).trans hn⟩
  obtain ⟨n,x,hx⟩ : ∃ n : ℕ, (interior (W n)).Nonempty := by
    by_contra h
    have h : ∀ n, ¬ (interior (W n)).Nonempty := fun n hn ↦ h ⟨n,hn⟩
    exact hS ((isMeagre_iUnion fun n ↦ ((hW n).isNowhereDense_iff.mpr (not_nonempty_iff_eq_empty.mp (h n))).isMeagre).mono hcov)
  have hxW := mem_iInter.mp (show x ∈ W n from interior_subset hx)
  rw [mem_interior_iff_mem_nhds,← map_add_left_nhds_zero] at hx
  let U := (fun y : E ↦ x+y) ⁻¹' W n
  obtain ⟨r,hr,hU⟩ := (hV (show U ∈ 𝓝 0 from hx)).exists_pos
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  refine ⟨r * ((n : ℝ) + n),fun y hy i ↦ ?_⟩
  obtain ⟨z,hz,rfl⟩ := hU (r : ℂ) hn.ge hy
  have hzW := mem_iInter.mp (show x+z ∈ W n from hz) i
  have hxz : ‖L i z‖ ≤ (n : ℝ)+n := calc
    ‖L i z‖ = ‖L i (x+z)-L i x‖ := by rw [map_add,add_sub_cancel_left]
    _ ≤ ‖L i (x+z)‖ + ‖L i x‖ := norm_sub_le _ _
    _ ≤ (n : ℝ)+n := add_le_add hzW (hxW i)
  rw [map_smul,norm_smul,hn]
  exact mul_le_mul_of_nonneg_left hxz hr.le

/-- Restricting a section-trivial angular character to the compact norm-one
quotient is injective. The resulting discrete dual is second countable. -/
private theorem sLocalMellinSchwartzBounds_meyer_angular_countable (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) : Countable (PontryaginDual.map τ).ker := by
  have := isClosed_sProjectedDiagonal (F := F) (S := T)
  let : T2Space (SIdeleQuotient F T) := inferInstanceAs (T2Space (_ ⧸ _))
  let (v : T) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing F T) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : T) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F T)ˣ := (sIdeleGroup_description F T).1.secondCountableTopology
  let : SecondCountableTopology (SIdeleQuotient F T) := inferInstance
  let N := (sIdeleQuotientNorm F T).ker
  have : CompactSpace N := isCompact_iff_compactSpace.mp
    (show IsCompact ((sIdeleQuotientNorm F T) ⁻¹' ({1} : Set ℝ≥0ˣ)) from
      (isProperMap_sIdeleQuotientNorm F T).isCompact_preimage isCompact_singleton)
  let : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  let : LocallyCompactSpace N := inferInstance
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual N) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap N Circle).secondCountableTopology
  have : Countable (PontryaginDual N) := countable_of_Lindelof_of_discrete
  let ι : N →ₜ* SIdeleQuotient F T := ⟨N.subtype,continuous_subtype_val⟩
  let R (χ : (PontryaginDual.map τ).ker) := PontryaginDual.map ι χ.val
  refine (show Injective R from fun χ ψ h ↦ ?_).countable
  apply Subtype.ext
  apply PontryaginDual.ext
  intro x
  let t := sIdeleQuotientNorm F T x
  let y : N := ⟨x / τ t,by change sIdeleQuotientNorm F T (x / τ t) = 1; rw [map_div,hτ t,div_self' (sIdeleQuotientNorm F T x)]⟩
  have hs (η : (PontryaginDual.map τ).ker) : η.val (τ t) = 1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp η.property) t
  have he : χ.val (x/τ t) = ψ.val (x/τ t) := DFunLike.congr_fun h y
  simpa only [map_div,hs,div_one] using he

/-- A countable cover of a Fréchet theta stage by the possible finitely generated
angular supports has a nonmeagre member. This one support works for every
weight, even if the original single-test estimates use unrelated subgroups. -/
private theorem sLocalMellinSchwartzBounds_meyer_common_stage_of_singletons {E D : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [BaireSpace E]
    [CommGroup D] [Countable D] (a : ℝ) (L : D → {z : ℂ // z.re = a} → E →L[ℂ] ℂ)
    (v : ℕ → E) (hv : Bornology.IsVonNBounded ℂ (range v))
    (single : ∀ x : E, ∃ H : Subgroup D, H.FG ∧
      (∀ χ ∉ H, ∀ z, L χ z x = 0) ∧ ∀ (p : GroupSeminorm H) (k m : ℕ),
        ∃ B : ℝ, ∀ (χ : H) z, (1+p χ)^k * ‖z.val^m * L χ.val z x‖ ≤ B) :
    ∃ H : Subgroup D, H.FG ∧ (∀ χ ∉ H, ∀ n z, L χ z (v n) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n z,
        (1+p χ)^k * ‖z.val^m * L χ.val z (v n)‖ ≤ B := by
  classical
  let H (s : Finset D) := Subgroup.closure (s : Set D)
  let U (s : Finset D) : Set E := {x | (∀ χ ∉ H s, ∀ z, L χ z x = 0) ∧
    ∀ (p : GroupSeminorm (H s)) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H s) z,
      (1+p χ)^k * ‖z.val^m * L χ.val z x‖ ≤ B}
  have hcover : (⋃ s : Finset D, U s) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨J,hfg,hJ⟩ := single x
    obtain ⟨t,ht,hfin⟩ := J.fg_iff.mp hfg
    have eq : H hfin.toFinset = J := by simpa [H] using ht
    rw [← eq] at hJ
    exact mem_iUnion.mpr ⟨hfin.toFinset,hJ⟩
  obtain ⟨s,hs⟩ : ∃ s : Finset D, ¬ IsMeagre (U s) := by
    by_contra h
    have h : ∀ s, IsMeagre (U s) := fun s ↦ not_not.mp (fun h0 ↦ h ⟨s,h0⟩)
    exact not_isMeagre_of_mem_residual (Filter.univ_mem : (univ : Set E) ∈ residual E) (hcover ▸ isMeagre_iUnion h)
  refine ⟨H s,(H s).fg_iff.mpr ⟨(s : Set D),rfl,s.finite_toSet⟩,?_,?_⟩
  · intro χ hχ n z
    let K := (L χ z).ker
    have hclosed : IsClosed (K : Set E) := (L χ z).isClosed_ker
    have htop : K = ⊤ := K.eq_top_of_nonempty_interior' <| by
      by_contra he
      exact hs (((hclosed.isNowhereDense_iff.mpr (not_nonempty_iff_eq_empty.mp he)).isMeagre).mono
        (fun x hx ↦ (show x ∈ U s from hx).1 χ hχ z))
    exact (show v n ∈ K from htop ▸ Submodule.mem_top)
  · intro p k m
    let J := H s × {z : ℂ // z.re = a}
    let W (i : J) := (((1 + p i.1)^k : ℝ) : ℂ) * i.2.val^m
    let A (i : J) : E →L[ℂ] ℂ := W i • (L i.1.val i.2)
    have he (i : J) (x : E) : ‖A i x‖ = (1+p i.1)^k * ‖i.2.val^m * L i.1.val i.2 x‖ := by
      change ‖((((1+p i.1)^k : ℝ) : ℂ) * i.2.val^m) * L i.1.val i.2 x‖ = _
      rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by linarith [apply_nonneg p i.1]) _)]
    have hpoint (x : E) (hx : x ∈ U s) : ∃ B : ℝ, ∀ i, ‖A i x‖ ≤ B := by
      obtain ⟨B,hB⟩ := hx.2 p k m
      refine ⟨B,fun i ↦ ?_⟩
      rw [he]
      exact hB i.1 i.2
    obtain ⟨B,hB⟩ := sLocalMellinSchwartzBounds_meyer_nonmeagre_uniform (U s) hs A hpoint (range v) hv
    refine ⟨B,fun χ n z ↦ ?_⟩
    exact (he (χ,z) (v n)).symm.le.trans (hB (v n) (mem_range_self n) (χ,z))

/-- Lift the scalar comparison to a given Fréchet stage using representatives
of its points. All changes of coordinates in the weighted estimates are made
before the Baire-category argument. -/
private theorem sLocalMellinSchwartzBounds_meyer_quotient_family {P Q E D : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [BaireSpace E]
    [CommGroup D] [Countable D] (a : ℝ) (q : P → Q) (hq : Surjective q) (i : E → Q)
    (Z : P → D → ℂ → ℂ) (L : D → {z : ℂ // z.re = a} → E →L[ℂ] ℂ)
    (he : ∀ f y, q f = i y → ∀ χ z, L χ z y = Z f χ z.val)
    (v : ℕ → P) (x : ℕ → E) (hx : ∀ n, q (v n) = i (x n))
    (hb : Bornology.IsVonNBounded ℂ (range x))
    (single : ∀ f, ∃ H : Subgroup D, H.FG ∧ (∀ χ ∉ H, ∀ z : ℂ, z.re = a → Z f χ z = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) z, z.re = a → (1+p χ)^k * ‖z^m * Z f χ.val z‖ ≤ B) :
    ∃ H : Subgroup D, H.FG ∧ (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → Z (v n) χ z = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n z, z.re = a → (1+p χ)^k * ‖z^m * Z (v n) χ.val z‖ ≤ B := by
  have hsingle (y : E) : ∃ H : Subgroup D, H.FG ∧ (∀ χ ∉ H, ∀ z, L χ z y = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) z, (1+p χ)^k * ‖z.val^m * L χ.val z y‖ ≤ B := by
    obtain ⟨f,hf⟩ := hq (i y)
    obtain ⟨H,hH,hs,hw⟩ := single f
    refine ⟨H,hH,fun χ hχ z ↦ (he f y hf χ z).trans (hs χ hχ z.val z.property),fun p k m ↦ ?_⟩
    obtain ⟨B,hB⟩ := hw p k m
    refine ⟨B,fun χ z ↦ ?_⟩
    rw [he f y hf]
    exact hB χ z.val z.property
  obtain ⟨H,hH,hs,hw⟩ := sLocalMellinSchwartzBounds_meyer_common_stage_of_singletons a L x hb hsingle
  refine ⟨H,hH,fun χ hχ n z hz ↦ (he _ _ (hx n) χ ⟨z,hz⟩).symm.trans (hs χ hχ n ⟨z,hz⟩),fun p k m ↦ ?_⟩
  obtain ⟨B,hB⟩ := hw p k m
  refine ⟨B,fun χ n z hz ↦ ?_⟩
  have hh := hB χ n ⟨z,hz⟩
  rw [he _ _ (hx n)] at hh
  exact hh

/-- Positive-line Mellin evaluation factors through a continuous linear functional
on the theta quotient, with the normalization of the integral. -/
private theorem sLocalMellinSchwartzBounds_meyer_line_evaluations (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (a : ℝ) (ha : 1 < a) : ∃ E : (PontryaginDual.map τ).ker → {z : ℂ // z.re = a} →
      SLocalAdelicThetaSpace F T →L[ℂ] ℂ, ∀ f χ z,
      E χ z ((sLocalAdelicTheta F T).ker.mkQ f) = sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z.val) := by
  let A := (PontryaginDual.map τ).ker
  let Q := SLocalAdelicThetaSpace F T
  let K := (sLocalAdelicTheta F T).ker
  let J := {z : ℂ // z.re = a}
  have hc : Continuous (sLocalThetaMellin (F := F) (S := T)) :=
    K.isQuotientMap_mkQ.continuous_iff.mpr sLocalIdelicMellin_continuous
  have hpos (z : J) : 0 < z.val.re := by rw [z.property]; exact zero_lt_one.trans ha
  let E (χ : A) (z : J) : Q →L[ℂ] ℂ := (ContinuousMap.evalCLM ℂ
    ⟨chartₜ(T,χ.val) z.val,sLocalOrderBound_positive χ.val (hpos z)⟩).comp
      ((Submodule.subtypeL _).comp ⟨sLocalThetaMellin,hc⟩)
  refine ⟨E,fun f χ z ↦ ?_⟩
  change sLocalIdelicZFunction f _ = _
  rw [sLocalThetaMellinIntegral_eq_zeta _ ⟨χ.val,z.val,hpos z,rfl⟩,
      ← sLocalIdelicZFunction_eq_integral _ ⟨χ.val,z.val,hpos z,rfl⟩]

/-- The forward comparison for all bounded families follows from the zeroth
weighted positive-line comparison for individual tests. The same Baire argument
works on each actual Fréchet theta stage and for the chosen norm section. -/
private theorem sLocalMellinSchwartzBounds_meyer_angular_family_of_singletons (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (M : Submodule ℂ (SLocalAdelicThetaSpace F T)) (hM : IsFrechetTVS M)
    (hm : (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) ⊆ M)
    (hb : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)))
    (a : ℝ) (ha : 1 < a)
    (single : ∀ f : ℬₛ(T), ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ (z : ℂ), z.re = a → sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z) = 0) ∧
      (∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral f (chartₜ(T,χ.val.val) z)‖ ≤ B)) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral (v n) (chartₜ(T,χ.val.val) z)‖ ≤ B := by
  let A := (PontryaginDual.map τ).ker
  let Q := SLocalAdelicThetaSpace F T
  let K := (sLocalAdelicTheta F T).ker
  let J := {z : ℂ // z.re = a}
  let : T2Space Q := sLocalAdelicThetaSpace_strictLF.1
  obtain ⟨hadd,hpoly,hmetr,hcomp⟩ := hM
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace M := hcomp
  let : IsCountablyGenerated (uniformity M) := by rw [uniformity_eq_comap_nhds_zero]; infer_instance
  let : BaireSpace M := by let := UniformSpace.metricSpace M; infer_instance
  let : Countable A := sLocalMellinSchwartzBounds_meyer_angular_countable T τ hτ
  let x (n : ℕ) : M := ⟨K.mkQ (v n),hm (mem_range_self n)⟩
  have hboth : Bornology.IsVonNBounded ℂ (M.subtypeL '' range x) := hb.subset (by
    rintro _ ⟨_,⟨n,rfl⟩,rfl⟩; exact mem_range_self n)
  have hx : Bornology.IsVonNBounded ℂ (range x) := by
    have hi : IsInducing M.subtypeL := IsEmbedding.subtypeVal.isInducing
    rw [Bornology.isVonNBounded_iff_tendsto_smallSets_nhds,hi.nhds_eq_comap,map_zero,
      smallSets_comap_eq_comap_image,tendsto_comap_iff]
    simpa only [Function.comp_def,image_smul_set] using hboth.tendsto_smallSets_nhds
  obtain ⟨E,he⟩ := sLocalMellinSchwartzBounds_meyer_line_evaluations T τ a ha
  let L (χ : A) (z : J) : M →L[ℂ] ℂ := (E χ z).comp M.subtypeL
  let Z (f : ℬₛ(T)) (χ : A) (z : ℂ) := sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z)
  exact sLocalMellinSchwartzBounds_meyer_quotient_family a K.mkQ K.mkQ_surjective M.subtype Z L
    (fun f y hf χ z ↦ (congrArg (E χ z) hf).symm.trans (he f χ z))
    v x (fun _ ↦ rfl) hx single

/-- A compact level at which finitely many continuous archimedean characters
separate the remaining points of an open subgroup yields a Lie quotient. -/
private theorem sLocalMellinSchwartzBounds_meyer_quotient_coordinates {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {ι : Type*} [Finite ι] (U L : Subgroup G) (hu : IsOpen (U : Set G))
    (hc : IsClosed (L : Set G)) (f : ι → G →ₜ* ℂˣ)
    (hL : ∀ x, x ∈ L ↔ x ∈ U ∧ ∀ i, f i x = 1) : IsLocallyEuclidean (G ⧸ L) := by
  let : IsClosed (L : Set G) := hc
  let π := QuotientGroup.mk' L
  let g (i : ι) : (G ⧸ L) →ₜ* ℂˣ :=
    ⟨QuotientGroup.lift L (f i).toMonoidHom (fun x hx ↦ ((hL x).mp hx).2 i),
      (QuotientGroup.isQuotientMap_mk L).continuous_iff.mpr (f i).continuous⟩
  let e := toEuclidean (E := ℂ)
  have hh : IsLocallyEuclidean ℂˣ := ⟨_, ⟨(e.toHomeomorph.isOpenEmbedding.comp
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℂ))).singletonChartedSpace⟩⟩
  obtain ⟨W,hW,hp⟩ := exists_nhds_one_of_isLocallyEuclidean hh
  let N := U.map π
  have hn : IsOpen (N : Set (G ⧸ L)) := QuotientGroup.isOpenMap_coe _ hu
  let K : Set (G ⧸ L) := {x | x ∈ N ∧ ∀ i, g i x ∈ W}
  have hk : K ∈ 𝓝 (1 : G ⧸ L) := by
    have h : ∀ i, ∀ᶠ x in 𝓝 (1 : G ⧸ L), g i x ∈ W := fun i ↦
      ((g i).continuous.tendsto' _ _ (map_one (g i))).eventually hW
    have hN : ∀ᶠ x in 𝓝 (1 : G ⧸ L), x ∈ N := hn.mem_nhds N.one_mem
    exact hN.and (eventually_all.mpr h)
  apply isLocallyEuclidean_of_noSmallCyclicSubgroups hk
  intro x hx
  have hmem : x ∈ N := by simpa only [pow_one] using (hx 1).1
  obtain ⟨y,hy,rfl⟩ := hmem
  apply (QuotientGroup.eq_one_iff _).mpr
  apply (hL y).mpr
  refine ⟨hy,fun i ↦ hp _ fun n ↦ ?_⟩
  have h := (hx n).2 i
  rwa [map_pow] at h

/-- The actual S-principal-congruence quotient is locally Euclidean in all
number fields. The finite congruence conditions form an open subgroup; on
it the complex embeddings of the archimedean units detect the level. -/
private theorem sLocalMellinSchwartzBounds_meyer_principal_raw_lie (T : Finset V) (k : ℕ) (L : Subgroup (SAdeleRing F T)ˣ)
    (hcl : IsClosed (L : Set (SAdeleRing F T)ˣ))
    (hL : ∀ x : (SAdeleRing F T)ˣ, x ∈ L ↔ x.val.1 = 1 ∧
      ∀ w : T, Valued.v (x.val.2 w-1) ≤ WithZero.exp (-(k+1 : ℤ))) :
    IsLocallyEuclidean ((SAdeleRing F T)ˣ ⧸ L) := by
  let R := SAdeleRing F T
  let D := (w : T) → w.val.adicCompletion F
  let A := InfiniteAdeleRing F
  let proj : Rˣ →* Rˣ := Units.map
    ((MonoidHom.inr A D).comp (MonoidHom.snd A D))
  let U := L.comap proj
  have hu (x : Rˣ) : x ∈ U ↔ ∀ w : T, Valued.v (x.val.2 w-1) ≤ WithZero.exp (-(k+1 : ℤ)) := by
    change proj x ∈ L ↔ _
    rw [hL]; exact and_iff_right rfl
  have ho : IsOpen (U : Set Rˣ) := by
    apply Subgroup.isOpen_of_mem_nhds
    have hfin (w : T) : ∀ᶠ g : Rˣ in 𝓝 1, Valued.v (g.val.2 w-1) ≤ WithZero.exp (-(k+1 : ℤ)) := by
      obtain ⟨z,hz⟩ := w.val.valuedAdicCompletion_surjective F (WithZero.exp (-(k+1 : ℤ)))
      have hz0 : z ≠ 0 := fun he ↦ by subst z; simp at hz
      have hcont : Continuous (fun g : Rˣ ↦ ‖g.val.2 w-1‖) :=
        (((continuous_apply w).comp (continuous_snd.comp Units.continuous_val)).sub continuous_const).norm
      have hnear : ∀ᶠ g : Rˣ in 𝓝 1, ‖g.val.2 w-1‖ < ‖z‖ :=
        (isOpen_lt hcont continuous_const).mem_nhds (by
          change ‖(1 : w.val.adicCompletion F) - 1‖ < ‖z‖
          rw [sub_self,norm_zero]; exact norm_pos_iff.mpr hz0)
      exact hnear.mono fun g hg ↦ hz ▸ Valued.toNormedField.norm_le_iff.mp hg.le
    exact (eventually_all.mpr hfin).mono fun g hg ↦ (hu g).mpr hg
  let alg (w : InfinitePlace F) : R →* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom.comp
      ((Pi.evalMonoidHom _ w).comp (MonoidHom.fst A D))
  let f (w : InfinitePlace F) : Rˣ →ₜ* ℂˣ := ⟨Units.map (alg w),
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)).units_map _⟩
  let : T2Space Rˣ := (sIdeleGroup_description F T).2.1
  let : LocallyCompactSpace Rˣ := (sIdeleGroup_description F T).2.2.1
  apply sLocalMellinSchwartzBounds_meyer_quotient_coordinates U L ho hcl f
  intro x
  rw [hL,hu]
  constructor
  · rintro ⟨h,hf⟩
    refine ⟨hf,fun w ↦ Units.ext ?_⟩
    change InfinitePlace.Completion.extensionEmbedding w (x.val.1 w) = 1
    rw [h]; exact map_one _
  · rintro ⟨h,ha⟩
    refine ⟨funext fun w ↦ (InfinitePlace.Completion.extensionEmbedding w).injective ?_,h⟩
    exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) (ha w) |>.trans (map_one _).symm

private theorem sLocalMellinSchwartzBounds_meyer_annihilator_cg {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (L : Subgroup G)
    (hc : IsClosed (L : Set G)) (h : IsLocallyEuclidean (G ⧸ L)) :
    IsCompactlyGeneratedGroup (lcaAnnihilator L) := by
  let : IsClosed (L : Set G) := hc
  obtain ⟨e,_⟩ := lcaQuotientDual_equiv_annihilator L hc
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv e
    (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean h)

private theorem sLocalMellinSchwartzBounds_meyer_level_closed_annihilator {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (K : Subgroup G) :
    IsClosed (lcaAnnihilator K : Set (PontryaginDual G)) := by
  have he : (lcaAnnihilator K : Set (PontryaginDual G)) =
      ⋂ k : K, {χ : PontryaginDual G | χ k.val = 1} := by
    ext χ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_lcaAnnihilator_iff]
  rw [he]
  exact isClosed_iInter fun k ↦ isClosed_eq (pontryaginDual_eval (G := G) k.val).continuous continuous_const

private theorem sLocalMellinSchwartzBounds_meyer_compact_generation_of_closed_embedding {H L : Type*} [CommGroup H] [CommGroup L]
    [TopologicalSpace H] [TopologicalSpace L] [IsTopologicalGroup L] [T2Space L] [LocallyCompactSpace L]
    (f : H →* L) (hf : IsClosedEmbedding f) (hL : IsCompactlyGeneratedGroup L) :
    IsCompactlyGeneratedGroup H := by
  have hr : IsCompactlyGeneratedGroup f.range := isCompactlyGeneratedGroup_closedSubgroup hL f.range hf.isClosed_range
  let e := MulEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h ↦ hf.injective (congrArg Subtype.val h),
    fun ⟨_,x,hx⟩ ↦ ⟨x,Subtype.ext hx⟩⟩
  have hd : IsInducing f.rangeRestrict := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let d : H ≃ₜ* f.range := ⟨e,hd.continuous,
    (e.toEquiv.toHomeomorphOfIsInducing hd).symm.continuous⟩
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv d.symm hr

/-- Pullback embeds the annihilator of the image as a closed subgroup of the original annihilator. -/
private theorem sLocalMellinSchwartzBounds_meyer_good_quotient_map {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (K : Subgroup G) (hK : IsClosed (K : Set G))
    (k : Subgroup G) (hkc : IsCompact (k : Set G)) (hk : IsBruhatGoodSubgroup k) :
    IsBruhatGoodSubgroup (k.map (QuotientGroup.mk' K)) := by
  let : IsClosed (K : Set G) := hK
  let q := QuotientGroup.mk' K
  let k' := k.map q
  have hk' : IsCompact (k' : Set (G ⧸ K)) := hkc.image QuotientGroup.continuous_mk
  refine ⟨hk'.isClosed,isOpen_lcaAnnihilator k' hk',?_⟩
  obtain ⟨e,he⟩ := lcaQuotientDual_equiv_annihilator K hK
  let i := (lcaAnnihilator K).subtype.comp (e.toMonoidHom.comp (lcaAnnihilator k').subtype)
  let f := i.codRestrict (lcaAnnihilator k) fun χ ↦ (mem_lcaAnnihilator_iff k _).mpr fun u ↦ by
    change (e χ.val).val u.val = 1
    rw [he]
    exact (mem_lcaAnnihilator_iff k' _).mp χ.property ⟨q u.val,⟨u.val,u.property,rfl⟩⟩
  have hi : IsClosedEmbedding i := (sLocalMellinSchwartzBounds_meyer_level_closed_annihilator K).isClosedEmbedding_subtypeVal.comp
    (e.toHomeomorph.isClosedEmbedding.comp (sLocalMellinSchwartzBounds_meyer_level_closed_annihilator k').isClosedEmbedding_subtypeVal)
  let : LocallyCompactSpace (lcaAnnihilator k) := hk.2.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  exact sLocalMellinSchwartzBounds_meyer_compact_generation_of_closed_embedding f
    (IsClosedEmbedding.of_comp_iff (sLocalMellinSchwartzBounds_meyer_level_closed_annihilator k).isClosedEmbedding_subtypeVal |>.mp hi) hk.2.2

private theorem sLocalMellinSchwartzBounds_meyer_angular_discrete (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) : DiscreteTopology (PontryaginDual.map τ).ker := by
  have := isClosed_sProjectedDiagonal (F := F) (S := T)
  let : T2Space (SIdeleQuotient F T) := inferInstanceAs (T2Space (_ ⧸ _))
  let N := (sIdeleQuotientNorm F T).ker
  have : CompactSpace N := isCompact_iff_compactSpace.mp
    (show IsCompact ((sIdeleQuotientNorm F T) ⁻¹' ({1} : Set ℝ≥0ˣ)) from
      (isProperMap_sIdeleQuotientNorm F T).isCompact_preimage isCompact_singleton)
  let ι : N →ₜ* SIdeleQuotient F T := ⟨N.subtype,continuous_subtype_val⟩
  let R (χ : (PontryaginDual.map τ).ker) := PontryaginDual.map ι χ.val
  apply DiscreteTopology.of_continuous_injective ((PontryaginDual.map ι).continuous.comp continuous_subtype_val)
  intro χ ψ h
  apply Subtype.ext
  apply PontryaginDual.ext
  intro x
  let t := sIdeleQuotientNorm F T x
  let y : N := ⟨x / τ t,by change sIdeleQuotientNorm F T (x / τ t) = 1; rw [map_div,hτ t,div_self' (sIdeleQuotientNorm F T x)]⟩
  have hs (η : (PontryaginDual.map τ).ker) : η.val (τ t) = 1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp η.property) t
  have he : χ.val (x/τ t) = ψ.val (x/τ t) := DFunLike.congr_fun h y
  simpa only [map_div,hs,div_one] using he

private theorem sLocalMellinSchwartzBounds_meyer_finitely_generated_slice {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [LocallyCompactSpace C] [T2Space C] (J E : Subgroup C)
    (hj : IsOpen (J : Set C)) (he : IsClosed (E : Set C)) [DiscreteTopology E]
    (hc : IsCompactlyGeneratedGroup J) : (J.comap E.subtype).FG := by
  let H := J.comap E.subtype
  let : LocallyCompactSpace J := hj.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let p : H →* J := (E.subtype.comp H.subtype).codRestrict J (fun x ↦ x.property)
  have hf : IsClosedEmbedding (E.subtype.comp H.subtype) := he.isClosedEmbedding_subtypeVal.comp
    ((J.isClosed_of_isOpen hj).preimage continuous_subtype_val).isClosedEmbedding_subtypeVal
  have hp : IsClosedEmbedding p := (IsClosedEmbedding.of_comp_iff
    (J.isClosed_of_isOpen hj).isClosedEmbedding_subtypeVal).mp hf
  obtain ⟨S,_,hs,hgen⟩ := sLocalMellinSchwartzBounds_meyer_compact_generation_of_closed_embedding p hp hc
  refine H.fg_iff.mpr ⟨H.subtype '' S,?_, hs.finite_of_discrete.image _⟩
  rw [← MonoidHom.map_closure,hgen,Subgroup.map_top,H.range_subtype]

/-- All bounded S-local theta families have finitely generated angular support,
for every number field and every choice of the norm section. -/
private theorem sLocalMellinSchwartzBounds_meyer_general_angular_support (T : Finset V)
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
    (hv : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      ∀ χ ∉ H, ∀ n (z : ℂ), 0 < z.re →
        sLocalThetaMellinIntegral (v n) (quasiCharacterNormTwist (sIdeleQuotientNorm F T)
          (isProperMap_sIdeleQuotientNorm F T).continuous
          ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ.val) z) = 0 := by
  have hdiag := isClosed_sProjectedDiagonal (F := F) (S := T)
  let : T2Space (SAdeleRing F T)ˣ := (sIdeleGroup_description F T).2.1
  let : LocallyCompactSpace (SAdeleRing F T)ˣ := (sIdeleGroup_description F T).2.2.1
  let : T2Space (SIdeleQuotient F T) := inferInstanceAs (T2Space (_ ⧸ _))
  let : LocallyCompactSpace (SIdeleQuotient F T) := inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_bounded_representatives_level T v
    ((sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded T v).mpr hv)
  obtain ⟨L,hc,_,hL⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels_groups (F := F) T
  let π : (SAdeleRing F T)ˣ →* SIdeleQuotient F T := QuotientGroup.mk' _
  have hcL := hc k
  have hgood : IsBruhatGoodSubgroup (L k) :=
    ⟨hcL.isClosed,isOpen_lcaAnnihilator _ hcL,
      sLocalMellinSchwartzBounds_meyer_annihilator_cg _ hcL.isClosed (sLocalMellinSchwartzBounds_meyer_principal_raw_lie T k (L k) hcL.isClosed (hL k))⟩
  have hqi := sLocalMellinSchwartzBounds_meyer_good_quotient_map _ hdiag (L k) hcL hgood
  let J := lcaAnnihilator ((L k).map π)
  let E := (PontryaginDual.map τ).ker
  have hE : IsClosed (E : Set (PontryaginDual (SIdeleQuotient F T))) :=
    isClosed_singleton.preimage (PontryaginDual.map τ).continuous
  let : DiscreteTopology E := sLocalMellinSchwartzBounds_meyer_angular_discrete T τ hτ
  let H := J.comap E.subtype
  refine ⟨H,sLocalMellinSchwartzBounds_meyer_finitely_generated_slice J E hqi.2.1 hE hqi.2.2,fun χ hχ n z hz ↦ ?_⟩
  have hn : ¬ ∀ u : (L k).map π, χ.val u.val = 1 := fun h ↦
    hχ ((mem_lcaAnnihilator_iff _ _).mpr h)
  obtain ⟨d,hd⟩ := not_forall.mp hn
  obtain ⟨g,hg,hgd⟩ := d.property
  obtain ⟨ha,hf⟩ := (hL k g).mp hg
  let c := quasiCharacterNormTwist (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
    ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ.val) z
  have hnorm : sIdeleQuotientNorm F T (QuotientGroup.mk g) = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    let ev : (((SAdeleRing F T)ˣ →* ℝ≥0ˣ) →* ℝ) := NNReal.toRealHom.toMonoidHom.comp
      ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g))
    change ev (sIdeleNorm F T) = 1
    simp only [sIdeleNorm, map_mul, map_prod]
    change (∏ v : InfinitePlace F, ‖g.val.1 v‖ ^ v.mult) * ∏ w : T, ‖g.val.2 w‖ = 1
    have hone (w : T) : ‖g.val.2 w‖ = 1 := by
      apply Valued.toNormedField.norm_eq_one_iff.mpr
      have he : WithZero.exp (-(k+1 : ℤ)) < 1 := by
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by omega)
      simpa only [add_sub_cancel] using Valued.v.map_one_add_of_lt ((hf w).trans_lt he)
    have eone (w : InfinitePlace F) : (1 : InfiniteAdeleRing F) w = 1 := rfl
    simp [ha,hone,eone]
  have hne : c (QuotientGroup.mk g) ≠ 1 := by
    change (χ.val (π g) : ℂ) * (((sIdeleQuotientNorm F T (QuotientGroup.mk g)).val : ℝ) : ℂ) ^ z ≠ 1
    rw [hnorm,hgd]
    simpa only [Units.val_one,NNReal.coe_one,Complex.ofReal_one,Complex.one_cpow,mul_one] using
      (show (χ.val d.val : ℂ) ≠ 1 from fun h ↦ hd (Circle.ext h))
  have hreg : 0 ≤ sLocalIdelicOrderBound c := sLocalOrderBound_positive χ.val hz
  have he := congrArg (fun x : SLocalAdelicThetaSpace F T ↦ (sLocalThetaMellin x).val ⟨c,hreg⟩)
    (hk g ha hf n)
  change (sLocalIdelicMellin (schwartzBruhatUnitTranslate g (v n))).val ⟨c,hreg⟩ =
    (sLocalIdelicMellin (v n)).val ⟨c,hreg⟩ at he
  rw [sLocalIdelicMellin_unitTranslate] at he
  change c (QuotientGroup.mk g) * sLocalIdelicZFunction (v n) c = sLocalIdelicZFunction (v n) c at he
  have hzero : sLocalIdelicZFunction (v n) c = 0 := by
    by_contra hn
    exact hne (mul_right_cancel₀ hn (he.trans (one_mul _).symm))
  rw [sLocalThetaMellinIntegral_eq_zeta _ ⟨χ.val,z,hz,rfl⟩,
    ← sLocalIdelicZFunction_eq_integral _ ⟨χ.val,z,hz,rfl⟩]
  exact hzero

/-- Subadditivity controls every integer multiple by the corresponding absolute coefficient. -/
private theorem sLocalMellinSchwartzBounds_meyer_int_weight {A : Type*} [AddCommGroup A] (w : A → ℝ)
    (h0 : w 0 = 0) (hadd : ∀ x y, w (x + y) ≤ w x + w y)
    (hneg : ∀ x, w (-x) = w x) (x : A) (n : ℤ) :
    w (n • x) ≤ |(n : ℝ)| * w x := by
  have hnat (k : ℕ) : w (k • x) ≤ (k : ℝ) * w x := by
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      rw [succ_nsmul, Nat.cast_succ, add_mul, one_mul]
      exact (hadd _ _).trans (add_le_add ih le_rfl)
  cases n with
  | ofNat k => simpa using hnat k
  | negSucc k =>
    have hz : Int.negSucc k = -((k+1 : ℕ) : ℤ) := by omega
    rw [hz, neg_zsmul, hneg, natCast_zsmul, Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (show 0 ≤ ((k+1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
    exact hnat (k+1)

/-- In finitely generated abelian groups, finitely many real homomorphisms
control all group seminorms; the finite torsion factor costs an additive constant. -/
private theorem sLocalMellinSchwartzBounds_meyer_abelian_coordinates (H : Type*) [CommGroup H] [Group.FG H] :
    ∃ r : ℕ, ∃ l : Fin r → H →* Multiplicative ℝ, ∀ p : GroupSeminorm H,
      ∃ C ≥ (0 : ℝ), ∀ x : H, p x ≤ C * (1 + ∑ i, |(l i x).toAdd|) := by
  classical
  let : AddGroup.FG (Additive H) := GroupFG.iff_add_fg.mp inferInstance
  obtain ⟨r,I,_,q,hq,k,⟨e'⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive H)
  let P := (i : I) → ZMod (q i ^ k i)
  let (i : I) : NeZero (q i ^ k i) := ⟨pow_ne_zero _ (hq i).ne_zero⟩
  let : Fintype P := inferInstanceAs (Fintype ((i : I) → ZMod (q i ^ k i)))
  let e : Additive H ≃+ (Fin r → ℤ) × P :=
    e'.trans (AddEquiv.prodCongr Finsupp.addEquivFunOnFinite (DirectSum.addEquivProd _))
  let a (j : Fin r) : Additive H →+ ℤ :=
    (Pi.evalAddMonoidHom _ j).comp ((AddMonoidHom.fst _ _).comp e.toAddMonoidHom)
  let l (j : Fin r) : H →* Multiplicative ℝ :=
    AddMonoidHom.toMultiplicativeRight ((Int.castAddHom ℝ).comp (a j))
  refine ⟨r,l,fun p ↦ ?_⟩
  let w (x : (Fin r → ℤ) × P) := p ((e.symm x).toMul)
  have hn (x) : 0 ≤ w x := apply_nonneg _ _
  have h0 : w 0 = 0 := by simp [w]
  have ha (x y) : w (x+y) ≤ w x+w y := by
    simpa only [w,map_add,toMul_add] using map_mul_le_add p (e.symm x).toMul (e.symm y).toMul
  have hneg (x) : w (-x) = w x := by simp [w,map_inv_eq_map]
  let b (j : Fin r) : (Fin r → ℤ) × P := (Pi.single j 1,0)
  let B := ∑ j : Fin r, w (b j)
  let C := (∑ t : P, w (0,t)) + B
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ hn _
  have hT : 0 ≤ ∑ t : P, w (0,t) := Finset.sum_nonneg fun _ _ ↦ hn _
  refine ⟨C, add_nonneg hT hB,fun x ↦ ?_⟩
  let y := e (Additive.ofMul x)
  let W := ∑ j : Fin r, |((y.1 j : ℤ) : ℝ)|
  have hw : 0 ≤ W := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have eq : (∑ j : Fin r, y.1 j • b j) + (0,y.2) = y := by
    refine Prod.ext ?_ ?_
    · funext i
      simp [b,Prod.fst_sum,Pi.single_apply,Finset.sum_apply]
    · simp [b,Prod.snd_sum]
  have hs (S : Finset (Fin r)) :
      w (∑ j ∈ S, y.1 j • b j) ≤ ∑ j ∈ S, w (y.1 j • b j) := by
    induction S using Finset.induction_on with
    | empty => simp [h0]
    | insert j S hj ih =>
      rw [Finset.sum_insert hj,Finset.sum_insert hj]
      exact (ha _ _).trans (add_le_add le_rfl ih)
  have hcoord : ∑ j, w (y.1 j • b j) ≤ W*B := by
    rw [show B = ∑ j, w (b j) from rfl,Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ (sLocalMellinSchwartzBounds_meyer_int_weight w h0 ha hneg (b j) (y.1 j)).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun k ↦ |((y.1 k : ℤ) : ℝ)|)
      (fun k _ ↦ abs_nonneg _) (Finset.mem_univ j)) (hn _)
  have htail := Finset.single_le_sum (f := fun t : P ↦ w (0,t))
    (fun t _ ↦ hn _) (Finset.mem_univ y.2)
  have hsum : w y ≤ W*B + w (0,y.2) := by
    conv_lhs => rw [← eq]
    exact (ha _ _).trans (add_le_add ((hs _).trans hcoord) le_rfl)
  have hpx : p x = w y := by simp [w,y]
  rw [hpx]
  change w y ≤ C * (1+W)
  dsimp only [C]
  nlinarith [mul_nonneg hw hT]

/-- Every homomorphism on a subgroup of the discrete dual of a compact group
is the restriction of a real logarithmic frequency of a one-parameter flow. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_coordinate_on_compact.{u} {N A : Type u}
    [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N] [T2Space N] [CompactSpace N]
    [CommGroup A] (j : A →* PontryaginDual N) (hj : Injective j)
    (r : A →* Multiplicative ℝ) :
    ∃ γ : Multiplicative ℝ →ₜ* N, ∀ (χ : A) (t : ℝ),
      j χ (γ (Multiplicative.ofAdd t)) = Circle.exp (2 * Real.pi * (t * (r χ).toAdd)) := by
  classical
  let D := PontryaginDual N
  let down : ULift.{u} ℝ ≃ₗ[ℤ] ℝ := ULift.moduleEquiv
  let : DivisibleBy (ULift.{u} ℝ) ℤ := divisibleByOfSMulRightSurj _ ℤ fun {n} hn y ↦ by
    obtain ⟨x,hx⟩ := DivisibleBy.surjective_smul ℝ ℤ hn (down y)
    refine ⟨down.symm x,down.injective ?_⟩
    rw [map_smul,down.apply_symm_apply]; exact hx
  have := (Module.Baer.of_divisible (ULift.{u} ℝ)).injective
  let i : Additive A →ₗ[ℤ] Additive D := j.toAdditive.toIntLinearMap
  let p : Additive A →ₗ[ℤ] ℝ := (AddMonoidHom.toMultiplicativeRight.symm r).toIntLinearMap
  have hi : Injective i := hj
  obtain ⟨L,hL⟩ := Module.Injective.out i hi (down.symm.toLinearMap.comp p)
  let f := (AddMonoidHom.toMultiplicativeRight (down.toLinearMap.comp L).toAddMonoidHom)
  let φ : D →ₜ* Multiplicative ℝ := ⟨f,continuous_of_discreteTopology⟩
  have hf (χ : A) : (φ (j χ)).toAdd = (r χ).toAdd := by
    exact (congrArg down (hL (Additive.ofMul χ))).trans (down.apply_symm_apply _)
  obtain ⟨d,hd⟩ := exists_realPontryaginDualEquiv
  obtain ⟨e,he⟩ := pontryaginDual_bidual (G := N)
  let η := (PontryaginDual.map φ).comp (d : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))
  let γ := (e.symm : PontryaginDual D →ₜ* N).comp η
  refine ⟨γ,fun χ t ↦ ?_⟩
  rw [← he]
  change e (e.symm (η (Multiplicative.ofAdd t))) (j χ) = _
  rw [e.apply_symm_apply]
  exact (hd t (φ (j χ)).toAdd).trans (by rw [hf])

/-- A continuous real one-parameter subgroup lifts homomorphically through a
covering homomorphism. Both preservation of products and normalization at 1
come from uniqueness of based lifts. -/
private theorem sLocalMellinSchwartzBounds_meyer_lift_real_flow {G C : Type*} [CommGroup G] [TopologicalSpace G]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup G] [IsTopologicalGroup C]
    (q : G →ₜ* C) (hq : IsCoveringMap q) (a : Multiplicative ℝ →ₜ* C) :
    ∃ l : Multiplicative ℝ →ₜ* G, q.comp l = a := by
  let f : C(ℝ,C) := ⟨fun t ↦ a (Multiplicative.ofAdd t),a.continuous⟩
  obtain ⟨g,⟨hg0,hg⟩,_⟩ := hq.existsUnique_continuousMap_lifts f 0 1 ((map_one q).trans (map_one a).symm)
  have hv (s : ℝ) : q (g s) = a (Multiplicative.ofAdd s) := congrFun hg s
  have hmul (s t : ℝ) : g (s+t) = g s * g t := by
    let l (p : ℝ × ℝ) := g (p.1+p.2)
    let r (p : ℝ × ℝ) := g p.1 * g p.2
    have h := hq.eq_of_comp_eq (g₁ := l) (g₂ := r)
      (g.continuous.comp (continuous_fst.add continuous_snd))
      ((g.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd))
      (funext fun p ↦ (hv _).trans ((map_mul a _ _).trans ((map_mul q _ _).trans
        (congrArg₂ (·*·) (hv p.1) (hv p.2))).symm))
      (0,0) (show g (0+0) = g 0 * g 0 by rw [zero_add,hg0,one_mul])
    exact congrFun h (s,t)
  let l : Multiplicative ℝ →ₜ* G :=
    { toFun s := g s.toAdd, map_one' := hg0, map_mul' x y := hmul x.toAdd y.toAdd,
      continuous_toFun := g.continuous }
  exact ⟨l,ContinuousMonoidHom.ext fun t ↦ hv t.toAdd⟩

/-- The actual raw S-ideles lift any prescribed norm section, including the
one over which the angular/radial boundedness condition quantifies. -/
private theorem sLocalMellinSchwartzBounds_meyer_lift_section (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) :
    ∃ γ : ℝ≥0ˣ →ₜ* (SAdeleRing F T)ˣ,
      RightInverse γ (sIdeleNorm F T) ∧ ∀ t, QuotientGroup.mk (γ t) = τ t := by
  let q : (SAdeleRing F T)ˣ →ₜ* SIdeleQuotient F T := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  have hq : IsCoveringMap q :=
    ((sProjectedDiagonal F T).isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr (discreteTopology_sProjectedDiagonal (F := F) (S := T)))).isCoveringMap
  let e := positiveRealLogEquiv
  obtain ⟨g,hg⟩ := sLocalMellinSchwartzBounds_meyer_lift_real_flow q hq (τ.comp (e.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ))
  let γ := g.comp (e : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
  have h (t) : q (γ t) = τ t := (DFunLike.congr_fun hg (e t)).trans (congrArg τ (e.symm_apply_apply t))
  refine ⟨γ,fun t ↦ ?_,h⟩
  exact (congrArg (sIdeleQuotientNorm F T) (h t)).trans (hτ t)

/-- A Haar-integrable function and its Haar-integrable, continuous derivative
along a real group flow satisfy integration by parts without compact support. -/
private theorem sLocalMellinSchwartzBounds_meyer_integral_flow_derivative_zero {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (g : ℝ → G) (hg : Continuous g) (f d : G → ℂ) (hd : Continuous d)
    (hf : Integrable f μ) (hdi : Integrable d μ)
    (hD : ∀ x t, HasDerivAt (fun s ↦ f (g s * x)) (d (g t * x)) t) :
    ∫ x, d x ∂μ = 0 := by
  let D (s : ℝ) (y : G) := d (g s * y)
  have hDc : Continuous (Function.uncurry D) := hd.comp ((hg.comp continuous_fst).mul continuous_snd)
  have hI : Integrable (Function.uncurry D) ((volume.restrict (uIoc (0:ℝ) 1)).prod μ) := by
    apply (integrable_prod_iff hDc.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun s ↦ (measurePreserving_mul_left μ (g s)).integrable_comp_of_integrable hdi,?_⟩
    simp only [Function.uncurry_apply_pair]
    have H (s : ℝ) : ∫ y, ‖D s y‖ ∂μ = ∫ y, ‖d y‖ ∂μ :=
      integral_mul_left_eq_self (μ := μ) (fun y ↦ ‖d y‖) (g s)
    simp_rw [H]
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (continuous_const.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self
  have hs (x : G) : (∫ s in (0:ℝ)..1, D s x) = f (g 1 * x) - f (g 0 * x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hD x t)
      ((hd.comp (hg.mul_const x)).intervalIntegrable _ _)
  have H := intervalIntegral_integral_swap (μ := μ) (f := D) hI
  have Hl (s : ℝ) : ∫ y, D s y ∂μ = ∫ y, d y ∂μ := integral_mul_left_eq_self _ _
  simp_rw [hs,Hl] at H
  have hx (s : ℝ) : Integrable (fun x ↦ f (g s*x)) μ :=
    (measurePreserving_mul_left μ (g s)).integrable_comp_of_integrable hf
  rw [integral_sub (hx 1) (hx 0),integral_mul_left_eq_self,integral_mul_left_eq_self,sub_self] at H
  simpa using H

/-- On the real logarithmic parameter, the physical S-adelic theta generator
gives the derivative of its quotient function at every point of every orbit. -/
private theorem sLocalMellinSchwartzBounds_meyer_theta_real_orbit (T : Finset V) (γ : ℝ≥0ˣ →ₜ* (SAdeleRing F T)ˣ)
    (f : ℬₛ(T)) (x : (SIdeleQuotient F T)) (s : ℝ) :
    let e : ℝ ≃ₜ ℝ≥0ˣ := (Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm)
    let q : (SAdeleRing F T)ˣ →* (SIdeleQuotient F T) := QuotientGroup.mk' _
    HasDerivAt (fun t : ℝ ↦ sLocalAdelicThetaOnClasses F T f (q (γ (e t)) * x))
      (sLocalAdelicThetaOnClasses F T (sAdeleDirectionalDeriv F T γ f) (q (γ (e s)) * x)) s := by
  intro e q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
  let y := γ (e s) * g
  let D := sAdeleDirectionalDeriv F T γ f
  let Θ := sLocalAdelicTheta F T
  have he0 : e 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hey (u v : ℝ) : e (u+v) = e u * e v := Units.ext (NNReal.coe_inj.mp (Real.exp_add u v))
  have he : Tendsto e (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℝ≥0ˣ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((e.continuous.tendsto' _ _ he0).mono_left nhdsWithin_le_nhds),?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun h ↦ ht (e.injective (h.trans he0.symm))
  have hmul (t : ℝ) : γ (e (s+t)) * g = γ (e t) * y := by
    rw [hey,map_mul γ (e s) (e t)]; dsimp [y]; ac_rfl
  let θ (v : ℬₛ(T)) (t : ℝ) := Θ v (γ (e t) * g)
  have hco (v : ℬₛ(T)) (t : ℝ) :
      sLocalAdelicThetaOnClasses F T v (q (γ (e t)) * q g) = θ v t := by
    rw [← map_mul q]
    exact sLocalAdelicThetaOnClasses_mk F T v _
  change HasDerivAt (fun t : ℝ ↦ sLocalAdelicThetaOnClasses F T f (q (γ (e t)) * q g))
    (sLocalAdelicThetaOnClasses F T D (q (γ (e s)) * q g)) s
  simp_rw [hco]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have ht : Tendsto (fun t : ℝ ↦ (θ f (s+t)-θ f s) / ((Real.exp t : ℂ)-1))
      (𝓝[≠] 0) (𝓝 (θ D s)) := by
    apply ((sLocalAdelicTheta_directionalDeriv F T γ f y).comp he).congr
    intro t
    change (Θ f (γ (e t)*y)-Θ f y) / ((Real.exp t : ℂ)-1) =
      (Θ f (γ (e (s+t))*g)-Θ f y) / ((Real.exp t : ℂ)-1)
    rw [hmul]
  have hratio : Tendsto (fun t : ℝ ↦ (t⁻¹ : ℝ) • ((Real.exp t : ℂ)-1))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa using (hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_exp 0).ofReal_comp)
  have hprod := hratio.mul ht
  rw [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ) (a := 0)] with t ht0
  have hne : (Real.exp t : ℂ)-1 ≠ 0 := sub_ne_zero.mpr (fun hi ↦
    ht0 (Real.exp_injective (by rw [Real.exp_zero]; exact_mod_cast hi)))
  rw [smul_mul_assoc,mul_div_left_comm,div_self hne,mul_one]

/-- The derivative of a raw flow acts by the negative flow exponent on
Mellin values, independently of the angular character and the positive line. -/
private theorem sLocalMellinSchwartzBounds_meyer_full_flow_multiplier (T : Finset V) (γ : ℝ≥0ˣ →ₜ* (SAdeleRing F T)ˣ)
    (f : ℬₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T)) (z β : ℂ) (hz : 0 < z.re)
    (hβ : ∀ t : ℝ, chartₜ(T,χ) z (QuotientGroup.mk (γ
      ((Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm) t))) =
        Complex.exp ((t : ℂ) * β)) :
    sLocalThetaMellinIntegral (sAdeleDirectionalDeriv F T γ f) (chartₜ(T,χ) z) =
      -β * sLocalThetaMellinIntegral f (chartₜ(T,χ) z) := by
  let : MeasurableSpace (SIdeleQuotient F T) := borel _
  let : BorelSpace (SIdeleQuotient F T) := ⟨rfl⟩
  let (v : T) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing F T) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : T) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F T)ˣ := (sIdeleGroup_description F T).1.secondCountableTopology
  let : SecondCountableTopology (SIdeleQuotient F T) := inferInstance
  have := isClosed_sProjectedDiagonal (F := F) (S := T)
  let : T2Space (SIdeleQuotient F T) := inferInstanceAs (T2Space (_ ⧸ _))
  let : LocallyCompactSpace (SAdeleRing F T)ˣ := (sIdeleGroup_description F T).2.2.1
  let : LocallyCompactSpace (SIdeleQuotient F T) := inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
  let μ := sLocalQuotientTamagawaMeasure F T
  let : μ.IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := T)).1
  let q : (SAdeleRing F T)ˣ →ₜ* (SIdeleQuotient F T) := ⟨QuotientGroup.mk' _,QuotientGroup.continuous_mk⟩
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g (t : ℝ) := q (γ (e t))
  let c := chartₜ(T,χ) z
  let D := sAdeleDirectionalDeriv F T γ f
  let W (v : ℬₛ(T)) (x : (SIdeleQuotient F T)) := sLocalAdelicThetaOnClasses F T v x * c x
  have hW (v) : Integrable (W v) μ := sLocalThetaMellinIntegral_integrable v c ⟨χ,z,hz,rfl⟩
  have hcont (v) : Continuous (W v) := (sLocalAdelicThetaOnClasses F T v).continuous.mul c.continuous
  let d (x : (SIdeleQuotient F T)) := W D x + β * W f x
  have hd : Continuous d := (hcont D).add (continuous_const.mul (hcont f))
  have hdi : Integrable d μ := (hW D).add ((hW f).const_mul β)
  have hpoint (x : (SIdeleQuotient F T)) (t : ℝ) : HasDerivAt (fun s ↦ W f (g s * x)) (d (g t * x)) t := by
    have he (s : ℝ) : c (g s * x) = Complex.exp ((s:ℂ)*β) * c x := (map_mul c _ _).trans (congrArg (· * c x) (hβ s))
    have hchar : HasDerivAt (fun s : ℝ ↦ c (g s * x)) (β * c (g t * x)) t := by
      simp_rw [he]
      have H := ((((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const β).cexp).mul_const (c x))
      exact H.congr_deriv (by change Complex.exp ((t:ℂ)*β) * (1*β)*c x = _; ring)
    refine ((sLocalMellinSchwartzBounds_meyer_theta_real_orbit T γ f x t).mul hchar).congr_deriv ?_
    change sLocalAdelicThetaOnClasses F T D (g t*x) * c (g t*x) +
      sLocalAdelicThetaOnClasses F T f (g t*x) * (β * c (g t*x)) =
      sLocalAdelicThetaOnClasses F T D (g t*x) * c (g t*x) +
        β * (sLocalAdelicThetaOnClasses F T f (g t*x) * c (g t*x))
    ring
  have hzero := sLocalMellinSchwartzBounds_meyer_integral_flow_derivative_zero μ g
    (q.continuous.comp (γ.continuous.comp e.continuous)) (W f) d hd (hW f) hdi hpoint
  change (∫ x, W D x + β * W f x ∂μ) = 0 at hzero
  rw [integral_add (hW D) ((hW f).const_mul β),integral_const_mul] at hzero
  change (∫ x, W D x ∂μ) = -β * ∫ x, W f x ∂μ
  linear_combination hzero

/-- A positive Mellin line is bounded simultaneously in every unitary character and height. -/
private theorem sLocalMellinSchwartzBounds_meyer_uniform_unweighted (T : Finset V) (f : ℬₛ(T)) (a : ℝ) (_ha : 0 < a) :
    ∃ B : ℝ, ∀ (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ), z.re = a →
      ‖sLocalThetaMellinIntegral f (chartₜ(T,χ) z)‖ ≤ B := by
  let μ := sLocalQuotientTamagawaMeasure F T
  let Θ := sLocalAdelicThetaOnClasses F T f
  let v (q : (SIdeleQuotient F T)) := ((sIdeleQuotientNorm F T q).val : ℝ)
  have hnorm (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ) (q) :
      ‖Θ q * chartₜ(T,χ) z q‖ = ‖Θ q‖ * v q ^ z.re := by
    rw [norm_mul]
    congr 1
    change ‖(χ q : ℂ) * ((v q : ℝ) : ℂ)^z‖ = _
    rw [norm_mul,Circle.norm_coe,one_mul]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _
  refine ⟨∫ q, ‖Θ q‖ * v q^a ∂μ, fun χ z hz ↦ ?_⟩
  change ‖∫ q, Θ q * chartₜ(T,χ) z q ∂μ‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans_eq
  exact integral_congr_ae (.of_forall fun q ↦ hz ▸ hnorm χ z q)

/-- Finite uniform differentiations of a physical test bound every power of
one plus the sum of the associated real frequency magnitudes. -/
private theorem sLocalMellinSchwartzBounds_meyer_joint_weights {E X ι : Type*} [Fintype ι] (M : E → X → ℂ)
    (v : ι → X → ℝ) (D : ι → E → E) (hM : ∀ f, ∃ B : ℝ, ∀ x, ‖M f x‖ ≤ B)
    (hv : ∀ i f x, |v i x| * ‖M f x‖ ≤ ‖M (D i f) x‖) :
    ∀ j : ℕ, ∀ f, ∃ B : ℝ, ∀ x,
      (1+∑ i, |v i x|)^j * ‖M f x‖ ≤ B := by
  intro j
  induction j with
  | zero => simpa using hM
  | succ n ih =>
    intro f
    choose B hB using fun i ↦ ih (D i f)
    obtain ⟨B₀,h₀⟩ := ih f
    refine ⟨B₀ + ∑ i, B i,fun x ↦ ?_⟩
    let T := 1+∑ i, |v i x|
    have hT : 0 ≤ T := add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    have hsum : ∑ i, T^n * (|v i x| * ‖M f x‖) ≤ ∑ i, B i := by
      exact Finset.sum_le_sum fun i _ ↦ (mul_le_mul_of_nonneg_left (hv i f x)
        (pow_nonneg hT n)).trans (hB i x)
    calc
      T^(n+1) * ‖M f x‖ =
          T^n * ‖M f x‖ + ∑ i, T^n * (|v i x| * ‖M f x‖) := by
        rw [pow_succ]
        conv_lhs => rw [show T^n * T = T^n * (1+∑ i, |v i x|) from rfl]
        rw [mul_add,mul_one,add_mul,Finset.mul_sum,Finset.sum_mul]
        simp only [mul_assoc]
      _ ≤ _ := add_le_add (h₀ x) hsum

/-- Polynomial seminorm weights and complex radial powers are controlled by
the joint family with one plus the sum of absolute lattice coordinates and the height. -/
private theorem sLocalMellinSchwartzBounds_meyer_bound_two_weights {X ι : Type*} [Fintype ι] (M : X → ℂ)
    (z : X → ℂ) (p : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (l : ι → X → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hp : ∀ x, p x ≤ C * (1+∑ i, |l i x|))
    (H : X → ℝ) (hH : ∀ x, H x = 1 + ‖z x‖ + ∑ i, |l i x|)
    (hb : ∀ j : ℕ, ∃ B : ℝ, ∀ x, (H x)^j * ‖M x‖ ≤ B)
    (k m : ℕ) : ∃ B : ℝ, ∀ x, (1+p x)^k * ‖(z x)^m * M x‖ ≤ B := by
  obtain ⟨B,hB⟩ := hb (k+m)
  refine ⟨(1+C)^k * B,fun x ↦ ?_⟩
  have hsum : 0 ≤ ∑ i, |l i x| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have h1 : 1 ≤ H x := by rw [hH]; linarith [norm_nonneg (z x)]
  have hz : ‖z x‖ ≤ H x := by rw [hH]; linarith
  have hpx : 1+p x ≤ (1+C)*H x := by
    rw [hH]
    nlinarith [hp x,norm_nonneg (z x),mul_nonneg hC (norm_nonneg (z x))]
  have hpx0 : 0 ≤ 1+p x := add_nonneg zero_le_one (hp0 x)
  have hnon : 0 ≤ 1+C := by linarith
  rw [norm_mul,norm_pow]
  calc
    (1+p x)^k * (‖z x‖^m * ‖M x‖) ≤ ((1+C)*H x)^k * ((H x)^m * ‖M x‖) := by
      gcongr
    _ = (1+C)^k * ((H x)^(k+m) * ‖M x‖) := by rw [mul_pow,pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB x) (pow_nonneg hnon k)

/-- Divisibility and self-duality realize the unnormalized frequency through a compact group. -/
private theorem sLocalMellinSchwartzBounds_meyer_normalized_real_coordinate.{u} {N A : Type u}
    [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N] [T2Space N] [CompactSpace N]
    [CommGroup A] (j : A →* PontryaginDual N) (hj : Injective j) (l : A →* Multiplicative ℝ) :
    ∃ γ : Multiplicative ℝ →ₜ* N, ∀ (χ : A) (t : ℝ), j χ (γ (Multiplicative.ofAdd t)) =
      Circle.exp (t * (l χ).toAdd) := by
  let l' : A →* Multiplicative ℝ :=
    { toFun x := Multiplicative.ofAdd ((l x).toAdd/(2*Real.pi))
      map_one' := by change (l 1).toAdd/(2*Real.pi) = 0; simp
      map_mul' x y := by
        change (l (x*y)).toAdd/(2*Real.pi) = (l x).toAdd/(2*Real.pi) + (l y).toAdd/(2*Real.pi)
        rw [map_mul]; exact add_div _ _ _ }
  obtain ⟨g,hg⟩ := sLocalMellinSchwartzBounds_meyer_real_coordinate_on_compact j hj l'
  refine ⟨g,fun χ t ↦ (hg χ t).trans (congrArg Circle.exp ?_)⟩
  change 2*Real.pi*(t*((l χ).toAdd/(2*Real.pi))) = t*(l χ).toAdd
  field_simp [Real.pi_ne_zero]

private theorem sLocalMellinSchwartzBounds_meyer_angular_normone_coordinate (T : Finset V)
    (τ : ℝ≥0ˣ →ₜ* (SIdeleQuotient F T)) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (H : Subgroup (PontryaginDual.map τ).ker) (l : H →* Multiplicative ℝ) :
    ∃ g : Multiplicative ℝ →ₜ* (sIdeleQuotientNorm F T).ker, ∀ (χ : H) (t : ℝ),
      χ.val.val (g (Multiplicative.ofAdd t)).val = Circle.exp (t*(l χ).toAdd) := by
  let N := (sIdeleQuotientNorm F T).ker
  have := isClosed_sProjectedDiagonal (F := F) (S := T)
  let : T2Space (SIdeleQuotient F T) := inferInstanceAs (T2Space (_ ⧸ _))
  have : CompactSpace N := isCompact_iff_compactSpace.mp
    (show IsCompact ((sIdeleQuotientNorm F T) ⁻¹' ({1} : Set ℝ≥0ˣ)) from
      (isProperMap_sIdeleQuotientNorm F T).isCompact_preimage isCompact_singleton)
  let ι : N →ₜ* (SIdeleQuotient F T) := ⟨N.subtype,continuous_subtype_val⟩
  let j : H →* PontryaginDual N := (PontryaginDual.map ι).toMonoidHom.comp
    ((PontryaginDual.map τ).ker.subtype.comp H.subtype)
  have hj : Injective j := by
    intro x y h
    apply Subtype.ext; apply Subtype.ext; apply PontryaginDual.ext
    intro c
    let u := sIdeleQuotientNorm F T c
    let n : N := ⟨c/τ u,by change sIdeleQuotientNorm F T (c/τ u) = 1; rw [map_div,hτ u,div_self']⟩
    have ht (w : H) : w.val.val (τ u) = 1 :=
      DFunLike.congr_fun (MonoidHom.mem_ker.mp w.val.property) u
    have hh : x.val.val (c/τ u) = y.val.val (c/τ u) := DFunLike.congr_fun h n
    simpa only [map_div,ht,div_one] using hh
  exact sLocalMellinSchwartzBounds_meyer_normalized_real_coordinate j hj l

private theorem sLocalMellinSchwartzBounds_meyer_lift_normone_flow (T : Finset V)
    (g : Multiplicative ℝ →ₜ* (sIdeleQuotientNorm F T).ker) :
    ∃ γ : ℝ≥0ˣ →ₜ* (SAdeleRing F T)ˣ, ∀ t : ℝ, QuotientGroup.mk (γ
      ((Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm) t)) =
      (g (Multiplicative.ofAdd t)).val := by
  let N := (sIdeleQuotientNorm F T).ker
  let ι : N →ₜ* (SIdeleQuotient F T) := ⟨N.subtype,continuous_subtype_val⟩
  let q : (SAdeleRing F T)ˣ →ₜ* (SIdeleQuotient F T) := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  have hq : IsCoveringMap q :=
    ((sProjectedDiagonal F T).isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr
      (discreteTopology_sProjectedDiagonal (F := F) (S := T)))).isCoveringMap
  obtain ⟨v,hv⟩ := sLocalMellinSchwartzBounds_meyer_lift_real_flow q hq (ι.comp g)
  let γ := v.comp (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
  refine ⟨γ,fun t ↦ ?_⟩
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have ht : positiveRealLogEquiv (e t) = Multiplicative.ofAdd t := by
    change (positiveRealLogEquiv (e t)).toAdd = t
    rw [positiveRealLogEquiv_apply]; exact Real.log_exp t
  show q (γ (e t)) = ι (g (Multiplicative.ofAdd t))
  change q (v (positiveRealLogEquiv (e t))) = _
  rw [ht]; exact DFunLike.congr_fun hv _

/-- A real lattice coordinate is a logarithmic frequency of a physical
norm-one S-local flow for the *specified* norm section. -/
private theorem sLocalMellinSchwartzBounds_meyer_angular_realizing_flow (T : Finset V)
    (τ : ℝ≥0ˣ →ₜ* (SIdeleQuotient F T)) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (H : Subgroup (PontryaginDual.map τ).ker) (l : H →* Multiplicative ℝ) :
    ∃ γ : ℝ≥0ˣ →ₜ* (SAdeleRing F T)ˣ, ∀ (χ : H) (z : ℂ) (t : ℝ),
      chartₜ(T,χ.val.val) z (QuotientGroup.mk (γ
        ((Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm) t))) =
        Complex.exp ((t : ℂ) * ((l χ).toAdd * Complex.I)) := by
  obtain ⟨g,hg⟩ := sLocalMellinSchwartzBounds_meyer_angular_normone_coordinate (F := F) T τ hτ H l
  refine (sLocalMellinSchwartzBounds_meyer_lift_normone_flow (F := F) T g).elim fun γ hγ ↦ ?_
  refine ⟨γ,fun χ z t ↦ ?_⟩
  let y := g (Multiplicative.ofAdd t)
  refine (congrArg (chartₜ(T,χ.val.val) z) (hγ t)).trans ?_
  change (χ.val.val y.val : ℂ) * (((sIdeleQuotientNorm F T y.val).val : ℝ) : ℂ)^z = _
  have hc := congrArg (fun c : Circle ↦ (c : ℂ)) (hg χ t)
  have hn := congrArg (fun n : ℝ≥0ˣ ↦ ((n.val : ℝ) : ℂ)^z) y.property
  refine (congrArg₂ (· * ·) hc hn).trans ?_
  simp [Circle.coe_exp,mul_assoc]

/-- The lift of the specified section realizes the pure radial exponent. -/
private theorem sLocalMellinSchwartzBounds_meyer_radial_realizing_flow (T : Finset V)
    (τ : ℝ≥0ˣ →ₜ* (SIdeleQuotient F T)) (hτ : RightInverse τ (sIdeleQuotientNorm F T)) :
    ∃ γ : ℝ≥0ˣ →ₜ* (SAdeleRing F T)ˣ, ∀ (χ : (PontryaginDual.map τ).ker) (z : ℂ) (t : ℝ),
      chartₜ(T,χ.val) z (QuotientGroup.mk (γ
        ((Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm) t))) =
        Complex.exp ((t : ℂ) * z) := by
  obtain ⟨γ,hγ,hq⟩ := sLocalMellinSchwartzBounds_meyer_lift_section T τ hτ
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  refine ⟨γ,fun χ z t ↦ ?_⟩
  have h : χ.val (τ (e t)) = 1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp χ.property) _
  change (χ.val (QuotientGroup.mk (γ (e t))) : ℂ) *
    (((sIdeleQuotientNorm F T (QuotientGroup.mk (γ (e t)))).val : ℝ) : ℂ)^z = _
  rw [hq,h,hτ]
  change (1 : ℂ) * ((Real.exp t : ℝ) : ℂ)^z = _
  rw [one_mul,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp]

private theorem sLocalMellinSchwartzBounds_meyer_stage_weights_of_multipliers {E H : Type*} [CommGroup H] [Group.FG H]
    (M : E → H → ℂ → ℂ) (a : ℝ)
    (hun : ∀ w, ∃ B : ℝ, ∀ (χ : H) (z : ℂ), z.re = a → ‖M w χ z‖ ≤ B)
    (rad : ∃ D₀ : E → E, ∀ (w : E) (χ : H) (z : ℂ), z.re = a → M (D₀ w) χ z = -z * M w χ z)
    (ang : ∀ l : H →* Multiplicative ℝ, ∃ D : E → E, ∀ (w : E) (χ : H) (z : ℂ), z.re = a →
      M (D w) χ z = -((l χ).toAdd * Complex.I) * M w χ z)
    (f : E) (p : GroupSeminorm H) (k m : ℕ) : ∃ B : ℝ, ∀ (χ : H) (z : ℂ), z.re = a →
      (1+p χ)^k * ‖z^m*M f χ z‖ ≤ B := by
  obtain ⟨r,l,hl⟩ := sLocalMellinSchwartzBounds_meyer_abelian_coordinates H
  obtain ⟨C,hC,hp⟩ := hl p
  choose D₁ h₁ using fun i ↦ ang (l i)
  obtain ⟨D₀,h₀⟩ := rad
  let X := H × {z : ℂ // z.re = a}
  let Z (w : E) (x : X) := M w x.1 x.2.val
  let L (i : Fin r) (x : X) := (l i x.1).toAdd
  let v : Option (Fin r) → X → ℝ := fun i x ↦ i.elim ‖x.2.val‖ (fun j ↦ L j x)
  let D : Option (Fin r) → E → E := fun i ↦ i.elim D₀ D₁
  have hm (w) : ∃ B : ℝ, ∀ x, ‖Z w x‖ ≤ B := by
    obtain ⟨B,hB⟩ := hun w
    exact ⟨B,fun x ↦ hB x.1 x.2.val x.2.property⟩
  have hd (i) (w : E) (x : X) : |v i x| * ‖Z w x‖ ≤ ‖Z (D i w) x‖ := by
    cases i with
    | none =>
      change |‖x.2.val‖| * ‖M w x.1 x.2.val‖ ≤ ‖M (D₀ w) x.1 x.2.val‖
      rw [h₀ w x.1 x.2.val x.2.property,norm_mul,norm_neg,abs_of_nonneg (norm_nonneg _)]
    | some j =>
      change |(l j x.1).toAdd| * ‖M w x.1 x.2.val‖ ≤ ‖M (D₁ j w) x.1 x.2.val‖
      rw [h₁ j w x.1 x.2.val x.2.property,norm_mul,norm_neg,norm_mul,Complex.norm_I,mul_one]
      have hr : ‖(((l j x.1).toAdd : ℝ) : ℂ)‖ = |(l j x.1).toAdd| :=
        (Complex.norm_real _).trans (Real.norm_eq_abs _)
      rw [hr]
  let W (x : X) := 1+∑ i, |v i x|
  have hW (x : X) : W x = 1 + ‖x.2.val‖ + ∑ i, |L i x| := by
    simp [W,v,Fintype.sum_option,abs_of_nonneg (norm_nonneg _),add_assoc]
  have hall := sLocalMellinSchwartzBounds_meyer_joint_weights Z v D hm hd
  obtain ⟨B,hB⟩ := sLocalMellinSchwartzBounds_meyer_bound_two_weights (Z f) (fun x : X ↦ x.2.val) (fun x ↦ p x.1)
    (fun x ↦ apply_nonneg _ _) L C hC (fun x ↦ hp x.1) W hW (fun j ↦ hall j f) k m
  exact ⟨B,fun χ z hz ↦ hB (χ,⟨z,hz⟩)⟩

private theorem sLocalMellinSchwartzBounds_meyer_all_scalar_angular_weights (T : Finset V)
    (τ : ℝ≥0ˣ →ₜ* (SIdeleQuotient F T)) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (f : ℬₛ(T)) (a : ℝ) (ha : 0 < a) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ (z : ℂ), z.re = a → sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral f (chartₜ(T,χ.val.val) z)‖ ≤ B := by
  have hf : Bornology.IsVonNBounded ℂ (range (fun _ : ℕ ↦ (sLocalAdelicTheta F T).ker.mkQ f)) := by
    rw [range_const]; exact Bornology.isVonNBounded_singleton _
  obtain ⟨H,hfg,hH⟩ := sLocalMellinSchwartzBounds_meyer_general_angular_support (F := F) T τ hτ (fun _ ↦ f) hf
  refine ⟨H,hfg,fun χ hn z hz ↦ hH χ hn 0 z (ha.trans_eq hz.symm),fun p k m ↦ ?_⟩
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hfg
  let M (w : ℬₛ(T)) (χ : H) (z : ℂ) := sLocalThetaMellinIntegral w (chartₜ(T,χ.val.val) z)
  refine sLocalMellinSchwartzBounds_meyer_stage_weights_of_multipliers M a ?_ ?_ ?_ f p k m
  · intro w
    obtain ⟨B,hB⟩ := sLocalMellinSchwartzBounds_meyer_uniform_unweighted (F := F) T w a ha
    exact ⟨B,fun χ ↦ hB χ.val.val⟩
  · obtain ⟨g,hg⟩ := sLocalMellinSchwartzBounds_meyer_radial_realizing_flow (F := F) T τ hτ
    exact ⟨sAdeleDirectionalDeriv F T g,fun w χ z hz ↦ sLocalMellinSchwartzBounds_meyer_full_flow_multiplier (F := F) T g w
      χ.val.val z z (ha.trans_eq hz.symm) (hg χ.val z)⟩
  · intro l
    refine (sLocalMellinSchwartzBounds_meyer_angular_realizing_flow (F := F) T τ hτ H l).elim fun g hg ↦ ?_
    exact ⟨sAdeleDirectionalDeriv F T g,fun w χ z hz ↦ sLocalMellinSchwartzBounds_meyer_full_flow_multiplier (F := F) T g w
      χ.val.val z ((l χ).toAdd * Complex.I) (ha.trans_eq hz.symm) (hg χ z)⟩

/-- The single-test comparison applies in particular to the higher-degree, infinite angular-support case. -/
private theorem sLocalMellinSchwartzBounds_meyer_single_test_angular_bound (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (f : ℬₛ(T)) (hF : Module.finrank ℚ F ≠ 1)
    (a : ℝ) (ha : 1 < a)
    (hs : {χ : (PontryaginDual.map τ).ker | ∃ z : ℂ, z.re = a ∧
      sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z) ≠ 0}.Infinite) :
    ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ (z : ℂ), z.re = a → sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral f (chartₜ(T,χ.val.val) z)‖ ≤ B := by
  exact sLocalMellinSchwartzBounds_meyer_all_scalar_angular_weights T τ hτ f a (zero_lt_one.trans ha)

/-- A single test either has finitely many nonzero angular coefficients on the
line or belongs to the higher-degree, infinite-support comparison. -/
private theorem sLocalMellinSchwartzBounds_meyer_single_test_from_active (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (f : ℬₛ(T)) (hF : Module.finrank ℚ F ≠ 1)
    (a : ℝ) (ha : 1 < a) : ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ (z : ℂ), z.re = a → sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z) = 0) ∧
      (∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral f (chartₜ(T,χ.val.val) z)‖ ≤ B) := by
  let S : Set (PontryaginDual.map τ).ker := {χ | ∃ z : ℂ, z.re = a ∧ sLocalThetaMellinIntegral f (chartₜ(T,χ.val) z) ≠ 0}
  by_cases hS : S.Finite
  · have hf : Bornology.IsVonNBounded ℂ (range fun _ : ℕ ↦ (sLocalAdelicTheta F T).ker.mkQ f) := by
      rw [range_const]; exact Bornology.isVonNBounded_singleton _
    obtain ⟨H,hH,hs,hw⟩ := sLocalMellinSchwartzBounds_meyer_finite_content T τ (fun _ ↦ f) hf a (zero_lt_one.trans ha) S hS
      (fun χ hn _ z hz ↦ not_not.mp (fun h0 ↦ hn ⟨z,hz,h0⟩))
    refine ⟨H,hH,fun χ hχ z hz ↦ hs χ hχ 0 z hz,fun p k m ↦ ?_⟩
    obtain ⟨B,hB⟩ := hw p k m
    exact ⟨B,fun χ z hz ↦ hB χ 0 z hz⟩
  · exact sLocalMellinSchwartzBounds_meyer_single_test_angular_bound T τ hτ f hF a ha hS

section
open scoped FourierTransform

/-- A uniform quadratic bound on one Mellin line controls the original
functions with the corresponding radial weight. The estimate holds down
to every positive radius and does not require derivatives of Mellin values. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_inverse_ray (a : ℝ) (ha : 1 ≤ a) (f : ℕ → ℝ → ℂ)
    (hc : ∀ n, Continuous (f n)) (hM : ∀ n, MellinConvergent (f n) a)
    (hC : ∀ n, Continuous (fun t : ℝ ↦ mellin (f n) ((a : ℂ) + (t : ℂ)*Complex.I)))
    (M : ℝ) (hb : ∀ (n : ℕ) (t : ℝ),
      ‖((a : ℂ) + (t : ℂ)*Complex.I)^2 * mellin (f n) ((a : ℂ) + (t : ℂ)*Complex.I)‖ ≤ M) :
    ∀ n (x : ℝ), 0 < x → x^a * ‖f n x‖ ≤ M / 2 := by
  let L (t : ℝ) := (a : ℂ) + (t : ℂ)*Complex.I
  have hm : 0 ≤ M := (norm_nonneg _).trans (hb 0 0)
  have ht (t : ℝ) : 0 < 1+t^2 := by positivity
  have hk : Integrable (fun t : ℝ ↦ M * (1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul M
  have hdec (n : ℕ) (t : ℝ) : ‖mellin (f n) (L t)‖ ≤ M * (1+t^2)⁻¹ := by
    rw [← div_eq_mul_inv,le_div_iff₀ (ht t),mul_comm]
    have hpow : 1+t^2 ≤ ‖L t‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [L]; nlinarith
    exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans ((by
      simpa only [norm_mul,norm_pow,L] using hb n t) : _)
  intro n x hx
  have hv : Complex.VerticalIntegrable (mellin (f n)) a := by
    apply hk.mono' (hC n).aestronglyMeasurable
    exact .of_forall (hdec n)
  rw [← mellinInv_mellin_eq a (f n) hx (hM n) hv (hc n).continuousAt]
  let s := x^(-a)
  have hs : 0 ≤ s := Real.rpow_nonneg hx.le _
  have hi :
      ‖∫ t : ℝ, (x : ℂ)^(-(L t)) • mellin (f n) (L t)‖ ≤ s * M * Real.pi := by
    have hg : Integrable (fun t : ℝ ↦ s * (M * (1+t^2)⁻¹)) := hk.const_mul s
    have h := norm_integral_le_of_norm_le hg (.of_forall fun t ↦ show
        ‖(x : ℂ)^(-(L t)) • mellin (f n) (L t)‖ ≤ s * (M * (1+t^2)⁻¹) from by
      rw [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simpa [s,L] using mul_le_mul_of_nonneg_left (hdec n t) hs)
    simpa only [integral_const_mul, integral_univ_inv_one_add_sq,mul_assoc] using h
  have ha0 : 0 ≤ x^a := Real.rpow_nonneg hx.le _
  change x^a * ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
    (x : ℂ)^(-(L t)) • mellin (f n) (L t))‖ ≤ M/2
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  have hh : x^a * s = 1 := by
    rw [show s = x^(-a) from rfl,← Real.rpow_add hx,add_neg_cancel,Real.rpow_zero]
  calc
    x^a * ((1/(2*Real.pi))*_) ≤ x^a * ((1/(2*Real.pi))*(s*M*Real.pi)) := by
      gcongr
    _ = M/2 := by
      field_simp [Real.pi_ne_zero]; nlinarith [congrArg (· * M * Real.pi) hh]

/-- A single weighted absolute Fourier moment bounds the corresponding
ordinary derivative everywhere. This includes the origin, which Mellin ray
inversion itself does not control. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_derivative_from_fourier_moment (f : SchwartzMap ℝ ℂ)
    (j : ℕ) (M : ℝ) (h : ∫ x : ℝ, |x|^j * ‖(𝓕 f) x‖ ≤ M) :
    ∀ x, ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ (2*Real.pi)^j * M := by
  let g : SchwartzMap ℝ ℂ := 𝓕 f
  have hi (k : ℕ) : Integrable (fun x : ℝ ↦ x^k • g x) := by
    apply (g.integrable_pow_mul volume k).mono' (by fun_prop)
    exact .of_forall fun x ↦ by simp [Real.norm_eq_abs]
  have hF : (f : ℝ → ℂ) = fun x : ℝ ↦ 𝓕 (g : ℝ → ℂ) (-x) := by
    rw [← show 𝓕⁻ g = f from FourierTransform.fourierInv_fourier_eq f]
    funext x
    rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg]
  intro x
  rw [hF,iteratedDeriv_comp_neg]
  have hforce : ‖(-1 : ℝ)^j • iteratedDeriv j (𝓕 (g : ℝ → ℂ)) (-x)‖ =
      ‖iteratedDeriv j (𝓕 (g : ℝ → ℂ)) (-x)‖ := by simp
  rw [hforce,Real.iteratedDeriv_fourier (N := (j : ℕ∞)) (fun k _ ↦ hi k) le_rfl]
  refine (Real.norm_fourier_le_integral_norm _ _).trans ?_
  have he (u : ℝ) : ‖(-2*Real.pi*Complex.I*u)^j • g u‖ =
      (2*Real.pi)^j * (|u|^j * ‖g u‖) := by
    simp [norm_pow,abs_of_nonneg Real.pi_pos.le,Real.norm_eq_abs,
      mul_pow,mul_assoc]
  simp_rw [he,integral_const_mul]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg (by positivity) j)

/-- On the positive ray, Re(s)=3/2 controls every positive-order additive
moment near zero. An arbitrarily large positive line makes the same moment
integrable at infinity. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_positive_moments (f : ℕ → SchwartzMap ℝ ℂ)
    (h : ∀ a : ℝ, 1 < a → ∃ M ≥ (0:ℝ), ∀ n (x : ℝ), 0 < x → x^a * ‖f n x‖ ≤ M) :
    ∀ j : ℕ, 0 < j → ∃ M : ℝ, ∀ n, ∫ x in Ioi (0:ℝ), x^j * ‖f n x‖ ≤ M := by
  intro j hj
  obtain ⟨A,hA,hsmall⟩ := h (3/2) (by norm_num)
  obtain ⟨B,hB,hlarge⟩ := h ((j:ℝ)+2) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  let e := (j:ℝ)-3/2
  have hs : -1 < e := by
    dsimp [e]
    have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
    linarith
  let S := Ioc (0 : ℝ) 1
  let T := Ioi (1 : ℝ)
  have hIs : IntegrableOn (fun x : ℝ ↦ x^e) S := by
    apply (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1) hs).1
  have hIt : IntegrableOn (fun x : ℝ ↦ x^(-2:ℝ)) T := integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  refine ⟨(∫ x in S, A*x^e) + (∫ x in T, B*x^(-2:ℝ)), fun n ↦ ?_⟩
  let w (x : ℝ) := x^j * ‖f n x‖
  have hw : IntegrableOn w (Ioi 0) := by
    apply ((f n).integrable_pow_mul volume j).integrableOn.congr_fun _ measurableSet_Ioi
    intro x hx; simp [w,Real.norm_of_nonneg hx.le]
  have hT₀ : T ⊆ Ioi (0:ℝ) := fun x hx ↦ zero_lt_one.trans hx
  have hS₀ : S ⊆ Ioi (0:ℝ) := fun x hx ↦ hx.1
  have heq : Ioi (0:ℝ) = S ∪ T := by ext x; change 0<x ↔ (0<x ∧ x≤1) ∨ 1<x; constructor <;> intro hx <;> grind
  change ∫ x in Ioi (0:ℝ), w x ≤ _
  rw [heq,setIntegral_union (by apply Set.disjoint_left.mpr; intro x hx hx'; exact (not_lt_of_ge hx.2) hx')
    measurableSet_Ioi (hw.mono_set hS₀) (hw.mono_set hT₀)]
  apply add_le_add
  · apply setIntegral_mono_on (hw.mono_set hS₀) (hIs.const_mul A) measurableSet_Ioc
    intro x hx
    have hx0 := hx.1
    have H := mul_le_mul_of_nonneg_left (hsmall n x hx0) (Real.rpow_nonneg hx0.le e)
    rw [← mul_assoc,← Real.rpow_add hx0,show e+(3/2:ℝ) = (j:ℝ) by dsimp [e]; ring,
      Real.rpow_natCast,mul_comm _ A] at H
    exact H
  · apply setIntegral_mono_on (hw.mono_set hT₀) (hIt.const_mul B) measurableSet_Ioi
    intro x hx
    have hx0 := hT₀ hx
    have H := mul_le_mul_of_nonneg_left (hlarge n x hx0) (Real.rpow_nonneg hx0.le (-2))
    rw [← mul_assoc,← Real.rpow_add hx0,show (-2:ℝ)+((j:ℝ)+2) = (j:ℝ) by ring,
      Real.rpow_natCast,mul_comm _ B] at H
    exact H

/-- Uniform derivative bounds at the origin and all weighted ray estimates
at infinity give boundedness in the actual real Schwartz space. The missing
zeroth-order estimate on the unit interval follows from the first derivative
and the single value at the endpoint. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_bounds_suffice (f : ℕ → SchwartzMap ℝ ℂ)
    (hd : ∀ j : ℕ, 0 < j → ∃ C : ℝ, ∀ n x, ‖iteratedDeriv j (f n : ℝ → ℂ) x‖ ≤ C)
    (hr : ∀ k j : ℕ, ∃ C : ℝ, ∀ n x, 1 ≤ |x| →
      |x|^k * ‖iteratedDeriv j (f n : ℝ → ℂ) x‖ ≤ C) :
    Bornology.IsVonNBounded ℂ (range f) := by
  obtain ⟨B,hB⟩ := hr 0 0
  obtain ⟨D,hD⟩ := hd 1 (by decide)
  have hB0 (n) : ‖f n 1‖ ≤ B := by simpa using hB n 1 (by norm_num)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 0)
  have hon (j : ℕ) : ∃ C : ℝ, ∀ n x, |x| ≤ 1 → ‖iteratedDeriv j (f n : ℝ → ℂ) x‖ ≤ C := by
    cases j with
    | zero =>
      refine ⟨B+2*D,fun n x hx ↦ ?_⟩
      have hle := abs_le.mp hx
      have hdiff : ∀ t ∈ Icc x 1, HasDerivWithinAt (f n : ℝ → ℂ) (deriv (f n) t) (Icc x 1) t :=
        fun t _ ↦ ((f n).differentiable t).hasDerivAt.hasDerivWithinAt
      have hder : ∀ t ∈ Ico x 1, ‖deriv (f n : ℝ → ℂ) t‖ ≤ D :=
        fun t _ ↦ by simpa using hD n t
      have h := norm_image_sub_le_of_norm_deriv_le_segment' hdiff (by
        intro t ht; simpa using hD n t) 1 ⟨hle.2,le_rfl⟩
      have H := norm_sub_norm_le (f n x) (f n 1)
      rw [norm_sub_rev] at h
      simpa only [iteratedDeriv_zero] using (show ‖f n x‖ ≤ B+2*D by
        nlinarith [hB0 n,mul_nonneg hD0 (show 0 ≤ x+1 by linarith [hle.1])])
    | succ j =>
      obtain ⟨C,hC⟩ := hd _ (Nat.succ_pos j)
      exact ⟨C,fun n x _ ↦ hC n x⟩
  apply (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bddAbove.mpr
  rintro ⟨k,j⟩
  obtain ⟨C,hC⟩ := hr k j
  obtain ⟨B₀,h₀⟩ := hon j
  refine ⟨max C B₀,?_⟩
  rintro _ ⟨_,⟨n,rfl⟩,rfl⟩
  refine SchwartzMap.seminorm_le_bound' ℂ k j (f n) ?_ (fun x ↦ ?_)
  · exact ((norm_nonneg _).trans (h₀ 0 0 (by norm_num))).trans (le_max_right _ _)
  · rcases le_total 1 |x| with h | h
    · exact (hC n x h).trans (le_max_left _ _)
    · have hp : |x|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) h
      exact ((mul_le_of_le_one_left (norm_nonneg _) hp).trans (h₀ n x h)).trans (le_max_right _ _)

/-- A Schwartz function is `O(x^(-a))` at infinity for every `a`. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_atTop (G : SchwartzMap ℝ ℂ) (a : ℝ) :
    (G : ℝ → ℂ) =O[atTop] (· ^ (-a)) := by
  have h := G.isBigO_cocompact_rpow (-a)
  refine (h.mono atTop_le_cocompact).congr' (EventuallyEq.refl _ _) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos hx]

/-- A Schwartz function is bounded near zero. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_zero (G : SchwartzMap ℝ ℂ) :
    (G : ℝ → ℂ) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  have hb : (G : ℝ → ℂ) =O[⊤] (fun _ ↦ (1 : ℝ)) := by
    obtain ⟨C, -, hC⟩ := G.decay 0 0
    refine Asymptotics.isBigO_iff.mpr ⟨C, .of_forall fun x ↦ ?_⟩
    simpa using hC x
  refine (hb.mono le_top).congr' (EventuallyEq.refl _ _) (.of_forall fun x ↦ ?_)
  simp

private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_convergent (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent G s :=
  mellinConvergent_of_isBigO_rpow (G.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_atTop G (s.re + 1)) (lt_add_one _) (sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_zero G) (by simpa using hs)

private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_differentiableAt (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin G) s :=
  mellin_differentiableAt_of_isBigO_rpow
    (G.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_atTop G (s.re + 1)) (lt_add_one _) (sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_zero G) (by simpa using hs)

private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_ibp (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin G s = -(1 / s) * mellin (SchwartzMap.derivCLM ℂ ℂ G) (s + 1) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  let G' := SchwartzMap.derivCLM ℂ ℂ G
  let u : ℝ → ℂ := fun t ↦ (t : ℂ) ^ ((s - 1) + 1) / ((s - 1) + 1)
  have hu_eq (t : ℝ) : u t = (t : ℂ) ^ s / s := by simp [u]
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u ((x : ℂ) ^ (s - 1)) x := fun x hx ↦
    hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) (fun h ↦ hs0 (by linear_combination h))
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (G : ℝ → ℂ) (G' x) x := fun x _ ↦
    (G.differentiableAt).hasDerivAt
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hG's := sLocalMellinSchwartzBounds_meyer_real_mellin_convergent G' hs1
  have hGs := sLocalMellinSchwartzBounds_meyer_real_mellin_convergent G hs
  have huv' : IntegrableOn (u * (G' : ℝ → ℂ)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hG's.const_mul (1 / s)) (fun t _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, hu_eq, smul_eq_mul, add_sub_cancel_right]
    ring
  have hu'v : IntegrableOn ((fun x : ℝ ↦ (x : ℂ) ^ (s - 1)) * (G : ℝ → ℂ)) (Ioi 0) := hGs
  have h0 : Tendsto (u * (G : ℝ → ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t : ℂ) ^ s / s * G t) 0 :=
      ((Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).div_const s).mul
        G.continuous.continuousAt
    have := hc.tendsto
    simp only [Complex.ofReal_zero, Complex.zero_cpow hs0, zero_div, zero_mul] at this
    refine tendsto_nhdsWithin_of_tendsto_nhds (this.congr fun t ↦ ?_)
    simp only [Pi.mul_apply, hu_eq]
  have hinf : Tendsto (u * (G : ℝ → ℂ)) atTop (𝓝 0) := by
    have hub : u =O[atTop] (fun t : ℝ ↦ t ^ s.re) := by
      refine Asymptotics.isBigO_iff.mpr ⟨‖s‖⁻¹, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [hu_eq, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _), div_eq_mul_inv, mul_comm]
    have hprod := hub.mul (sLocalMellinSchwartzBounds_meyer_real_mellin_isBigO_atTop G (s.re + 1))
    have hexp : (fun t : ℝ ↦ t ^ s.re * t ^ (-(s.re + 1))) =ᶠ[atTop] fun t ↦ t ^ (-1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
      ring_nf
    exact (hprod.congr' (EventuallyEq.refl _ _) hexp).trans_tendsto
      (tendsto_rpow_neg_atTop one_pos)
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at key
  unfold mellin
  have hL : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G t) =
      -∫ t in Ioi (0 : ℝ), u t * G' t := by
    rw [key, neg_neg]
    rfl
  rw [hL]
  have hR : (∫ t in Ioi (0 : ℝ), u t * G' t) =
      (1 / s) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1 - 1) • G' t := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp only [hu_eq, smul_eq_mul, add_sub_cancel_right]
    ring
  rw [hR]
  ring

/-- All polynomial height weights for a family of Mellin transforms pass to
ordinary derivatives, after translating the positive line once. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_bounds_derivative (f : ℕ → SchwartzMap ℝ ℂ) (a : ℝ)
    (ha : 1 ≤ a) (h : ∀ m : ℕ, ∃ B : ℝ, ∀ n (s : ℂ), s.re = a →
      ‖s^m * mellin (f n) s‖ ≤ B) :
    ∀ m : ℕ, ∃ B : ℝ, ∀ n (z : ℂ), z.re = a+1 →
      ‖z^m * mellin (SchwartzMap.derivCLM ℂ ℂ (f n)) z‖ ≤ B := by
  intro m
  obtain ⟨B,hB⟩ := h (m+1)
  refine ⟨2^m*B,fun n z hz ↦ ?_⟩
  let s := z-1
  have hs : s.re = a := by simp [s,hz]
  have hpos : 0 < s.re := by linarith
  have hne : s ≠ 0 := by intro h'; rw [h'] at hpos; exact (lt_irrefl _) hpos
  obtain hv := sLocalMellinSchwartzBounds_meyer_real_mellin_ibp (f n) hpos
  have hzp : s+1 = z := by simp [s]
  rw [hzp] at hv
  have hv' : mellin (SchwartzMap.derivCLM ℂ ℂ (f n)) z = -s * mellin (f n) s := by
    rw [hv]; field_simp
  have hs1 : 1 ≤ ‖s‖ := ha.trans <| hs ▸ (Complex.re_le_norm s)
  have hzs : ‖z‖ ≤ 2*‖s‖ := by
    have H := norm_add_le s (1:ℂ)
    rw [hzp,norm_one] at H
    linarith
  rw [hv',norm_mul,norm_pow,norm_mul,norm_neg]
  calc
    ‖z‖^m * (‖s‖*‖mellin (f n) s‖) ≤ (2*‖s‖)^m * (‖s‖*‖mellin (f n) s‖) := by gcongr
    _ = 2^m * ‖s^(m+1)*mellin (f n) s‖ := by rw [mul_pow,norm_mul,norm_pow,pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB n s hs) (by positivity)

private theorem sLocalMellinSchwartzBounds_meyer_real_mellin_bounds_all_derivatives (f : ℕ → SchwartzMap ℝ ℂ)
    (h : ∀ a : ℝ, 1 < a → ∀ m : ℕ, ∃ B : ℝ, ∀ n (s : ℂ), s.re = a →
      ‖s^m * mellin (f n) s‖ ≤ B) :
    ∀ j : ℕ, ∀ a : ℝ, j+1 < a → ∀ m : ℕ, ∃ B : ℝ, ∀ n (s : ℂ), s.re = a →
      ‖s^m * mellin ((SchwartzMap.derivCLM ℂ ℂ)^[j] (f n)) s‖ ≤ B := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    intro a ha
    have hb : (j:ℝ)+1 < a-1 := by push_cast at ha; linarith
    have hb' : (1:ℝ) ≤ a-1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have H := sLocalMellinSchwartzBounds_meyer_real_mellin_bounds_derivative (fun n ↦ (SchwartzMap.derivCLM ℂ ℂ)^[j] (f n))
      (a-1) hb' (ih (a-1) hb)
    simpa only [Function.iterate_succ_apply',sub_add_cancel] using H

private theorem sLocalMellinSchwartzBounds_meyer_rational_units (ξ : (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ) :
    ξ = 1 ∨ ξ = -1 := by
  have hmem : ∀ x : (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ),
      ∃ y : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ y = (x : ℚ) := by
    intro x
    have he : ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ = ⊥ := by
      rw [Finset.coe_empty, integer_empty]
    have hx : (x : ℚ) ∈ (⊥ : Subalgebra (𝓞 ℚ) ℚ) := he ▸ x.property
    exact Algebra.mem_bot.mp hx
  obtain ⟨a, ha⟩ := hmem ξ.val
  obtain ⟨b, hb⟩ := hmem (ξ⁻¹).val
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, ha, hb, map_one]
    have h := congrArg Subtype.val ξ.mul_inv
    exact h
  have hu : IsUnit (Rat.ringOfIntegersEquiv a) := (IsUnit.of_mul_eq_one b hab).map _
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    have ha1 : a = 1 := Rat.ringOfIntegersEquiv.injective (h.trans (map_one _).symm)
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_one]
    rfl
  · right
    have ha1 : a = -1 := Rat.ringOfIntegersEquiv.injective (h.trans (by simp))
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_neg, map_one]
    rfl

private theorem sLocalMellinSchwartzBounds_meyer_rational_one_ne_neg_one :
    (1 : (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ) ≠ -1 := by
  intro h
  have h' := congrArg (fun u : (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ ↦
    Subtype.val (Units.val u)) h
  norm_num at h'

private theorem sLocalMellinSchwartzBounds_meyer_rational_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sLocalMellinSchwartzBounds_meyer_rational_abs (z : Rat.infinitePlace.Completion) :
    |InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z,
    ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem sLocalMellinSchwartzBounds_meyer_rational_thetaClasses (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (φ : ℝ → ℂ) (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace)) +
      φ (-(InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace))) := by
  have hU : (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ ∅)
      (Subring.subtype (integralAdelesOutside ℚ ∅)))))
      (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ ∅)) (-1)) = -1 := by
    apply Units.ext
    change ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ).val) =
      (-1 : (SAdeleRing ℚ ∅)ˣ).val
    simp
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  dsimp only
  rw [tsum_eq_sum (s := {1, -1}) (fun ξ hξ ↦ ?_)]
  · rw [Finset.sum_pair sLocalMellinSchwartzBounds_meyer_rational_one_ne_neg_one]
    simp only [MonoidHom.comp_apply, hU, map_one, one_mul, hf]
    simp only [Units.val_neg, neg_mul, one_mul]
    rw [show ((-(x : SAdeleRing ℚ ∅)).1 Rat.infinitePlace) =
      -((x : SAdeleRing ℚ ∅).1 Rat.infinitePlace) from rfl, map_neg]
  · rcases sLocalMellinSchwartzBounds_meyer_rational_units ξ with h | h <;> simp_all

private theorem sLocalMellinSchwartzBounds_meyer_rational_normOne_trivial (h : (sIdeleQuotientNorm ℚ ∅).ker) : h = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  apply Subtype.ext
  change (QuotientGroup.mk x : SIdeleQuotient ℚ ∅) = 1
  rw [sIdeleQuotient_mk_eq_one]
  have hn : ‖x.val.1 Rat.infinitePlace‖ = 1 := by
    rw [← sLocalMellinSchwartzBounds_meyer_rational_norm]
    have h1 : sIdeleNorm ℚ ∅ x = 1 := hg
    rw [h1]
    simp
  rw [← sLocalMellinSchwartzBounds_meyer_rational_abs] at hn
  rcases (abs_eq zero_le_one).mp hn with h1 | h1
  · refine ⟨1, ?_⟩
    simp only [map_one]
    apply Units.ext
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans (map_one _).symm
  · refine ⟨-1, ?_⟩
    apply Units.ext
    change (x : SAdeleRing ℚ ∅) = ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ).val)
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans ((map_neg _ _).trans (congrArg Neg.neg (map_one _))).symm

open LineDeriv in

/-- The total mass of the rational norm-one quotient at the empty finite stage is positive. -/
theorem sLocalNormOneQuotientMeasure_ratEmpty_mass_pos : 0 < (sLocalNormOneQuotientMeasure ℚ ∅).real univ := by
  let : MeasurableSpace (sIdeleQuotientNorm ℚ ∅).ker := borel _
  let : BorelSpace (sIdeleQuotientNorm ℚ ∅).ker := ⟨rfl⟩
  have := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  have : Subsingleton (sIdeleQuotientNorm ℚ ∅).ker :=
    ⟨fun a b ↦ (sLocalMellinSchwartzBounds_meyer_rational_normOne_trivial a).trans (sLocalMellinSchwartzBounds_meyer_rational_normOne_trivial b).symm⟩
  have : Finite (sIdeleQuotientNorm ℚ ∅).ker := Finite.of_subsingleton
  have : CompactSpace (sIdeleQuotientNorm ℚ ∅).ker := Finite.compactSpace
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨1, trivial⟩).ne'
    isCompact_univ.measure_lt_top.ne

/-- Over ℚ with `S = ∅` the homogeneous theta function is the theta function on classes
times the total norm-one mass. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_homTheta (χ₀ : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ χ₀ f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * sLocalAdelicThetaOnClasses ℚ ∅ f g := by
  let : MeasurableSpace (sIdeleQuotientNorm ℚ ∅).ker := borel _
  let : BorelSpace (sIdeleQuotientNorm ℚ ∅).ker := ⟨rfl⟩
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply,
    integral_congr_ae (g := fun _ ↦ sLocalAdelicThetaOnClasses ℚ ∅ f g) (ae_of_all _ fun h ↦ ?_)]
  · rw [integral_const, Complex.real_smul]
  · have := sLocalMellinSchwartzBounds_meyer_rational_normOne_trivial h
    subst this
    simp

/-- At the empty rational finite stage the homogeneous theta function is the sign sum of
its real profile, evaluated at the quotient norm and multiplied by the angular Haar mass. -/
theorem sLocalHomogeneousTheta_ratEmpty_eq_evenProfile
    (χ : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (p : ℝ → ℂ)
    (hp : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      p (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) (q : SIdeleQuotient ℚ ∅) :
    let r : ℝ := ((sIdeleQuotientNorm ℚ ∅ q).val : ℝ)
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ χ f q =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * (p r + p (-r)) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  let t := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (u.val.1 Rat.infinitePlace)
  have hr : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk u)).val : ℝ) = |t| :=
    (sLocalMellinSchwartzBounds_meyer_rational_norm u).trans
      (sLocalMellinSchwartzBounds_meyer_rational_abs _).symm
  rw [sLocalMellinSchwartzBounds_meyer_rational_homTheta,
    sLocalMellinSchwartzBounds_meyer_rational_thetaClasses f p hp u]
  change _ * (p t + p (-t)) = _
  rw [hr]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_neg, add_comm]

private theorem sLocalMellinSchwartzBounds_meyer_rational_test_coordinates :
    ∃ E : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(SAdeleRing ℚ ∅),
      ∀ (f : SchwartzMap ℝ ℂ) (x : SAdeleRing ℚ ∅),
        E f (Multiplicative.ofAdd x) = f (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace (x.1 Rat.infinitePlace)) := by
  let D : Type := (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ
  let _ : Unique D := uniqueOfSubsingleton 0
  let real : Rat.infinitePlace.Completion ≃ᵢ ℝ :=
    InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let coord : SAdeleRing ℚ ∅ ≃ₜ ℝ := (Homeomorph.prodUnique (InfiniteAdeleRing ℚ) D).trans
    ((Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans real.toHomeomorph)
  let e : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' coord fun x y ↦
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).map_add
        (x.toAdd.1 Rat.infinitePlace) (y.toAdd.1 Rat.infinitePlace)
  with_reducible refine realSchwartzBruhat_equiv.elim fun R hR ↦ ?_
  let : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  let : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  let : T2Space (Multiplicative (SAdeleRing ℚ ∅)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ ∅)) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨A,hA⟩ := exists_schwartzBruhat_comp_equivCLM e
  obtain ⟨B,hB⟩ := exists_schwartzBruhat_comp_equivCLM e.symm
  have hAB : Function.LeftInverse B A := by
    intro f
    apply Subtype.ext
    funext x
    rw [hB,hA,e.apply_symm_apply]
  have hBA : Function.RightInverse B A := by
    intro f
    apply Subtype.ext
    funext x
    rw [hA,hB,e.symm_apply_apply]
  refine ⟨R.trans (ContinuousLinearEquiv.equivOfInverse A B hAB hBA),fun f x ↦ ?_⟩
  exact (hA (R f) (Multiplicative.ofAdd x)).trans (hR f (coord x))

private theorem sLocalMellinSchwartzBounds_meyer_rational_ray_haar (p : ℝ → ℂ) (s : ℂ) :
    (∫ t : ℝ≥0ˣ, p (Real.log (t.val : ℝ)) * (((t.val : ℝ) : ℂ) ^ s) ∂positiveRealHaar) =
      mellin (fun t ↦ p (Real.log t)) s := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (x : ℝ) : (e x).val = (Real.exp x).toNNReal := by
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  have hm : positiveRealHaar = volume.map e := by
    apply congrArg (fun a : ℝ → ℝ≥0ˣ ↦ volume.map a)
    funext x
    exact Units.ext (he x).symm
  rw [hm, e.measurableEmbedding.integral_map, mellin, ← integral_comp_exp]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [he, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (p x)]
  congr 2
  ring


/-- On the rational empty-place quotient the trivial Mellin coefficients are
the classical Mellin values of the even profile up to the fixed positive
norm-one mass. This normalization is independent of the sequence of tests. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_theta_mellin (φ : SchwartzMap ℝ ℂ)
    (f : ℬ(SAdeleRing ℚ ∅))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (z : ℂ) (hz : 0 < z.re) :
    sLocalThetaMellinIntegral f (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
      (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
      (1 : SIdeleQuotient ℚ ∅ →ₜ* ℂ) z) =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) *
        mellin (fun t : ℝ ↦ φ t + φ (-t)) z := by
  let : MeasurableSpace (sIdeleQuotientNorm ℚ ∅).ker := borel _
  let : BorelSpace (sIdeleQuotientNorm ℚ ∅).ker := ⟨rfl⟩
  let μ := sLocalNormOneQuotientMeasure ℚ ∅
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  let p (u : ℝ) := φ (Real.exp u) + φ (-Real.exp u)
  have hm : mellin (fun t : ℝ ↦ p (Real.log t)) z = mellin (fun t : ℝ ↦ φ t+φ (-t)) z := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [p,Real.exp_log hx]
  rw [← hm,← sLocalMellinSchwartzBounds_meyer_rational_ray_haar p z,← integral_const_mul]
  let π := Units.map (adeleProjection ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))).toMonoidHom
  have hπ : Continuous π := (continuous_fst.prodMk (continuous_pi fun w : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
    (RestrictedProduct.continuous_eval w.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* (SAdeleRing ℚ ∅)ˣ := ⟨π.comp (canonicalIdeleNormSection ℚ),
    hπ.comp (canonicalIdeleNormSection_continuous ℚ)⟩
  have hτ : RightInverse τ (sIdeleNorm ℚ ∅) := sIdeleNorm_project_canonicalSection ℚ ∅
  let χ : PontryaginDual (SIdeleQuotient ℚ ∅) := 1
  have hc : ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) = 1 :=
    ContinuousMonoidHom.ext (fun _ ↦ rfl)
  rw [←hc,← sLocalRadialMellinIntegral_eq_theta τ hτ f χ z hz]
  unfold sLocalRadialMellinIntegral
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  let x := τ t
  let y := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (x.val.1 Rat.infinitePlace)
  have hy : |y| = (t.val : ℝ) := (sLocalMellinSchwartzBounds_meyer_rational_abs _).trans ((sLocalMellinSchwartzBounds_meyer_rational_norm x).symm.trans
    (congrArg (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)) (hτ t)))
  have hp : φ y + φ (-y) = p (Real.log (t.val : ℝ)) := by
    rw [show p (Real.log (t.val : ℝ)) = φ (t.val : ℝ) + φ (-(t.val : ℝ)) by
      simp [p,Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))],← hy]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,neg_neg,add_comm]
  have h1 := sLocalMellinSchwartzBounds_meyer_rational_homTheta (1 : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) f
    (QuotientGroup.mk x)
  rw [sLocalMellinSchwartzBounds_meyer_rational_thetaClasses f φ hf] at h1
  change sLocalHomogeneousAdelicTheta ℚ ∅ μ 1 f (QuotientGroup.mk x) *
    ((1:ℂ)*(((sIdeleNorm ℚ ∅ x).val : ℝ) : ℂ)^z) =
    (μ.real univ : ℂ) * (p (Real.log (t.val : ℝ)) * (((t.val : ℝ) : ℂ)^z))
  have hh : sLocalHomogeneousAdelicTheta ℚ ∅ μ 1 f (QuotientGroup.mk x) =
      (μ.real univ : ℂ) * (φ y + φ (-y)) := h1
  rw [hh,hp,show sIdeleNorm ℚ ∅ x = t from hτ t,one_mul,mul_assoc]

/-- Reflection commutes with the real Fourier transform and averaging the
two reflected tests gives a representative of the original theta class. -/
private theorem sLocalMellinSchwartzBounds_meyer_real_symmetrized_profile :
    ∃ S : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ,
      (∀ (φ : SchwartzMap ℝ ℂ) x, S φ x = φ x + φ (-x)) ∧
      ∀ φ : SchwartzMap ℝ ℂ, 𝓕 (S φ) = S (𝓕 φ) := by
  let R : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
  let S := ContinuousLinearMap.id ℂ (SchwartzMap ℝ ℂ) + R
  have hS (φ : SchwartzMap ℝ ℂ) (x : ℝ) : S φ x = φ x+φ (-x) := rfl
  refine ⟨S,hS,fun φ ↦ ?_⟩
  change 𝓕 (φ + R φ) = S (𝓕 φ)
  rw [FourierTransform.fourier_add]
  ext x
  rw [hS]
  change 𝓕 φ x + 𝓕 (R φ) x = _
  congr 1
  change 𝓕 ((φ : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ) x = 𝓕 (φ : ℝ → ℂ) (-x)
  exact Real.fourier_comp_linearIsometry _ _ _

private theorem sLocalMellinSchwartzBounds_meyer_inverse_real_profiles
    (f : ℕ → SchwartzMap ℝ ℂ) (hf : ∀ n x, f n (-x) = f n x)
    (hF : ∀ n x, 𝓕 (f n) (-x) = 𝓕 (f n) x)
    (hM : ∀ v ∈ ({f,fun n ↦ 𝓕 (f n)} : Set (ℕ → SchwartzMap ℝ ℂ)),
      ∀ a : ℝ, 1 < a → ∀ m : ℕ, ∃ B : ℝ, ∀ n (z : ℂ), z.re = a →
        ‖z^m*mellin (v n) z‖ ≤ B) :
    Bornology.IsVonNBounded ℂ (range f) := by
  have hbd (v : ℕ → SchwartzMap ℝ ℂ) (hv : v ∈ ({f,fun n ↦ 𝓕 (f n)} : Set _))
      (j : ℕ) (a : ℝ) (ha : (j:ℝ)+1 < a) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n (x : ℝ), 0 < x →
        x^a * ‖iteratedDeriv j (v n : ℝ → ℂ) x‖ ≤ B := by
    let D := SchwartzMap.derivCLM ℂ ℂ
    let w (n : ℕ) := D^[j] (v n)
    have hpoint (n i : ℕ) : ((D^[i] (v n) : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
        iteratedDeriv i (v n : ℝ → ℂ) := by
      induction i with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply',iteratedDeriv_succ,← ih]; rfl
    obtain ⟨C,hC⟩ := sLocalMellinSchwartzBounds_meyer_real_mellin_bounds_all_derivatives v (hM v hv) j a ha 2
    have ha1 : 1 ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hco (n) : Continuous (fun t : ℝ ↦ mellin (w n) ((a:ℂ)+(t:ℂ)*Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      let z (t : ℝ) := (a:ℂ)+(t:ℂ)*Complex.I
      have hz : 0 < (z x).re := by simp [z]; linarith
      exact ContinuousAt.comp (f := z) (g := mellin (w n))
        (sLocalMellinSchwartzBounds_meyer_real_mellin_differentiableAt (w n) hz).continuousAt (by dsimp [z]; fun_prop)
    have H := sLocalMellinSchwartzBounds_meyer_real_inverse_ray a ha1 (fun n ↦ (w n : ℝ → ℂ)) (fun n ↦ (w n).continuous)
      (fun n ↦ sLocalMellinSchwartzBounds_meyer_real_mellin_convergent (w n) (by simp; linarith)) hco C
      (fun n t ↦ hC n _ (by simp))
    refine ⟨max (C/2) 0,le_max_right _ _,fun n x hx ↦ ?_⟩
    rw [← hpoint]
    exact (H n x hx).trans (le_max_left _ _)
  have hfF : (fun n ↦ 𝓕 (f n)) ∈ ({f,fun n ↦ 𝓕 (f n)} : Set _) := by simp
  have hpos := sLocalMellinSchwartzBounds_meyer_real_positive_moments (fun n ↦ 𝓕 (f n)) (by
    intro a ha; simpa only [Nat.cast_zero,zero_add,iteratedDeriv_zero] using hbd _ hfF 0 a (by simpa))
  apply sLocalMellinSchwartzBounds_meyer_real_bounds_suffice f
  · intro j hj
    obtain ⟨B,hB⟩ := hpos j hj
    refine ⟨(2*Real.pi)^j*(2*B),fun n x ↦ ?_⟩
    apply sLocalMellinSchwartzBounds_meyer_real_derivative_from_fourier_moment _ j _ _ x
    have hEven (y : ℝ) : ‖𝓕 (f n) |y|‖ = ‖𝓕 (f n) y‖ := by
      rcases le_total 0 y with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h,hF]
    have he := integral_comp_abs (f := fun y : ℝ ↦ y^j*‖𝓕 (f n) y‖)
    simp_rw [hEven] at he
    exact he.trans_le (by gcongr; exact hB n)
  · intro k j
    let a : ℝ := max (k:ℝ) ((j:ℝ)+1)+1
    have ha : (j:ℝ)+1 < a := (le_max_right _ _).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    obtain ⟨B,_,hB⟩ := hbd f (by simp) j a ha
    refine ⟨B,fun n x hx ↦ ?_⟩
    have hx0 : 0 < |x| := zero_lt_one.trans_le hx
    have hEven : ‖iteratedDeriv j (f n : ℝ → ℂ) |x|‖ = ‖iteratedDeriv j (f n : ℝ → ℂ) x‖ := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · have eq : (fun t : ℝ ↦ f n (-t)) = f n := funext (hf n)
        have hz := congrArg norm (iteratedDeriv_comp_neg j (f n : ℝ → ℂ) x)
        rw [eq] at hz
        simpa [norm_smul,abs_of_nonpos h] using hz.symm
    have hp : |x|^k ≤ |x|^a := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hx
      exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
    rw [← hEven]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (hB n _ hx0)

/-- On a theta stage realized by even real Schwartz profiles compatibly with Fourier and Mellin, the weighted estimates imply boundedness. -/
private theorem sLocalMellinSchwartzBounds_meyer_inverse_of_even_real_profiles
    (T : Finset (HeightOneSpectrum (𝓞 F))) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
    (hv : ∀ w ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
      sLocalMellinSchwartzBounds T τ w sLocalThetaMellinIntegral)
    (c : ℝ) (hc : 0 < c)
    (P : SchwartzBruhat (Multiplicative (SAdeleRing F T)) → SchwartzMap ℝ ℂ)
    (L : SchwartzMap ℝ ℂ →L[ℂ] SLocalAdelicThetaSpace F T)
    (hP : ∀ g, (∀ x : ℝ, P g (-x) = P g x) ∧
      P (sAdeleSchwartzFourier g) = 𝓕 (P g) ∧
      (sLocalAdelicTheta F T).ker.mkQ g = L (P g) ∧
      ∀ z : ℂ, 1 < z.re → sLocalThetaMellinIntegral g (quasiCharacterNormTwist
        (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
        (1 : SIdeleQuotient F T →ₜ* ℂ) z) = (c : ℂ) * mellin (P g) z) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) := by
  let f (n : ℕ) := P (v n)
  have he (n : ℕ) (x : ℝ) : f n (-x) = f n x := (hP (v n)).1 x
  have hFe (n : ℕ) (x : ℝ) : 𝓕 (f n) (-x) = 𝓕 (f n) x := by
    rw [show 𝓕 (f n) = P (sAdeleSchwartzFourier (v n)) from (hP _).2.1.symm]
    exact (hP _).1 x
  have line (w : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
      (hw : sLocalMellinSchwartzBounds T τ w sLocalThetaMellinIntegral)
      (a : ℝ) (ha : 1 < a) (m : ℕ) :
      ∃ B : ℝ, ∀ n (z : ℂ), z.re = a → ‖z^m*mellin (P (w n)) z‖ ≤ B := by
    obtain ⟨H,_,_,hw'⟩ := (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ w).mp hw a ha
    obtain ⟨B,hB⟩ := hw' 0 0 m
    have htr : ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ((1 : H).val.val)) = 1 :=
      ContinuousMonoidHom.ext fun _ ↦ rfl
    refine ⟨B/c,fun n z hz ↦ ?_⟩
    rw [le_div_iff₀ hc]
    have h := hB 1 n z hz
    simp only [htr,pow_zero,one_mul,(hP (w n)).2.2.2 z (hz.symm ▸ ha)] at h
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hc.le,mul_left_comm,mul_comm,mul_assoc] using h
  have hb : Bornology.IsVonNBounded ℂ (range f) := by
    apply sLocalMellinSchwartzBounds_meyer_inverse_real_profiles f he hFe
    intro w hw a ha m
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact line v (hv _ (by simp)) a ha m
    · obtain rfl := Set.mem_singleton_iff.mp hw
      simpa only [f,fun n ↦ (hP (v n)).2.1] using
        line (fun n ↦ sAdeleSchwartzFourier (v n)) (hv _ (by simp)) a ha m
  apply (hb.image L).subset
  rintro _ ⟨n,rfl⟩
  exact ⟨f n,⟨n,rfl⟩,(hP (v n)).2.2.1.symm⟩

/-- The trivial Mellin coefficient, ordinary additive Fourier transform, and theta
class have a common even real Schwartz model over ℚ with no finite places. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_even_real_profiles :
    ∃ c : ℝ, 0 < c ∧ ∃ (P : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)) → SchwartzMap ℝ ℂ)
      (L : SchwartzMap ℝ ℂ →L[ℂ] SLocalAdelicThetaSpace ℚ ∅),
      ∀ g, (∀ x : ℝ, P g (-x) = P g x) ∧
        P (sAdeleSchwartzFourier g) = 𝓕 (P g) ∧
        (sLocalAdelicTheta ℚ ∅).ker.mkQ g = L (P g) ∧
        ∀ z : ℂ, 1 < z.re → sLocalThetaMellinIntegral g (quasiCharacterNormTwist
          (sIdeleQuotientNorm ℚ ∅) (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
          (1 : SIdeleQuotient ℚ ∅ →ₜ* ℂ) z) = (c : ℂ) * mellin (P g) z := by
  let : MeasurableSpace (sIdeleQuotientNorm ℚ ∅).ker := borel _
  let : BorelSpace (sIdeleQuotientNorm ℚ ∅).ker := ⟨rfl⟩
  obtain ⟨E,hE⟩ := sLocalMellinSchwartzBounds_meyer_rational_test_coordinates
  obtain ⟨S,hS,hSF⟩ := sLocalMellinSchwartzBounds_meyer_real_symmetrized_profile
  let A : SchwartzMap ℝ ℂ →L[ℂ] SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)) :=
    (1/2 : ℂ) • E.toContinuousLinearMap
  let L := (sLocalAdelicTheta ℚ ∅).ker.mkQL.comp A
  let P (g : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) := S (E.symm g)
  refine ⟨_,sLocalNormOneQuotientMeasure_ratEmpty_mass_pos,P,L,fun g ↦ ?_⟩
  have coord (g : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (x : SAdeleRing ℚ ∅) :
      g (Multiplicative.ofAdd x) = E.symm g (InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace (x.1 Rat.infinitePlace)) := by rw [← hE,E.apply_symm_apply]
  refine ⟨fun x ↦ ?_,?_,?_,fun z hz ↦ ?_⟩
  · simp only [P,hS,neg_neg,add_comm]
  · change S (E.symm (sAdeleSchwartzFourier g)) = 𝓕 (S (E.symm g))
    rw [hSF]
    apply congrArg S
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    funext x
    exact (sAdeleSchwartzFourier_ratEmpty_apply (E.symm g) g (coord g) x.toAdd).trans
      (hE _ x.toAdd).symm
  · symm
    change (sLocalAdelicTheta ℚ ∅).ker.mkQ (A (P g)) = (sLocalAdelicTheta ℚ ∅).ker.mkQ g
    rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq,LinearMap.mem_ker,map_sub,sub_eq_zero]
    ext x
    rw [← sLocalAdelicThetaOnClasses_mk,← sLocalAdelicThetaOnClasses_mk]
    have hA (y : SAdeleRing ℚ ∅) : (A (P g)) (Multiplicative.ofAdd y) =
        (((1/2 : ℂ) • P g : SchwartzMap ℝ ℂ) : ℝ → ℂ)
          (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (y.1 Rat.infinitePlace)) := by
      change (1/2 : ℂ) * E (P g) (Multiplicative.ofAdd y) = (1/2 : ℂ) * _
      rw [hE]
    rw [sLocalMellinSchwartzBounds_meyer_rational_thetaClasses _ _ hA,sLocalMellinSchwartzBounds_meyer_rational_thetaClasses _ _ (coord g)]
    simp only [smul_apply,smul_eq_mul,P,hS,neg_neg]
    ring
  · rw [sLocalMellinSchwartzBounds_meyer_rational_theta_mellin (E.symm g) g (coord g) z (zero_lt_one.trans hz)]
    rw [show (P g : ℝ → ℂ) = (fun t ↦ (E.symm g) t + (E.symm g) (-t)) from funext (hS _)]

/-- The inverse comparison on the rational stage with no finite places holds for
arbitrary spans of theta classes. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_empty_inverse_from_model
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient ℚ ∅)
    (hv : sLocalMellinSchwartzBounds ∅ τ v sLocalThetaMellinIntegral)
    (hF : sLocalMellinSchwartzBounds ∅ τ (fun n ↦ sAdeleSchwartzFourier (v n)) sLocalThetaMellinIntegral) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta ℚ ∅).ker.mkQ (v n)) := by
  obtain ⟨c,hc,P,L,hP⟩ := sLocalMellinSchwartzBounds_meyer_rational_even_real_profiles
  apply sLocalMellinSchwartzBounds_meyer_inverse_of_even_real_profiles ∅ τ v _ c hc P L hP
  intro w hw
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · exact hv
  · obtain rfl := Set.mem_singleton_iff.mp hw
    exact hF

/-- Classical input: R. Meyer, *On a representation of the idele class group related to
primes and zeros of L-functions*, Duke Math. J. 127 (2005), arXiv:math/0311468 (page numbers
are those of the preprint), Corollary 4.17, p. 34, and Lemma 4.20, p. 36, at α = 1: the
direction from bounds on the Mellin transforms to bounded classes, in the cases that Lean does
not prove.
For a sequence of tests whose θ-classes have one conductor level and lie in one Fréchet
subspace of the θ-quotient: if the Mellin transforms of the θ-functions of the tests, and of
their additive Fourier transforms, are bounded on every line of real part greater than one
(supported on a finitely generated subgroup of the discrete factor of the dual, with every
polynomial weight bounded uniformly in the index), then the θ-classes form a bounded set.
Deviation: This is what remains of the criterion `sLocalMellinSchwartzBounds_meyer`, which is
proved from it below. Proved in Lean, and excluded here by hypothesis: the case in which the
classes span a finite-dimensional space (`hS`), and the case in which they are given by even
real Schwartz profiles (`hreal`; it covers ℚ with no finite place). The other direction of the
criterion is proved in Lean as well (`sLocalMellinSchwartzBounds_meyer_general_forward`). The
hypotheses `hk`, `hM` and `hm` follow from the bounds and are proved before this statement is
applied. The bounds are written without derivatives, which is equivalent
(`sLocalMellinSchwartzBounds_meyer_zeroth_iff`), and the conclusion is boundedness in the
quotient, which is equivalent to representatives in one bounded set
(`sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded`).
The paper states its results for bornological spaces and in the variable of the idele
classes. Writing them for this library is the project's work and is not proved in Lean:
that the bounded sets of the Schwartz–Bruhat space here are the paper's, that the kernel of
the S-unit sum is the closed span the paper divides by, the normalizations of the Fourier
transform and of the Haar measures, and the seminorms on the dual group. The integrator and
an independent reviewer checked these steps against the paper for the whole criterion (#7346);
no specialist in the paper's framework has. -/
private theorem sLocalMellinSchwartzBounds_meyer_infinite_span_outside_real_profiles (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (hreal : ¬ ∃ c : ℝ, 0 < c ∧ ∃ (P : ℬₛ(T) → SchwartzMap ℝ ℂ)
      (L : SchwartzMap ℝ ℂ →L[ℂ] SLocalAdelicThetaSpace F T),
      ∀ g, (∀ x : ℝ, P g (-x) = P g x) ∧
        P (sAdeleSchwartzFourier g) = 𝓕 (P g) ∧
        (sLocalAdelicTheta F T).ker.mkQ g = L (P g) ∧
        ∀ z : ℂ, 1 < z.re → sLocalThetaMellinIntegral g (quasiCharacterNormTwist
          (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
          (1 : SIdeleQuotient F T →ₜ* ℂ) z) = (c : ℂ) * mellin (P g) z)
    (hS : ¬ FiniteDimensional ℂ (Submodule.span ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))))
    (k : ℕ) (hk : ∀ g : (SAdeleRing F T)ˣ, g.val.1 = 1 →
      (∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(k+1 : ℤ))) → ∀ n,
        (sLocalAdelicTheta F T).ker.mkQ (schwartzBruhatUnitTranslate g (v n)) = (sLocalAdelicTheta F T).ker.mkQ (v n))
    (M : Submodule ℂ (SLocalAdelicThetaSpace F T)) (hM : IsFrechetTVS M)
    (hm : (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) ⊆ M)
    (hw : ∀ f ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → ℬₛ(T))),
      ∀ a : ℝ, 1 < a → ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → sLocalThetaMellinIntegral (f n) (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral (f n) (chartₜ(T,χ.val.val) z)‖ ≤ B) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) := by
  sorry

/-- The real Schwartz profile criterion covers the rational empty-place stage of the inverse comparison. -/
private theorem sLocalMellinSchwartzBounds_meyer_infinite_span_bound (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (hS : ¬ FiniteDimensional ℂ (Submodule.span ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))))
    (k : ℕ) (hk : ∀ g : (SAdeleRing F T)ˣ, g.val.1 = 1 →
      (∀ w : T, Valued.v (g.val.2 w - 1) ≤ WithZero.exp (-(k+1 : ℤ))) → ∀ n,
        (sLocalAdelicTheta F T).ker.mkQ (schwartzBruhatUnitTranslate g (v n)) = (sLocalAdelicTheta F T).ker.mkQ (v n))
    (M : Submodule ℂ (SLocalAdelicThetaSpace F T)) (hM : IsFrechetTVS M)
    (hm : (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) ⊆ M)
    (hw : ∀ f ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → ℬₛ(T))),
      ∀ a : ℝ, 1 < a → ∃ H : Subgroup (PontryaginDual.map τ).ker, H.FG ∧
      (∀ χ ∉ H, ∀ n (z : ℂ), z.re = a → sLocalThetaMellinIntegral (f n) (chartₜ(T,χ.val) z) = 0) ∧
      ∀ (p : GroupSeminorm H) (k m : ℕ), ∃ B : ℝ, ∀ (χ : H) n (z : ℂ), z.re = a →
        (1+p χ)^k * ‖z^m*sLocalThetaMellinIntegral (f n) (chartₜ(T,χ.val.val) z)‖ ≤ B) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) := by
  by_contra hn
  apply hn
  apply sLocalMellinSchwartzBounds_meyer_infinite_span_outside_real_profiles T τ hτ v _ hS k hk M hM hm hw
  rintro ⟨c, hc, P, L, hP⟩
  apply hn
  apply sLocalMellinSchwartzBounds_meyer_inverse_of_even_real_profiles T τ v _ c hc P L hP
  intro w hw'
  exact (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ w).mpr (hw w hw')

end

/-- For bounded classes, the fixed-conductor comparison only needs the weights
across infinite angular support. Finite support has uniform radial strip bounds. -/
private theorem sLocalMellinSchwartzBounds_meyer_general_forward (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (hb : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))) :
    sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral := by
  by_cases hF : Module.finrank ℚ F = 1
  · exact (sLocalMellinSchwartzBounds_meyer_degree_one_forward T hF τ hτ v hb).1
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_bounded_representatives_level T v ((sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded T v).mpr hb)
  obtain ⟨M,hM,hm⟩ := sLocalMellinSchwartzBounds_meyer_conductor_stage T k v hk
  apply (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ v).mpr
  intro a ha
  exact sLocalMellinSchwartzBounds_meyer_angular_family_of_singletons T τ hτ v M hM hm hb a ha
    (fun f ↦ sLocalMellinSchwartzBounds_meyer_single_test_from_active T τ hτ f hF a ha)

/-- In finite-dimensional spans a single line suffices for the inverse implication. -/
private theorem sLocalMellinSchwartzBounds_meyer_span_of_bounds (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T)) (v : ℕ → ℬₛ(T))
    (hS : FiniteDimensional ℂ (Submodule.span ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n))))
    (h : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)) := by
  apply sLocalMellinSchwartzBounds_meyer_finite_span_inverse T τ hτ v hS
  obtain ⟨H,_,hs,hw⟩ := (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ v).mp h 2 (by norm_num)
  intro χ z hz
  by_cases hχ : χ ∈ H
  · obtain ⟨B,hB⟩ := hw 0 0 0
    exact ⟨B,fun n ↦ by simpa using hB ⟨χ,hχ⟩ n z hz⟩
  · exact ⟨0,fun n ↦ by rw [hs χ hχ n z hz,norm_zero]⟩

/-- On every positive vertical line the integral of the local integer Gaussian against
the trivial norm twist has modulus at least half the Tamagawa mass of the local units. -/
private theorem sLocalMellinSchwartzBounds_meyer_gaussian_lower (v : V) :
    let localTwist := quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom : (v.adicCompletion F)ˣ →* ℝ≥0ˣ)
      (continuous_finiteLocalModule v)
      ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (v.adicCompletion F)ˣ))
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, 0 < z.re →
      B ≤ ‖@localIdelicZetaIntegral _ _ _ (borel _) (finiteLocalMultiplicativeTamagawaMeasure F v) (fun x ↦ (finiteStandardGaussian v 1) (Multiplicative.ofAdd x)) (localTwist z)‖ := by
  intro localTwist
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hUo : IsOpen ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) := by
    let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    convert isCompact_closedBall (0 : (v.adicCompletion F)) 1 using 1
    ext x
    simp only [SetLike.mem_coe,Metric.mem_closedBall,dist_zero_right,Valued.toNormedField.norm_le_one_iff]
    exact HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  let mass : ℝ := (finiteLocalMultiplicativeTamagawaMeasure F v).real (v.adicCompletionIntegers F).units
  have hm : 0 < mass := ENNReal.toReal_pos (hUo.measure_pos _ ⟨1,Subgroup.one_mem _⟩).ne' hUc.measure_lt_top.ne
  obtain ⟨π₀,hπ₀⟩ := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.adicCompletion F)ˣ := Units.mk0 π₀ hπ₀.ne_zero
  have hπ : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer π.val := hπ₀
  refine ⟨mass/2,half_pos hm,fun z hz ↦ ?_⟩
  let c := (localTwist z)
  let f := (finiteStandardGaussian v 1)
  obtain ⟨D,hD,hEval⟩ := exists_finiteEigendistribution_eq_zetaIntegral v 1 z hz
  have heig : ∀ (u : (v.adicCompletion F)ˣ) (f : SchwartzBruhat (Multiplicative (v.adicCompletion F))),
      D (schwartzBruhatUnitTranslate u f) = c u * D f := hD
  have hlocal : D (finitePlaceDifference v π f) = (1-c π) * D f := by
    change D (f-schwartzBruhatUnitTranslate π f) = _
    rw [map_sub,heig]
    ring
  have hu (g : (v.adicCompletion F)ˣ) (hg : g ∈ (v.adicCompletionIntegers F).units) : c g = 1 := by
    change (1 : ℂ) * (‖g.val‖ : ℂ)^z = 1
    rw [Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hg)]
    simp
  have hi : D (finitePlaceDifference v π f) = (mass : ℂ) := by
    rw [hEval]
    have hh : (fun x ↦ finitePlaceDifference v π f (Multiplicative.ofAdd x)) =
        (Units.val '' ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ)).indicator (fun _ ↦ (1 : ℂ)) :=
      funext (finitePlaceDifference_integerIndicator v π hπ)
    rw [hh]
    exact localIdelicZetaIntegral_indicator (finiteLocalMultiplicativeTamagawaMeasure F v) c _ hUo.measurableSet hUc.measure_lt_top.ne hu
  have huπ : ‖c π‖ ≤ 1 := by
    change ‖(1:ℂ) * (‖π.val‖ : ℂ)^z‖ ≤ 1
    rw [one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr π.ne_zero)]
    apply Real.rpow_le_one (norm_nonneg _)
    · rw [norm_uniformizer_adicCompletion v _ hπ]
      exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).le
    · exact hz.le
  have hk : ‖1-c π‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have hm' : mass ≤ 2 * ‖D f‖ := calc
    mass = ‖(mass:ℂ)‖ := by rw [Complex.norm_real,Real.norm_of_nonneg hm.le]
    _ = ‖1-c π‖*‖D f‖ := by rw [← norm_mul,← hlocal,hi]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  rw [← hEval]
  linarith

private theorem sLocalMellinSchwartzBounds_meyer_rational_empty_arch (f : ℬ(SAdeleRing ℚ ∅)) :
    ∃ A : (w : InfinitePlace ℚ) → SchwartzBruhat (Multiplicative w.Completion),
      ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
        ∏ w, A w (Multiplicative.ofAdd (x.1 w)) := by
  let D : Type := (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ
  let _ : Unique D := uniqueOfSubsingleton 0
  let coord : SAdeleRing ℚ ∅ ≃ₜ Rat.infinitePlace.Completion := (Homeomorph.prodUnique (InfiniteAdeleRing ℚ) D).trans
    (Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion))
  let e : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative Rat.infinitePlace.Completion :=
    ContinuousMulEquiv.mk' coord fun _ _ ↦ rfl
  let : T2Space (Multiplicative Rat.infinitePlace.Completion) := inferInstanceAs (T2Space Rat.infinitePlace.Completion)
  let : LocallyCompactSpace (Multiplicative Rat.infinitePlace.Completion) := inferInstanceAs (LocallyCompactSpace Rat.infinitePlace.Completion)
  let : T2Space (Multiplicative (SAdeleRing ℚ ∅)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ ∅)) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨A,hA⟩ := exists_schwartzBruhat_comp_equivCLM e.symm
  let fam (w : InfinitePlace ℚ) : SchwartzBruhat (Multiplicative w.Completion) := by
    obtain rfl := Subsingleton.elim w Rat.infinitePlace
    exact A f
  refine ⟨fam,fun x ↦ ?_⟩
  rw [Fintype.prod_unique]
  change f (Multiplicative.ofAdd x) = A f (e (Multiplicative.ofAdd x))
  rw [hA,e.symm_apply_apply]

/-- Adjoining the integer indicators multiplies the rational theta Mellin coefficient
by the product of the ordinary local Gaussian zeta integrals. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_insert_mellin (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (f : ℬ(SAdeleRing ℚ ∅)) (z : ℂ) (hz : 0 < z.re) :
    let twist (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (t : ℂ) := quasiCharacterNormTwist
        (sIdeleQuotientNorm ℚ S) (isProperMap_sIdeleQuotientNorm ℚ S).continuous
        ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (SIdeleQuotient ℚ S))) t
    let localTwist (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℂ) := quasiCharacterNormTwist
        (Units.map nnNormHom.toMonoidHom : (v.adicCompletion ℚ)ˣ →* ℝ≥0ˣ) (continuous_finiteLocalModule v)
        ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (v.adicCompletion ℚ)ˣ)) t
    let localFactor (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℂ) :=
        @localIdelicZetaIntegral _ _ _ (borel _) (finiteLocalMultiplicativeTamagawaMeasure ℚ v)
          (fun x ↦ finiteStandardGaussian v 1 (Multiplicative.ofAdd x)) (localTwist v t)
    sLocalThetaMellinIntegral (sAdeleSchwartzTransition ℚ (Finset.empty_subset T) f) (twist T z) =
      sLocalThetaMellinIntegral f (twist ∅ z) * ∏ v : T, (localFactor v.val z) := by
  intro twist localTwist localFactor
  classical
  let P := sAdeleSchwartzTransition ℚ (Finset.empty_subset T)
  obtain ⟨A,hA⟩ := sLocalMellinSchwartzBounds_meyer_rational_empty_arch f
  have hpos (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ∃ (χ : PontryaginDual (SIdeleQuotient ℚ S)) (s : ℂ),
      0 < s.re ∧ (twist S z) = quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
        (isProperMap_sIdeleQuotientNorm ℚ S).continuous ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) s :=
    ⟨1,z,hz,rfl⟩
  let B (v : T) := finiteStandardGaussian v.val 1
  let Ψ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (w : InfinitePlace ℚ) := sLocalInfiniteRestriction w (twist S z)
  have hΨ (w : InfinitePlace ℚ) : Ψ T w = Ψ ∅ w := by
    ext u; exact (sLocalInfiniteRestriction_normTwist (S := T) w z u).trans
      (sLocalInfiniteRestriction_normTwist (S := ∅) w z u).symm
  have hfin (v : T) : sLocalFiniteRestriction v (twist T z) = (localTwist v.val z) := by
    ext u
    change (1:ℂ) * (_ : ℂ)^z = (1:ℂ) * (_ : ℂ)^z
    rw [one_mul,one_mul]
    apply congrArg (fun t : ℂ ↦ t^z)
    have h := sLocalFiniteRestriction_norm v u
    change (1:ℂ)*(_ : ℂ)^(1:ℂ) = _ at h
    simpa only [one_mul,Complex.cpow_one] using h
  have hfactor (x : SAdeleRing ℚ T) : P f (Multiplicative.ofAdd x) =
      (∏ w, A w (Multiplicative.ofAdd (x.1 w))) * ∏ v : T, B v (Multiplicative.ofAdd (x.2 v)) := by
    rw [sAdeleSchwartzTransition_apply]
    let y : SAdeleRing ℚ ∅ := (x.1,fun w ↦ x.2 ⟨w.val,Finset.empty_subset T w.property⟩)
    have hb (v : T) : B v (Multiplicative.ofAdd (x.2 v)) =
        if x.2 v ∈ v.val.adicCompletionIntegers ℚ then 1 else 0 := by
      change finiteStandardGaussianValue v.val 1 (x.2 v) = _
      unfold finiteStandardGaussianValue
      split_ifs <;> simp_all
    by_cases h : ∀ v : T, x.2 v ∈ v.val.adicCompletionIntegers ℚ
    · rw [if_pos (fun v _ ↦ h v)]
      simp only [hb,if_pos (h _),Finset.prod_const_one,mul_one]
      exact hA y
    · obtain ⟨v,hv⟩ := not_forall.mp h
      rw [if_neg (fun h' ↦ hv (h' v (by simp)))]
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hb,if_neg hv]),mul_zero]
  rw [sLocalThetaMellinIntegral_eq_zeta _ (hpos T),sLocalThetaMellinIntegral_eq_zeta _ (hpos ∅)]
  rw [sLocalIdelicZetaIntegral_pureTensor (twist T z) (hpos T) (P f) A B hfactor]
  rw [sLocalIdelicZetaIntegral_pureTensor (twist ∅ z) (hpos ∅) f A (fun v ↦ finiteStandardGaussian v.val 1) (by
    intro x; simpa using hA x)]
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one,hfin]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  rw [show sLocalInfiniteRestriction w (twist T z) = sLocalInfiniteRestriction w (twist ∅ z) from hΨ w]

/-- Over the rational field with no finite places, all weighted trivial Mellin
lines of a family and of its additive Fourier transforms suffice even when the
theta classes span an infinite-dimensional subspace. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_empty_inverse_of_trivial_heights (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hv : ∀ w ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))),
      ∀ a : ℝ, 1 < a → ∀ m : ℕ, ∃ B : ℝ, ∀ n (z : ℂ), z.re = a →
        ‖z^m*sLocalThetaMellinIntegral (w n) (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
          (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous (1 : SIdeleQuotient ℚ ∅ →ₜ* ℂ) z)‖ ≤ B) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta ℚ ∅).ker.mkQ (v n)) := by
  obtain ⟨τ,hτ⟩ := sIdeleQuotientNorm_exists_section ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  have surj : Function.Surjective τ := by
    intro x
    refine ⟨sIdeleQuotientNorm ℚ ∅ x,?_⟩
    let h := sIdeleQuotientNorm ℚ ∅
    have hk : h (x / τ (h x)) = 1 := by rw [map_div,hτ]; simp
    have HE := congrArg Subtype.val (sLocalMellinSchwartzBounds_meyer_rational_normOne_trivial ⟨x / τ (h x),hk⟩)
    exact (div_eq_one.mp HE).symm
  have onlyOne (χ : (PontryaginDual.map τ).ker) : χ = 1 := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨u,rfl⟩ := surj x
    exact DFunLike.congr_fun χ.property u
  have hw (g : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
      (hg : g ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))))) :
      sLocalMellinSchwartzBounds ∅ τ g sLocalThetaMellinIntegral := by
    apply (sLocalMellinSchwartzBounds_meyer_zeroth_iff ∅ τ g).mpr
    intro a ha
    let H : Subgroup (PontryaginDual.map τ).ker := ⊥
    refine ⟨H,Subgroup.FG.bot,?_,fun p k m ↦ ?_⟩
    · intro χ hχ
      exact False.elim (hχ ((onlyOne χ).symm ▸ H.one_mem))
    obtain ⟨B,hB⟩ := hv g hg a ha m
    refine ⟨B,fun χ n z hz ↦ ?_⟩
    have hχ : χ = 1 := Subtype.ext (onlyOne χ.val)
    subst χ
    have htr : ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (SIdeleQuotient ℚ ∅))) = 1 := ContinuousMonoidHom.ext fun _ ↦ rfl
    simpa [htr] using hB n z hz
  exact sLocalMellinSchwartzBounds_meyer_rational_empty_inverse_from_model v τ (hw v (by simp)) (hw _ (by simp))

private theorem sLocalMellinSchwartzBounds_meyer_rational_theta_mellin_congr (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (f g : ℬ(SAdeleRing ℚ T)) (h : (sLocalAdelicTheta ℚ T).ker.mkQ f = (sLocalAdelicTheta ℚ T).ker.mkQ g)
    (c : SIdeleQuotient ℚ T →ₜ* ℂ) :
    sLocalThetaMellinIntegral f c = sLocalThetaMellinIntegral g c := by
  rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq,LinearMap.mem_ker,map_sub,sub_eq_zero] at h
  apply integral_congr_ae (.of_forall fun u ↦ ?_)
  obtain ⟨t,rfl⟩ := QuotientGroup.mk_surjective u
  change sLocalAdelicThetaOnClasses ℚ T f (QuotientGroup.mk t) * _ =
    sLocalAdelicThetaOnClasses ℚ T g (QuotientGroup.mk t) * _
  rw [sLocalAdelicThetaOnClasses_mk,sLocalAdelicThetaOnClasses_mk,show sLocalAdelicTheta ℚ T f = _ from h]

/-- If every rational theta class comes from the archimedean stage, the inverse
comparison holds after adjoining any finite set of places. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_insertion_inverse (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient ℚ T)
    (v : ℕ → ℬ(SAdeleRing ℚ T))
    (hh : range (fun n ↦ (sLocalAdelicTheta ℚ T).ker.mkQ (v n)) ⊆ (sLocalThetaTransition (F := ℚ) (Finset.empty_subset T)).range)
    (hw : ∀ w ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → ℬ(SAdeleRing ℚ T))),
      sLocalMellinSchwartzBounds T τ w sLocalThetaMellinIntegral) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta ℚ T).ker.mkQ (v n)) := by
  classical
  let twist (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (t : ℂ) := quasiCharacterNormTwist
      (sIdeleQuotientNorm ℚ S) (isProperMap_sIdeleQuotientNorm ℚ S).continuous
      ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (SIdeleQuotient ℚ S))) t
  let localTwist (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℂ) := quasiCharacterNormTwist
      (Units.map nnNormHom.toMonoidHom : (v.adicCompletion ℚ)ˣ →* ℝ≥0ˣ) (continuous_finiteLocalModule v)
      ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (v.adicCompletion ℚ)ˣ)) t
  let localFactor (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℂ) :=
      @localIdelicZetaIntegral _ _ _ (borel _) (finiteLocalMultiplicativeTamagawaMeasure ℚ v)
        (fun x ↦ finiteStandardGaussian v 1 (Multiplicative.ofAdd x)) (localTwist v t)
  let hST := Finset.empty_subset T
  let i := sLocalThetaTransition (F := ℚ) hST
  let j := sAdeleSchwartzTransition ℚ hST
  let Fq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) := (existsUnique_sLocalThetaFourier (F := ℚ) (S := S)).exists.choose
  have good (w : (HeightOneSpectrum (𝓞 ℚ))) : ¬ w.asIdeal ∣ differentIdeal ℤ (𝓞 ℚ) := by
    have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
      rw [Ideal.one_eq_top,← Ideal.absNorm_eq_one_iff,NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ),NumberField.discr_rat]
      rfl
    rw [hd,← isUnit_iff_dvd_one]
    exact fun hu ↦ w.isPrime.ne_top (Ideal.isUnit_iff.mp hu)
  have hprop (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : ℬ(SAdeleRing ℚ S)) : Fq S ((sLocalAdelicTheta ℚ S).ker.mkQ x) = (sLocalAdelicTheta ℚ S).ker.mkQ (sAdeleSchwartzFourier x) :=
    (existsUnique_sLocalThetaFourier (F := ℚ) (S := S)).exists.choose_spec.2 x
  have lift (n : ℕ) : ∃ f : ℬ(SAdeleRing ℚ ∅), i ((sLocalAdelicTheta ℚ ∅).ker.mkQ f) = (sLocalAdelicTheta ℚ T).ker.mkQ (v n) := by
    obtain ⟨y,hy⟩ := hh ⟨n,rfl⟩
    obtain ⟨f,rfl⟩ := (sLocalAdelicTheta ℚ ∅).ker.mkQ_surjective y
    exact ⟨f,hy⟩
  choose f hfv using lift
  have eqF (n : ℕ) : i ((sLocalAdelicTheta ℚ ∅).ker.mkQ (sAdeleSchwartzFourier (f n))) = (sLocalAdelicTheta ℚ T).ker.mkQ (sAdeleSchwartzFourier (v n)) := by
    rw [← hprop,← hprop,← hfv]
    exact (sLocalThetaFourier_transition hST (fun w _ _ ↦ good w) ((sLocalAdelicTheta ℚ ∅).ker.mkQ (f n))).symm
  choose b hb hbz using (fun w : T ↦ sLocalMellinSchwartzBounds_meyer_gaussian_lower w.val)
  let C := ∏ w : T, b w
  have hc : 0 < C := Finset.prod_pos (fun w _ ↦ hb w)
  have lower (z : ℂ) (hz : 0 < z.re) : C ≤ ‖∏ w : T, (localFactor w.val z)‖ := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun w _ ↦ (hb w).le) (fun w _ ↦ hbz w z hz)
  have line (u : ℕ → ℬ(SAdeleRing ℚ ∅)) (w : ℕ → ℬ(SAdeleRing ℚ T)) (he : ∀ n, i ((sLocalAdelicTheta ℚ ∅).ker.mkQ (u n)) = (sLocalAdelicTheta ℚ T).ker.mkQ (w n))
      (hw : sLocalMellinSchwartzBounds T τ w sLocalThetaMellinIntegral)
      (a : ℝ) (ha : 1 < a) (m : ℕ) :
      ∃ B : ℝ, ∀ n (z : ℂ), z.re = a → ‖z^m * sLocalThetaMellinIntegral (u n) (twist ∅ z)‖ ≤ B := by
    obtain ⟨H,_,_,h⟩ := (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ w).mp hw a ha
    obtain ⟨D,hD⟩ := h 0 0 m
    refine ⟨D/C,fun n z hz ↦ ?_⟩
    have hpos : 0 < z.re := hz.symm ▸ (zero_lt_one.trans ha)
    rw [le_div_iff₀ hc]
    calc
      _ ≤ ‖z^m*sLocalThetaMellinIntegral (u n) (twist ∅ z)‖ * ‖∏ w : T, (localFactor w.val z)‖ :=
        mul_le_mul_of_nonneg_left (lower z hpos) (norm_nonneg _)
      _ = ‖z^m*sLocalThetaMellinIntegral (j (u n)) (twist T z)‖ := by
        rw [← norm_mul,mul_assoc,sLocalMellinSchwartzBounds_meyer_rational_insert_mellin T (u n) z hpos]
      _ = ‖z^m*sLocalThetaMellinIntegral (w n) (twist T z)‖ := by
        rw [sLocalMellinSchwartzBounds_meyer_rational_theta_mellin_congr T _ _ (he n)]
      _ ≤ D := by simpa using hD 1 n z hz
  have hbnd : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta ℚ ∅).ker.mkQ (f n)) := by
    apply sLocalMellinSchwartzBounds_meyer_rational_empty_inverse_of_trivial_heights
    intro w hw' a ha m
    have htr : ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅))) = 1 := ContinuousMonoidHom.ext fun _ ↦ rfl
    rcases Set.mem_insert_iff.mp hw' with hzero | hw'
    · rw [hzero]
      simpa only [twist,htr] using line f v hfv (hw _ (by simp)) a ha m
    · rw [Set.mem_singleton_iff.mp hw']
      simpa only [twist,htr] using line (fun n ↦ sAdeleSchwartzFourier (f n))
        (fun n ↦ sAdeleSchwartzFourier (v n)) eqF (hw _ (by simp)) a ha m
  let iL : SLocalAdelicThetaSpace ℚ ∅ →L[ℂ] SLocalAdelicThetaSpace ℚ T :=
    ⟨i,(sLocalThetaTransition_isClosedEmbedding (F := ℚ) hST).continuous⟩
  apply (hbnd.image iL).subset
  rintro _ ⟨n,rfl⟩
  exact ⟨_,⟨n,rfl⟩,hfv n⟩

/-- The full bounded-lift equivalence holds for arbitrary families on the rational
archimedean stage, including those with infinite-dimensional theta span. -/
private theorem sLocalMellinSchwartzBounds_meyer_rational_empty
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient ℚ ∅) (hτ : RightInverse τ (sIdeleQuotientNorm ℚ ∅))
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) :
    (∃ A : Set (SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))), Bornology.IsVonNBounded ℂ A ∧
      (range fun n ↦ (sLocalAdelicTheta ℚ ∅).ker.mkQ (v n)) ⊆ (sLocalAdelicTheta ℚ ∅).ker.mkQL '' A) ↔
      sLocalMellinSchwartzBounds ∅ τ v sLocalThetaMellinIntegral ∧
        sLocalMellinSchwartzBounds ∅ τ (fun n ↦ sAdeleSchwartzFourier (v n)) sLocalThetaMellinIntegral := by
  rw [sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded ∅ v]
  constructor
  · exact sLocalMellinSchwartzBounds_meyer_degree_one_forward ∅ (by simp) τ hτ v
  · rintro ⟨hv,hF⟩
    exact sLocalMellinSchwartzBounds_meyer_rational_empty_inverse_from_model v τ hv hF

/-- A criterion for bounded θ-classes, after R. Meyer, *On a representation of the idele class
group related to primes and zeros of L-functions*, Duke Math. J. 127 (2005), arXiv:math/0311468
(page numbers are those of the preprint). Used: Corollary 4.17, p. 34, with the summation map of §5.2,
p. 38; Lemma 4.20, p. 36, at α = 1, with (12) and (15), p. 17, the reflection of weights on
p. 25, Proposition 4.4 and (24), pp. 26–28; and the Fourier isomorphism and the bornologies of
§4.1, pp. 23–24.
The degree-zero isomorphism identifies the S-unit coinvariants, via summation, with
`T(C_S)`. A family in the quotient bornology has representatives in one bounded set.
With α = 1 the embedding tests this bornology on the weighted lines of real part > 1
for the test and its additive Fourier transform (the involution J reflects the weight
as s ↦ 1 − s). We write the Schwartz bornology on those lines on the Fourier side.
A norm section splits the dual as a real line times the
discrete group of characters trivial on the section. An elementary stage on this dual is
supported on a finitely generated subgroup of the discrete factor. On that stage
the ordinary Schwartz seminorms are polynomial weights in the discrete variable
and derivatives of polynomially weighted functions on the real line. Every group
seminorm is bounded by a multiple of word length, itself a group seminorm. The
subgroup and the seminorm bounds may depend on the line.
Lean proves that bounded classes have bounded Mellin transforms, and the converse when the
classes span a finite-dimensional space or are given by even real Schwartz profiles (#7434).
The rest of the converse is the classical input
`sLocalMellinSchwartzBounds_meyer_infinite_span_outside_real_profiles`, which is not proved in
Lean; what the project added in writing the paper's statement for this library is said
there. -/
private theorem sLocalMellinSchwartzBounds_meyer
    (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v : ℕ → ℬₛ(T)) :
    (∃ A : Set ℬₛ(T), Bornology.IsVonNBounded ℂ A ∧
      (range fun n ↦ (Kₛ(T)).mkQ (v n)) ⊆ (Kₛ(T)).mkQL '' A) ↔
      sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral ∧
        sLocalMellinSchwartzBounds T τ (fun n ↦ sAdeleSchwartzFourier (v n)) sLocalThetaMellinIntegral := by
  constructor
  · intro h
    have hb := (sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded T v).mp h
    exact ⟨sLocalMellinSchwartzBounds_meyer_general_forward T τ hτ v hb,sLocalMellinSchwartzBounds_meyer_general_forward T τ hτ _ (sLocalMellinSchwartzBounds_meyer_fourier_bounded T v hb)⟩
  intro h
  apply (sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded T v).mpr
  by_cases hS : FiniteDimensional ℂ (Submodule.span ℂ (range fun n ↦ (sLocalAdelicTheta F T).ker.mkQ (v n)))
  · exact sLocalMellinSchwartzBounds_meyer_span_of_bounds T τ hτ v hS h.1
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_mellin_bounds_level T τ hτ v h.1
  obtain ⟨M,hM,hm⟩ := sLocalMellinSchwartzBounds_meyer_conductor_stage T k v hk
  apply sLocalMellinSchwartzBounds_meyer_infinite_span_bound T τ hτ v hS k hk M hM hm
  intro f hf
  rcases Set.mem_insert_iff.mp hf with hf | hf
  · subst f
    exact (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ v).mp h.1
  obtain rfl := Set.mem_singleton_iff.mp hf
  exact (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ _).mp h.2

/-- If the Mellin transforms of a sequence are dominated on every nonzero weight line
by the transforms of bounded tests, their theta classes are bounded. The functional
equation transfers the comparison to the Fourier transforms. Bounds on neighboring
lines control all Schwartz seminorms in Meyer's description of the coinvariants. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_bounded
    (T : Finset V) (b f : ℕ → ℬₛ(T)) (hb : Bornology.IsVonNBounded ℂ (range b))
    (h : ∀ r : ℝ, r ≠ 0 → ∃ C : ℝ, ∀ n (χ : PontryaginDual (SIdeleQuotient F T)),
      let c := quasiCharacterNormTwist (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) (r : ℂ)
      0 ≤ sLocalIdelicOrderBound c → ‖sLocalIdelicZFunction (f n) c‖ ≤ C * ‖sLocalIdelicZFunction (b n) c‖) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ (Kₛ(T)).mkQ (f n)) := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F T
  have hm (v : ℕ → ℬₛ(T)) := (sLocalMellinSchwartzBounds_meyer T τ hτ v).trans
    (and_congr (sLocalMellinSchwartzBounds_unfold T τ v) (sLocalMellinSchwartzBounds_unfold T τ _))
  have hpair := (hm b).mp ⟨range b, hb, forall_mem_range.mpr (fun n ↦ ⟨b n, mem_range_self n, rfl⟩)⟩
  suffices hs : sLocalMellinSchwartzBounds T τ f ∧
      sLocalMellinSchwartzBounds T τ (fun n ↦ sAdeleSchwartzFourier (f n)) by
    obtain ⟨A, hA, hcov⟩ := (hm f).mpr hs
    exact (hA.image (Kₛ(T)).mkQL).subset hcov
  have hline (r : ℝ) (hr : r ≠ 0) : ∃ C : ℝ,
      ∀ n (χ : PontryaginDual (SIdeleQuotient F T)) (z : ℂ), z.re = r →
        0 ≤ sLocalIdelicOrderBound (chartₜ(T, χ) z) →
        ‖sLocalIdelicZFunction (f n) (chartₜ(T, χ) z)‖ ≤ C * ‖sLocalIdelicZFunction (b n) (chartₜ(T, χ) z)‖ := by
    obtain ⟨C, hC⟩ := h r hr
    refine ⟨C, fun n χ z hz hreg ↦ ?_⟩
    obtain ⟨ψ, he⟩ := sLocalMellinSchwartzBounds_unitary T χ z
    rw [hz] at he
    exact he ▸ hC n ψ (he.symm ▸ hreg)
  constructor
  · apply sLocalMellinSchwartzBounds_transfer T τ b f hpair.1
    intro r hr
    obtain ⟨C, hC⟩ := hline r (zero_lt_one.trans hr).ne'
    exact ⟨C, fun n χ z hz ↦ hC n χ z hz (sLocalOrderBound_positive χ (hz ▸ (zero_lt_one.trans hr)))⟩
  · apply sLocalMellinSchwartzBounds_transfer T τ _ _ hpair.2
    intro r hr
    obtain ⟨C, hC⟩ := hline (1 - r) (sub_ne_zero.mpr hr.ne)
    exact ⟨C, fun n ↦ sLocalMellinSchwartzBounds_fourier
      T (b n) (f n) r C hr (hC n)⟩

end

/-- Sequential closedness of Mellin divisibility on Schwartz–Bruhat tests. On the line
of unitary characters times the norm, divide by the nowhere-zero dilation multiplier.
If a convergent sequence of tests has quotients represented by tests, the quotient for
its limit is represented by a test. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (u : ((S : Set V).integer F)ˣ) :
    let g := Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
      (Units.map (integralAdeleDiagonal F S).toMonoidHom u)
    let c := fun χ : PontryaginDual (SIdeleQuotient F T) ↦
      quasiCharacterNormTwist (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) 1
    sIdeleNorm F T g ≠ 1 → IsSeqClosed {h : ℬₛ(T) | ∃ f : ℬₛ(T), ∀ χ,
      sLocalIdelicZFunction f (c χ) = sLocalIdelicZFunction h (c χ) / (1 - c χ (QuotientGroup.mk g))} := by
  intro g c hg b h hb hlim
  clear_value g
  choose f hf using hb
  let q := (Kₛ(T)).mkQL
  let a : SIdeleQuotient F T := QuotientGroup.mk g
  let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
  let D := ContinuousLinearMap.id ℂ Θₛ(T) - ρ a
  obtain ⟨ε, hε, hgap⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_gap T g hg 1 one_ne_zero
  have den (χ) : 1 - c χ a ≠ 0 :=
    norm_pos_iff.mp (hε.trans_le (by simpa only [Complex.ofReal_one] using hgap χ))
  have symbol := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_symbol T g
  let Z (x : Θₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T)) :=
    (sLocalThetaMellin x).val ⟨c χ, sLocalOrderBound_positive χ (s := 1) (by norm_num)⟩
  have hZ : Injective Z := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_line T
  have eqn (n : ℕ) : D (q (f n)) = q (b n) := by
    apply hZ
    funext χ
    change (sLocalThetaMellin (D (q (f n)))).val _ = sLocalIdelicZFunction (b n) (c χ)
    exact (symbol (f n) ⟨c χ, sLocalOrderBound_positive χ (s := 1) (by norm_num)⟩).trans
      ((mul_comm ..).trans ((eq_div_iff (den χ)).mp (hf n χ)))
  have hbounded := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_bounded
    T b f (hlim.isVonNBounded_range ℂ) (by
      intro r hr
      obtain ⟨δ, hδ, hδχ⟩ :=
        sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division_gap T g hg r hr
      refine ⟨δ⁻¹, ?_⟩
      intro n χ d hd
      have he := symbol (f n) ⟨d, hd⟩
      change (sLocalThetaMellin (D (q (f n)))).val ⟨d, hd⟩ = _ at he
      rw [eqn n] at he
      change sLocalIdelicZFunction (b n) d = (1 - d a) * sLocalIdelicZFunction (f n) d at he
      rw [he, norm_mul, ← mul_assoc]
      exact le_mul_of_one_le_left (norm_nonneg _) ((inv_mul_cancel₀ hδ.ne').symm.le.trans
        (mul_le_mul_of_nonneg_left (hδχ χ) (inv_nonneg.mpr hδ.le))))
  let : T2Space (Θₛ(T)) := sLocalAdelicThetaSpace_strictLF.1
  let : MontelSpace ℂ (Θₛ(T)) := sLocalAdelicThetaSpace_montel
  have hc := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure hbounded.closure
  obtain ⟨y, _, hy⟩ := (hc.image D.continuous).isClosed.mem_of_tendsto
    ((q.continuous.tendsto h).comp hlim) (Eventually.of_forall fun n ↦
      ⟨q (f n), subset_closure (mem_range_self n), eqn n⟩)
  obtain ⟨x, rfl⟩ := (Kₛ(T)).mkQ_surjective y
  refine ⟨x, fun χ ↦ (eq_div_iff (den χ)).mpr ?_⟩
  have he := symbol x ⟨c χ, sLocalOrderBound_positive χ (s := 1) (by norm_num)⟩
  change (sLocalThetaMellin (D (q x))).val _ = _ at he
  rw [show D (q x) = q h from hy] at he
  exact (mul_comm ..).trans he.symm

/-- On the stage with the selected finite place removed, take the translation by
the projection of a diagonal S-unit. When its modulus changes, the difference
between the identity and that translation is open onto its image on theta classes. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (u : ((S : Set V).integer F)ˣ) :
    let g := Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
      (Units.map (integralAdeleDiagonal F S).toMonoidHom u)
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    let D := ContinuousLinearMap.id ℂ Θₛ(T) - ρ (QuotientGroup.mk g)
    sIdeleNorm F T g ≠ 1 → IsOpenMap D.toLinearMap.rangeRestrict := by
  intro g ρ D hg
  let : PolynormableSpace ℂ Θₛ(T) := sLocalAdelicThetaSpace_polynormable
  let : BarrelledSpace ℂ Θₛ(T) := sLocalAdelicThetaSpace_barrelled
  let c (χ : PontryaginDual (SIdeleQuotient F T)) := quasiCharacterNormTwist
    (sIdeleQuotientNorm F T) (isProperMap_sIdeleQuotientNorm F T).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) 1
  let Z (x : Θₛ(T)) (χ : PontryaginDual (SIdeleQuotient F T)) :=
    (sLocalThetaMellin x).val ⟨c χ, sLocalOrderBound_positive χ (by norm_num)⟩
  have hZ : Injective Z := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_line T
  have hmod (χ) : ‖c χ (QuotientGroup.mk g)‖ = ((sIdeleNorm F T g).val : ℝ) := by
    change ‖(χ (QuotientGroup.mk g) : ℂ) * _ ^ (1 : ℂ)‖ = _
    rw [Complex.cpow_one, norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk,
      Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  have hgap (χ) : |1 - ((sIdeleNorm F T g).val : ℝ)| ≤ ‖1 - c χ (QuotientGroup.mk g)‖ := by
    simpa only [norm_one, hmod] using abs_norm_sub_norm_le (1 : ℂ) (c χ (QuotientGroup.mk g))
  have hden (χ) : 1 - c χ (QuotientGroup.mk g) ≠ 0 :=
    norm_pos_iff.mp ((abs_pos.mpr (sub_ne_zero.mpr (fun he ↦ hg (Units.ext (NNReal.eq he.symm))))).trans_le
      (hgap χ))
  have hDZ (x : Θₛ(T)) (χ) : Z (D x) χ = (1 - c χ (QuotientGroup.mk g)) * Z x χ := by
    obtain ⟨f, rfl⟩ := (Kₛ(T)).mkQ_surjective x
    have he : D ((Kₛ(T)).mkQ f) = (Kₛ(T)).mkQ f - (Kₛ(T)).mkQ (schwartzBruhatUnitTranslate g f) :=
      congrArg ((Kₛ(T)).mkQ f - ·) ((existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 g f)
    rw [he]
    dsimp only [Z]
    rw [map_sub]
    change (sLocalIdelicMellin f).val _ - (sLocalIdelicMellin (schwartzBruhatUnitTranslate g f)).val _ = _
    have h := sLocalIdelicMellin_unitTranslate g f ⟨c χ, sLocalOrderBound_positive χ (by norm_num)⟩
    exact (congrArg ((sLocalIdelicMellin f).val _ - ·) h).trans (by
      change _ - c χ _ * Z ((Kₛ(T)).mkQ f) χ = (1 - c χ _) * Z ((Kₛ(T)).mkQ f) χ
      rw [sub_mul, one_mul]
      rfl)
  have hi : Injective D := fun x y e ↦ hZ (funext fun χ ↦
    mul_left_cancel₀ (hden χ) ((hDZ x χ).symm.trans ((congrArg (fun z ↦ Z z χ) e).trans (hDZ y χ))))
  obtain ⟨P, hsum, hF, hproj, hρ⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_levels (F := F) T
  have hcomm (n x) : P n (D x) = D (P n x) := by
    change P n (x - ρ _ x) = P n x - ρ _ (P n x)
    rw [map_sub, hρ]
  apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_sum D P hsum hF hproj hi hcomm
  intro n z y hl
  obtain ⟨φ, a, h, -, ha, halim, hy⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_lift T _ _ hl
  have hdiv := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation_division v i hv u hg
  have hd (j : ℕ) : ∃ f : ℬₛ(T), ∀ χ, sLocalIdelicZFunction f (c χ) =
      sLocalIdelicZFunction (a j) (c χ) / (1 - c χ (QuotientGroup.mk g)) := by
    obtain ⟨f, hf⟩ := (Kₛ(T)).mkQ_surjective (z (φ j)).val
    refine ⟨f, fun χ ↦ (eq_div_iff (hden χ)).mpr ?_⟩
    change Z ((Kₛ(T)).mkQ f) χ * _ = Z ((Kₛ(T)).mkQ (a j)) χ
    rw [hf, ha, hDZ, mul_comm]
  obtain ⟨f, hf⟩ := hdiv hd halim
  refine ⟨(Kₛ(T)).mkQ f, hZ (funext fun χ ↦ ?_)⟩
  rw [hDZ, ← hy]
  change (1 - c χ _) * sLocalIdelicZFunction f (c χ) = sLocalIdelicZFunction h (c χ)
  exact (congrArg ((1 - c χ (QuotientGroup.mk g)) * ·) (hf χ)).trans (mul_div_cancel₀ _ (hden χ))

/-- A translation by a diagonal S-unit gives the identity on S-local theta classes. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_diagonal
    {S : Finset V} (u : ((S : Set V).integer F)ˣ) (f : ℬₛ(S)) :
    f - schwartzBruhatUnitTranslate (sUnitEmbedding F S u) f ∈ Kₛ(S) := by
  have he := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
  have hq : (QuotientGroup.mk (sUnitEmbedding F S u) : SIdeleQuotient F S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨_, ⟨u, rfl⟩, rfl⟩
  have h := he (sUnitEmbedding F S u) f
  rw [hq, map_one] at h
  exact (Submodule.Quotient.eq _).mp h

/-- The diagonal action on the face is the projection of the same S-unit to the
remaining coordinates. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_translate
    {T S : Finset V} (v : S) (i : T ⊆ S) (hv : ∀ w : S, w.val ∉ T ↔ w = v)
    (u : ((S : Set V).integer F)ˣ) (r : ℬₛ(S) →L[ℂ] ℬₛ(T))
    (hr : ∀ f (x : SAdeleRing F S), x.2 v = 0 →
      r f (Multiplicative.ofAdd (x.1, fun w : T ↦ x.2 ⟨w.val, i w.property⟩)) =
        f (Multiplicative.ofAdd x)) (f : ℬₛ(S)) :
    let g := Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
      (Units.map (integralAdeleDiagonal F S).toMonoidHom u)
    r (schwartzBruhatUnitTranslate (sUnitEmbedding F S u) f) = schwartzBruhatUnitTranslate g (r f) := by
  classical
  intro g
  let a := sUnitEmbedding F S u
  let old (x : SAdeleRing F S) : SAdeleRing F T := (x.1, fun w ↦ x.2 ⟨w.val, i w.property⟩)
  apply SchwartzBruhat.ext
  intro y
  let x : SAdeleRing F S := (y.toAdd.1, fun w ↦ if h : w.val ∈ T then y.toAdd.2 ⟨w.val, h⟩ else 0)
  have hx : x.2 v = 0 := dite_eq_right ((hv v).mpr rfl)
  have hy : old x = y.toAdd := Prod.ext rfl (funext fun w ↦ dite_eq_left w.property)
  have hmul : old (a.inv * x) = g.inv * old x := rfl
  have hz : (a.inv * x).2 v = 0 := by change _ * x.2 v = 0; rw [hx, mul_zero]
  change r (schwartzBruhatUnitTranslate a f) (Multiplicative.ofAdd y.toAdd) = _
  rw [← hy, hr _ _ hx, schwartzBruhatUnitTranslate_apply]
  exact (hr f _ hz).symm.trans (congrArg (fun p ↦ r f (Multiplicative.ofAdd p))
    (hmul.trans (congrArg (g.inv * ·) hy)))

/-- Paper: Lemma 5.3.1.5, p. 242.
Restrict theta-null tests to the face `x_v = 0`, giving the space of all traces the
quotient topology from tests. This restriction is open onto its image. Equivalently, for
each zero-neighborhood in the theta kernel, its traces contain a relative zero-neighborhood
among the traces of theta-null tests. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_open
    {S : Finset V} (v : S) (Z : Submodule ℂ ℬₛ(S))
    (hZ : ∀ f, f ∈ Z ↔ ∀ x : SAdeleRing F S, x.2 v = 0 → f (Multiplicative.ofAdd x) = 0) :
    IsOpenMap (Z.mkQ.comp (Kₛ(S)).subtype).rangeRestrict := by
  classical
  let T := S.erase v.val
  have i : T ⊆ S := Finset.erase_subset _ _
  have hv (w : S) : w.val ∉ T ↔ w = v := by
    change w.val ∉ S.erase v.val ↔ w = v
    rw [Finset.mem_erase, and_iff_left w.property, not_not, Subtype.ext_iff]
  obtain ⟨r, hker, hrj, hface⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_restrict v i hv Z hZ
  obtain ⟨u, hnorm, hshell⟩ :=
    sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_shells v i hv r hface
  let g := Units.map ((adeleProjection F T).comp (integralAdelesOutside F S).subtype).toMonoidHom
    (Units.map (integralAdeleDiagonal F S).toMonoidHom u)
  let q := (Kₛ(T)).mkQL
  let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
  let D := ContinuousLinearMap.id ℂ Θₛ(T) - ρ (QuotientGroup.mk g)
  let B := D.toLinearMap.range
  let δ : Θₛ(T) →L[ℂ] B := D.codRestrict B (fun c ↦ ⟨c, rfl⟩)
  let d := δ.comp q
  have hopen : IsOpenMap d :=
    (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_dilation v i hv u hnorm).comp
      (Kₛ(T)).isOpenMap_mkQ
  let J : ℬₛ(T) →L[ℂ] ℬₛ(S) :=
    ⟨sAdeleSchwartzTransition F i, (sAdeleSchwartzTransition_isEmbedding F i).continuous⟩
  let A : ℬₛ(T) →L[ℂ] ℬₛ(T) :=
    ⟨unitTranslateEnd g, continuous_sAdeleSchwartz_unitTranslate.comp (continuous_const.prodMk continuous_id)⟩
  let U : ℬₛ(S) →L[ℂ] ℬₛ(S) :=
    ⟨unitTranslateEnd (sUnitEmbedding F S u),
      continuous_sAdeleSchwartz_unitTranslate.comp (continuous_const.prodMk continuous_id)⟩
  have hd (c : ℬₛ(T)) : D (q c) = q (c - A c) := by
    rw [map_sub]
    exact congrArg (q c - ·) ((existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 g c)
  let R := Z.liftQL r hker.ge
  let m := Z.mkQ.comp (Kₛ(S)).subtype
  let h := R.comp m.range.subtypeL
  have ht (y : m.range) : q (h y) ∈ B := by
    obtain ⟨_, ⟨k, hk⟩, rfl⟩ := y
    obtain ⟨I, a, ha, hsum⟩ := hshell k hk
    obtain ⟨c, hc⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_telescope
      unitTranslateEnd g (Kₛ(T)) I a _ hsum
    rw [← ha] at hc
    exact ⟨q c, (hd c).trans ((Submodule.Quotient.eq _).mpr hc).symm⟩
  let t := (q.comp h).codRestrict B ht
  let H := (h.comp (ContinuousLinearMap.fst ℂ m.range ℬₛ(T))) +
    (A.comp (ContinuousLinearMap.snd ℂ m.range ℬₛ(T)))
  let l := J.comp H - (U.comp J).comp (ContinuousLinearMap.snd ℂ m.range ℬₛ(T))
  apply sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_lift
    (Kₛ(S)) Z.mkQ t d hopen l
  intro y c heq
  have hy : q (h y) = q (c - A c) := (congrArg Subtype.val heq).trans (hd c)
  have hk : h y - (c - A c) ∈ Kₛ(T) := (Submodule.Quotient.eq _).mp hy
  have hl : l (y, c) = J (h y + A c) - U (J c) := rfl
  rw [hl]
  constructor
  · have hJ := sLocalThetaTransition_preserves_kernel (F := F) i hk
    have hU := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_diagonal u (J c)
    convert (Kₛ(S)).add_mem hJ hU using 1
    change J (h y + A c) - U (J c) = J (h y - (c - A c)) + (J c - U (J c))
    simp only [map_add, map_sub]
    abel
  · obtain ⟨_, ⟨k, hk⟩, rfl⟩ := y
    apply (Submodule.Quotient.eq Z).mpr
    apply hker.le
    change r (J (r k + A c) - U (J c) - k) = 0
    rw [map_sub, map_sub, show r (J (r k + A c)) = r k + A c from hrj _]
    have hU : r (U (J c)) = A c :=
      (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_translate v i hv u r hface
        (J c)).trans (congrArg A (hrj c))
    rw [hU, add_sub_cancel_right]
    exact sub_self _


/-- Paper: Lemma 5.3.1.5, p. 242.
On theta functions invariant under the integer units at one finite place, every continuous
quotient seminorm is bounded by a continuous quotient seminorm of the difference with the
uniformizer translate. The Mellin identity theorem on page 242 gives injectivity. The relative
openness argument there controls seminorms before taking the theta quotient. A reconstruction
of the primitive along uniformizer orbits with bounds modulo the theta kernel would give this
estimate. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound {S : Finset V} (v : S)
    (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) (p : Seminorm ℂ Θₛ(S)) (hp : Continuous p) :
    ∃ q : Seminorm ℂ Θₛ(S), Continuous q ∧ ∀ f : ℬₛ(S),
      (∀ (u : (HeightOneSpectrum.adicCompletionIntegers F v.val).units) (x : (SAdeleRing F S)ˣ),
        sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v u.val)⁻¹ * x) =
          sLocalAdelicTheta F S f x) →
      p ((Kₛ(S)).mkQ f) ≤ q ((Kₛ(S)).mkQ
        (f - schwartzBruhatUnitTranslate (adelicPrincipalValueLocalUnit v π) f)) := by
  let T := sLocalThetaPrincipalValue F (Finset.singleton_subset_iff.mpr v.2)
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.2)
  let : PolynormableSpace ℂ Θₛ(S) := sLocalAdelicThetaSpace_polynormable
  have hi : IsInducing T := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_descend
    (Kₛ(S)) P T (sAdelePrincipalValue_isClosedEmbedding _).isInducing
    (sLocalThetaPrincipalValue_continuous _)
    (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_injective v π hπ)
    (fun _ ↦ rfl) (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_trace_open v P.range
      (sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_face v))
  obtain ⟨q, hq, hle⟩ := Seminorm.exists_le_comp_of_isInducing hp hi
  refine ⟨q, hq, fun f hf ↦ ?_⟩
  have he : (Kₛ(S)).mkQ (f - schwartzBruhatUnitTranslate (adelicPrincipalValueLocalUnit v π) f) =
      T ((Kₛ(S)).mkQ f) := by
    apply (Submodule.Quotient.eq _).mpr
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    ext x
    have h := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound_removed v π hπ f hf x
    rw [map_sub, ContinuousMap.sub_apply] at h ⊢
    rw [sAdelePrincipalValue_preserves_thetaKernel_translate, ← h]
    exact sub_sub_cancel _ _
  rw [he]
  exact hle _

/-- On the unit-invariant theta functions the average is a single translate. Thus the
uniformizer difference and principal value give the same quotient class. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_difference {S : Finset V} (v : S)
    (π : (v.val.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.val.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer
      (π : v.val.adicCompletion F)) (f : ℬₛ(S))
    (hf : ∀ (u : (HeightOneSpectrum.adicCompletionIntegers F v.val).units) (x : (SAdeleRing F S)ˣ),
      sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v u.val)⁻¹ * x) =
        sLocalAdelicTheta F S f x) :
    (Kₛ(S)).mkQ (f - schwartzBruhatUnitTranslate (adelicPrincipalValueLocalUnit v π) f) =
      (Kₛ(S)).mkQ (sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property) f) := by
  apply (Submodule.Quotient.eq _).mpr
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
  ext x
  rw [map_sub, ContinuousMap.sub_apply, sAdelePrincipalValue_preserves_thetaKernel_translate,
    sLocalAdelicTheta_sAdelePrincipalValue_singleton v π hπ]
  let U := (HeightOneSpectrum.adicCompletionIntegers F v.val).units
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
  let : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  have hU : MeasurableSet (U : Set (v.val.adicCompletion F)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  rw [setIntegral_congr_fun hU (g := fun _ ↦
    sLocalAdelicTheta F S f ((adelicPrincipalValueLocalUnit v π)⁻¹ * x)) (fun u hu ↦ by
      rw [sAdelePrincipalValue_preserves_thetaKernel_translate,
        sLocalThetaPrincipalValue_isClosedEmbedding_localUnit_mul, mul_inv_rev, mul_assoc]
      exact hf ⟨u, hu⟩ _), setIntegral_const, Complex.real_smul]
  have hm : (μ.real U : ℂ) ≠ 0 := by
    exact_mod_cast (finitePlacePrincipalValue_integrable v.val π 0 1).1.ne'
  change _ = _ - (μ.real U : ℂ)⁻¹ * ((μ.real U : ℂ) * _)
  rw [inv_mul_cancel_left₀ hm]

/-- For a continuous endomorphism of a complete Hausdorff locally convex space, an inverse
seminorm estimate on the vectors `x - P x` suffices. The term `P x` is already controlled,
and an inducing additive map has complete image. -/
private theorem sLocalThetaPrincipalValue_isClosedEmbedding_of_bound {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E]
    (hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (P : E →ₗ[ℂ] E) (hP : Continuous P)
    (hbound : ∀ p : Seminorm ℂ E, Continuous p → ∃ q : Seminorm ℂ E, Continuous q ∧
      ∀ x, p (x - P x) ≤ q (P (x - P x))) : IsClosedEmbedding P := by
  have hind : IsInducing P := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm (by simpa only [map_zero] using (hP.tendsto 0).le_comap) (fun W hW ↦ ?_)
    obtain ⟨p, hp, hpW⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hW
    obtain ⟨q, hq, hle⟩ := hbound p hp
    let t := p + q.comp (LinearMap.id - P)
    have ht : Continuous t := hp.add (hq.comp (continuous_id.sub hP))
    refine ⟨t.ball 0 1, Seminorm.ball_mem_nhds ht one_pos, fun x hx ↦ hpW ?_⟩
    apply (Seminorm.mem_ball_zero p).mpr
    have hx' := (Seminorm.mem_ball_zero t).mp hx
    refine lt_of_le_of_lt ?_ hx'
    calc p x = p (P x + (x - P x)) := by rw [add_sub_cancel]
         _ ≤ p (P x) + p (x - P x) := map_add_le_add _ _ _
         _ ≤ t (P x) := by
           change _ ≤ p (P x) + q (P x - P (P x))
           simpa only [map_sub] using add_le_add_right (hle x) (p (P x))
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hc
  exact ⟨hind.isEmbedding,
    (AddMonoidHom.isUniformInducing_of_isInducing hind).isComplete_range.isClosed⟩

private theorem sLocalThetaPrincipalValue_isClosedEmbedding_singleton {S : Finset V} (v : S) :
    IsClosedEmbedding (sLocalThetaPrincipalValue F (Finset.singleton_subset_iff.mpr v.property)) := by
  let : T2Space Θₛ(S) := (sLocalAdelicThetaSpace_lf (F := F) (S := S)).1
  let : PolynormableSpace ℂ Θₛ(S) := sLocalAdelicThetaSpace_polynormable
  apply sLocalThetaPrincipalValue_isClosedEmbedding_of_bound sLocalAdelicThetaSpace_complete _
    (sLocalThetaPrincipalValue_continuous _)
  intro p hp
  let hv := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (hv.choose : v.val.adicCompletion F) hv.choose_spec.ne_zero
  obtain ⟨q, hq, hle⟩ := sLocalThetaPrincipalValue_isClosedEmbedding_difference_bound v π
    hv.choose_spec p hp
  refine ⟨q, hq, fun x ↦ ?_⟩
  obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective x
  let P := sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr v.property)
  let g := f - P f
  have hg := sLocalThetaPrincipalValue_isClosedEmbedding_unitInvariant v π hv.choose_spec f
  have h := hle g hg
  rw [sLocalThetaPrincipalValue_isClosedEmbedding_difference v π hv.choose_spec g hg] at h
  change p ((Kₛ(S)).mkQ f - (Kₛ(S)).mkQ (P f)) ≤
    q ((sLocalThetaPrincipalValue F _) ((Kₛ(S)).mkQ f - (Kₛ(S)).mkQ (P f)))
  rw [← (Kₛ(S)).mkQ.map_sub]
  exact h

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value on theta classes is a closed topological embedding. -/
theorem sLocalThetaPrincipalValue_isClosedEmbedding {S S₀ : Finset V} (h₀ : S₀ ⊆ S)
    (hn : S₀.Nonempty) :
    IsClosedEmbedding (sLocalThetaPrincipalValue F h₀) := by
  classical
  let R (v : V) : ℬₛ(S) →ₗ[ℂ] ℬₛ(S) := if h : v ∈ S then
    sAdelePrincipalValue F (Finset.singleton_subset_iff.mpr h) else 1
  have factor (l : List V) (hl : ∀ v ∈ l, v ∈ S) :
      ∃ A : Θₛ(S) →ₗ[ℂ] Θₛ(S), IsClosedEmbedding A ∧
        ∀ f, A ((Kₛ(S)).mkQ f) = (Kₛ(S)).mkQ ((l.map R).prod f) := by
    induction l with
    | nil => exact ⟨1, IsClosedEmbedding.id, fun _ ↦ rfl⟩
    | cons v l ih =>
      have hv := hl v List.mem_cons_self
      obtain ⟨A, hA, he⟩ := ih fun w hw ↦ hl w (List.mem_cons_of_mem _ hw)
      let P := sLocalThetaPrincipalValue F (Finset.singleton_subset_iff.mpr hv)
      refine ⟨P.comp A,
        (sLocalThetaPrincipalValue_isClosedEmbedding_singleton (F := F) ⟨v, hv⟩).comp hA, fun f ↦ ?_⟩
      rw [LinearMap.comp_apply, he, List.map_cons, List.prod_cons]
      simp only [R, dite_eq_left hv]
      rfl
  obtain ⟨A, hA, he⟩ := factor S₀.val.toList (fun v hv ↦ h₀ (Multiset.mem_toList.mp hv))
  suffices sLocalThetaPrincipalValue F h₀ = A by rwa [this]
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (Kₛ(S)).mkQ_surjective x
  exact (sLocalThetaPrincipalValue_mk h₀ f).trans
    ((congrArg (Kₛ(S)).mkQ (sAdelePrincipalValue_preserves_thetaKernel_list h₀ f)).trans (he f).symm)

private theorem sLocalThetaPrincipalValue_transition_tmul {ι A X : Type*} {M : ι → Type*}
    [TopologicalSpace A] [AddCommGroup A] [Module ℂ A] [TopologicalSpace X]
    [AddCommGroup X] [Module ℂ X] [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] X)
    (P : ∀ i, M i →ₗ[ℂ] M i) (a : A) (b : ∀ i, M i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, M i)
    let Q : W →ₗ[ℂ] W := PiTensorProduct.map P
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A)
      Q).comp e.symm.toLinearMap)) (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, b i))) =
        e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, P i (b i))) := by
  change e ((TensorProduct.map _ (PiTensorProduct.map P)) (e.symm (e _))) = _
  erw [e.symm_apply_apply]
  apply congrArg e
  exact (TensorProduct.map_tmul LinearMap.id (PiTensorProduct.map P) a _).trans
    (congrArg (TensorProduct.tmul ℂ a) (PiTensorProduct.map_tprod P b))

open Classical in
private theorem sLocalThetaPrincipalValue_transition_factors {ι : Type*} {M : ι → Type*}
    [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)]
    {S₀ S T : Finset ι} (h₀ : S₀ ⊆ S) (P : ∀ v, M v →ₗ[ℂ] M v) (c : ∀ v, M v)
    (g : ∀ w : S, M w.val) :
    let extend := fun (b : ∀ w : S, M w.val) (w : T) ↦
      if hw : w.val ∈ S then b ⟨w.val, hw⟩ else c w.val
    let op := fun (R : Finset ι) (b : ∀ w : R, M w.val) (w : R) ↦
      (if w.val ∈ S₀ then P w.val else LinearMap.id) (b w)
    extend (op S g) = op T (extend g) := by
  funext w
  by_cases hw : w.val ∈ S
  · simp [hw]
  · simp [hw, show w.val ∉ S₀ from fun h ↦ hw (h₀ h)]

open Classical in
private theorem sLocalThetaPrincipalValue_transition_tests {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) :
    (sAdeleSchwartzTransition F hST).comp (sAdelePrincipalValue F h₀) =
      (sAdelePrincipalValue F (h₀.trans hST)).comp (sAdeleSchwartzTransition F hST) := by
  let e (R : Finset V) := (sAdeleSchwartz_inductiveTensor_equiv F R).choose
  apply sLocalThetaPrincipalValue_transition_ext (e S)
  intro a g
  let pureTest (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) : ℬₛ(R) :=
    e R (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
  let P (v : V) : ℬ(v.adicCompletion F) →ₗ[ℂ] ℬ(v.adicCompletion F) :=
    if v ∈ S₀ then (finitePlacePrincipalValue v).toLinearMap else LinearMap.id
  let op (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) (w : R) :=
    P w.val (b w)
  have pv (R : Finset V) (hR : S₀ ⊆ R) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) :
      sAdelePrincipalValue F hR (pureTest R b) = pureTest R (op R b) := by
    unfold sAdelePrincipalValue
    with_reducible exact sLocalThetaPrincipalValue_transition_tmul (e R) (fun w : R ↦ P w.val) a b
  let extend (b : ∀ w : S, ℬ(w.val.adicCompletion F)) (w : T) :=
    if hw : w.val ∈ S then b ⟨w.val, hw⟩ else finiteStandardGaussian w.val 1
  have insertTest (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      sAdeleSchwartzTransition F hST (pureTest S b) = pureTest T (extend b) := by
    apply Subtype.ext
    funext x
    have hg (w : T) (hw : w.val ∉ S) (y : w.val.adicCompletion F) :
        extend b w (Multiplicative.ofAdd y) =
          (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F)).indicator
            (fun _ ↦ (1 : ℂ)) y := by
      rw [show extend b w = finiteStandardGaussian w.val 1 by simp [extend, hw]]
      change finiteStandardGaussianValue w.val 1 y = _
      unfold finiteStandardGaussianValue
      exact ite_eq_left fun u _ ↦ rfl
    have hr (w : S) : extend b ⟨w.val, hST w.property⟩ = b w := by
      simp only [extend, dite_eq_left w.property]
    have spec (R : Finset V) (d : ∀ w : R, ℬ(w.val.adicCompletion F)) (y : SAdeleRing F R) :
        pureTest R d (Multiplicative.ofAdd y) = a (Multiplicative.ofAdd y.1) *
          ∏ w : R, d w (Multiplicative.ofAdd (y.2 w)) := by
      with_reducible exact (sAdeleSchwartz_inductiveTensor_equiv F R).choose_spec a d y
    with_reducible refine Eq.trans ?_ (spec T (extend b) x.toAdd).symm
    change sAdeleSchwartzTransition F hST (pureTest S b) (Multiplicative.ofAdd x.toAdd) = _
    with_reducible
      refine sAdeleSchwartzTransition_pure F hST a (extend b) hg (pureTest S b) ?_ x.toAdd
    intro y
    simp only [hr]
    with_reducible exact spec S b y
  with_reducible change sAdeleSchwartzTransition F hST (sAdelePrincipalValue F h₀ (pureTest S g)) =
    sAdelePrincipalValue F (h₀.trans hST) (sAdeleSchwartzTransition F hST (pureTest S g))
  have hcomm : extend (op S g) = op T (extend g) := by
    with_reducible
      exact sLocalThetaPrincipalValue_transition_factors (M := fun v : V ↦ ℬ(v.adicCompletion F))
        (T := T) h₀ (fun v ↦ (finitePlacePrincipalValue v).toLinearMap)
        (fun v ↦ finiteStandardGaussian v 1) g
  with_reducible
    exact (congrArg (sAdeleSchwartzTransition F hST) (pv S h₀ g)).trans
      ((insertTest (op S g)).trans ((congrArg (pureTest T) hcomm).trans
        ((pv T (h₀.trans hST) (extend g)).symm.trans
          (congrArg (sAdelePrincipalValue F (h₀.trans hST)) (insertTest g).symm))))

private theorem sLocalThetaPrincipalValue_transition_mapQ {X Y : Type*} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (K : Submodule ℂ X) (L : Submodule ℂ Y)
    (i : X →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X) (q : Y →ₗ[ℂ] Y) (hi : K ≤ L.comap i)
    (hp : K ≤ K.comap p) (hq : L ≤ L.comap q) (h : i.comp p = q.comp i) :
    (K.mapQ L i hi).comp (K.mapQ K p hp) = (L.mapQ L q hq).comp (K.mapQ L i hi) := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  exact congrArg L.mkQ (DFunLike.congr_fun h f)

/-- Paper: Lemma 5.3.1.5, p. 242.
The principal value commutes with passage from an S-local theta stage to a larger stage. -/
theorem sLocalThetaPrincipalValue_transition {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hST : S ⊆ T) (hn : S₀.Nonempty) :
    (sLocalThetaTransition (F := F) hST).comp (sLocalThetaPrincipalValue F h₀) =
      (sLocalThetaPrincipalValue F (h₀.trans hST)).comp (sLocalThetaTransition hST) := by
  unfold sLocalThetaTransition sLocalThetaPrincipalValue
  apply sLocalThetaPrincipalValue_transition_mapQ
  exact sLocalThetaPrincipalValue_transition_tests h₀ hST

/-- Paper: Lemma 5.3.1.5, p. 242.
The local and global principal value operators commute with insertion of an S-local theta stage. -/
theorem sLocalThetaPrincipalValue_toGlobal {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) :
    (sLocalThetaToGlobal F S).comp (sLocalThetaPrincipalValue F h₀) =
      (globalThetaPrincipalValue F S₀).comp (sLocalThetaToGlobal F S) := by
  unfold sLocalThetaToGlobal sLocalThetaPrincipalValue globalThetaPrincipalValue
  apply sLocalThetaPrincipalValue_transition_mapQ
  exact sLocalThetaPrincipalValue_toGlobal_tests h₀

/-- Weil's local principal value commutes with multiplicative translation, since both only
rescale the argument. -/
private theorem globalThetaPrincipalValue_equivariant_local (v : V) (c : (v.adicCompletion F)ˣ)
    (h : ℬ(v.adicCompletion F)) :
    finitePlacePrincipalValue v (schwartzBruhatUnitTranslate c h) =
      schwartzBruhatUnitTranslate c (finitePlacePrincipalValue v h) := by
  let hπ0 := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (hπ0.choose : v.adicCompletion F) hπ0.choose_spec.ne_zero
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  apply Subtype.ext
  funext x
  change finitePlacePrincipalValue v (schwartzBruhatUnitTranslate c h)
      (Multiplicative.ofAdd x.toAdd) =
    schwartzBruhatUnitTranslate c (finitePlacePrincipalValue v h) (Multiplicative.ofAdd x.toAdd)
  rw [schwartzBruhatUnitTranslate_apply, finitePlacePrincipalValue_spec v π hπ0.choose_spec,
    finitePlacePrincipalValue_spec v π hπ0.choose_spec]
  unfold finitePlacePrincipalValueFun
  simp only [schwartzBruhatUnitTranslate_apply, toAdd_ofAdd]
  congr 2
  refine setIntegral_congr_fun ?_ fun u _ ↦ ?_
  · exact (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  · exact congrArg (fun y ↦ h (Multiplicative.ofAdd y)) (by ring)

/-- Two linear maps agree once they agree on the pure tensors of an inductive tensor product
with a projective tensor power. -/
private theorem globalThetaPrincipalValue_equivariant_ext {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B)
    (L₁ L₂ : B →ₗ[ℂ] B)
    (h : ∀ (a : A) (g : ∀ i, D i), L₁ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) =
      L₂ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (x : B) :
    L₁ x = L₂ x := by
  obtain ⟨t, rfl⟩ := e.surjective x
  let W := FinestLocallyConvex (⨂[ℂ] i, D i)
  let M₁ : A ⊗[ℂ] W →ₗ[ℂ] B := L₁ ∘ₗ (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B)
  let M₂ : A ⊗[ℂ] W →ₗ[ℂ] B := L₂ ∘ₗ (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B)
  have hM : M₁ = M₂ := by
    refine TensorProduct.ext' fun a z ↦ ?_
    refine PiTensorProduct.induction_on (motive := fun z : ⨂[ℂ] i, D i ↦
      M₁ (a ⊗ₜ[ℂ] (z : W)) = M₂ (a ⊗ₜ[ℂ] (z : W))) z ?_ ?_
    · intro r g
      have ht : (a ⊗ₜ[ℂ] (((r • (⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
          r • (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) :=
        (TensorProduct.mk ℂ A W a).map_smul r (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)
      have hp : M₁ (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) =
          M₂ (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) := h a g
      exact (congrArg M₁ ht).trans ((map_smul M₁ r _).trans ((congrArg (r • ·) hp).trans
        ((map_smul M₂ r _).symm.trans (congrArg M₂ ht.symm))))
    · intro z₁ z₂ h₁ h₂
      have ht : (a ⊗ₜ[ℂ] (((z₁ + z₂ : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
          a ⊗ₜ[ℂ] (z₁ : W) + a ⊗ₜ[ℂ] (z₂ : W) :=
        (TensorProduct.mk ℂ A W a).map_add (z₁ : W) (z₂ : W)
      exact (congrArg M₁ ht).trans ((map_add M₁ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans
        ((map_add M₂ _ _).symm.trans (congrArg M₂ ht.symm))))
  exact LinearMap.congr_fun hM t

open Classical in
/-- The S-local principal value commutes with translation by an S-idele. -/
private theorem globalThetaPrincipalValue_equivariant_stage {S₀ : Finset V}
    (gS : (SAdeleRing F S₀)ˣ) (k : ℬₛ(S₀)) :
    sAdelePrincipalValue F (Finset.Subset.refl S₀) (schwartzBruhatUnitTranslate gS k) =
      schwartzBruhatUnitTranslate gS (sAdelePrincipalValue F (Finset.Subset.refl S₀) k) := by
  let e' := (sAdeleSchwartz_inductiveTensor_equiv F S₀).choose
  have he' := (sAdeleSchwartz_inductiveTensor_equiv F S₀).choose_spec
  let P := sAdelePrincipalValue F (Finset.Subset.refl S₀)
  let T : ℬₛ(S₀) →ₗ[ℂ] ℬₛ(S₀) :=
    { toFun := schwartzBruhatUnitTranslate gS
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let gInf : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom gS
  let gw (w : S₀) : (w.val.adicCompletion F)ˣ :=
    Units.map ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).toMonoidHom gS
  have hT (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S₀, ℬ(w.val.adicCompletion F)) :
      T (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = e' (schwartzBruhatUnitTranslate gInf a ⊗ₜ[ℂ]
        (⨂ₜ[ℂ] w, schwartzBruhatUnitTranslate (gw w) (g w))) := by
    apply Subtype.ext
    funext x
    refine (he' a g ((↑gS⁻¹ : SAdeleRing F S₀) * x.toAdd)).trans (Eq.trans ?_
      (he' (schwartzBruhatUnitTranslate gInf a)
        (fun w ↦ schwartzBruhatUnitTranslate (gw w) (g w)) x.toAdd).symm)
    rfl
  have hyp : ∀ (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S₀, ℬ(w.val.adicCompletion F)),
      (P ∘ₗ T) (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = (T ∘ₗ P) (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := by
    intro a g
    have h1 := sAdelePrincipalValue_tmul (Finset.Subset.refl S₀) (schwartzBruhatUnitTranslate gInf a)
      (fun w ↦ schwartzBruhatUnitTranslate (gw w) (g w))
    have h2 := sAdelePrincipalValue_tmul (Finset.Subset.refl S₀) a g
    refine (congrArg P (hT a g)).trans (h1.trans ?_)
    refine Eq.trans ?_ (congrArg T h2).symm
    refine Eq.trans ?_ (hT a _).symm
    have hfun : (fun w : S₀ ↦ if w.val ∈ S₀ then
          finitePlacePrincipalValue w.val (schwartzBruhatUnitTranslate (gw w) (g w))
        else schwartzBruhatUnitTranslate (gw w) (g w)) =
        fun w ↦ schwartzBruhatUnitTranslate (gw w)
          (if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w) := by
      funext w
      simp only [w.property, ite_true]
      exact globalThetaPrincipalValue_equivariant_local w.val (gw w) (g w)
    exact congrArg (fun φ : ∀ w : S₀, ℬ(w.val.adicCompletion F) ↦
      e' (schwartzBruhatUnitTranslate gInf a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, φ w))) hfun
  exact globalThetaPrincipalValue_equivariant_ext
    (D := fun w : S₀ ↦ ℬ(w.val.adicCompletion F)) e' (P ∘ₗ T) (T ∘ₗ P)
    (by with_reducible exact hyp) k

open Classical in
/-- The S-local principal value commutes with translation by an S-idele, for any set of
selected places: the selected factors are invariant by the local commutation and the
remaining factors act by the identity on both sides. -/
private theorem sLocalThetaPrincipalValue_equivariant_stage {S₀ S : Finset V} (h₀ : S₀ ⊆ S)
    (gS : (SAdeleRing F S)ˣ) (k : ℬₛ(S)) :
    sAdelePrincipalValue F h₀ (schwartzBruhatUnitTranslate gS k) =
      schwartzBruhatUnitTranslate gS (sAdelePrincipalValue F h₀ k) := by
  let e' := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he' := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let P := sAdelePrincipalValue F h₀
  let T : ℬₛ(S) →ₗ[ℂ] ℬₛ(S) :=
    { toFun := schwartzBruhatUnitTranslate gS
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let gInf : (InfiniteAdeleRing F)ˣ := Units.map (RingHom.fst _ _).toMonoidHom gS
  let gw (w : S) : (w.val.adicCompletion F)ˣ :=
    Units.map ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).toMonoidHom gS
  have hT (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      T (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = e' (schwartzBruhatUnitTranslate gInf a ⊗ₜ[ℂ]
        (⨂ₜ[ℂ] w, schwartzBruhatUnitTranslate (gw w) (g w))) := by
    apply Subtype.ext
    funext x
    refine (he' a g ((↑gS⁻¹ : SAdeleRing F S) * x.toAdd)).trans (Eq.trans ?_
      (he' (schwartzBruhatUnitTranslate gInf a)
        (fun w ↦ schwartzBruhatUnitTranslate (gw w) (g w)) x.toAdd).symm)
    rfl
  have hyp : ∀ (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F)),
      (P ∘ₗ T) (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) = (T ∘ₗ P) (e' (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := by
    intro a g
    have h1 := sAdelePrincipalValue_tmul (F := F) h₀ (schwartzBruhatUnitTranslate gInf a)
      (fun w ↦ schwartzBruhatUnitTranslate (gw w) (g w))
    have h2 := sAdelePrincipalValue_tmul (F := F) h₀ a g
    refine (congrArg P (hT a g)).trans (h1.trans ?_)
    refine Eq.trans ?_ (congrArg T h2).symm
    refine Eq.trans ?_ (hT a _).symm
    have hfun : (fun w : S ↦ if w.val ∈ S₀ then
          finitePlacePrincipalValue w.val (schwartzBruhatUnitTranslate (gw w) (g w))
        else schwartzBruhatUnitTranslate (gw w) (g w)) =
        fun w ↦ schwartzBruhatUnitTranslate (gw w)
          (if w.val ∈ S₀ then finitePlacePrincipalValue w.val (g w) else g w) := by
      funext w
      by_cases hw : w.val ∈ S₀
      · simp only [hw, ite_true]
        exact globalThetaPrincipalValue_equivariant_local w.val (gw w) (g w)
      · simp only [hw, ite_false]
    exact congrArg (fun φ : ∀ w : S, ℬ(w.val.adicCompletion F) ↦
      e' (schwartzBruhatUnitTranslate gInf a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, φ w))) hfun
  exact globalThetaPrincipalValue_equivariant_ext
    (D := fun w : S ↦ ℬ(w.val.adicCompletion F)) e' (P ∘ₗ T) (T ∘ₗ P)
    (by with_reducible exact hyp) k

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value commutes with each S-idele translation on theta classes. -/
theorem sLocalThetaPrincipalValue_equivariant {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    Submodule.Quotient.mk
        (sAdelePrincipalValue F h₀ (schwartzBruhatUnitTranslate g f)) =
      (Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (sAdelePrincipalValue F h₀ f)) : Θₛ(S)) :=
  congrArg Submodule.Quotient.mk (sLocalThetaPrincipalValue_equivariant_stage h₀ g f)

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value commutes with each idele translation on theta classes. -/
theorem globalThetaPrincipalValue_equivariant {S₀ : Finset V}
    (hn : S₀.Nonempty) (g : IdeleGroup (𝓞 F) F) (f : ℬ(𝔸[F])) :
    Submodule.Quotient.mk (adelePrincipalValue F S₀ (schwartzBruhatUnitTranslate g f)) =
      (Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (adelePrincipalValue F S₀ f)) : Θ𝔽) := by
  apply congrArg
  have : Fact (∀ w : {w : V // w ∉ S₀},
      IsOpen (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))) :=
    ⟨fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F)⟩
  let : IsTopologicalRing (FiniteAdeleTail F S₀) :=
    RestrictedProduct.isTopologicalRing (fun w : {w : V // w ∉ S₀} ↦ w.val.adicCompletion F)
  let Tl := ℬ(FiniteAdeleTail F S₀)
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose
  have he := (sAdeleTailSchwartz_inductiveTensor_equiv F S₀).choose_spec
  let P := adelePrincipalValue F S₀
  let T : ℬ(𝔸[F]) →ₗ[ℂ] ℬ(𝔸[F]) :=
    { toFun := schwartzBruhatUnitTranslate g
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let gS : (SAdeleRing F S₀)ˣ := Units.map (adeleProjection F S₀).toMonoidHom g
  have hval : finiteAdeleTailProjection F S₀ g.val.2 * finiteAdeleTailProjection F S₀ g.inv.2 = 1 := by
    apply RestrictedProduct.ext
    intro w
    exact congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 w.val) g.val_inv
  have hinv : finiteAdeleTailProjection F S₀ g.inv.2 * finiteAdeleTailProjection F S₀ g.val.2 = 1 := by
    apply RestrictedProduct.ext
    intro w
    exact congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 w.val) g.inv_val
  let gt : (FiniteAdeleTail F S₀)ˣ := ⟨_, _, hval, hinv⟩
  have hT (k : ℬₛ(S₀)) (b : Tl) : T (e (k ⊗ₜ[ℂ] b)) =
      e (schwartzBruhatUnitTranslate gS k ⊗ₜ[ℂ] schwartzBruhatUnitTranslate gt b) := by
    apply Subtype.ext
    funext x
    refine (he k b ((↑g⁻¹ : AdeleRing (𝓞 F) F) * x.toAdd)).trans (Eq.trans ?_
      (he (schwartzBruhatUnitTranslate gS k) (schwartzBruhatUnitTranslate gt b) x.toAdd).symm)
    rfl
  obtain ⟨t, rfl⟩ := e.surjective f
  suffices h : P ∘ₗ T ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S₀) Tl →ₗ[ℂ] _) =
      T ∘ₗ P ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S₀) Tl →ₗ[ℂ] _) from
    LinearMap.congr_fun h t
  refine TensorProduct.ext' fun k b ↦ ?_
  have h1 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl S₀)
    (schwartzBruhatUnitTranslate gS k) (schwartzBruhatUnitTranslate gt b)
  have h2 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl S₀) k b
  change P (T (e (k ⊗ₜ[ℂ] b))) = T (P (e (k ⊗ₜ[ℂ] b)))
  refine (congrArg P (hT k b)).trans (h1.trans ?_)
  refine Eq.trans ?_ (congrArg T h2).symm
  refine Eq.trans ?_ (hT _ b).symm
  exact congrArg (fun z ↦ e (z ⊗ₜ[ℂ] schwartzBruhatUnitTranslate gt b))
    (globalThetaPrincipalValue_equivariant_stage gS k)

private theorem globalThetaPrincipalValue_isotypicAverage_tensor
    {M N Y : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (e : InductiveTensor M N ≃L[ℂ] Y)
    (f : M →ₗ[ℂ] M) (g : N →ₗ[ℂ] N) (hf : f = LinearMap.id) (hg : g = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map f g).comp e.symm.toLinearMap) = LinearMap.id := by
  subst f g
  have H : TensorProduct.map (LinearMap.id (R := ℂ) (M := M)) (LinearMap.id (R := ℂ) (M := N)) =
      LinearMap.id := TensorProduct.map_id
  rw [H]
  apply LinearMap.ext
  exact e.apply_symm_apply

private theorem globalThetaPrincipalValue_isotypicAverage_emptyTensor
    {ι M Y : Type*} {N : ι → Type*} [IsEmpty ι]
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (e : InductiveTensor M (FinestLocallyConvex (⨂[ℂ] i, N i)) ≃L[ℂ] Y)
    (L : ∀ i, N i →ₗ[ℂ] N i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, N i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map L
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id (R := ℂ) (M := M)) P).comp
      e.symm.toLinearMap) = LinearMap.id := by
  intro W P
  have hp : P = LinearMap.id := (congrArg (PiTensorProduct.map (R := ℂ))
    (Subsingleton.elim L (fun i ↦ (LinearMap.id : N i →ₗ[ℂ] N i)))).trans PiTensorProduct.map_id
  exact globalThetaPrincipalValue_isotypicAverage_tensor e LinearMap.id P rfl hp

/-- With no places in `S`, the adelic principal value projection is the identity. -/
theorem globalThetaPrincipalValue_isotypicAverage_emptyTest :
    adelePrincipalValue F ∅ = LinearMap.id := by
  unfold adelePrincipalValue
  with_reducible_and_instances
    refine globalThetaPrincipalValue_isotypicAverage_tensor _ _ _ ?_ rfl
  unfold sAdelePrincipalValue
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_emptyTensor (ι := ↥(∅ : Finset V)) _ _

private theorem globalThetaPrincipalValue_isotypicAverage_mapQ_id {E : Type*}
    [AddCommGroup E] [Module ℂ E] (K : Submodule ℂ E) (P : E →ₗ[ℂ] E)
    (hK : K ≤ K.comap P) (h : P = LinearMap.id) (x : E ⧸ K) : K.mapQ K P hK x = x := by
  subst P
  exact Submodule.Quotient.induction_on K x fun _ ↦ rfl

private theorem globalThetaPrincipalValue_isotypicAverage_empty (x : Θ𝔽) :
    globalThetaPrincipalValue F ∅ x = x := by
  unfold globalThetaPrincipalValue
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_mapQ_id _ _ _
      (globalThetaPrincipalValue_isotypicAverage_emptyTest (F := F)) x

private theorem globalThetaPrincipalValue_isotypicAverage_onReps {G C E X : Type*}
    (π : G → C) (m : E → X) (hπ : Surjective π) (hm : Surjective m)
    (p : E → E) (t : G → E → E) (P : X → X) (ρ : C → X → X)
    (hp : ∀ f, P (m f) = m (p f)) (ht : ∀ g f, ρ (π g) (m f) = m (t g f))
    (h : ∀ g f, m (p (t g f)) = m (t g (p f))) (q : C) (y : X) :
    P (ρ q y) = ρ q (P y) := by
  obtain ⟨g, rfl⟩ := hπ q
  obtain ⟨f, rfl⟩ := hm y
  rw [ht, hp, hp, ht, h]

private theorem globalThetaPrincipalValue_isotypicAverage_action {S₀ : Finset V} (hn : S₀.Nonempty)
    (q : IdeleClassGroup (𝓞 F) F) (y : Θ𝔽) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    globalThetaPrincipalValue F S₀ (ρ q y) = ρ q (globalThetaPrincipalValue F S₀ y) := by
  intro ρ
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_onReps
      (QuotientGroup.mk : IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F)
      (Submodule.Quotient.mk (p := K𝔽)) QuotientGroup.mk_surjective
      (Submodule.Quotient.mk_surjective _)
      (adelePrincipalValue F S₀) schwartzBruhatUnitTranslate (globalThetaPrincipalValue F S₀)
      (fun g y ↦ ρ g y) (globalThetaPrincipalValue_mk S₀)
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
      (globalThetaPrincipalValue_equivariant hn) q y

private theorem globalThetaPrincipalValue_isotypicAverage_commutes
    {G E : Type*} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    {μ : Measure G} {ρ : G →* (E →L[ℂ] E)} {χ : PontryaginDual G} {A : E →L[ℂ] E}
    (hA : IsPettisIsotypicAverageOn μ univ ρ χ A) (P : E →L[ℂ] E)
    (hP : ∀ g y, P (ρ g y) = ρ g (P y)) (x : E) : P (A x) = A (P x) := by
  have h : HasPettisIntegral (.positive (μ.restrict univ))
      (fun g ↦ P (star (χ g : ℂ) • ρ g x)) (P (A x)) := by
    obtain ⟨hi, he⟩ := hA x
    refine ⟨fun φ ↦ hi (φ.comp P), LinearMap.ext fun φ ↦ ?_⟩
    exact LinearMap.congr_fun he (φ.comp P)
  simp only [map_smul, hP] at h
  exact h.unique (hA (P x))

private theorem sLocalThetaPrincipalValue_isotypicAverage_action {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (q : SIdeleQuotient F S) (y : Θₛ(S)) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
    sLocalThetaPrincipalValue F h₀ (ρ q y) = ρ q (sLocalThetaPrincipalValue F h₀ y) := by
  intro ρ
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_onReps
      (QuotientGroup.mk : (SAdeleRing F S)ˣ → SIdeleQuotient F S)
      (Submodule.Quotient.mk (p := Kₛ(S))) QuotientGroup.mk_surjective
      (Submodule.Quotient.mk_surjective _)
      (sAdelePrincipalValue F h₀) schwartzBruhatUnitTranslate (sLocalThetaPrincipalValue F h₀)
      (fun g y ↦ ρ g y) (sLocalThetaPrincipalValue_mk h₀)
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
      (fun g f ↦ congrArg (Submodule.Quotient.mk (p := Kₛ(S)))
        (sLocalThetaPrincipalValue_equivariant_stage h₀ g f)) q y

/-- Paper: Lemma 5.3.1.5, p. 242.
The S-local principal value commutes with the norm-one character average of §5.2.3. -/
theorem sLocalThetaPrincipalValue_isotypicAverage {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) (x : Θₛ(S)) :
    let A := (existsUnique_sLocalThetaIsotypicAverage (F := F) χ).exists.choose
    sLocalThetaPrincipalValue F h₀ (A x) = A (sLocalThetaPrincipalValue F h₀ x) := by
  intro A
  let P : Θₛ(S) →L[ℂ] Θₛ(S) :=
    ⟨sLocalThetaPrincipalValue F h₀, sLocalThetaPrincipalValue_continuous h₀⟩
  let ρ₀ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
  let : T2Space Θₛ(S) := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ Θₛ(S) := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : IsTopologicalAddGroup Θₛ(S) := PolynormableSpace.isTopologicalAddGroup ℂ Θₛ(S)
  let : ContinuousSMul ℂ Θₛ(S) := (PolynormableSpace.withSeminorms ℂ Θₛ(S)).continuousSMul
  let : MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _
  with_reducible_and_instances
    refine globalThetaPrincipalValue_isotypicAverage_commutes
      (μ := sLocalNormOneQuotientMeasure F S)
      (ρ := ρ₀.comp (MonoidHom.ker (sIdeleQuotientNorm F S)).subtype) (χ := χ) (A := A)
      (P := P) (existsUnique_sLocalThetaIsotypicAverage (F := F) χ).exists.choose_spec ?_ x
  intro g y
  exact sLocalThetaPrincipalValue_isotypicAverage_action h₀ g.val y

private theorem globalThetaPrincipalValue_isotypicAverage_nonempty (S₀ : Finset V) (hn : S₀.Nonempty)
    (χ : PontryaginDual (ideleClassNorm F).ker) (x : Θ𝔽) :
    let A := (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose
    globalThetaPrincipalValue F S₀ (A x) = A (globalThetaPrincipalValue F S₀ x) := by
  intro A
  let P : Θ𝔽 →L[ℂ] Θ𝔽 := ⟨globalThetaPrincipalValue F S₀, globalThetaPrincipalValue_continuous S₀⟩
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup Θ𝔽 := PolynormableSpace.isTopologicalAddGroup ℂ Θ𝔽
  let : ContinuousSMul ℂ Θ𝔽 := (PolynormableSpace.withSeminorms ℂ Θ𝔽).continuousSMul
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  refine globalThetaPrincipalValue_isotypicAverage_commutes
    (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose_spec P ?_ x
  intro g y
  exact globalThetaPrincipalValue_isotypicAverage_action (F := F) hn g.val y

private theorem globalThetaPrincipalValue_isotypicAverage_cases {ι E : Type*}
    (P : Finset ι → E → E) (A : E → E) (he : ∀ y, P ∅ y = y)
    (hn : ∀ t : Finset ι, t.Nonempty → ∀ y, P t (A y) = A (P t y))
    (s : Finset ι) (x : E) : P s (A x) = A (P s x) := by
  rcases s.eq_empty_or_nonempty with rfl | h
  · rw [he, he]
  · exact hn s h x

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value commutes with the norm-one character average of §5.2.3. -/
theorem globalThetaPrincipalValue_isotypicAverage (S₀ : Finset V)
    (χ : PontryaginDual (ideleClassNorm F).ker) (x : Θ𝔽) :
    let A := (existsUnique_globalThetaIsotypicAverage (F := F) χ).exists.choose
    globalThetaPrincipalValue F S₀ (A x) = A (globalThetaPrincipalValue F S₀ x) := by
  intro A
  with_reducible_and_instances
    exact globalThetaPrincipalValue_isotypicAverage_cases
      (fun S y ↦ globalThetaPrincipalValue F S y) A
      (globalThetaPrincipalValue_isotypicAverage_empty (F := F))
      (fun S hn y ↦ globalThetaPrincipalValue_isotypicAverage_nonempty (F := F) S hn χ y) S₀ x

/-- Through an inducing linear map into a polynormable space, every continuous seminorm of the
source is bounded by a continuous seminorm of the target. -/
private theorem globalThetaPrincipalValue_isClosedEmbedding_bound {X E : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (f : X →ₗ[ℂ] E) (hf : IsInducing f) (s : Seminorm ℂ X) (hs : Continuous s) :
    ∃ t : Seminorm ℂ E, Continuous t ∧ ∀ z, s z ≤ t (f z) := by
  have : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  obtain ⟨F, C, -, hle⟩ :=
    Seminorm.bound_of_continuous (hf.withSeminorms (PolynormableSpace.withSeminorms ℂ E)) s hs
  refine ⟨C • F.sup (fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.1),
    (Seminorm.continuous_finsetSup fun t _ ↦ t.2).const_smul _, fun z ↦ (hle z).trans ?_⟩
  simp only [smul_apply, Seminorm.finset_sup_apply, SeminormFamily.comp_apply,
    Seminorm.comp_apply, le_refl]

/-- An endomorphism of a space exhausted by closed embedded stages is a closed embedding when it
restricts to a closed embedding on each stage and commutes with continuous projections onto the
stages that fix every earlier stage. -/
private theorem globalThetaPrincipalValue_isClosedEmbedding_ofProjections {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [hE : PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (ι : ∀ n, X n →L[ℂ] E) (hι : ∀ n, IsClosedEmbedding (ι n))
    (P : E →L[ℂ] E) (Pn : ∀ n, X n →L[ℂ] X n) (hPn : ∀ n, IsClosedEmbedding (Pn n))
    (hP : ∀ n z, P (ι n z) = ι n (Pn n z))
    (pr : ℕ → E →L[ℂ] E) (hmem : ∀ n x, pr n x ∈ range (ι n))
    (hfix : ∀ n m, n ≤ m → ∀ z, pr m (ι n z) = ι n z)
    (hprP : ∀ n x, pr n (P x) = P (pr n x))
    (hexh : ∀ x, ∃ n z, ι n z = x)
    (hfin : ∀ q : Seminorm ℂ E, (∀ n, Continuous (q ∘ ι n)) → Continuous q) :
    IsClosedEmbedding P := by
  have : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  have hPι (n : ℕ) : IsClosedEmbedding (fun z ↦ P (ι n z)) := by
    have h : (fun z ↦ P (ι n z)) = ι n ∘ Pn n := funext (hP n)
    rw [h]
    exact (hι n).comp (hPn n)
  -- Injectivity is checked on a stage containing the vector.
  have hinj : Injective P := by
    refine (injective_iff_map_eq_zero P).mpr fun x hx ↦ ?_
    obtain ⟨n, z, rfl⟩ := hexh x
    have hz : z = 0 := (hPι n).injective (by simpa using hx)
    rw [hz, map_zero]
  -- A limit point of the range is fixed by the projection of its stage, which maps the
  -- range into the closed range of the stage.
  have hclosed : IsClosed (range P) := by
    refine isClosed_of_closure_subset fun y hy ↦ ?_
    obtain ⟨m, z, rfl⟩ := hexh y
    have hmaps : MapsTo (pr m) (range P) (range fun w ↦ P (ι m w)) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hmem m x
      exact ⟨w, by rw [hprP, ← hw]⟩
    have h := map_mem_closure (pr m).continuous hy hmaps
    rw [(hPι m).isClosed_range.closure_eq, hfix m m le_rfl] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨ι m w, hw⟩
  -- The successive differences of the projections split each vector into finitely many
  -- stage pieces, on each of which the stage estimate applies.
  let D : ℕ → E →L[ℂ] E := fun n ↦ Nat.casesOn n (pr 0) fun k ↦ pr (k + 1) - pr k
  have hDsum (m : ℕ) (x : E) : ∑ n ∈ Finset.range (m + 1), D n x = pr m x := by
    induction m with
    | zero => simp [D]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp [D]
  have hDzero (m : ℕ) (z : X m) (n : ℕ) (hn : m < n) : D n (ι m z) = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [D, sub_apply]
    rw [hfix m (k + 1) (by omega), hfix m k (by omega), sub_self]
  have hDmem (n : ℕ) (x : E) : ∃ w, ι n w = D n x := by
    cases n with
    | zero => exact hmem 0 x
    | succ k =>
      obtain ⟨a, ha⟩ := hmem (k + 1) x
      obtain ⟨b, hb⟩ := hmem k x
      obtain ⟨c, hc⟩ := hmem (k + 1) (ι k b)
      rw [hfix k (k + 1) (Nat.le_succ k)] at hc
      exact ⟨a - c, by simp [D, ha, hb, hc]⟩
  have hDP (n : ℕ) (x : E) : D n (P x) = P (D n x) := by
    cases n with
    | zero => exact hprP 0 x
    | succ k => simp [D, hprP]
  have key (p : Seminorm ℂ E) (hp : Continuous p) :
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ x, p x ≤ q (P x) := by
    have hb (n : ℕ) : ∃ t : Seminorm ℂ E, Continuous t ∧ ∀ z, p (ι n z) ≤ t (P (ι n z)) := by
      obtain ⟨t, ht, hle⟩ := globalThetaPrincipalValue_isClosedEmbedding_bound
        ((P : E →ₗ[ℂ] E).comp (ι n : X n →ₗ[ℂ] E)) (hPι n).isInducing
        (p.comp (ι n : X n →ₗ[ℂ] E)) (hp.comp (ι n).continuous)
      exact ⟨t, ht, hle⟩
    choose t ht htle using hb
    have hsupp (x : E) : ∃ m, ∀ n, m < n → D n x = 0 := by
      obtain ⟨m, z, rfl⟩ := hexh x
      exact ⟨m, hDzero m z⟩
    have hsumm (x : E) : Summable fun n ↦ t n (D n x) := by
      obtain ⟨m, hm⟩ := hsupp x
      refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun n hn ↦ ?_
      rw [Finset.mem_range, not_lt] at hn
      rw [hm n (by omega), map_zero]
    let q : Seminorm ℂ E := Seminorm.of (fun x ↦ ∑' n, t n (D n x))
      (fun x y ↦ by
        have h := (hsumm x).add (hsumm y)
        calc ∑' n, t n (D n (x + y)) ≤ ∑' n, (t n (D n x) + t n (D n y)) :=
              (hsumm (x + y)).tsum_le_tsum (fun n ↦ by rw [map_add]; exact map_add_le_add _ _ _) h
          _ = _ := (hsumm x).tsum_add (hsumm y))
      (fun a x ↦ by
        simp only [map_smul, map_smul_eq_mul]
        exact tsum_mul_left)
    have hq : Continuous q := by
      refine hfin q fun k ↦ ?_
      have h : (fun z ↦ q (ι k z)) = fun z ↦ ∑ n ∈ Finset.range (k + 1), t n (D n (ι k z)) := by
        funext z
        refine tsum_eq_sum fun n hn ↦ ?_
        rw [Finset.mem_range, not_lt] at hn
        rw [hDzero k z n (by omega), map_zero]
      change Continuous (fun z ↦ q (ι k z))
      rw [h]
      exact continuous_finsetSum _ fun n _ ↦ (ht n).comp ((D n).continuous.comp (ι k).continuous)
    refine ⟨q, hq, fun x ↦ ?_⟩
    obtain ⟨m, z, rfl⟩ := hexh x
    calc p (ι m z) = p (∑ n ∈ Finset.range (m + 1), D n (ι m z)) := by
          rw [hDsum, hfix m m le_rfl]
      _ ≤ ∑ n ∈ Finset.range (m + 1), p (D n (ι m z)) :=
          Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ ∑ n ∈ Finset.range (m + 1), t n (D n (P (ι m z))) := by
          refine Finset.sum_le_sum fun n _ ↦ ?_
          obtain ⟨w, hw⟩ := hDmem n (ι m z)
          rw [hDP, ← hw]
          exact htle n w
      _ ≤ ∑' n, t n (D n (P (ι m z))) :=
          (hsumm _).sum_le_tsum _ fun n _ ↦ apply_nonneg _ _
  have hind : IsInducing P := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ (fun U hU ↦ ?_)
    · have h := P.continuous.tendsto 0
      rw [map_zero] at h
      exact h.le_comap
    · obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
      obtain ⟨q, hq, hpq⟩ := key p hp
      refine ⟨q.ball 0 1, Seminorm.ball_mem_nhds hq one_pos, fun x hx ↦ hpU ?_⟩
      rw [mem_preimage, Seminorm.mem_ball_zero] at hx
      exact (Seminorm.mem_ball_zero p).mpr ((hpq x).trans_lt hx)
  exact ⟨⟨hind, hinj⟩, hclosed⟩

/-- Continuous linear left inverses of the steps of a chain of stages, commuting with operators
compatible with the stage maps, assemble into continuous projections onto the stages that fix
the earlier stages and commute with the operator on the limit. -/
private theorem globalThetaPrincipalValue_isClosedEmbedding_projections {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    [hX : ∀ n, PolynormableSpace ℂ (X n)]
    (ι : ∀ n, X n →L[ℂ] E) (hι : ∀ n, Injective (ι n))
    (j : ∀ n, X n →L[ℂ] X (n + 1)) (hj : ∀ n z, ι (n + 1) (j n z) = ι n z)
    (r : ∀ n, X (n + 1) →L[ℂ] X n) (hr : ∀ n z, r n (j n z) = z)
    (P : E →L[ℂ] E) (Pn : ∀ n, X n →L[ℂ] X n) (hP : ∀ n z, P (ι n z) = ι n (Pn n z))
    (hrP : ∀ n z, r n (Pn (n + 1) z) = Pn n (r n z))
    (hexh : ∀ x, ∃ n z, ι n z = x)
    (hfin : ∀ (N : ℕ) (q : Seminorm ℂ E), (∀ d, Continuous (q ∘ ι (N + d))) → Continuous q) :
    ∃ pr : ℕ → E →L[ℂ] E, (∀ n x, pr n x ∈ range (ι n)) ∧
      (∀ n m, n ≤ m → ∀ z, pr m (ι n z) = ι n z) ∧ (∀ n x, pr n (P x) = P (pr n x)) := by
  have hnest (a b : ℕ) (hab : a ≤ b) (z : X a) : ∃ w : X b, ι b w = ι a z := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨z, rfl⟩
    | succ b _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨j b w, (hj b w).trans hw⟩
  -- The composite of the left inverses from stage `n + d` down to stage `n`.
  let R (n : ℕ) : ∀ d, X (n + d) →L[ℂ] X n := fun d ↦
    Nat.rec (motive := fun d ↦ X (n + d) →L[ℂ] X n) (ContinuousLinearMap.id ℂ (X n))
      (fun d R ↦ R.comp (r (n + d))) d
  have hRsucc (n d : ℕ) (z : X (n + (d + 1))) : R n (d + 1) z = R n d (r (n + d) z) := rfl
  have hRP (n d : ℕ) (z : X (n + d)) : R n d (Pn (n + d) z) = Pn n (R n d z) := by
    induction d with
    | zero => rfl
    | succ d ih =>
      have h := hrP (n + d) z
      exact (congrArg (R n d) h).trans (ih (r (n + d) z))
  -- The composite only depends on the vector of the limit that a stage vector represents.
  have hcons (n d : ℕ) (z : X (n + d)) (d' : ℕ) (hd : d ≤ d') :
      ∀ z' : X (n + d'), ι (n + d') z' = ι (n + d) z → R n d' z' = R n d z := by
    induction d', hd using Nat.le_induction with
    | base => exact fun z' h ↦ congrArg (R n d) (hι _ h)
    | succ d' hdd' ih =>
      intro z' h
      obtain ⟨w, hw⟩ := hnest (n + d) (n + d') (by omega) z
      have hz' : z' = j (n + d') w := hι (n + d' + 1) (h.trans (hw.symm.trans (hj _ w).symm))
      rw [hz']
      exact (congrArg (R n d') (hr (n + d') w)).trans (ih w hw)
  have hcons' (n d d' : ℕ) (z : X (n + d)) (z' : X (n + d'))
      (h : ι (n + d') z' = ι (n + d) z) : R n d' z' = R n d z := by
    rcases le_total d d' with hd | hd
    · exact hcons n d z d' hd z' h
    · exact (hcons n d' z' d hd z h.symm).symm
  have hrep (n : ℕ) (x : E) : ∃ d, ∃ z : X (n + d), ι (n + d) z = x := by
    obtain ⟨k, z, rfl⟩ := hexh x
    obtain ⟨w, hw⟩ := hnest k (n + k) (by omega) z
    exact ⟨k, w, hw⟩
  have hcommon (n : ℕ) (x y : E) :
      ∃ d, ∃ a b : X (n + d), ι (n + d) a = x ∧ ι (n + d) b = y := by
    obtain ⟨d₁, z₁, rfl⟩ := hrep n x
    obtain ⟨d₂, z₂, rfl⟩ := hrep n y
    obtain ⟨a, ha⟩ := hnest (n + d₁) (n + max d₁ d₂) (by omega) z₁
    obtain ⟨b, hb⟩ := hnest (n + d₂) (n + max d₁ d₂) (by omega) z₂
    exact ⟨max d₁ d₂, a, b, ha, hb⟩
  choose dx zx hzx using hrep
  have hQ (n d : ℕ) (z : X (n + d)) : R n (dx n (ι (n + d) z)) (zx n (ι (n + d) z)) = R n d z :=
    hcons' n d _ z _ (hzx n _)
  let Q (n : ℕ) : E →ₗ[ℂ] X n :=
    { toFun := fun x ↦ R n (dx n x) (zx n x)
      map_add' := fun x y ↦ by
        obtain ⟨d, a, b, rfl, rfl⟩ := hcommon n x y
        have h := hQ n d (a + b)
        rw [map_add] at h
        rw [h, hQ, hQ, map_add]
      map_smul' := fun c x ↦ by
        obtain ⟨d, z, rfl⟩ : ∃ d, ∃ z : X (n + d), ι (n + d) z = x := ⟨dx n x, zx n x, hzx n x⟩
        have h := hQ n d (c • z)
        rw [map_smul] at h
        rw [h, hQ, map_smul]
        rfl }
  have hQapp (n d : ℕ) (z : X (n + d)) : Q n (ι (n + d) z) = R n d z := hQ n d z
  have hQc (n : ℕ) : Continuous (Q n) := by
    refine (PolynormableSpace.withSeminorms ℂ (X n)).continuous_of_continuous_comp (Q n)
      fun s ↦ hfin n ((s.1).comp (Q n)) fun d ↦ ?_
    have h : ⇑((s.1).comp (Q n)) ∘ ι (n + d) = s.1 ∘ R n d :=
      funext fun z ↦ congrArg s.1 (hQapp n d z)
    rw [h]
    exact s.2.comp (R n d).continuous
  refine ⟨fun n ↦ (ι n).comp ⟨Q n, hQc n⟩, fun n x ↦ ⟨_, rfl⟩, fun n m hnm z ↦ ?_,
    fun n x ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hnest n m hnm z
    change ι m (Q m (ι n z)) = ι n z
    rw [← hw]
    exact congrArg (ι m) (hQapp m 0 w)
  · obtain ⟨d, z, rfl⟩ : ∃ d, ∃ z : X (n + d), ι (n + d) z = x := ⟨dx n x, zx n x, hzx n x⟩
    change ι n (Q n (P (ι (n + d) z))) = P (ι n (Q n (ι (n + d) z)))
    rw [hP (n + d), hP n, hQapp, hQapp, hRP]

/-- The finite places of a number field form a countable set, since their ideals are finitely
generated over the countable ring of integers. -/
private theorem globalThetaPrincipalValue_isClosedEmbedding_countable : Countable V := by
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have h : Function.Surjective (fun s : Finset (𝓞 F) ↦ Ideal.span (s : Set (𝓞 F))) :=
    fun I ↦ IsNoetherian.noetherian I
  let : Countable (Ideal (𝓞 F)) := h.countable
  exact (show Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) from fun _ _ h ↦
    HeightOneSpectrum.ext h).countable

open Classical in
/-- On the product of an old test `f` and a test `g` at one new place `v`, the principal value
of the enlarged stage acts through `f`. -/
private theorem globalThetaPrincipalValue_isClosedEmbedding_insertTest {S₀ S : Finset V}
    (h₀ : S₀ ⊆ S) (v : V) (hv : v ∉ S)
    (e : InductiveTensor ℬₛ(S) ℬ(FinitePlaceProduct F (insert v S \ S)) ≃L[ℂ] ℬₛ(insert v S))
    (he : ∀ (f : ℬₛ(S)) (g : ℬ(FinitePlaceProduct F (insert v S \ S)))
      (z : SAdeleRing F (insert v S)),
      e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd z) =
        f (Multiplicative.ofAdd (z.1, fun w : S ↦
          z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
        g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦
          z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)))
    (g : ℬ(FinitePlaceProduct F (insert v S \ S))) (f : ℬₛ(S)) :
    sAdelePrincipalValue F (h₀.trans (Finset.subset_insert v S)) (e (f ⊗ₜ[ℂ] g)) =
      e (sAdelePrincipalValue F h₀ f ⊗ₜ[ℂ] g) := by
  have hd := sAdeleDifferenceSchwartz_insert_pure (F := F) v hv e he g
  let φ := hd.choose
  have hφ := hd.choose_spec
  let eR (R : Finset V) := (sAdeleSchwartz_inductiveTensor_equiv F R).choose
  let P (u : V) : ℬ(u.adicCompletion F) →ₗ[ℂ] ℬ(u.adicCompletion F) :=
    if u ∈ S₀ then (finitePlacePrincipalValue u).toLinearMap else LinearMap.id
  let op (R : Finset V) (b : ∀ w : R, ℬ(w.val.adicCompletion F)) (w : R) := P w.val (b w)
  have pv (R : Finset V) (hR : S₀ ⊆ R) (a : ℬ(InfiniteAdeleRing F))
      (b : ∀ w : R, ℬ(w.val.adicCompletion F)) :
      sAdelePrincipalValue F hR (eR R (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))) =
        eR R (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, op R b w)) := by
    unfold sAdelePrincipalValue
    with_reducible exact sLocalThetaPrincipalValue_transition_tmul (eR R) (fun w : R ↦ P w.val) a b
  let G (u : V) : ℬ(u.adicCompletion F) := if h : u = v then h ▸ φ else 0
  let extend (b : ∀ w : S, ℬ(w.val.adicCompletion F)) (w : ↥(insert v S)) :
      ℬ(w.val.adicCompletion F) :=
    if hw : w.val ∈ S then b ⟨w.val, hw⟩ else G w.val
  have hext (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      e (eR S (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ⊗ₜ[ℂ] g) =
        eR (insert v S) (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, extend b w)) := by
    refine hφ a b (extend b) (fun w ↦ dite_eq_left w.property) ?_
    change (if hw : v ∈ S then b ⟨v, hw⟩ else G v) = φ
    rw [dite_eq_right hv]
    change (if h : v = v then h ▸ φ else 0) = φ
    rw [dite_eq_left rfl]
  have hcomm (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      extend (op S b) = op (insert v S) (extend b) := by
    with_reducible
      exact sLocalThetaPrincipalValue_transition_factors (M := fun u : V ↦ ℬ(u.adicCompletion F))
        (T := insert v S) h₀ (fun u ↦ (finitePlacePrincipalValue u).toLinearMap) G b
  have key (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F)) :
      e (sAdelePrincipalValue F h₀ (eR S (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))) ⊗ₜ[ℂ] g) =
        sAdelePrincipalValue F (h₀.trans (Finset.subset_insert v S))
          (e (eR S (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ⊗ₜ[ℂ] g)) := by
    have h1 := congrArg (fun k ↦ e (k ⊗ₜ[ℂ] g)) (pv S h₀ a b)
    have h2 := hext a (op S b)
    have h3 := congrArg (fun c : ∀ w : ↥(insert v S), ℬ(w.val.adicCompletion F) ↦
      eR (insert v S) (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, c w))) (hcomm b)
    have h4 := pv (insert v S) (h₀.trans (Finset.subset_insert v S)) a (extend b)
    have h5 := congrArg (sAdelePrincipalValue F (h₀.trans (Finset.subset_insert v S))) (hext a b)
    exact h1.trans (h2.trans (h3.trans (h4.symm.trans h5.symm)))
  let Eg : ℬₛ(S) →ₗ[ℂ] ℬₛ(insert v S) := e.toLinearMap.comp ((TensorProduct.mk ℂ _ _).flip g)
  have hsq := sLocalThetaPrincipalValue_transition_ext (eR S) Eg (sAdelePrincipalValue F h₀)
    (sAdelePrincipalValue F (h₀.trans (Finset.subset_insert v S))) key
  exact (LinearMap.congr_fun hsq f).symm

open Classical in
/-- Paper: Lemma 5.3.1.5, proof, p. 242.
At a stage `S` containing the selected places `S₀`, the transition of theta classes to the stage
`T = insert v S` with one more finite place `v` has a continuous linear left inverse that
commutes with the principal value.

The left inverse is the one of `sLocalThetaTransition_exists_leftInverse_insert_commute`. On the
class of the product of an old test `f` and a new test `g` it is a finite combination of classes
of translates of `f`. The principal value of `T` acts on `f ⊗ g` through `f`, and on classes it
commutes with translation by S-ideles (`sLocalThetaPrincipalValue_equivariant`).
With the closed embeddings on the stages, these left inverses give the global closed embedding
`globalThetaPrincipalValue_isClosedEmbedding`. They replace the printed step that the global
range is the image of the range at one fixed stage.
The larger stage `T` is an argument with `hT : T = insert v S`, so that the lemma applies to
stages that equal `insert v S` without being written that way. -/
private theorem globalThetaPrincipalValue_isClosedEmbedding_retraction {S₀ S T : Finset V}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) (hST : S ⊆ T) (v : V) (hv : v ∉ S)
    (hT : T = insert v S) :
    ∃ r : Θₛ(T) →L[ℂ] Θₛ(S),
      Function.LeftInverse r (sLocalThetaTransition (F := F) hST) ∧
      ∀ x, r (sLocalThetaPrincipalValue F (h₀.trans hST) x) =
        sLocalThetaPrincipalValue F h₀ (r x) := by
  subst hT
  have hr := sLocalThetaTransition_exists_leftInverse_insert_commute (F := F) (S := S) v hv
  have hd := sAdeleDifferenceSchwartz_inductiveTensor_equiv F (Finset.subset_insert v S)
  let r := hr.choose
  let e := hd.choose
  refine ⟨r, hr.choose_spec.1, fun x ↦ ?_⟩
  -- On the class of a product of an old and a new test, the principal value passes to the old
  -- test, and the left inverse commutes with it there.
  have key (f : ℬₛ(S)) (g : ℬ(FinitePlaceProduct F (insert v S \ S))) :
      r (sLocalThetaPrincipalValue F (h₀.trans hST) (Submodule.Quotient.mk (e (f ⊗ₜ[ℂ] g)))) =
        sLocalThetaPrincipalValue F h₀ (r (Submodule.Quotient.mk (e (f ⊗ₜ[ℂ] g)))) :=
    (congrArg (fun k ↦ r (Submodule.Quotient.mk k : Θₛ(insert v S)))
      (globalThetaPrincipalValue_isClosedEmbedding_insertTest h₀ v hv e hd.choose_spec g f)).trans
      (hr.choose_spec.2 e hd.choose_spec (sAdelePrincipalValue F h₀)
        (sLocalThetaPrincipalValue F h₀) (fun _ ↦ rfl)
        (fun γ f ↦ sLocalThetaPrincipalValue_equivariant h₀ hn γ f) f g)
  have hlin : (r.toLinearMap.comp (sLocalThetaPrincipalValue F (h₀.trans hST))).comp
        ((Kₛ(insert v S)).mkQ.comp e.toLinearMap) =
      ((sLocalThetaPrincipalValue F h₀).comp r.toLinearMap).comp
        ((Kₛ(insert v S)).mkQ.comp e.toLinearMap) :=
    TensorProduct.ext' key
  obtain ⟨k, rfl⟩ := (Kₛ(insert v S)).mkQ_surjective x
  obtain ⟨t, rfl⟩ := e.surjective k
  exact LinearMap.congr_fun hlin t

-- TODO(paper-gap): The proof of global closed range claims that the image is contained in
-- any fixed S-stage. This does not follow from stage compatibility and fails at larger stages.

/-- Paper: Lemma 5.3.1.5, p. 242.
The global principal value on theta classes is a closed topological embedding. -/
theorem globalThetaPrincipalValue_isClosedEmbedding {S₀ : Finset V} (hn : S₀.Nonempty) :
    IsClosedEmbedding (globalThetaPrincipalValue F S₀) := by
  classical
  have : Countable V := globalThetaPrincipalValue_isClosedEmbedding_countable (F := F)
  have : Nonempty V := ⟨hn.choose⟩
  obtain ⟨e, he⟩ := exists_surjective_nat V
  -- A cofinal chain of stages that starts at `S₀` and adds one place at a time.
  let S : ℕ → Finset V := fun n ↦
    Nat.rec (motive := fun _ ↦ Finset V) S₀ (fun k T ↦ insert (e k) T) n
  have hstep (n : ℕ) : S n ⊆ S (n + 1) := Finset.subset_insert (e n) (S n)
  have hmono : Monotone S := monotone_nat_of_le_succ hstep
  have h₀ (n : ℕ) : S₀ ⊆ S n := hmono (Nat.zero_le n)
  have hcof (T : Finset V) (N : ℕ) : ∃ d, T ⊆ S (N + d) := by
    choose k hk using he
    refine ⟨T.sup fun v ↦ k v + 1, fun v hv ↦ ?_⟩
    have hle : k v + 1 ≤ N + T.sup fun v ↦ k v + 1 :=
      (Finset.le_sup (f := fun v ↦ k v + 1) hv).trans (Nat.le_add_left _ _)
    have hv' : e (k v) ∈ S (k v + 1) := Finset.mem_insert_self (e (k v)) (S (k v))
    rw [hk v] at hv'
    exact hmono hle hv'
  let ι (n : ℕ) : Θₛ(S n) →L[ℂ] Θ𝔽 :=
    ⟨sLocalThetaToGlobal F (S n), sLocalThetaToGlobal_continuous⟩
  let j (n : ℕ) : Θₛ(S n) →L[ℂ] Θₛ(S (n + 1)) :=
    ⟨sLocalThetaTransition (hstep n), sLocalThetaTransition_continuous (hstep n)⟩
  let Pn (n : ℕ) : Θₛ(S n) →L[ℂ] Θₛ(S n) :=
    ⟨sLocalThetaPrincipalValue F (h₀ n), sLocalThetaPrincipalValue_continuous (h₀ n)⟩
  let P : Θ𝔽 →L[ℂ] Θ𝔽 := ⟨globalThetaPrincipalValue F S₀, globalThetaPrincipalValue_continuous S₀⟩
  have hret (n : ℕ) : ∃ r : Θₛ(S (n + 1)) →L[ℂ] Θₛ(S n),
      Function.LeftInverse r (sLocalThetaTransition (F := F) (hstep n)) ∧
      ∀ z, r (sLocalThetaPrincipalValue F ((h₀ n).trans (hstep n)) z) =
        sLocalThetaPrincipalValue F (h₀ n) (r z) := by
    by_cases hv : e n ∈ S n
    · -- The step adds no place, and the transition back is a left inverse.
      have hsub : S (n + 1) ⊆ S n := Finset.insert_subset hv subset_rfl
      refine ⟨⟨sLocalThetaTransition hsub, sLocalThetaTransition_continuous hsub⟩,
        fun z ↦ sLocalThetaToGlobal_injective (F := F) (S := S n) ?_,
        fun z ↦ LinearMap.congr_fun (sLocalThetaPrincipalValue_transition (h₀ (n + 1)) hsub hn) z⟩
      exact (LinearMap.congr_fun (sLocalThetaToGlobal_comp hsub) _).trans
        (LinearMap.congr_fun (sLocalThetaToGlobal_comp (hstep n)) z)
    · exact globalThetaPrincipalValue_isClosedEmbedding_retraction (h₀ n) hn (hstep n) (e n) hv rfl
  choose r hr hrP using hret
  have hexh (x : Θ𝔽) : ∃ n, ∃ z : Θₛ(S n), ι n z = x := by
    obtain ⟨T, y, rfl⟩ := sLocalThetaToGlobal_exhaustive x
    obtain ⟨d, hd⟩ := hcof T 0
    exact ⟨0 + d, sLocalThetaTransition hd y, LinearMap.congr_fun (sLocalThetaToGlobal_comp hd) y⟩
  -- Seminorms continuous on every stage are continuous on the global quotient.
  have hW : WithSeminorms (Subtype.val : {p : Seminorm ℂ Θ𝔽 //
      ∀ T, Continuous (p ∘ sLocalThetaToGlobal F T)} → Seminorm ℂ Θ𝔽) :=
    ⟨sLocalThetaToGlobal_finalTopology⟩
  have hfin (N : ℕ) (q : Seminorm ℂ Θ𝔽) (hq : ∀ d, Continuous (q ∘ ι (N + d))) : Continuous q := by
    refine hW.continuous_seminorm ⟨q, fun T ↦ ?_⟩
    obtain ⟨d, hd⟩ := hcof T N
    have h : q ∘ sLocalThetaToGlobal F T = (q ∘ ι (N + d)) ∘ sLocalThetaTransition hd :=
      funext fun y ↦ congrArg q (LinearMap.congr_fun (sLocalThetaToGlobal_comp hd) y).symm
    rw [h]
    exact (hq d).comp (sLocalThetaTransition_continuous hd)
  have hP (n : ℕ) (z : Θₛ(S n)) : P (ι n z) = ι n (Pn n z) :=
    (LinearMap.congr_fun (sLocalThetaPrincipalValue_toGlobal (h₀ n) hn) z).symm
  obtain ⟨pr, hmem, hfix, hprP⟩ := globalThetaPrincipalValue_isClosedEmbedding_projections
    (hX := fun n ↦ sLocalAdelicThetaSpace_polynormable) ι
    (fun n ↦ sLocalThetaToGlobal_injective) j
    (fun n z ↦ LinearMap.congr_fun (sLocalThetaToGlobal_comp (hstep n)) z) r hr P Pn hP hrP hexh
    hfin
  exact globalThetaPrincipalValue_isClosedEmbedding_ofProjections
    (hE := globalAdelicThetaSpace_polynormable) ι
    (fun n ↦ ⟨sLocalThetaToGlobal_isEmbedding, sLocalThetaToGlobal_isClosed_range⟩) P Pn
    (fun n ↦ sLocalThetaPrincipalValue_isClosedEmbedding (h₀ n) hn) hP pr hmem hfix hprP hexh
    fun q hq ↦ hfin 0 q fun d ↦ hq (0 + d)

end AdelicPrincipalValue


section DistributionOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "𝒟(" E ")" => 𝓓((⊤ : TopologicalSpace.Opens E), ℂ)

/-- Paper: Theorem 5.3.2.3, p. 245.
A distribution has order at most N if on each compact support it is bounded by the sup norms
of derivatives of orders zero through N. The same predicate applies to a tempered distribution
by restricting it to compactly supported test functions. -/
def DistributionOrderLE (T : 𝒟(E) → ℂ) (N : ℕ) : Prop :=
  ∀ K : Compacts E, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : 𝒟(E)), tsupport (f : E → ℂ) ⊆ (K : Set E) →
      ∀ B : ℝ, 0 ≤ B →
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ B) →
        ‖T f‖ ≤ C * B

/-- Paper: Theorem 5.3.2.1, p. 243.
Point evaluation on compactly supported tests has order at most zero. -/
theorem distributionOrderLE_eval (x : E) :
    DistributionOrderLE (fun f : 𝒟(E) ↦ f x) 0 := by
  intro K
  refine ⟨1, zero_le_one, fun f _ B _ h ↦ ?_⟩
  have hx := h 0 le_rfl x
  rw [norm_iteratedFDeriv_zero] at hx
  rw [one_mul]
  exact hx

/-- Paper: Theorem 5.3.2.1, p. 243.
The distributional support of a tempered distribution is contained in the origin. -/
abbrev TemperedSupportedAtOrigin (T : StrongDual ℂ 𝓢(E, ℂ)) : Prop :=
  Distribution.dsupport (⇑T) ⊆ {(0 : E)}

/-- Paper: Theorem 5.3.2.1, p. 243.
The Dirac distribution at zero is supported at zero. -/
theorem temperedSupportedAtOrigin_delta :
    TemperedSupportedAtOrigin (TemperedDistribution.delta (0 : E)) := by
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx {0}
    (TemperedDistribution.isVanishingOn_delta 0) isClosed_singleton

/-- Paper: Theorem 5.3.2.1, p. 243 and Definition D.1.8.2, p. 779.
A pointwise identification with additive Schwartz–Bruhat functions transports
the support of Appendix D to the distributional support of the classical test space. -/
theorem temperedSupport_eq_bruhatSupport_preimage
    (e : 𝓢(E, ℂ) ≃L[ℂ] SchwartzBruhat (Multiplicative E))
    (he : ∀ (f : 𝓢(E, ℂ)) (x : E), e f (Multiplicative.ofAdd x) = f x)
    (T : StrongDual ℂ 𝓢(E, ℂ)) :
    Distribution.dsupport (⇑T) = Multiplicative.ofAdd ⁻¹'
      schwartzBruhatDistributionSupport (T.comp e.symm.toContinuousLinearMap) := by
  let a : E ≃ₜ Multiplicative E := Homeomorph.refl E
  have hs (f : 𝓢(E, ℂ)) :
      tsupport (f : E → ℂ) = a ⁻¹' tsupport (e f : Multiplicative E → ℂ) := by
    have h : (e f : Multiplicative E → ℂ) ∘ a = (f : E → ℂ) := funext (he f)
    rw [← tsupport_comp_eq_preimage _ a, h]
  ext x
  change x ∈ Distribution.dsupport (⇑T) ↔ a x ∈ schwartzBruhatDistributionSupport _
  apply not_iff_not.mp
  refine (Distribution.notMem_dsupport_iff (f := (T : 𝓢(E, ℂ) → ℂ)) x).trans ?_
  simp only [schwartzBruhatDistributionSupport, Set.mem_compl_iff, not_not,
    schwartzBruhatVanishingLocus, Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨U, hU, ho, hx⟩
    refine ⟨a '' U, ⟨a.isOpenMap U ho, ?_⟩, ⟨x, hx, rfl⟩⟩
    intro g hg
    change T (e.symm g) = 0
    apply hU
    rw [hs, e.apply_symm_apply]
    exact (Set.preimage_mono hg).trans (by rw [Set.preimage_image_eq _ a.injective])
  · rintro ⟨U, ⟨ho, hU⟩, hx⟩
    refine ⟨a ⁻¹' U, ?_, ho.preimage a.continuous, hx⟩
    intro f hf
    have h := hU (e f) (fun y hy ↦ by
      obtain ⟨z, rfl⟩ := a.surjective y
      exact hf (by rwa [hs]))
    change T (e.symm (e f)) = 0 at h
    simpa only [e.symm_apply_apply] using h

end DistributionOrder

section RealOrigin

open scoped PowerSeries.WithPiTopology

local notation "𝒟ℝ" => 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℂ)

/-- Paper: Theorem 5.3.2.1, p. 243.
The kth derivative of the real Dirac distribution uses the negative transpose of
differentiation on real Schwartz functions. -/
def realDiracDerivative (k : ℕ) : StrongDual ℂ 𝓢(ℝ, ℂ) :=
  (-1 : ℂ)^k •
    (TemperedDistribution.delta (0 : ℝ)).comp ((SchwartzMap.derivCLM ℂ ℂ)^k)

/-- The kth Dirac derivative is `(-1)^k` times the kth derivative at zero. -/
private theorem realSchwartzFlatQuotient_strongDual_dirac (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    realDiracDerivative k f = (-1 : ℂ) ^ k * iteratedDeriv k (f : ℝ → ℂ) 0 := by
  have hd : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f)) = _
      rw [ih]
  change (-1 : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ ^ k) f) 0 = _
  rw [congrFun hd 0]

/-- The Dirac derivatives of `x ↦ xⁿ χ(x / ε)`, which agrees with `xⁿ` near zero. -/
private theorem realSchwartzFlatQuotient_strongDual_scaled_dirac (χ : ContDiffBump (0 : ℝ))
    (n : ℕ) (G ψ : 𝓢(ℝ, ℂ)) (hG : ∀ y, G y = (y : ℂ) ^ n * ((χ y : ℝ) : ℂ)) (ε : ℝ)
    (hε : 0 < ε) (hψ : ∀ x, ψ x = (ε : ℂ) ^ n * G (ε⁻¹ * x)) (j : ℕ) :
    realDiracDerivative j ψ = (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0 := by
  rw [realSchwartzFlatQuotient_strongDual_dirac, ← realSchwartzFlatQuotient_strongDual_pow]
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hball : Metric.ball (0 : ℝ) (ε * χ.rIn) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (mul_pos hε χ.rIn_pos)
  filter_upwards [hball] with x hx
  have hx' : ε⁻¹ * x ∈ Metric.closedBall (0 : ℝ) χ.rIn := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
      inv_mul_le_iff₀ hε]
    exact hx.le
  rw [hψ, hG, χ.one_of_mem_closedBall hx', Complex.ofReal_one, mul_one, Complex.ofReal_mul,
    mul_pow, ← mul_assoc, ← mul_pow, Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hε.ne'),
    one_pow, one_mul]

/-- Borel's lemma with uniform bounds: for every bound on the derivatives at zero, one bounded
set of Schwartz functions realizes every sequence of Dirac derivatives within that bound. -/
private theorem realSchwartzFlatQuotient_strongDual_borel (M : ℕ → ℝ) :
    ∃ S : Set 𝓢(ℝ, ℂ), Bornology.IsVonNBounded ℂ S ∧ ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ M n) →
      ∃ f ∈ S, ∀ n, realDiracDerivative n f = c n := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hχ : χ.rOut ≤ 1 := le_rfl
  choose G hG using realSchwartzFlatQuotient_strongDual_exists_bump χ
  have hGc (n : ℕ) : HasCompactSupport (G n : ℝ → ℂ) :=
    (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (realSchwartzFlatQuotient_strongDual_bump_tsupport χ hχ n (G n) (hG n))
  let C (n m : ℕ) : ℝ := SchwartzMap.seminorm ℂ 0 m (G n)
  have hC (n m : ℕ) : 0 ≤ C n m := apply_nonneg _ _
  let δ (n : ℕ) : ℝ := (1 / 2) ^ n / (|M n| + 1)
  have hδ (n : ℕ) : 0 < δ n := by positivity
  have hsC (n : ℕ) : 0 < ∑ m ∈ Finset.range n, C n m + 1 := by
    have : 0 ≤ ∑ m ∈ Finset.range n, C n m := Finset.sum_nonneg fun m _ ↦ hC n m
    linarith
  let ε (n : ℕ) : ℝ := min 1 (δ n / (∑ m ∈ Finset.range n, C n m + 1))
  have hε (n : ℕ) : 0 < ε n := lt_min one_pos (div_pos (hδ n) (hsC n))
  choose φ hφe using fun n ↦
    realSchwartzFlatQuotient_strongDual_exists_scaled (G n) (hGc n) n (ε n) (hε n).ne'
  have hφ (n m k : ℕ) (hmn : m < n) : SchwartzMap.seminorm ℂ k m (φ n) ≤ δ n := by
    have hS : C n m ≤ ∑ m ∈ Finset.range n, C n m + 1 := by
      have := Finset.single_le_sum (fun m _ ↦ hC n m) (Finset.mem_range.mpr hmn)
      linarith
    calc SchwartzMap.seminorm ℂ k m (φ n) ≤ ε n * C n m :=
          realSchwartzFlatQuotient_strongDual_scaled_seminorm χ hχ n m k hmn (G n) (φ n) (hG n)
            (ε n) (hε n) (min_le_left _ _) (hφe n)
      _ ≤ δ n / (∑ m ∈ Finset.range n, C n m + 1) * (∑ m ∈ Finset.range n, C n m + 1) := by
          gcongr
          · exact min_le_right _ _
      _ = δ n := div_mul_cancel₀ _ (hsC n).ne'
  let u (i : ℕ × ℕ) (n : ℕ) : ℝ :=
    (1 / 2) ^ n + if n ≤ i.2 then |M n| * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0
  have hu (i : ℕ × ℕ) : Summable (u i) := by
    refine (summable_geometric_of_lt_one (by norm_num) (by norm_num)).add ?_
    refine summable_of_ne_finset_zero (s := Finset.range (i.2 + 1)) fun n hn ↦ ?_
    rw [Finset.mem_range, not_lt] at hn
    simp [show ¬ n ≤ i.2 by omega]
  let b (c : ℕ → ℂ) (n : ℕ) : ℂ := c n * (-1 : ℂ) ^ n / (n.factorial : ℂ)
  have hb (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M n) (n : ℕ) : ‖b c n‖ ≤ |M n| := by
    have hf : (1 : ℝ) ≤ n.factorial := mod_cast n.factorial_pos
    simp only [b, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      Complex.norm_natCast]
    calc ‖c n‖ / (n.factorial : ℝ) ≤ ‖c n‖ / 1 := by gcongr
      _ = ‖c n‖ := div_one _
      _ ≤ |M n| := (hc n).trans (le_abs_self _)
  have hx (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M n) (i : ℕ × ℕ) (n : ℕ) :
      schwartzSeminormFamily ℂ ℝ ℂ i (b c n • φ n) ≤ u i n := by
    rw [SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul]
    have h0 : 0 ≤ SchwartzMap.seminorm ℂ i.1 i.2 (φ n) := apply_nonneg _ _
    have hg : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    by_cases hn : n ≤ i.2
    · simp only [u, hn, ↓reduceIte]
      have := mul_le_mul_of_nonneg_right (hb c hc n) h0
      linarith
    · simp only [u, hn, ↓reduceIte, add_zero]
      calc ‖b c n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) ≤ |M n| * δ n :=
            mul_le_mul (hb c hc n) (hφ n i.2 i.1 (by omega)) h0 (abs_nonneg _)
        _ = (1 / 2) ^ n * (|M n| / (|M n| + 1)) := by simp only [δ]; ring
        _ ≤ (1 / 2) ^ n * 1 := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ = (1 / 2) ^ n := mul_one _
  have hsum (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ M n) :=
    realSchwartzFlatQuotient_strongDual_summable (schwartz_withSeminorms ℂ ℝ ℂ)
      (fun n ↦ b c n • φ n) u hu (hx c hc)
  refine ⟨{f | ∃ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ M n) ∧ f = ∑' n, b c n • φ n}, ?_, fun c hc ↦ ?_⟩
  · rw [(schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded]
    intro i
    have h0 : 0 ≤ ∑' n, u i n := tsum_nonneg fun n ↦ by
      have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      have : 0 ≤ if n ≤ i.2 then |M n| * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0 := by
        split_ifs
        · exact mul_nonneg (abs_nonneg _) (apply_nonneg _ _)
        · exact le_rfl
      simp only [u]
      linarith
    refine ⟨∑' n, u i n + 1, by linarith, ?_⟩
    rintro f ⟨c, hc, rfl⟩
    exact ((hsum c hc).2 i).trans_lt (by linarith)
  · refine ⟨∑' n, b c n • φ n, ⟨c, hc, rfl⟩, fun j ↦ ?_⟩
    rw [ContinuousLinearMap.map_tsum _ (hsum c hc).1]
    have hd (n : ℕ) : realDiracDerivative j (φ n) =
        (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0 :=
      realSchwartzFlatQuotient_strongDual_scaled_dirac χ n (G n) (φ n) (hG n) (ε n) (hε n)
        (hφe n) j
    simp only [map_smul, smul_eq_mul, hd]
    rw [tsum_eq_single j fun n hn ↦ by simp [Ne.symm hn]]
    simp only [↓reduceIte]
    have hf : (j.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero j
    simp only [b]
    field_simp
    rw [← pow_mul, mul_comm j 2, pow_mul, neg_one_sq, one_pow, mul_one]

/-- Paper: Theorem 5.3.2.1, p. 243.
The first derivative of the real Dirac distribution evaluates to minus the derivative at zero. -/
theorem realDiracDerivative_one (f : 𝓢(ℝ, ℂ)) :
    realDiracDerivative 1 f = -deriv (f : ℝ → ℂ) 0 := by
  change (-1 : ℂ) ^ 1 • (((SchwartzMap.derivCLM ℂ ℂ) ^ 1) f) 0 = _
  rw [pow_one, pow_one, SchwartzMap.derivCLM_apply, neg_one_smul]

open scoped Manifold in
/-- A compactly supported test away from zero is a finite sum of tests on open sets
where the distribution vanishes. -/
private theorem realTemperedDistribution_zero_of_away (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {(0 : ℝ)}) (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (f : ℝ → ℂ)) (h0 : 0 ∉ tsupport (f : ℝ → ℂ)) : T f = 0 := by
  classical
  let K := tsupport (f : ℝ → ℂ)
  have hx (x : K) : x.val ∉ Distribution.dsupport (⇑T) := by
    intro h
    exact h0 ((Set.mem_singleton_iff.mp (hT h)) ▸ x.property)
  choose U hv ho hmem using fun x : K ↦ (Distribution.notMem_dsupport_iff x.val).mp (hx x)
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U ho fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hmem _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℝ)
    (isClosed_tsupport (f : ℝ → ℂ)) (fun i : s ↦ U i.val) (fun i ↦ ho i.val)
    (by simpa only [iUnion_subtype] using hs)
  let g (i : s) : 𝓢(ℝ, ℂ) := (hc.smul_left (f := (ρ i : ℝ → ℝ))).toSchwartzMap
    ((contMDiff_iff_contDiff.mp (ρ i).contMDiff).smul (f.smooth ⊤))
  have hz (i : s) : T (g i) = 0 :=
    hv i.val (g i) ((tsupport_smul_subset_left _ _).trans (hρ i))
  have hsum : f = ∑ i : s, g i := by
    ext x
    simp only [sum_apply]
    change f x = ∑ i : s, ρ i x • f x
    rw [← Finset.sum_smul]
    by_cases h : x ∈ K
    · rw [← finsum_eq_sum_of_fintype, ρ.sum_eq_one h, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport h, smul_zero]
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hz i

/-- Repeated mean-value bounds on a ball. Each vanishing derivative at the origin
contributes one power of its radius. -/
private theorem realTemperedDistribution_jet_bound (f : 𝓢(ℝ, ℂ)) (ε : ℝ) (hε : 0 ≤ ε)
    (j d : ℕ) (hjet : ∀ i < d, iteratedDeriv (j + i) (f : ℝ → ℂ) 0 = 0)
    (x : ℝ) (hx : |x| ≤ ε) :
    ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ ε ^ d * SchwartzMap.seminorm ℂ 0 (j + d) f := by
  induction d generalizing j x with
  | zero => simpa using SchwartzMap.le_seminorm' ℂ 0 j f x
  | succ d ih =>
    let K := Metric.closedBall (0 : ℝ) ε
    have hz : iteratedDeriv j (f : ℝ → ℂ) 0 = 0 := by simpa using hjet 0 (Nat.zero_lt_succ d)
    have hstep (y : ℝ) (hy : y ∈ K) :
        ‖deriv (iteratedDeriv j (f : ℝ → ℂ)) y‖ ≤
          ε ^ d * SchwartzMap.seminorm ℂ 0 (j + (d + 1)) f := by
      rw [← iteratedDeriv_succ]
      simpa only [Nat.succ_add, Nat.add_succ] using
        ih (j + 1) (fun i hi ↦ by
          simpa only [Nat.succ_add, Nat.add_succ] using hjet (i + 1) (Nat.succ_lt_succ hi)) y (by simpa [K, Real.dist_eq] using hy)
    have hd := (convex_closedBall (0 : ℝ) ε).norm_image_sub_le_of_norm_deriv_le
      (fun y _ ↦ ((f.smooth (j + 1 : ℕ)).differentiable_iteratedDeriv j (by exact_mod_cast Nat.lt_succ_self j)).differentiableAt)
      hstep (Metric.mem_closedBall_self hε) (show x ∈ K by simpa [K, Real.dist_eq] using hx)
    rw [hz, sub_zero, sub_zero, Real.norm_eq_abs] at hd
    calc _ ≤ _ := hd
         _ ≤ (ε ^ d * SchwartzMap.seminorm ℂ 0 (j + (d + 1)) f) * ε := by gcongr
         _ = _ := by rw [pow_succ]; ring


/-- Multiplication by a smooth cutoff equal to one near zero preserves the value
of a point-supported distribution, by density of compactly supported tests. -/
private theorem realTemperedDistribution_cutoff_eq (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {(0 : ℝ)}) (b : ℝ → ℂ)
    (hb : b.HasTemperateGrowth) (h1 : b =ᶠ[𝓝 0] 1) (f : 𝓢(ℝ, ℂ)) :
    T (SchwartzMap.smulLeftCLM ℂ b f) = T f := by
  apply closure_minimal (s := {g : 𝓢(ℝ, ℂ) | HasCompactSupport (g : ℝ → ℂ)})
    (t := {g | T (SchwartzMap.smulLeftCLM ℂ b g) = T g}) _
    (isClosed_eq (T.continuous.comp (SchwartzMap.smulLeftCLM ℂ b).continuous) T.continuous)
    (SchwartzMap.dense_hasCompactSupport f)
  intro g hg
  change T (SchwartzMap.smulLeftCLM ℂ b g) = T g
  rw [← sub_eq_zero, ← map_sub]
  apply realTemperedDistribution_zero_of_away T hT
  · change HasCompactSupport (⇑(SchwartzMap.smulLeftCLM ℂ b g) - (g : ℝ → ℂ))
    rw [SchwartzMap.smulLeftCLM_apply hb]
    exact (HasCompactSupport.smul_left (f := b) (show HasCompactSupport (g : ℝ → ℂ) from hg)).sub hg
  · apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [h1] with x hx
    simp [SchwartzMap.smulLeftCLM_apply_apply hb, show b x = 1 from hx]

/-- The first `N` derivatives of a shrinking cutoff times a function with zero
`N`-jet are uniformly of order at most its radius. -/
private theorem realTemperedDistribution_cutoff_bound (b f : 𝓢(ℝ, ℂ))
    (hb : tsupport (b : ℝ → ℂ) ⊆ Metric.closedBall 0 1)
    (N m : ℕ) (hm : m ≤ N) (hjet : ∀ j ≤ N, iteratedDeriv j (f : ℝ → ℂ) 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k : ℕ,
      SchwartzMap.seminorm ℂ k m (SchwartzMap.smulLeftCLM ℂ (fun x ↦ b (ε⁻¹ * x)) f) ≤ ε * C := by
  let A := SchwartzMap.seminorm ℂ 0 (N + 1) f
  let B (i : ℕ) := SchwartzMap.seminorm ℂ 0 i b
  have hA : 0 ≤ A := apply_nonneg _ _
  have hB (i : ℕ) : 0 ≤ B i := apply_nonneg _ _
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B i * A, by positivity, ?_⟩
  intro ε hε hε1 k
  let bε := fun x : ℝ ↦ b (ε⁻¹ * x)
  have htemp : bε.HasTemperateGrowth := by dsimp [bε]; fun_prop
  refine SchwartzMap.seminorm_le_bound' ℂ k m _ (by positivity) fun x ↦ ?_
  rw [SchwartzMap.smulLeftCLM_apply htemp]
  change |x| ^ k * ‖iteratedDeriv m (fun y ↦ b (ε⁻¹ * y) * f y) x‖ ≤ _
  by_cases hx : |x| ≤ ε
  · have hb' : ContDiff ℝ m bε := (b.smooth m).comp (contDiff_const.mul contDiff_id)
    rw [iteratedDeriv_fun_mul hb'.contDiffAt (f.smooth m).contDiffAt]
    have hk := pow_le_one₀ (abs_nonneg x) (hx.trans hε1) (n := k)
    refine (mul_le_of_le_one_left (norm_nonneg _) hk).trans ((norm_sum_le _ _).trans ?_)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    let j := m - i
    let d := N + 1 - j
    have hjd : j + d = N + 1 := by dsimp [j, d]; omega
    have hdi : i < d := by dsimp [d, j]; omega
    have hf : ‖iteratedDeriv j (f : ℝ → ℂ) x‖ ≤ ε ^ d * A := by
      simpa only [hjd, A] using realTemperedDistribution_jet_bound f ε hε.le j d
        (fun l hl ↦ hjet (j + l) (by omega)) x hx
    have hbnd : ‖iteratedDeriv i (b : ℝ → ℂ) (ε⁻¹ * x)‖ ≤ B i := by
      simpa [B] using SchwartzMap.le_seminorm' ℂ 0 i b (ε⁻¹ * x)
    have hp : (ε⁻¹) ^ i * ε ^ d ≤ ε := by
      rw [← pow_sub_mul_pow ε hdi.le, mul_left_comm, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow,
        mul_one]
      simpa using pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ d - i by omega)
    rw [iteratedDeriv_comp_const_smul (b.smooth i), norm_mul, norm_mul, norm_smul,
      norm_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), Complex.norm_natCast]
    calc _ ≤ ((m.choose i : ℝ) * ((ε⁻¹) ^ i * B i)) * (ε ^ d * A) := by gcongr
         _ = ((ε⁻¹) ^ i * ε ^ d) * ((m.choose i : ℝ) * B i * A) := by ring
         _ ≤ _ := by gcongr
  · have hout : ε⁻¹ * x ∉ tsupport (b : ℝ → ℂ) := by
      intro h
      have h' := hb h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
        inv_mul_le_iff₀ hε, mul_one] at h'
      exact hx h'
    have heq : (fun y ↦ b (ε⁻¹ * y) * f y) =ᶠ[𝓝 x] 0 := by
      have hcont : ContinuousAt (fun y : ℝ ↦ ε⁻¹ * y) x := by fun_prop
      filter_upwards [hcont (notMem_tsupport_iff_eventuallyEq.mp hout)] with y hy
      simp [show b (ε⁻¹ * y) = 0 from hy]
    rw [heq.iteratedDeriv_eq, iteratedDeriv_const_zero, norm_zero, mul_zero]
    positivity


/-- Continuity bounds a tempered distribution by finitely many Schwartz seminorms.
Localization and the shrinking-cutoff bound therefore make it vanish on a finite jet kernel. -/
private theorem realTemperedDistribution_finite_jet (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {(0 : ℝ)}) :
    ∃ N : ℕ, ∀ f : 𝓢(ℝ, ℂ), (∀ j ≤ N, iteratedDeriv j (f : ℝ → ℂ) 0 = 0) → T f = 0 := by
  classical
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) T.continuous.norm
  let N := s.sup Prod.snd
  refine ⟨N, fun f hf ↦ ?_⟩
  let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let b : 𝓢(ℝ, ℂ) := (χ.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp χ.contDiff)
  have hb : tsupport (b : ℝ → ℂ) ⊆ Metric.closedBall 0 1 :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans χ.tsupport_eq.subset
  have h1 : (b : ℝ → ℂ) =ᶠ[𝓝 0] 1 := by
    filter_upwards [χ.eventuallyEq_one] with x hx
    change ((χ x : ℝ) : ℂ) = 1
    simp [show χ x = 1 from hx]
  choose D hD hbound using fun i : s ↦ realTemperedDistribution_cutoff_bound b f hb N i.val.2
    (Finset.le_sup (f := Prod.snd) i.property) hf
  let M := ∑ i : s, D i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ hD i
  have hsmall (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : ‖T f‖ ≤ (C : ℝ) * (ε * M) := by
    let g := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ b (ε⁻¹ * x)) f
    have htemp : (fun x : ℝ ↦ b (ε⁻¹ * x)).HasTemperateGrowth := by fun_prop
    have hc : Tendsto (fun x : ℝ ↦ ε⁻¹ * x) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using (continuous_const_mul ε⁻¹).tendsto (0 : ℝ)
    have heq : T g = T f := realTemperedDistribution_cutoff_eq T hT _ htemp (hc h1) f
    rw [← heq]
    refine (hC g).trans ?_
    change (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) g ≤ _
    gcongr
    apply Seminorm.finset_sup_apply_le (mul_nonneg hε.le hM)
    intro i hi
    exact (hbound ⟨i, hi⟩ ε hε hε1 i.1).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ ↦ hD j) (Finset.mem_univ (⟨i, hi⟩ : s))) hε.le)
  apply norm_le_zero_iff.mp
  have ht : Tendsto (fun ε : ℝ ↦ (C : ℝ) * (ε * M)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_mul, mul_zero] using (hid.mul_const M).const_mul (C : ℝ)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with ε hε hε1
  exact hsmall ε hε hε1.le

/-- Paper: Theorem 5.3.2.1, p. 243.
Every real tempered distribution supported at zero is a finite linear combination of
derivatives of the Dirac distribution at zero. -/
theorem realTemperedDistribution_eq_sum_diracDerivative (T : StrongDual ℂ 𝓢(ℝ, ℂ))
    (hT : TemperedSupportedAtOrigin T) :
    ∃ (N : ℕ) (c : Fin (N + 1) → ℂ),
      T = ∑ k : Fin (N + 1), c k • realDiracDerivative k.val := by
  obtain ⟨N, hN⟩ := realTemperedDistribution_finite_jet T hT
  let L (k : Fin (N + 1)) := (realDiracDerivative k.val).toLinearMap
  have hker : (⨅ k, LinearMap.ker (L k)) ≤ LinearMap.ker T.toLinearMap := by
    intro f hf
    apply hN f
    intro j hj
    have hz := (Submodule.mem_iInf _).mp hf (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (N + 1))
    change realDiracDerivative j f = 0 at hz
    rw [realSchwartzFlatQuotient_strongDual_dirac, mul_eq_zero] at hz
    exact hz.resolve_left (pow_ne_zero _ (by norm_num))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨N, c, ?_⟩
  ext f
  simpa only [sum_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_apply, L,
    ContinuousLinearMap.coe_coe] using (LinearMap.congr_fun hc f).symm

/-- Paper: Theorem 5.3.2.1(1), p. 243.
The flat real Schwartz subspace is the intersection of the kernels of all Dirac derivatives. -/
def realSchwartzFlatAtOrigin : Submodule ℂ 𝓢(ℝ, ℂ) :=
  ⨅ k : ℕ, LinearMap.ker (realDiracDerivative k).toLinearMap

/-- Paper: Theorem 5.3.2.1(1), p. 243.
A real Schwartz function lies in the flat subspace exactly when every derivative at zero
vanishes. -/
theorem mem_realSchwartzFlatAtOrigin_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ realSchwartzFlatAtOrigin ↔
      ∀ k : ℕ, iteratedDeriv k (f : ℝ → ℂ) 0 = 0 := by
  have hd (k : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) f)) = _
      rw [ih]
  rw [realSchwartzFlatAtOrigin, Submodule.mem_iInf]
  apply forall_congr'
  intro k
  change (-1 : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ ^ k) f) 0 = 0 ↔ _
  rw [congrFun (hd k) 0, mul_eq_zero]
  simp

/-- Paper: Theorem 5.3.2.1(1), p. 243.
The flat real Schwartz subspace is closed. -/
theorem realSchwartzFlatAtOrigin_isClosed :
    IsClosed (realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)) := by
  rw [realSchwartzFlatAtOrigin, Submodule.coe_iInf]
  exact isClosed_iInter fun k ↦ (realDiracDerivative k).isClosed_ker

/-- Every bounded set of the flat quotient is the image of a bounded set of Schwartz
functions. -/
private theorem realSchwartzFlatQuotient_strongDual_lift
    (B : Set (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ S : Set 𝓢(ℝ, ℂ), Bornology.IsVonNBounded ℂ S ∧ B ⊆ realSchwartzFlatAtOrigin.mkQ '' S := by
  have hle (n : ℕ) : realSchwartzFlatAtOrigin ≤ (realDiracDerivative n).ker := fun f hf ↦
    (Submodule.mem_iInf _).mp hf n
  have hM (n : ℕ) : ∃ M : ℝ, ∀ y ∈ B,
      ‖realSchwartzFlatAtOrigin.liftQL (realDiracDerivative n) (hle n) y‖ ≤ M := by
    have := hB.image (realSchwartzFlatAtOrigin.liftQL (realDiracDerivative n) (hle n))
    rw [NormedSpace.isVonNBounded_iff] at this
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp this
    exact ⟨M, fun y hy ↦ hM _ ⟨y, hy, rfl⟩⟩
  choose M hM using hM
  obtain ⟨S, hS, hlift⟩ := realSchwartzFlatQuotient_strongDual_borel M
  refine ⟨S, hS, fun y hy ↦ ?_⟩
  obtain ⟨g, rfl⟩ := realSchwartzFlatAtOrigin.mkQ_surjective y
  obtain ⟨f, hf, hfd⟩ := hlift (fun n ↦ realDiracDerivative n g) (fun n ↦ hM n _ hy)
  refine ⟨f, hf, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
  rw [LinearMap.mem_ker, map_sub]
  change realDiracDerivative n f - realDiracDerivative n g = 0
  rw [hfd n, sub_self]

/-- A Borel series `∑ bₙ φₙ` whose terms past `m` are dominated by a summable sequence converges
in the Schwartz space. Its Dirac derivatives are those of the coefficients, and its seminorms of
order at most `m` are bounded by the first `m + 1` terms plus the dominating sum. -/
private theorem realSchwartzTaylor_equiv_series (m : ℕ) (φ : ℕ → 𝓢(ℝ, ℂ)) (b : ℕ → ℂ)
    (w : ℕ → ℝ) (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n)
    (hφ : ∀ n k j, j < n → m < n → ‖b n‖ * SchwartzMap.seminorm ℂ k j (φ n) ≤ w n)
    (hd : ∀ n j, realDiracDerivative j (φ n) =
      (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ j, realDiracDerivative j f = b j * (-1 : ℂ) ^ j * (j.factorial : ℂ)) ∧
      ∀ k j, j ≤ m → SchwartzMap.seminorm ℂ k j f ≤
        ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ k j (φ n) + ∑' n, w n := by
  let v (i : ℕ × ℕ) (n : ℕ) : ℝ :=
    if n ≤ max i.2 m then ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0
  have hv (i : ℕ × ℕ) : Summable (v i) := by
    refine summable_of_ne_finset_zero (s := Finset.range (max i.2 m + 1)) fun n hn ↦ ?_
    rw [Finset.mem_range, not_lt] at hn
    simp only [v, show ¬ n ≤ max i.2 m by omega, ↓reduceIte]
  let u (i : ℕ × ℕ) (n : ℕ) : ℝ := w n + v i n
  have hx (i : ℕ × ℕ) (n : ℕ) : schwartzSeminormFamily ℂ ℝ ℂ i (b n • φ n) ≤ u i n := by
    rw [SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul]
    by_cases hn : n ≤ max i.2 m
    · simp only [u, v, hn, ↓reduceIte]
      linarith [hw0 n]
    · simp only [u, v, hn, ↓reduceIte, add_zero]
      exact hφ n i.1 i.2 (by omega) (by omega)
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  obtain ⟨hsum, hbound⟩ := realSchwartzFlatQuotient_strongDual_summable
    (schwartz_withSeminorms ℂ ℝ ℂ) (fun n ↦ b n • φ n) u (fun i ↦ hw.add (hv i)) hx
  refine ⟨∑' n, b n • φ n, fun j ↦ ?_, fun k j hj ↦ ?_⟩
  · rw [ContinuousLinearMap.map_tsum _ hsum]
    simp only [map_smul, smul_eq_mul, hd]
    rw [tsum_eq_single j fun n hn ↦ by simp [Ne.symm hn]]
    simp only [↓reduceIte]
    ring
  · have h := hbound (k, j)
    rw [SchwartzMap.schwartzSeminormFamily_apply] at h
    refine h.trans (le_of_eq ?_)
    rw [Summable.tsum_add hw (hv (k, j)), add_comm]
    congr 1
    rw [tsum_eq_sum (s := Finset.range (m + 1)) fun n hn ↦ ?_]
    · refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [Finset.mem_range] at hn
      simp only [v, show n ≤ max j m by omega, ↓reduceIte]
    · rw [Finset.mem_range, not_lt] at hn
      simp only [v, show ¬ n ≤ max j m by omega, ↓reduceIte]

/-- A small Borel lemma: for finitely many Schwartz seminorms and `r > 0`, every sequence whose
first `N` terms are below `δ` is the sequence of Taylor coefficients of a Schwartz function whose
seminorms in the family are below `r`. -/
private theorem realSchwartzTaylor_equiv_small (s : Finset (ℕ × ℕ)) (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∃ δ > 0, ∀ b : ℕ → ℂ, (∀ n ≤ N, ‖b n‖ < δ) → ∃ f : 𝓢(ℝ, ℂ),
      (∀ n, realDiracDerivative n f = b n * (-1 : ℂ) ^ n * (n.factorial : ℂ)) ∧
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f < r := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hχ : χ.rOut ≤ 1 := le_rfl
  choose G hG using realSchwartzFlatQuotient_strongDual_exists_bump χ
  have hGc (n : ℕ) : HasCompactSupport (G n : ℝ → ℂ) :=
    (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (realSchwartzFlatQuotient_strongDual_bump_tsupport χ hχ n (G n) (hG n))
  let m := s.sup Prod.snd
  let K : ℝ := ∑ i ∈ s, ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ i.1 i.2 (G n)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun n _ ↦ apply_nonneg _ _
  refine ⟨m, r / (2 * (K + 1)), by positivity, fun b hb ↦ ?_⟩
  let C (n j : ℕ) : ℝ := SchwartzMap.seminorm ℂ 0 j (G n)
  have hC (n j : ℕ) : 0 ≤ C n j := apply_nonneg _ _
  let w (n : ℕ) : ℝ := r / 4 * (1 / 2) ^ n
  have hw0 (n : ℕ) : 0 ≤ w n := by positivity
  have hwsum : HasSum w (r / 2) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (r / 4)
    convert this using 1
    norm_num
    ring
  have hsC (n : ℕ) : 0 < ∑ j ∈ Finset.range n, C n j + 1 := by
    have : 0 ≤ ∑ j ∈ Finset.range n, C n j := Finset.sum_nonneg fun j _ ↦ hC n j
    linarith
  let ε (n : ℕ) : ℝ := min 1 (w n / (‖b n‖ + 1) / (∑ j ∈ Finset.range n, C n j + 1))
  have hε (n : ℕ) : 0 < ε n := lt_min one_pos (by have := hsC n; positivity)
  choose ψ hψ using fun n ↦
    realSchwartzFlatQuotient_strongDual_exists_scaled (G n) (hGc n) n (ε n) (hε n).ne'
  let φ (n : ℕ) : 𝓢(ℝ, ℂ) := if n ≤ m then G n else ψ n
  have hd (n j : ℕ) : realDiracDerivative j (φ n) =
      (-1 : ℂ) ^ j * if j = n then (n.factorial : ℂ) else 0 := by
    by_cases hn : n ≤ m
    · simp only [φ, hn, ↓reduceIte]
      exact realSchwartzFlatQuotient_strongDual_scaled_dirac χ n (G n) (G n) (hG n) 1 one_pos
        (fun x ↦ by simp) j
    · simp only [φ, hn, ↓reduceIte]
      exact realSchwartzFlatQuotient_strongDual_scaled_dirac χ n (G n) (ψ n) (hG n) (ε n) (hε n)
        (hψ n) j
  have hφ (n k j : ℕ) (hjn : j < n) (hmn : m < n) :
      ‖b n‖ * SchwartzMap.seminorm ℂ k j (φ n) ≤ w n := by
    simp only [φ, show ¬ n ≤ m by omega, ↓reduceIte]
    have hS : C n j ≤ ∑ j ∈ Finset.range n, C n j + 1 := by
      have := Finset.single_le_sum (fun j _ ↦ hC n j) (Finset.mem_range.mpr hjn)
      linarith
    have h1 : SchwartzMap.seminorm ℂ k j (ψ n) ≤ w n / (‖b n‖ + 1) :=
      calc SchwartzMap.seminorm ℂ k j (ψ n) ≤ ε n * C n j :=
            realSchwartzFlatQuotient_strongDual_scaled_seminorm χ hχ n j k hjn (G n) (ψ n) (hG n)
              (ε n) (hε n) (min_le_left _ _) (hψ n)
        _ ≤ w n / (‖b n‖ + 1) / (∑ j ∈ Finset.range n, C n j + 1) *
              (∑ j ∈ Finset.range n, C n j + 1) := by
            gcongr
            · exact min_le_right _ _
        _ = w n / (‖b n‖ + 1) := div_mul_cancel₀ _ (hsC n).ne'
    calc ‖b n‖ * SchwartzMap.seminorm ℂ k j (ψ n) ≤ ‖b n‖ * (w n / (‖b n‖ + 1)) := by gcongr
      _ = w n * (‖b n‖ / (‖b n‖ + 1)) := by ring
      _ ≤ w n * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = w n := mul_one _
  obtain ⟨f, hfd, hfb⟩ :=
    realSchwartzTaylor_equiv_series m φ b w hwsum.summable hw0 hφ hd
  refine ⟨f, hfd, Seminorm.finset_sup_apply_lt hr fun i hi ↦ ?_⟩
  have him : i.2 ≤ m := Finset.le_sup (f := Prod.snd) hi
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  have hlow : ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) ≤
      r / (2 * (K + 1)) * K := by
    calc ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n)
        ≤ ∑ n ∈ Finset.range (m + 1), r / (2 * (K + 1)) * SchwartzMap.seminorm ℂ i.1 i.2 (G n) := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          rw [Finset.mem_range] at hn
          simp only [φ, show n ≤ m by omega, ↓reduceIte]
          exact mul_le_mul_of_nonneg_right (hb n (by omega)).le (apply_nonneg _ _)
      _ = r / (2 * (K + 1)) *
            ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ i.1 i.2 (G n) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ r / (2 * (K + 1)) * K := by
          gcongr
          exact Finset.single_le_sum (f := fun i : ℕ × ℕ ↦
            ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ i.1 i.2 (G n))
            (fun i _ ↦ Finset.sum_nonneg fun n _ ↦ apply_nonneg _ _) hi
  have hrK : r / (2 * (K + 1)) * K < r / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc SchwartzMap.seminorm ℂ i.1 i.2 f
      ≤ ∑ n ∈ Finset.range (m + 1), ‖b n‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) + ∑' n, w n :=
        hfb i.1 i.2 him
    _ < r / 2 + r / 2 := by rw [hwsum.tsum_eq]; linarith
    _ = r := add_halves r

/-- Paper: Theorem 5.3.2.1(2), p. 243.
The real Schwartz quotient by flat functions is identified with formal power series by the
Taylor map. The topology of coefficientwise convergence is generated by (5.3.2.3).
Deviation: The Taylor formula is applied to test functions, as required by the quotient domain. -/
theorem realSchwartzTaylor_equiv :
    ∃ e : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃L[ℂ] PowerSeries ℂ,
      ∀ (f : 𝓢(ℝ, ℂ)) (k : ℕ),
        PowerSeries.coeff k (e (realSchwartzFlatAtOrigin.mkQ f)) =
          iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ) := by
  let a (k : ℕ) : StrongDual ℂ 𝓢(ℝ, ℂ) :=
    ((-1 : ℂ) ^ k / (k.factorial : ℂ)) • realDiracDerivative k
  have hfact (k : ℕ) : (k.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero k
  have hsq (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have ha (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
      a k f = iteratedDeriv k (f : ℝ → ℂ) 0 / (k.factorial : ℂ) := by
    simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      realSchwartzFlatQuotient_strongDual_dirac]
    rw [div_mul_eq_mul_div, div_left_inj₀ (hfact k), ← mul_assoc, hsq, one_mul]
  have hinv (k : ℕ) (z : ℂ) :
      (-1 : ℂ) ^ k / (k.factorial : ℂ) * (z * (-1 : ℂ) ^ k * (k.factorial : ℂ)) = z := by
    rw [div_mul_eq_mul_div, div_eq_iff (hfact k)]
    linear_combination (z * (k.factorial : ℂ)) * hsq k
  let T : 𝓢(ℝ, ℂ) →ₗ[ℂ] PowerSeries ℂ :=
    { toFun := fun f ↦ PowerSeries.mk fun k ↦ a k f
      map_add' := fun f g ↦ by ext k; simp
      map_smul' := fun c f ↦ by ext k; simp }
  have hT (f : 𝓢(ℝ, ℂ)) (k : ℕ) : PowerSeries.coeff k (T f) = a k f := by
    change PowerSeries.coeff k (PowerSeries.mk fun k ↦ a k f) = _
    exact PowerSeries.coeff_mk _ _
  have hTc : Continuous T := by
    refine continuous_iff_continuousAt.mpr fun f ↦ ?_
    rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    simp only [hT]
    exact (a d).continuous.tendsto f
  let TL : 𝓢(ℝ, ℂ) →L[ℂ] PowerSeries ℂ := ⟨T, hTc⟩
  have hTL (f : 𝓢(ℝ, ℂ)) (k : ℕ) : PowerSeries.coeff k (TL f) = a k f := hT f k
  have hmem (f : 𝓢(ℝ, ℂ)) : f ∈ realSchwartzFlatAtOrigin ↔ TL f = 0 := by
    rw [realSchwartzFlatAtOrigin, Submodule.mem_iInf, PowerSeries.ext_iff]
    refine forall_congr' fun k ↦ ?_
    rw [LinearMap.mem_ker, hTL, map_zero]
    simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
    have : (-1 : ℂ) ^ k / (k.factorial : ℂ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num)) (hfact k)
    rw [mul_eq_zero, or_iff_right this]
  have hle : realSchwartzFlatAtOrigin ≤ TL.ker := fun f hf ↦ (hmem f).mp hf
  let E := realSchwartzFlatAtOrigin.liftQL TL hle
  have hE (f : 𝓢(ℝ, ℂ)) : E (realSchwartzFlatAtOrigin.mkQ f) = TL f := rfl
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).mpr fun y hy ↦ ?_
    obtain ⟨f, rfl⟩ := realSchwartzFlatAtOrigin.mkQ_surjective y
    rw [hE] at hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((hmem f).mpr hy)
  have hsurj : Function.Surjective E := by
    intro p
    let c (n : ℕ) : ℂ := PowerSeries.coeff n p * (-1 : ℂ) ^ n * (n.factorial : ℂ)
    obtain ⟨S, -, hS⟩ := realSchwartzFlatQuotient_strongDual_borel (fun n ↦ ‖c n‖)
    obtain ⟨f, -, hf⟩ := hS c fun n ↦ le_rfl
    refine ⟨realSchwartzFlatAtOrigin.mkQ f, ?_⟩
    rw [hE]
    ext k
    rw [hTL]
    simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hf, c]
    exact hinv k _
  let e : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃ₗ[ℂ] PowerSeries ℂ :=
    LinearEquiv.ofBijective (E : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) →ₗ[ℂ] PowerSeries ℂ)
      ⟨hinj, hsurj⟩
  have he (y : 𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) : e y = E y := rfl
  have hsymm : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro V hV
    have hq : realSchwartzFlatAtOrigin.mkQ ⁻¹' V ∈ 𝓝 (0 : 𝓢(ℝ, ℂ)) :=
      realSchwartzFlatAtOrigin.mkQL.continuous.continuousAt.preimage_mem_nhds
        (by simpa using hV)
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).hasBasis_zero_ball.mem_iff.mp hq
    obtain ⟨N, δ, hδ, hsmall⟩ := realSchwartzTaylor_equiv_small s r hr
    have hW : ∀ᶠ p in 𝓝 (0 : PowerSeries ℂ),
        ∀ n ∈ Finset.range (N + 1), ‖PowerSeries.coeff n p‖ < δ := by
      rw [Filter.eventually_all_finset]
      intro n _
      have h := (PowerSeries.WithPiTopology.continuous_coeff ℂ n).tendsto 0
      rw [map_zero] at h
      exact (h.eventually (Metric.ball_mem_nhds 0 hδ)).mono fun p hp ↦ by simpa using hp
    rw [Filter.mem_map]
    filter_upwards [hW] with p hp
    obtain ⟨f, hfd, hf⟩ := hsmall (fun n ↦ PowerSeries.coeff n p)
      fun n hn ↦ hp n (Finset.mem_range.mpr (by omega))
    have hp' : e.symm p = realSchwartzFlatAtOrigin.mkQ f := by
      rw [LinearEquiv.symm_apply_eq, he, hE]
      ext k
      rw [hTL]
      simp only [a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hfd]
      exact (hinv k _).symm
    rw [Set.mem_preimage, hp']
    exact hsub ((Seminorm.mem_ball_zero _).mpr hf)
  let eL : (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ≃L[ℂ] PowerSeries ℂ :=
    { e with
      continuous_toFun := E.continuous
      continuous_invFun := hsymm }
  refine ⟨eL, fun f k ↦ ?_⟩
  change PowerSeries.coeff k (TL f) = _
  rw [hTL, ha]

/-- Paper: Remark 5.3.2.2, p. 243.
Pullback from the strong dual of the real flat quotient embeds it in the strong dual of the
real Schwartz space with image the annihilator of the flat subspace. -/
theorem realSchwartzFlatQuotient_strongDual :
    let pull := fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
      T.comp realSchwartzFlatAtOrigin.mkQL
    IsEmbedding pull ∧ Set.range pull =
      {T : StrongDual ℂ 𝓢(ℝ, ℂ) | ∀ f ∈ realSchwartzFlatAtOrigin, T f = 0} := by
  intro pull
  refine ⟨realSchwartzFlatQuotient_strongDual_isEmbedding _
    realSchwartzFlatQuotient_strongDual_lift, ?_⟩
  change Set.range (fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
    T.comp realSchwartzFlatAtOrigin.mkQL) = _
  rw [range_transpose_mkQL]
  ext T
  simp [Set.mem_iInter]

/-- A continuous functional on formal power series vanishes on every series whose coefficients
up to some fixed order are zero. -/
private theorem realDiracDerivatives_polynomialEquiv_finite (L : PowerSeries ℂ →L[ℂ] ℂ) :
    ∃ N : ℕ, ∀ s : PowerSeries ℂ, (∀ n ≤ N, PowerSeries.coeff n s = 0) → L s = 0 := by
  by_contra h
  push Not at h
  choose s hs0 hs using h
  let t (N : ℕ) : PowerSeries ℂ := (L (s N))⁻¹ • s N
  have ht : Tendsto t atTop (𝓝 0) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    rw [map_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop d] with N hN
    simp [t, hs0 N d hN]
  have h1 := (L.continuous.tendsto 0).comp ht
  rw [map_zero] at h1
  have h2 : ⇑L ∘ t = fun _ ↦ 1 := by
    funext N
    simp [t, inv_mul_cancel₀ (hs N)]
  rw [h2] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

-- TODO(paper-gap): The coefficient seminorms in (5.3.2.2) give the coefficientwise
-- topology on the whole polynomial space and do not give its finest locally convex topology.

/-- Paper: Theorem 5.3.2.1(1), p. 243.
Polynomials with the finest locally convex topology identify with the strong dual of the
real Schwartz quotient by flat functions through the factorial-normalized Dirac derivatives.
The least order bound of the distribution is the polynomial's natural degree.
Deviation: Uses the finest locally convex topology and omits the false equivalence in (5.3.2.2). -/
theorem realDiracDerivatives_polynomialEquiv :
    ∃ e : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ]
        StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin),
      (∀ k : ℕ, ∀ f : 𝓢(ℝ, ℂ),
        e (Polynomial.monomial k 1) (realSchwartzFlatAtOrigin.mkQ f) =
          realDiracDerivative k f / (k.factorial : ℂ)) ∧
      ∀ (p : Polynomial ℂ) (N : ℕ),
        DistributionOrderLE
          (fun f : 𝒟ℝ ↦ e p (realSchwartzFlatAtOrigin.mkQ
            (f.hasCompactSupport.toSchwartzMap f.contDiff))) N ↔ p.natDegree ≤ N := by
  obtain ⟨τ, hτ⟩ := realSchwartzTaylor_equiv
  have hfact (k : ℕ) : (k.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero k
  let cf (k : ℕ) : PowerSeries ℂ →L[ℂ] ℂ :=
    ⟨PowerSeries.coeff k, PowerSeries.WithPiTopology.continuous_coeff ℂ k⟩
  let c (k : ℕ) : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    ((-1 : ℂ) ^ k) • (cf k).comp τ.toContinuousLinearMap
  have hc (k : ℕ) (y : 𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :
      c k y = (-1 : ℂ) ^ k * PowerSeries.coeff k (τ y) := rfl
  have hcf (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
      c k (realSchwartzFlatAtOrigin.mkQ f) = realDiracDerivative k f / (k.factorial : ℂ) := by
    rw [hc, hτ, realSchwartzFlatQuotient_strongDual_dirac]
    ring
  let Φ : Polynomial ℂ →ₗ[ℂ] StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    Polynomial.lsum fun k ↦ LinearMap.smulRight LinearMap.id (c k)
  have hΦ (p : Polynomial ℂ) (y : 𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :
      Φ p y = ∑ k ∈ p.support, p.coeff k * c k y := by
    simp [Φ, Polynomial.lsum_apply, Polynomial.sum_def, sum_apply]
  have hΦm (k : ℕ) (a : ℂ) : Φ (Polynomial.monomial k a) = a • c k := by
    simp [Φ, Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).mpr fun p hp ↦ ?_
    ext n
    have h := congrArg (fun T : StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) ↦
      T (τ.symm (PowerSeries.X ^ n))) hp
    simp only [hΦ, hc, ContinuousLinearEquiv.apply_symm_apply, PowerSeries.coeff_X_pow,
      zero_apply] at h
    rw [Finset.sum_eq_single n (fun k _ hk ↦ by simp [hk])
      (fun hn ↦ by simp [Polynomial.notMem_support_iff.mp hn])] at h
    simpa using h
  have hsurj : Function.Surjective Φ := by
    intro T
    let L : PowerSeries ℂ →L[ℂ] ℂ := T.comp τ.symm.toContinuousLinearMap
    obtain ⟨N, hN⟩ := realDiracDerivatives_polynomialEquiv_finite L
    refine ⟨∑ n ∈ Finset.range (N + 1),
      Polynomial.monomial n ((-1 : ℂ) ^ n * L (PowerSeries.X ^ n)), ?_⟩
    ext y
    rw [map_sum]
    simp only [hΦm, sum_apply, smul_apply, hc,
      smul_eq_mul]
    have hy : T y = L (τ y) := by simp [L]
    have hs : L (τ y - ∑ n ∈ Finset.range (N + 1),
        PowerSeries.coeff n (τ y) • PowerSeries.X ^ n) = 0 := by
      apply hN
      intro m hm
      rw [map_sub, map_sum]
      simp [PowerSeries.coeff_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_of_le hm]
    rw [map_sub, map_sum, sub_eq_zero] at hs
    rw [hy, hs]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [map_smul, smul_eq_mul]
    have : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (L (PowerSeries.X ^ n) * PowerSeries.coeff n (τ y)) * this
  let e₀ : Polynomial ℂ ≃ₗ[ℂ] StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let e₁ : FinestLocallyConvex (Polynomial ℂ) ≃ₗ[ℂ]
      StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) := e₀
  have he₁ (p : Polynomial ℂ) : e₁ p = Φ p := rfl
  have : IsClosed (realSchwartzFlatAtOrigin : Set 𝓢(ℝ, ℂ)) := realSchwartzFlatAtOrigin_isClosed
  let : UniformSpace (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    isUniformAddGroup_of_addCommGroup
  let : PolynormableSpace ℂ (StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin)) :=
    uniformConvergenceCLM_polynormable (F := ℂ)
      {B : Set (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) | Bornology.IsVonNBounded ℂ B}
      (fun _ h ↦ by exact h)
      (by rw [Bornology.sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  have hcont : Continuous e₁ :=
    continuous_of_finestLocallyConvex (Polynomial ℂ) e₁.toLinearMap
  have hsymm : Continuous e₁.symm := by
    refine (finestLocallyConvex_withSeminorms (Polynomial ℂ)).continuous_of_continuous_comp
      e₁.symm.toLinearMap fun p ↦ ?_
    refine Seminorm.continuous (r := 1) ?_
    let w (n : ℕ) : ℝ := p (Polynomial.monomial n 1)
    obtain ⟨S, hS, hSc⟩ :=
      realSchwartzFlatQuotient_strongDual_borel fun n ↦ (n.factorial : ℝ) * w n
    have hB : Bornology.IsVonNBounded ℂ (realSchwartzFlatAtOrigin.mkQ '' S) :=
      hS.image realSchwartzFlatAtOrigin.mkQL
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo hB
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with T hT
    rw [Seminorm.mem_ball_zero]
    change p (e₁.symm T) < 1
    obtain ⟨q, hq⟩ : ∃ q : Polynomial ℂ, e₁.symm T = q := ⟨_, rfl⟩
    have hTq : T = Φ q := by rw [← he₁, ← hq, LinearEquiv.apply_symm_apply]
    rw [hq]
    let d (n : ℕ) : ℂ :=
      (n.factorial : ℂ) * (w n : ℂ) * (star (q.coeff n) / (‖q.coeff n‖ : ℂ))
    have hd (n : ℕ) : ‖d n‖ ≤ (n.factorial : ℝ) * w n := by
      have hw : 0 ≤ w n := apply_nonneg _ _
      have hu : ‖star (q.coeff n) / (‖q.coeff n‖ : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
        exact div_self_le_one _
      calc ‖d n‖ = (n.factorial : ℝ) * w n * ‖star (q.coeff n) / (‖q.coeff n‖ : ℂ)‖ := by
            simp only [d, norm_mul, Complex.norm_natCast, Complex.norm_real,
              Real.norm_of_nonneg hw]
        _ ≤ (n.factorial : ℝ) * w n * 1 := by gcongr
        _ = (n.factorial : ℝ) * w n := mul_one _
    obtain ⟨f, hfS, hf⟩ := hSc d hd
    have hval : T (realSchwartzFlatAtOrigin.mkQ f) =
        ((∑ k ∈ q.support, w k * ‖q.coeff k‖ : ℝ) : ℂ) := by
      rw [hTq, hΦ]
      push_cast
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hq0 : q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
      have hn0 : (‖q.coeff k‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq0
      rw [hcf, hf k]
      simp only [d]
      field_simp
      rw [Complex.star_def, show q.coeff k * (k.factorial : ℂ) * (w k : ℂ) *
          (starRingEnd ℂ) (q.coeff k) = (q.coeff k * (starRingEnd ℂ) (q.coeff k)) *
          ((k.factorial : ℂ) * (w k : ℂ)) by ring, Complex.mul_conj']
      field_simp
      exact mul_div_cancel_left₀ _ (hfact k)
    have hle : p q ≤ ∑ k ∈ q.support, w k * ‖q.coeff k‖ := by
      conv_lhs => rw [q.as_sum_support]
      refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
        (Finset.sum_le_sum fun k _ ↦ ?_)
      rw [show Polynomial.monomial k (q.coeff k) = q.coeff k • Polynomial.monomial k 1 by
        rw [Polynomial.smul_monomial, smul_eq_mul, mul_one], map_smul_eq_mul, mul_comm]
    have hlt := hT ⟨f, hfS, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, hval, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦
        mul_nonneg (apply_nonneg _ _) (norm_nonneg _))] at hlt
    exact hle.trans_lt hlt
  let e : FinestLocallyConvex (Polynomial ℂ) ≃L[ℂ]
      StrongDual ℂ (𝓢(ℝ, ℂ) ⧸ realSchwartzFlatAtOrigin) :=
    { e₁ with
      continuous_toFun := hcont
      continuous_invFun := hsymm }
  have he (p : Polynomial ℂ) : e p = Φ p := rfl
  have hev (p : Polynomial ℂ) (g : 𝓢(ℝ, ℂ)) : e p (realSchwartzFlatAtOrigin.mkQ g) =
      ∑ k ∈ p.support, p.coeff k * (realDiracDerivative k g / (k.factorial : ℂ)) := by
    rw [he, hΦ]
    simp only [hcf]
  refine ⟨e, fun k f ↦ ?_, fun p N ↦ ⟨fun hord ↦ ?_, fun hdeg K ↦ ?_⟩⟩
  · rw [he, hΦm, one_smul, hcf]
  · by_contra hlt
    push Not at hlt
    have hpd : p.coeff p.natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hlt)
    have hpd' : 0 < ‖p.coeff p.natDegree‖ := norm_pos_iff.mpr hpd
    let K0 : Compacts ℝ := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
    obtain ⟨C, hC0, hC⟩ := hord K0
    let χ : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
    obtain ⟨G, hG⟩ := realSchwartzFlatQuotient_strongDual_exists_bump χ p.natDegree
    have hGc : HasCompactSupport (G : ℝ → ℂ) :=
      (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
        (realSchwartzFlatQuotient_strongDual_bump_tsupport χ le_rfl _ G hG)
    let A : ℝ := ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j G
    have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
    let ε : ℝ := min 1 (‖p.coeff p.natDegree‖ / (2 * (C * A + 1)))
    have hε : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hε2 : ε * (2 * (C * A + 1)) ≤ ‖p.coeff p.natDegree‖ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    obtain ⟨ψ, hψ⟩ := realSchwartzFlatQuotient_strongDual_exists_scaled G hGc p.natDegree ε hε.ne'
    have hψsupp : tsupport (ψ : ℝ → ℂ) ⊆ Metric.closedBall 0 1 := by
      refine closure_minimal (fun x hx ↦ ?_) Metric.isClosed_closedBall
      rw [mem_support, hψ] at hx
      have hGx : ε⁻¹ * x ∈ tsupport (G : ℝ → ℂ) := subset_tsupport _ (right_ne_zero_of_mul hx)
      have h := realSchwartzFlatQuotient_strongDual_bump_tsupport χ le_rfl _ G hG hGx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hε,
        inv_mul_le_iff₀ hε] at h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      nlinarith
    have hψc : HasCompactSupport (ψ : ℝ → ℂ) :=
      (isCompact_closedBall (0 : ℝ) 1).of_isClosed_subset (isClosed_tsupport _) hψsupp
    let φ : 𝒟ℝ := ⟨ψ, ψ.smooth ⊤, hψc, by simp⟩
    have hφ : φ.hasCompactSupport.toSchwartzMap φ.contDiff = ψ := by ext x; rfl
    have hbound := hC φ hψsupp (ε * A) (by positivity) fun j hj x ↦ by
      change ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) x‖ ≤ ε * A
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 := SchwartzMap.le_seminorm' ℂ 0 j ψ x
      rw [pow_zero, one_mul] at h1
      have h2 := realSchwartzFlatQuotient_strongDual_scaled_seminorm χ le_rfl p.natDegree j 0
        (by omega) G ψ hG ε hε hε1 hψ
      have h3 : SchwartzMap.seminorm ℂ 0 j G ≤ A :=
        Finset.single_le_sum (f := fun j ↦ SchwartzMap.seminorm ℂ 0 j G)
          (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
      calc ‖iteratedDeriv j (ψ : ℝ → ℂ) x‖ ≤ SchwartzMap.seminorm ℂ 0 j ψ := h1
        _ ≤ ε * SchwartzMap.seminorm ℂ 0 j G := h2
        _ ≤ ε * A := by gcongr
    simp only at hbound
    rw [hφ, hev] at hbound
    have hsum : ∑ k ∈ p.support, p.coeff k * (realDiracDerivative k ψ / (k.factorial : ℂ)) =
        p.coeff p.natDegree * (-1 : ℂ) ^ p.natDegree := by
      rw [Finset.sum_eq_single p.natDegree]
      · rw [realSchwartzFlatQuotient_strongDual_scaled_dirac χ _ G ψ hG ε hε hψ]
        simp only [↓reduceIte]
        rw [mul_div_assoc, div_self (hfact _), mul_one]
      · intro k _ hk
        rw [realSchwartzFlatQuotient_strongDual_scaled_dirac χ _ G ψ hG ε hε hψ]
        simp [hk]
      · intro h
        exact absurd (Polynomial.mem_support_iff.mpr hpd) h
    rw [hsum, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one] at hbound
    have hCA : 0 ≤ C * (ε * A) := by positivity
    nlinarith
  · refine ⟨∑ k ∈ p.support, ‖p.coeff k‖, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _,
      fun f _ B _ hf ↦ ?_⟩
    beta_reduce
    rw [hev, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
    have hkN : k ≤ N := (Polynomial.le_natDegree_of_mem_supp k hk).trans hdeg
    have hB := hf k hkN 0
    change ‖iteratedFDeriv ℝ k (f.hasCompactSupport.toSchwartzMap f.contDiff : ℝ → ℂ) 0‖ ≤ B
      at hB
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hB
    have hf1 : (1 : ℝ) ≤ k.factorial := mod_cast k.factorial_pos
    rw [norm_mul, norm_div, realSchwartzFlatQuotient_strongDual_dirac, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    gcongr
    exact (div_le_self (norm_nonneg _) hf1).trans hB

end RealOrigin

section CoordinatePlane

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "Eᵣ(" ι ")" => EuclideanSpace ℝ ι
local notation "𝒟(" ι ")" => 𝓓((⊤ : TopologicalSpace.Opens Eᵣ(ι)), ℂ)
local notation "𝒮(" ι ")" => 𝓢(Eᵣ(ι), ℂ)
local notation "𝒟'(" ι ")" => StrongDual ℂ 𝒟(ι)
local notation "𝒮'(" ι ")" => StrongDual ℂ 𝒮(ι)

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
The coordinate derivative for a multi-index acts by the indicated number of derivatives
in each coordinate. The factors can be ordered arbitrarily on smooth tests. -/
def coordinateDerivative {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (α : ι → ℕ) : A :=
  ((Finset.univ.toList : List ι).map (fun i ↦ derivative i ^ α i)).prod

/-- The coordinate derivative of the zero multi-index is the identity. -/
theorem coordinateDerivative_zero {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A) :
    coordinateDerivative derivative (0 : ι → ℕ) = 1 := by
  simp [coordinateDerivative]

open Classical in
/-- Paper: Theorem 5.3.2.3, p. 245.
A multi-index supported in one coordinate acts by the corresponding power
of that coordinate's derivative. -/
theorem coordinateDerivative_single {ι A : Type*} [Fintype ι] [Monoid A] (derivative : ι → A)
    (i : ι) (k : ℕ) :
    coordinateDerivative derivative (Pi.single i k) = derivative i ^ k := by
  have key : ∀ l : List ι, l.Nodup →
      (l.map fun j ↦ derivative j ^ (Pi.single i k : ι → ℕ) j).prod =
        if i ∈ l then derivative i ^ k else 1 := by
    intro l hl
    induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.nodup_cons] at hl
      by_cases h : a = i
      · subst h
        simp [hl.1, ih hl.2]
      · rw [List.map_cons, List.prod_cons, ih hl.2, Pi.single_apply, if_neg h,
          pow_zero, one_mul]
        simp [Ne.symm h]
  unfold coordinateDerivative
  rw [key _ (Finset.nodup_toList _)]
  simp

open Classical in
local notation "eᵣ" i => WithLp.toLp 2 (Pi.single i (1 : ℝ))

local notation "∂𝒟[" I ", " α "]" =>
  coordinateDerivative
    (fun i : I ↦ (LineDeriv.lineDerivOpCLM ℂ 𝒟(I) (eᵣ i : Eᵣ(I)) : 𝒟(I) →L[ℂ] 𝒟(I))) α
local notation "∂𝒮[" I ", " α "]" =>
  coordinateDerivative
    (fun i : I ↦ (LineDeriv.lineDerivOpCLM ℂ 𝒮(I) (eᵣ i : Eᵣ(I)) : 𝒮(I) →L[ℂ] 𝒮(I))) α

local notation "insertPlane" y =>
  WithLp.toLp 2 (Sum.elim (fun _ ↦ (0 : ℝ)) (fun j ↦ y j))

/-- Precomposition with a closed-embedding continuous linear map of norm at most one is a
continuous linear map between spaces of test functions. -/
private theorem exists_testFunction_coordinatePlaneRestriction_comp {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : E' →L[ℝ] E) (hg : IsClosedEmbedding g) (hn : ‖g‖ ≤ 1) :
    ∃ R : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ) →L[ℂ] 𝓓((⊤ : TopologicalSpace.Opens E'), ℂ),
      ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ)) (y : E'), R f y = f (g y) := by
  have hloc (K : TopologicalSpace.Compacts E) :
      ∃ M : ContDiffMapSupportedIn E ℂ ⊤ K →L[ℂ]
          ContDiffMapSupportedIn E' ℂ ⊤ ⟨g ⁻¹' K, hg.isCompact_preimage K.isCompact⟩,
        ∀ f y, M f y = f (g y) := by
    let M : ContDiffMapSupportedIn E ℂ ⊤ K →ₗ[ℂ]
        ContDiffMapSupportedIn E' ℂ ⊤ ⟨g ⁻¹' K, hg.isCompact_preimage K.isCompact⟩ :=
      { toFun := fun f ↦ ContDiffMapSupportedIn.of_support_subset
          (f.contDiff.comp g.contDiff) (fun _ hy ↦ f.support_subset hy)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    refine ⟨⟨M, WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ _ _)
      (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ _ _) _
      (Seminorm.IsBounded.of_real fun i ↦ ⟨{i}, 1, fun f ↦ ?_⟩)⟩, fun _ _ ↦ rfl⟩
    rw [Finset.sup_singleton, one_mul]
    refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg _ _) i _).mpr
      fun y _ ↦ ?_
    change ‖iteratedFDeriv ℝ i (⇑f ∘ g) y‖ ≤ _
    rw [g.iteratedFDeriv_comp_right f.contDiff y (mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    calc _ ≤ ‖iteratedFDeriv ℝ i f (g y)‖ * 1 := by
          gcongr
          exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hn
      _ ≤ _ := by
          rw [mul_one]
          exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
  let L : 𝓓((⊤ : TopologicalSpace.Opens E), ℂ) →ₗ[ℂ] 𝓓((⊤ : TopologicalSpace.Opens E'), ℂ) :=
    { toFun := fun f ↦ ⟨f ∘ g, f.contDiff.comp g.contDiff,
        f.hasCompactSupport.comp_isClosedEmbedding hg, fun _ _ ↦ trivial⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL : Continuous L := by
    refine (TestFunction.continuous_iff_continuous_comp L).mpr fun K hK ↦ ?_
    obtain ⟨M, hM⟩ := hloc K
    have h : L ∘ TestFunction.ofSupportedIn hK =
        TestFunction.ofSupportedIn (fun _ _ ↦ trivial) ∘ M :=
      funext fun f ↦ TestFunction.ext fun y ↦ (hM f y).symm
    rw [h]
    exact (TestFunction.continuous_ofSupportedIn _).comp M.continuous
  exact ⟨⟨L, hL⟩, fun _ _ ↦ rfl⟩

/-- Inserting zeros into the normal coordinates is a continuous linear map of norm at most one
whose norm is preserved, hence a closed embedding. -/
private theorem exists_coordinatePlaneRestriction_inclusion :
    ∃ g : Eᵣ(κ) →L[ℝ] Eᵣ(ι ⊕ κ), (∀ y : Eᵣ(κ), g y = insertPlane y) ∧
      IsClosedEmbedding g ∧ ‖g‖ ≤ 1 ∧ ∀ y, ‖g y‖ = ‖y‖ := by
  let g : Eᵣ(κ) →L[ℝ] Eᵣ(ι ⊕ κ) := LinearMap.toContinuousLinearMap
    { toFun := fun y ↦ insertPlane y
      map_add' := fun y y' ↦ by ext i; cases i <;> simp
      map_smul' := fun c y ↦ by ext i; cases i <;> simp }
  have hnorm (y : Eᵣ(κ)) : ‖g y‖ = ‖y‖ := by
    simp [g, EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  exact ⟨g, fun _ ↦ rfl, (AddMonoidHomClass.isometry_of_norm _ hnorm).isClosedEmbedding,
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by rw [hnorm, one_mul], hnorm⟩

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on compactly supported smooth functions. -/
theorem exists_testFunction_coordinatePlaneRestriction :
    ∃ R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ), ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by
  obtain ⟨g, hg, hce, hn, -⟩ := exists_coordinatePlaneRestriction_inclusion (ι := ι) (κ := κ)
  obtain ⟨R, hR⟩ := exists_testFunction_coordinatePlaneRestriction_comp g hce hn
  exact ⟨R, fun f y ↦ (hR f y).trans (congrArg f (hg y))⟩

/-- Paper: Theorem 5.3.2.3(1), p. 245.
Inserting zeros into the normal coordinates gives a continuous linear restriction map
on Schwartz functions. -/
theorem exists_schwartz_coordinatePlaneRestriction :
    ∃ R : 𝒮(ι ⊕ κ) →L[ℂ] 𝒮(κ), ∀ (f : 𝒮(ι ⊕ κ)) (y : Eᵣ(κ)),
      R f y = f (insertPlane y) := by
  obtain ⟨g, hg, -, -, hnorm⟩ := exists_coordinatePlaneRestriction_inclusion (ι := ι) (κ := κ)
  have hA : AntilipschitzWith 1 g := AntilipschitzWith.of_le_mul_dist fun y y' ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm, NNReal.coe_one, one_mul]
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ g.hasTemperateGrowth hA,
    fun f y ↦ congrArg f (hg y)⟩

local notation "R𝒟" => (exists_testFunction_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose
local notation "R𝒮" => (exists_schwartz_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose
local notation "weight(" α ")" => (∑ i, α i)
local notation "index(" N ")" =>
  {α : (ι ⊕ κ) → Fin (N + 1) // (∑ i, (α i : ℕ)) ≤ N}
local notation "multi(" α ")" => (fun i ↦ ((((α).val) i).val : ℕ))
local notation "normal(" α ")" => (fun i : ι ↦ multi(α) (Sum.inl i))
local notation "tangent(" α ")" => (fun i : κ ↦ multi(α) (Sum.inr i))
local notation "factors(" f ", " g ", " x ")" =>
  f (WithLp.toLp 2 (fun i : ι ↦ x (.inl i))) * g (WithLp.toLp 2 (fun j : κ ↦ x (.inr j)))

private theorem coordinateDerivative_line_commute (v w : Eᵣ(ι)) :
    Commute (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) v : 𝒟(ι) →L[ℂ] 𝒟(ι))
      (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) w) := by
  have hd (u : Eᵣ(ι)) (g : 𝒟(ι)) :
      ⇑((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) u : 𝒟(ι) →L[ℂ] 𝒟(ι)) g) =
        fun y ↦ fderiv ℝ (⇑g) y u := by
    ext y
    rw [TestFunction.lineDerivOpCLM_eq_lineDerivCLM, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le g le_top]
  apply ContinuousLinearMap.ext
  intro f
  apply TestFunction.ext
  intro x
  simp only [mul_apply_eq_comp, hd]
  have hf : DifferentiableAt ℝ (fderiv ℝ ⇑f) x :=
    ((f.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero).differentiableAt
  simp only [fderiv_clm_apply hf (differentiableAt_const _), fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact f.contDiff.contDiffAt.isSymmSndFDerivAt (by simp) v w

open Classical in
private theorem coordinateDerivative_add_single_one {I A : Type*} [Fintype I] [DecidableEq I] [Monoid A]
    (D : I → A) (hc : ∀ i j, Commute (D i) (D j)) (a : I → ℕ) (i : I) :
    coordinateDerivative D (a + Pi.single i 1) = D i * coordinateDerivative D a := by
  have h : ∀ l : List I, l.Nodup → (l.map (fun j ↦ D j ^ ((a + Pi.single i 1) : I → ℕ) j)).prod =
        (if i ∈ l then D i else 1) * (l.map (fun j ↦ D j ^ a j)).prod := by
    intro l hl
    induction l with
    | nil => simp
    | cons j l ih =>
      have hn := List.nodup_cons.mp hl
      simp only [List.map_cons, List.prod_cons, List.mem_cons]
      rw [ih hn.2, Pi.add_apply]
      by_cases he : j = i
      · subst j; simp [hn.1, pow_succ', mul_assoc]
      · by_cases hm : i ∈ l
        · simp only [Ne.symm he, false_or, hm, ite_true, Pi.single_eq_of_ne he, add_zero]
          rw [← mul_assoc, ← mul_assoc, ((hc j i).pow_left (a j)).eq]
        · simp [he, Ne.symm he, hm]
  simpa [coordinateDerivative] using h (Finset.univ.toList : List I) (Finset.nodup_toList _)

-- TODO(paper-gap): The count N^m in (2) disagrees with the sum in (5.3.2.4).
-- In (2)–(5) the coefficient orders must be upper bounds. The distributional transpose
-- also introduces the factor (-1)^|α| in (5.3.2.5) and (5.3.2.6).

open Classical in
/-- Paper: Theorem 5.3.2.3(2), p. 245.
A compactly supported distribution of order at most N supported on a coordinate plane is a sum
of transposed restrictions of derivatives. Each coefficient has compact support and its order
is bounded by N minus the derivative degree.
Deviation: The finite indices are exactly those in (5.3.2.4). Orders are upper bounds. -/
theorem distribution_coordinatePlane_decomposition [Nonempty ι] (T : 𝒟'(ι ⊕ κ)) (N : ℕ)
    (hT : DistributionOrderLE T N)
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hplane : Distribution.dsupport (⇑T) ⊆
      Set.range (fun y : Eᵣ(κ) ↦ (insertPlane y : Eᵣ(ι ⊕ κ)))) :
    ∃ A : index(N) → 𝒟'(κ),
      (∀ α, DistributionOrderLE (A α) (N - weight(multi(α))) ∧
        IsCompact (Distribution.dsupport (⇑(A α)))) ∧
      ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f)) := by
  let D (i : ι ⊕ κ) : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ) :=
    LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ))
  obtain ⟨K, A, hA, hsum⟩ := CoordinatePlane.exists_orderZero_coefficients
    (ι := ι) (κ := κ) T N hT hK hplane (coordinateDerivative D) (coordinateDerivative_zero D)
    (coordinateDerivative_add_single_one D (fun _ _ ↦ coordinateDerivative_line_commute _ _))
    R𝒟 exists_testFunction_coordinatePlaneRestriction.choose_spec
  refine ⟨A, fun α ↦ ⟨?_, K.isCompact.of_isClosed_subset Distribution.isClosed_dsupport (hA α).2⟩, hsum⟩
  intro K'
  obtain ⟨C, hC, h⟩ := (hA α).1 K'
  exact ⟨C, hC, fun f hf B hB hderiv ↦ h f hf B hB fun j hj ↦ hderiv j (hj.trans (Nat.zero_le _))⟩

private theorem coordinateDerivative_split_sum {M : Type*} [Monoid M] (D : (ι ⊕ κ) → M)
    (hc : ∀ i j, Commute (D i) (D j)) (a : (ι ⊕ κ) → ℕ) :
    coordinateDerivative D a =
      coordinateDerivative (D ∘ Sum.inr) (a ∘ Sum.inr) *
        coordinateDerivative (D ∘ Sum.inl) (a ∘ Sum.inl) := by
  classical
  let l := (Finset.univ : Finset (ι ⊕ κ)).toList
  let r := (Finset.univ : Finset κ).toList
  let s := (Finset.univ : Finset ι).toList
  have hp : l.Perm (r.map Sum.inr ++ s.map Sum.inl) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) _).2
    · intro i; cases i <;> simp [r, s]
    · apply List.nodup_append'.2
      refine ⟨(Finset.nodup_toList _).map Sum.inr_injective,
        (Finset.nodup_toList _).map Sum.inl_injective, ?_⟩
      apply List.disjoint_left.mpr
      rintro _ h₁ h₂
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp h₁
      simp at h₂
  have h := (hp.map (fun i ↦ D i ^ a i)).prod_eq' (List.pairwise_map.mpr
    (List.pairwise_of_forall_mem_list (fun i _ j _ ↦ (hc i j).pow_pow _ _)))
  simpa [coordinateDerivative, l, r, s, List.map_append, List.map_map, Function.comp_def] using h

open Classical in
private theorem coordinateDerivative_plane_line (R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ))
    (hR : ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)), R f y = f (insertPlane y))
    (j : κ) (f : 𝒟(ι ⊕ κ)) :
    R ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ (Sum.inr j) : Eᵣ(ι ⊕ κ)) :
        𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ)) f) =
      (LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) (eᵣ j : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ)) (R f) := by
  classical
  apply TestFunction.ext
  intro y
  simp only [hR, TestFunction.lineDerivOpCLM_eq_lineDerivCLM,
    TestFunction.lineDerivCLM_apply_of_le le_top, lineDeriv]
  congr 1
  funext t
  congr 1
  ext i
  cases i <;> simp

open Classical in
private theorem coordinateDerivative_plane_restrict (R : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(κ))
    (hR : ∀ (f : 𝒟(ι ⊕ κ)) (y : Eᵣ(κ)), R f y = f (insertPlane y))
    (a : (ι ⊕ κ) → ℕ) (f : 𝒟(ι ⊕ κ)) :
    R (∂𝒟[ι ⊕ κ, a] f) = ∂𝒟[κ, a ∘ Sum.inr]
      (R (∂𝒟[ι ⊕ κ, Sum.elim (a ∘ Sum.inl) (0 : κ → ℕ)] f)) := by
  let D (i : ι ⊕ κ) := (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) :
    𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ))
  let d (j : κ) := (LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) (eᵣ j : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ))
  have hD (i j : ι ⊕ κ) : Commute (D i) (D j) := coordinateDerivative_line_commute _ _
  have hd (j : κ) : Semiconj R (D (.inr j)) (d j) := coordinateDerivative_plane_line R hR j
  have hprod (l : List κ) : Semiconj R
      ((l.map fun j ↦ D (.inr j) ^ a (.inr j)).prod : 𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ))
      ((l.map fun j ↦ d j ^ a (.inr j)).prod : 𝒟(κ) →L[ℂ] 𝒟(κ)) := by
    induction l with
    | nil => exact fun _ ↦ rfl
    | cons j l ih =>
      simpa only [List.map_cons, List.prod_cons, FunLike.coe_mul_eq_comp,
        FunLike.coe_pow_eq_iterate] using ((hd j).iterate_right (a (.inr j))).comp_right ih
  let b := Sum.elim (a ∘ Sum.inl) (0 : κ → ℕ)
  change R (coordinateDerivative D a f) = coordinateDerivative d _ (R (coordinateDerivative D b f))
  rw [coordinateDerivative_split_sum D hD a, coordinateDerivative_split_sum D hD b]
  rw [show b ∘ Sum.inr = 0 from rfl, coordinateDerivative_zero, one_mul, mul_apply_eq_comp]
  exact hprod _ _

open Classical in
/-- Differentiating a pure tensor in a normal coordinate differentiates its first factor. -/
private theorem distribution_coordinatePlane_decomposition_apply_tmul_normal_line
    (i : ι) (f : 𝒟(ι ⊕ κ)) (g : 𝒟(ι)) (h : 𝒟(κ))
    (hf : ∀ x : Eᵣ(ι ⊕ κ), f x = factors(g, h, x)) (x : Eᵣ(ι ⊕ κ)) :
    (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ (Sum.inl i) : Eᵣ(ι ⊕ κ)) f) x =
      factors((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) g), h, x) := by
  simp only [TestFunction.lineDerivOpCLM_eq_lineDerivCLM,
    TestFunction.lineDerivCLM_apply_of_le le_top, lineDeriv]
  rw [← deriv_mul_const_field]
  congr 1
  funext t
  rw [hf]
  congr 2
  · ext j
    simp
  · ext j
    simp

open Classical in
/-- Restricting a purely normal derivative of a pure tensor evaluates its first factor at zero. -/
private theorem distribution_coordinatePlane_decomposition_apply_tmul_normal_restrict
    (b : ι → ℕ) (f : 𝒟(ι ⊕ κ)) (g : 𝒟(ι)) (h : 𝒟(κ))
    (hf : ∀ x : Eᵣ(ι ⊕ κ), f x = factors(g, h, x)) :
    R𝒟 (∂𝒟[ι ⊕ κ, Sum.elim b (0 : κ → ℕ)] f) = (∂𝒟[ι, b] g) 0 • h := by
  let D (i : ι ⊕ κ) := (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) :
    𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ))
  let d (i : ι) := (LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) : 𝒟(ι) →L[ℂ] 𝒟(ι))
  let P (F : 𝒟(ι ⊕ κ)) (G : 𝒟(ι)) := ∀ x : Eᵣ(ι ⊕ κ), F x = factors(G, h, x)
  have hpow (i : ι) (n : ℕ) (F : 𝒟(ι ⊕ κ)) (G : 𝒟(ι)) (hFG : P F G) :
      P ((D (.inl i) ^ n) F) ((d i ^ n) G) := by
    induction n with
    | zero => exact hFG
    | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
      exact distribution_coordinatePlane_decomposition_apply_tmul_normal_line i _ _ h ih
  have hprod (l : List ι) :
      P ((l.map (fun i ↦ D (.inl i) ^ b i)).prod f) ((l.map (fun i ↦ d i ^ b i)).prod g) := by
    induction l with
    | nil => exact hf
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      exact hpow i (b i) _ _ ih
  change R𝒟 (coordinateDerivative D (Sum.elim b (0 : κ → ℕ)) f) = _
  rw [coordinateDerivative_split_sum D (fun _ _ ↦ coordinateDerivative_line_commute _ _),
    show Sum.elim b (0 : κ → ℕ) ∘ Sum.inr = 0 from rfl, coordinateDerivative_zero, one_mul]
  apply TestFunction.ext
  intro y
  rw [exists_testFunction_coordinatePlaneRestriction.choose_spec]
  exact hprod Finset.univ.toList (insertPlane y)

open Classical in
/-- Paper: Theorem 5.3.2.3(3), p. 245.
On a pure tensor, the summand factors as the normal derivative evaluated at zero and the
tangential coefficient applied to the derivative of the tangential test.
Deviation: This is the test-function derivative form of (5.3.2.5), with the transpose signs
canceled. Using distributional derivatives in both factors requires a sign of (-1)^|α|. -/
theorem distribution_coordinatePlane_decomposition_apply_tmul {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f)))
    (f : 𝒟(ι ⊕ κ)) (g : 𝒟(ι)) (h : 𝒟(κ))
    (hf : ∀ x : Eᵣ(ι ⊕ κ), f x = factors(g, h, x)) :
    T f = ∑ α : index(N), (∂𝒟[ι, normal(α)] g) 0 * A α (∂𝒟[κ, tangent(α)] h) := by
  rw [hA f]
  apply Finset.sum_congr rfl
  intro α _
  rw [coordinateDerivative_plane_restrict R𝒟
    exists_testFunction_coordinatePlaneRestriction.choose_spec (multi(α)) f,
    distribution_coordinatePlane_decomposition_apply_tmul_normal_restrict _ f g h hf,
    map_smul, map_smul, smul_eq_mul]
  rfl

open Classical in
/-- Paper: Theorem 5.3.2.3(4), p. 245.
Tensoring a normal Dirac derivative with a tangential distribution is the transposed normal
derivative of the restriction to the coordinate plane. -/
def coordinatePlaneDiracTensor (β : ι → ℕ) (U : 𝒟'(κ)) : 𝒟'(ι ⊕ κ) :=
  (-1 : ℂ)^weight(β) • U.comp ((R𝒟).comp ∂𝒟[ι ⊕ κ, Sum.elim β (0 : κ → ℕ)])

/-- Paper: Theorem 5.3.2.3(4), p. 245.
At derivative order zero the tensor restricts the test to the coordinate plane and applies
the tangential distribution. -/
theorem coordinatePlaneDiracTensor_zero (U : 𝒟'(κ)) (f : 𝒟(ι ⊕ κ)) :
    coordinatePlaneDiracTensor (0 : ι → ℕ) U f = U (R𝒟 f) := by
  have h0 : Sum.elim (0 : ι → ℕ) (0 : κ → ℕ) = 0 := by
    ext i; cases i <;> rfl
  simp [coordinatePlaneDiracTensor, h0, coordinateDerivative_zero]

open Classical in
/-- Paper: Theorem 5.3.2.3(4), p. 245.
The decomposition is a finite sum of tensor products of normal Dirac derivatives with
tangential distributional derivatives.
Deviation: Each tensor in (5.3.2.6) has the factor (-1)^|α| required by (5.3.2.4). -/
theorem distribution_coordinatePlane_decomposition_eq_sum {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f))) :
    T = ∑ α : index(N), (-1 : ℂ)^weight(multi(α)) •
      coordinatePlaneDiracTensor (normal(α))
        ((-1 : ℂ)^weight(tangent(α)) • (A α).comp ∂𝒟[κ, tangent(α)]) := by
  ext f
  rw [hA, sum_apply]
  apply Finset.sum_congr rfl
  intro α _
  simp only [coordinatePlaneDiracTensor, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  rw [coordinateDerivative_plane_restrict R𝒟
    exists_testFunction_coordinatePlaneRestriction.choose_spec (multi(α)) f]
  rw [← mul_assoc ((-1 : ℂ)^weight(normal(α))) _ _, ← pow_add,
    ← Fintype.sum_sum_type (multi(α)), ← mul_assoc, ← mul_pow]
  simp [Function.comp_def]

open Classical in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
Passing from a compactly supported test to its Schwartz function commutes with all
coordinate derivatives. This also identifies derivatives of the tempered extensions. -/
theorem coordinateDerivative_testFunction_toSchwartz {ι : Type*} [Fintype ι]
    (β : ι → ℕ) (f : 𝒟(ι)) :
    let g := ∂𝒟[ι, β] f
    g.hasCompactSupport.toSchwartzMap g.contDiff =
      ∂𝒮[ι, β] (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
  intro g
  have hpow : ∀ i (k : ℕ) (f : 𝒟(ι)),
      ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) ^ k) f).hasCompactSupport.toSchwartzMap
          ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι) (eᵣ i : Eᵣ(ι)) ^ k) f).contDiff =
        (LineDeriv.lineDerivOpCLM ℂ 𝒮(ι) (eᵣ i : Eᵣ(ι)) ^ k)
          (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
    intro i k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      congr 1
  show (∂𝒟[ι, β] f).hasCompactSupport.toSchwartzMap (∂𝒟[ι, β] f).contDiff = _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l generalizing f with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [← ih, ← hpow]

open scoped Manifold in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
A compactly supported distribution has a tempered extension. Cutting a Schwartz test off by a
test function that equals one on a neighbourhood of the distribution's support does not change
the value of the distribution, and the resulting functional is continuous on the Schwartz space. -/
private theorem distribution_coordinatePlane_decomposition_tempered_extension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : StrongDual ℂ 𝓓((⊤ : Opens E), ℂ))
    (hA : IsCompact (Distribution.dsupport (⇑A))) :
    ∃ B : StrongDual ℂ 𝓢(E, ℂ),
      ∀ g : 𝓓((⊤ : Opens E), ℂ), B (g.hasCompactSupport.toSchwartzMap g.contDiff) = A g := by
  obtain ⟨K, hK, hsub⟩ := exists_compact_superset hA
  obtain ⟨χ, hχ, hzero, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E)
    (n := ⊤) Distribution.isClosed_dsupport hsub
  let b (x : E) : ℂ := χ x
  have hd : ContDiff ℝ (⊤ : ℕ∞) b :=
    Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp χ.contMDiff)
  have hb : tsupport b ⊆ K := hK.isClosed.closure_subset_iff.mpr fun x hx ↦
    by_contra fun hn ↦ hx (by simp [b, hzero x hn])
  let χT : 𝓓((⊤ : Opens E), ℂ) :=
    ⟨b, hd, hK.of_isClosed_subset (isClosed_tsupport b) hb, fun _ _ ↦ trivial⟩
  let J := schwartzToTestFunctionMulCLM χT
  refine ⟨A.comp J, fun g ↦ ?_⟩
  change A (J _) = A g
  rw [← sub_eq_zero, ← map_sub]
  apply testFunction_vanishes_off_dsupport
  intro x hx hxA
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
  filter_upwards [hχ.filter_mono (nhds_le_nhdsSet hxA)] with y hy
  change schwartzToTestFunctionMulCLM χT (g.hasCompactSupport.toSchwartzMap g.contDiff) y - g y = 0
  rw [schwartzToTestFunctionMulCLM_apply]
  change (χ y : ℂ) * g y - g y = 0
  simp [hy]

/-- Restriction to the coordinate plane commutes with passing a compactly supported test to
its Schwartz function: both restrictions are given by inserting zeros in the normal
coordinates. -/
private theorem distribution_coordinatePlane_decomposition_tempered_restriction_toSchwartz
    (f : 𝒟(ι ⊕ κ)) :
    let g := R𝒟 f
    R𝒮 (f.hasCompactSupport.toSchwartzMap f.contDiff) =
      g.hasCompactSupport.toSchwartzMap g.contDiff := by
  intro g
  ext y
  rw [(exists_schwartz_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose_spec _ y]
  simp only [HasCompactSupport.toSchwartzMap_toFun]
  exact ((exists_testFunction_coordinatePlaneRestriction (ι := ι) (κ := κ)).choose_spec f y).symm

open Classical in
/-- Passing from a compactly supported test on the product to its Schwartz function commutes
with coordinate derivatives, at the product type itself. -/
private theorem distribution_coordinatePlane_decomposition_tempered_toSchwartz
    (β : (ι ⊕ κ) → ℕ) (f : 𝒟(ι ⊕ κ)) :
    let g := ∂𝒟[ι ⊕ κ, β] f
    g.hasCompactSupport.toSchwartzMap g.contDiff =
      ∂𝒮[ι ⊕ κ, β] (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
  intro g
  have hpow : ∀ i (k : ℕ) (f : 𝒟(ι ⊕ κ)),
      ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) ^ k)
          f).hasCompactSupport.toSchwartzMap
          ((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) ^ k) f).contDiff =
        (LineDeriv.lineDerivOpCLM ℂ 𝒮(ι ⊕ κ) (eᵣ i : Eᵣ(ι ⊕ κ)) ^ k)
          (f.hasCompactSupport.toSchwartzMap f.contDiff) := by
    intro i k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
      congr 1
  show (∂𝒟[ι ⊕ κ, β] f).hasCompactSupport.toSchwartzMap (∂𝒟[ι ⊕ κ, β] f).contDiff = _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List (ι ⊕ κ)) = l
  induction l generalizing f with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [← ih, ← hpow]

open Classical in
/-- Paper: Theorem 5.3.2.3(5), p. 245.
The coefficient distributions and the ambient distribution have tempered extensions.
The identity holds for every Schwartz test after extension.
Deviation: The tempered identity uses the test-function derivative convention of (5.3.2.4),
equivalent to the signed tensor identity with distributional derivatives. -/
theorem distribution_coordinatePlane_decomposition_tempered {N : ℕ} (T : 𝒟'(ι ⊕ κ))
    (A : index(N) → 𝒟'(κ))
    (hK : ∀ α, IsCompact (Distribution.dsupport (⇑(A α))))
    (hA : ∀ f : 𝒟(ι ⊕ κ), T f = ∑ α : index(N), A α (R𝒟 (∂𝒟[ι ⊕ κ, multi(α)] f))) :
    ∃ (U : 𝒮'(ι ⊕ κ)) (B : index(N) → 𝒮'(κ)),
      (∀ f : 𝒟(ι ⊕ κ), U (f.hasCompactSupport.toSchwartzMap f.contDiff) = T f) ∧
      (∀ α, ∀ g : 𝒟(κ), B α (g.hasCompactSupport.toSchwartzMap g.contDiff) = A α g) ∧
      ∀ f : 𝒮(ι ⊕ κ), U f = ∑ α : index(N), B α (R𝒮 (∂𝒮[ι ⊕ κ, multi(α)] f)) := by
  choose B hB using fun α : index(N) =>
    distribution_coordinatePlane_decomposition_tempered_extension (A α) (hK α)
  refine ⟨∑ α : index(N), (B α).comp ((R𝒮).comp ∂𝒮[ι ⊕ κ, multi(α)]), B, ?_, fun α => hB α, ?_⟩
  · intro f
    simp only [sum_apply, ContinuousLinearMap.comp_apply]
    rw [hA f]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hder : ∂𝒮[ι ⊕ κ, multi(α)] (f.hasCompactSupport.toSchwartzMap f.contDiff) =
        (∂𝒟[ι ⊕ κ, multi(α)] f).hasCompactSupport.toSchwartzMap
          (∂𝒟[ι ⊕ κ, multi(α)] f).contDiff :=
      (distribution_coordinatePlane_decomposition_tempered_toSchwartz (multi(α)) f).symm
    rw [← hB α, ← distribution_coordinatePlane_decomposition_tempered_restriction_toSchwartz
      (∂𝒟[ι ⊕ κ, multi(α)] f), hder]
  · intro f
    simp only [sum_apply, ContinuousLinearMap.comp_apply]

namespace TestFunctionTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compatible compact localizations glue to a continuous operator on all test functions. -/
private theorem testFunction_glue_cutoffs {Z Y I : Type*}
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [AddCommGroup Y] [Module ℝ Y] [Module ℂ Y] [IsScalarTower ℝ ℂ Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyConvexSpace ℝ Y] [ContinuousSMul ℝ Y]
    (J : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] Z)
    (M : I → Z →L[ℂ] Z) (R : I → Z →L[ℂ] Y)
    (comm : ∀ i j z, R i (M j z) = R j (M i z))
    (fix : ∀ K : Compacts E, ∃ i, ∀ f : 𝓓((⊤ : Opens E), ℂ),
        tsupport (f : E → ℂ) ⊆ K → M i (J f) = J f) :
    ∃ Q : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] Y, ∀ i f, M i (J f) = J f → Q f = R i (J f) := by
  classical
  choose idx hidx using fix
  let Kf (f : 𝓓((⊤ : Opens E), ℂ)) : Compacts E := ⟨tsupport (f : E → ℂ), f.hasCompactSupport⟩
  let q (f : 𝓓((⊤ : Opens E), ℂ)) := R (idx (Kf f)) (J f)
  have hq (i : I) (f : 𝓓((⊤ : Opens E), ℂ)) (hf : M i (J f) = J f) : q f = R i (J f) := by
    have hh := comm (idx (Kf f)) i (J f)
    rwa [hf, hidx _ _ Subset.rfl] at hh
  refine ⟨TestFunction.limitCLM ℂ q (fun K hK ↦ ((R (idx K)).comp J).comp
    (TestFunction.ofSupportedInCLM ℂ hK)) (fun K hK f ↦ ?_), hq⟩
  exact hq (idx K) _ (hidx _ _ f.tsupport_subset)

section TensorProof
open UniformSpace
open scoped TensorProduct
local notation "D(" E ")" => 𝓓((⊤ : Opens E), ℂ)
local notation "S(" E ")" => 𝓢(E, ℂ)
local notation "Cι(" A ", " B ")" => Completion (InductiveTensor A B)

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

private local instance {X : Type*} [AddCommGroup X] [Module ℂ X] {I : Type*}
    (p : SeminormFamily ℂ X I) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

private local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    PolynormableSpace ℂ S(X) := (schwartz_withSeminorms ℂ X ℂ).toPolynormableSpace

private local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    PolynormableSpace ℂ D(X) := (testFunction_complex_polynormable (E := X)).2

variable {A B C : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]

open scoped Manifold in
private theorem compactTestOne (K : Compacts E) [FiniteDimensional ℝ E] :
    ∃ b : D(E), ∀ x ∈ K, b x = 1 := by
  obtain ⟨U, hU, hsub⟩ := exists_compact_superset K.isCompact
  obtain ⟨χ, hχ, hzero, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E)
    (n := ⊤) K.isCompact.isClosed hsub
  let b (x : E) : ℂ := χ x
  have hb : tsupport b ⊆ U := hU.isClosed.closure_subset_iff.mpr fun x hx ↦
    by_contra fun hn ↦ hx (by simp [b, hzero x hn])
  refine ⟨⟨b, Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp χ.contMDiff),
    hU.of_isClosed_subset (isClosed_tsupport b) hb, fun _ _ ↦ trivial⟩, fun x hx ↦ ?_⟩
  change (χ x : ℂ) = 1
  rw [hχ.self_of_nhdsSet x hx]
  rfl

/-- Factor the algebraic product through tests. Separate continuity can be checked on
a compact rectangle at a time, where one cutoff realizes the factorization. -/
private theorem localizedTensor_product
    (e : C ≃ₜ A × B) (U : InductiveTensor D(A) D(B) →L[ℂ] S(C))
    (hU : ∀ (a : D(A)) (b : D(B)) x, U (a ⊗ₜ[ℂ] b) x = a (e x).1 * b (e x).2) :
    ∃ P : InductiveTensor D(A) D(B) →L[ℂ] D(C), ∀ t, testFunctionToSchwartzCLM (P t) = U t := by
  classical
  let box (K : Compacts A) (H : Compacts B) : Compacts C :=
    ⟨e ⁻¹' ((K : Set A) ×ˢ (H : Set B)), e.isClosedEmbedding.isCompact_preimage (K.isCompact.prod H.isCompact)⟩
  have supp (a : D(A)) (b : D(B)) (K : Compacts A) (H : Compacts B)
      (ha : tsupport (a : A → ℂ) ⊆ K) (hb : tsupport (b : B → ℂ) ⊆ H) :
      tsupport ((U (a ⊗ₜ[ℂ] b)) : C → ℂ) ⊆ box K H := by
    refine (box K H).isCompact.isClosed.closure_subset_iff.mpr fun x hx ↦ ?_
    rw [mem_support, hU, mul_ne_zero_iff] at hx
    exact ⟨ha (subset_tsupport _ hx.1), hb (subset_tsupport _ hx.2)⟩
  have hc (t : InductiveTensor D(A) D(B)) : HasCompactSupport ((U t) : C → ℂ) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      let K : Compacts A := ⟨_, a.hasCompactSupport⟩
      let H : Compacts B := ⟨_, b.hasCompactSupport⟩
      exact (box K H).isCompact.of_isClosed_subset (isClosed_tsupport _)
        (supp a b K H Subset.rfl Subset.rfl)
    | add t s ht hs =>
      erw [map_add U]
      exact ht.add hs
  let P : InductiveTensor D(A) D(B) →ₗ[ℂ] D(C) :=
    { toFun := fun t ↦ ⟨U t, (U t).smooth ⊤, hc t, fun _ _ ↦ trivial⟩
      map_add' := fun t s ↦ TestFunction.ext fun x ↦ congrArg (fun f : S(C) ↦ f x) (map_add U t s)
      map_smul' := fun c t ↦ TestFunction.ext fun x ↦ congrArg (fun f : S(C) ↦ f x) (map_smul U c t) }
  have cut {t : InductiveTensor D(A) D(B)} {K : Compacts C} (ht : tsupport ((U t) : C → ℂ) ⊆ K)
      {b : D(C)} (hb : ∀ x ∈ K, b x = 1) : schwartzToTestFunctionMulCLM b (U t) = P t := by
    ext x
    rw [schwartzToTestFunctionMulCLM_apply]
    change b x * U t x = U t x
    by_cases h : x ∈ tsupport ((U t) : C → ℂ)
    · rw [hb x (ht h), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]
  have hsep := (continuous_inductiveTensor_iff U.toLinearMap).mp U.continuous
  refine ⟨⟨P, (continuous_inductiveTensor_iff P).mpr ⟨fun a ↦ ?_, fun b ↦ ?_⟩⟩, fun _ ↦ rfl⟩
  · change Continuous (P.comp (TensorProduct.mk ℂ D(A) D(B) a))
    apply (TestFunction.continuous_iff_continuous_comp _).2
    intro H hH
    let K : Compacts A := ⟨_, a.hasCompactSupport⟩
    obtain ⟨b, hb⟩ := compactTestOne (box K H)
    exact (((schwartzToTestFunctionMulCLM b).continuous.comp (hsep.1 a)).comp
      (TestFunction.continuous_ofSupportedIn hH)).congr fun f ↦ cut (supp _ _ _ _ Subset.rfl f.tsupport_subset) hb
  · change Continuous (P.comp ((TensorProduct.mk ℂ D(A) D(B)).flip b))
    apply (TestFunction.continuous_iff_continuous_comp _).2
    intro K hK
    let H : Compacts B := ⟨_, b.hasCompactSupport⟩
    obtain ⟨a, ha⟩ := compactTestOne (box K H)
    exact (((schwartzToTestFunctionMulCLM a).continuous.comp (hsep.2 b)).comp
      (TestFunction.continuous_ofSupportedIn hK)).congr fun f ↦ cut (supp _ _ _ _ f.tsupport_subset Subset.rfl) ha

private def testTensorMap {X Y V W : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V] [T2Space V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [PolynormableSpace ℂ W] [T2Space W]
    (a : X →L[ℂ] V) (b : Y →L[ℂ] W) :
    InductiveTensor X Y →L[ℂ] InductiveTensor V W :=
  ⟨inductiveTensorMap a.toLinearMap b.toLinearMap, inductiveTensorMap_continuous a b⟩

private theorem testCompletedTensor_ext {X Y V : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [T2Space V]
    (f g : Cι(X, Y) →L[ℂ] V) (h : ∀ x y, f (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) =
        g (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) : f = g := by
  have he : f.toLinearMap.comp Completion.toComplL.toLinearMap =
      g.toLinearMap.comp Completion.toComplL.toLinearMap := TensorProduct.ext' h
  exact ContinuousLinearMap.ext fun z ↦ Completion.induction_on z (isClosed_eq f.continuous g.continuous)
    fun x ↦ LinearMap.congr_fun he x

private def schwartzEval (x : E) : S(E) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)

/-- A real elementary factor carries the usual Schwartz topology. The range test is
the purely real case of the elementary Schwartz submodule characterization. -/
private theorem testTensor_realStage (d : ℕ) :
    ∃ J : S(EuclideanSpace ℝ (Fin d)) ≃L[ℂ] ElementarySchwartz d 0 0 PUnit.{1},
      ∀ f x, J f x = f x.1 := by
  let S := S(EuclideanSpace ℝ (Fin d))
  let T := ElementarySchwartz d 0 0 PUnit.{1}
  let L : S →ₗ[ℂ] T :=
    { toFun := fun f ↦ ⟨fun x ↦ f x.1, (elementarySchwartzSubmodule_real_iff f).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have h (s : T) (x : ElementaryLieGroup d 0 0 PUnit.{1}) : s (x.1, 0, 0, 0) = s x :=
    congrArg s (Prod.ext rfl (Subsingleton.elim _ _))
  have hb : Bijective L := by
    refine ⟨fun f g e ↦ SchwartzMap.ext fun x ↦ congrArg (fun s : T ↦ s (x, 0, 0, 0)) e, fun s ↦ ?_⟩
    have he := funext (h s)
    obtain ⟨f, hf⟩ := (elementarySchwartzSubmodule_real_iff (fun x ↦ s (x, 0, 0, 0))).mp
      (he.symm ▸ s.property)
    exact ⟨f, Subtype.ext (funext fun x ↦ (congrFun hf x.1).trans (h s x))⟩
  have hS := euclideanSchwartz_frechet d
  let : BarrelledSpace ℂ S := isFrechetTVS_barrelled hS
  have hc : Continuous L := continuous_toElementarySchwartz_of_eval L fun x ↦
    ⟨schwartzEval x.1, fun _ ↦ rfl⟩
  let q : S →L[ℂ] T := ⟨L, hc⟩
  have hopen := isOpenMap_of_surjective_toLF
    (isLFSpace_of_isFrechetTVS (elementarySchwartz_isFrechet (m := d) (n := 0) (r := 0) (F := PUnit.{1})))
    (X := fun _ ↦ S) (fun _ ↦ hS) (fun _ ↦ ContinuousLinearMap.id ℂ S)
    (fun _ ↦ Subset.rfl) (fun f ↦ ⟨0, f, rfl⟩) q hb.surjective
  have hq := hopen.isQuotientMap hc hb.surjective
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective L hb)
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hb.injective⟩), fun _ _ ↦ rfl⟩

/-- The whole group with trivial kernel is the largest structural pair for a real
vector group. This stage gives the Schwartz–Bruhat coordinate equivalence. The stage construction
follows Ch02_AdelicTheta/Sec2b and AppB_AnalyticNT/Sec4b. -/
private theorem testTensor_realCoordinates {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [FiniteDimensional ℝ E] (v : G ≃ₜ* Multiplicative E) :
    ∃ J : S(E) ≃L[ℂ] SchwartzBruhat G, ∀ f x, J f x = f (v x).toAdd := by
  classical
  let n := Module.finrank ℝ E
  let V := EuclideanSpace ℝ (Fin n)
  let b : E ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [V, n, finrank_euclideanSpace])
  let eb : Multiplicative E ≃ₜ* Multiplicative V :=
    ⟨b.toLinearEquiv.toAddEquiv.toMultiplicative, b.continuous, b.symm.continuous⟩
  let B := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit.{1}
  let : Unique B := uniqueOfSubsingleton 0
  let w : Multiplicative (ElementaryLieGroup n 0 0 PUnit.{1}) ≃ₜ* Multiplicative V :=
    ContinuousMulEquiv.mk' (Homeomorph.prodUnique _ _) fun _ _ ↦ rfl
  let p : ElementaryLCAPresentation G := ⟨n, 0, 0, PUnit.{1}, (v.trans eb).trans w.symm⟩
  have hG := (lca_elementary_iff (G := G)).mpr ⟨p⟩
  let i : (⊤ : Subgroup G) ≃ₜ* G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair G := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hG.1,
    isBruhatGoodSubgroup_bot_iff.mpr hG.2, bot_le⟩
  let j : G →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hj : IsOpenQuotientMap j := QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have inj : Function.Injective j := (MonoidHom.ker_eq_bot_iff j).mp (eq_bot_iff.mpr fun x hx ↦
    (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective j ⟨inj, hj.surjective⟩).toContinuousMulEquiv
    fun _ ↦ hj.isQuotientMap.isOpen_preimage
  let t : ElementaryLCAPresentation a.quotient := {p with equiv := q.symm.trans p.equiv}
  let A : SchwartzBruhatStage t →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a t
  have hA := schwartzBruhatStage_isEmbedding a t
  have hsur : Surjective A := by
    intro f
    obtain ⟨u, e', s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    obtain ⟨k, hk, -⟩ := schwartzBruhatStage_transition (show u ≤ a from ⟨le_top, le_top⟩) e' t
    exact ⟨k s, Subtype.ext ((hk s).trans hs)⟩
  let T := ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective A ⟨hA.injective, hsur⟩)
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hA, hsur⟩)
  let B := ContinuousLinearEquiv.equivOfInverse
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b.symm (F := ℂ))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b (F := ℂ))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (b.symm_apply_apply x))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (b.apply_symm_apply x))
  obtain ⟨R, hR⟩ := testTensor_realStage n
  refine ⟨(B.trans R).trans T, fun f x ↦ ?_⟩
  change (show SchwartzBruhat G from schwartzBruhatStageInclusion a t (R (B f))) x = _
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply, dite_eq_left (Subgroup.mem_top x)]
  change R (B f) (p.equiv (q.symm (q x))).toAdd = _
  rw [q.symm_apply_apply, hR]; exact congrArg f (b.symm_apply_apply (v x).toAdd)

private def testTensorInSchwartz : InductiveTensor D(A) D(B) →L[ℂ] InductiveTensor S(A) S(B) :=
  testTensorMap testFunctionToSchwartzCLM testFunctionToSchwartzCLM

private def testTensorCut (b : D(A) × D(B)) : InductiveTensor S(A) S(B) →L[ℂ] InductiveTensor D(A) D(B) :=
  testTensorMap (schwartzToTestFunctionMulCLM b.1) (schwartzToTestFunctionMulCLM b.2)

local notation "InclT" => testTensorInSchwartz (A := A) (B := B)
local notation "CutT" => testTensorCut (A := A) (B := B)
private def testTensorMul (b : D(A) × D(B)) : Cι(S(A), S(B)) →L[ℂ] Cι(S(A), S(B)) :=
  (InclT).completion.comp (CutT b).completion

local notation "MulT" => testTensorMul (A := A) (B := B)

private theorem testTensor_mul_pure (a : D(A) × D(B)) (f : S(A)) (g : S(B)) :
    MulT a (Completion.coe' (α := InductiveTensor S(A) S(B)) (f ⊗ₜ[ℂ] g)) =
      Completion.coe' (α := InductiveTensor S(A) S(B))
        (testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM a.1 f) ⊗ₜ[ℂ]
            testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM a.2 g)) := by
  let t : InductiveTensor S(A) S(B) := f ⊗ₜ[ℂ] g
  exact (congrArg (InclT).completion ((CutT a).completion_apply_coe t)).trans
    ((InclT).completion_apply_coe (CutT a t))

private theorem schwartzToTestFunctionMulCLM_comm (a b : D(E)) (f : S(E)) :
    schwartzToTestFunctionMulCLM a (testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM b f)) =
      schwartzToTestFunctionMulCLM b (testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM a f)) := by
  ext x
  rw [schwartzToTestFunctionMulCLM_apply, schwartzToTestFunctionMulCLM_apply]
  change a x * schwartzToTestFunctionMulCLM b f x = b x * schwartzToTestFunctionMulCLM a f x
  rw [schwartzToTestFunctionMulCLM_apply, schwartzToTestFunctionMulCLM_apply, mul_left_comm]

private theorem testTensor_cut_mul_pure (a b : D(A) × D(B)) (f : S(A)) (g : S(B)) :
    (CutT a).completion (MulT b (Completion.coe' (α := InductiveTensor S(A) S(B)) (f ⊗ₜ[ℂ] g))) =
      Completion.coe' (α := InductiveTensor D(A) D(B))
        (schwartzToTestFunctionMulCLM a.1 (testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM b.1 f)) ⊗ₜ[ℂ]
         schwartzToTestFunctionMulCLM a.2 (testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM b.2 g))) :=
  (congrArg (CutT a).completion (testTensor_mul_pure b f g)).trans ((CutT a).completion_apply_coe _)

private theorem testTensor_comm (a b : D(A) × D(B)) (z : Cι(S(A), S(B))) :
    (CutT a).completion (MulT b z) = (CutT b).completion (MulT a z) := by
  refine DFunLike.congr_fun (testCompletedTensor_ext
    ((CutT a).completion.comp (MulT b)) ((CutT b).completion.comp (MulT a)) ?_) z
  intro f g
  exact (testTensor_cut_mul_pure a b f g).trans ((congrArg (Completion.coe' (α := InductiveTensor D(A) D(B)))
    (congrArg₂ (TensorProduct.tmul ℂ) (schwartzToTestFunctionMulCLM_comm a.1 b.1 f)
      (schwartzToTestFunctionMulCLM_comm a.2 b.2 g))).trans
    (testTensor_cut_mul_pure b a f g).symm)

private theorem testTensor_mul_eval
    (e : C ≃ₜ A × B) (V : Cι(S(A), S(B)) ≃L[ℂ] S(C))
    (hV : ∀ (a : S(A)) (b : S(B)) x, V (Completion.coe' (α := InductiveTensor S(A) S(B))
        (a ⊗ₜ[ℂ] b)) x = a (e x).1 * b (e x).2)
    (a : D(A) × D(B)) (x : C) (z : Cι(S(A), S(B))) :
    V (MulT a z) x = (a.1 (e x).1 * a.2 (e x).2) * V z x := by
  let ev := (schwartzEval x).comp V.toContinuousLinearMap
  refine DFunLike.congr_fun (testCompletedTensor_ext (ev.comp (MulT a))
    ((a.1 (e x).1 * a.2 (e x).2) • ev) ?_) z
  intro f g
  change V ((InclT).completion ((CutT a).completion _)) x = _ * V _ x
  erw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
  change V (Completion.coe' (α := InductiveTensor S(A) S(B))
      (testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM a.1 f) ⊗ₜ[ℂ]
    testFunctionToSchwartzCLM (schwartzToTestFunctionMulCLM a.2 g))) x = _
  rw [hV, hV]; change schwartzToTestFunctionMulCLM a.1 f _ * schwartzToTestFunctionMulCLM a.2 g _ = _
  rw [schwartzToTestFunctionMulCLM_apply, schwartzToTestFunctionMulCLM_apply]; ring

private theorem testTensor_fix
    (e : C ≃ₜ A × B) (V : Cι(S(A), S(B)) ≃L[ℂ] S(C))
    (hV : ∀ (a : S(A)) (b : S(B)) x, V (Completion.coe' (α := InductiveTensor S(A) S(B))
        (a ⊗ₜ[ℂ] b)) x = a (e x).1 * b (e x).2) (f : D(C)) (b : D(A) × D(B))
    (hb : ∀ x ∈ tsupport (f : C → ℂ), b.1 (e x).1 * b.2 (e x).2 = 1) :
    MulT b (V.symm (testFunctionToSchwartzCLM f)) = V.symm (testFunctionToSchwartzCLM f) := by
  apply V.injective; apply SchwartzMap.ext; intro x
  rw [testTensor_mul_eval e V hV, V.apply_symm_apply]
  change (b.1 (e x).1 * b.2 (e x).2) * f x = f x
  by_cases h : x ∈ tsupport (f : C → ℂ)
  · rw [hb x h, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

/- On the Schwartz tensor product a product cutoff acts by pointwise multiplication.
The inverse sends a compact test to its Schwartz kernel inverse, then cuts off both
factors. Commutation makes this independent of the choice of cutoff. -/
section TestTensorKernel

private local instance : CompleteSpace D(C) := completeSpace_testFunction

variable
    (e : C ≃ₜ A × B) (V : Cι(S(A), S(B)) ≃L[ℂ] S(C))
    (hV : ∀ (a : S(A)) (b : S(B)) x, V (Completion.coe' (α := InductiveTensor S(A) S(B))
        (a ⊗ₜ[ℂ] b)) x = a (e x).1 * b (e x).2)

private def testTensorForward (V : Cι(S(A), S(B)) ≃L[ℂ] S(C)) :=
  V.toContinuousLinearMap.comp (Completion.toComplL.comp InclT)

private def testTensorBack (V : Cι(S(A), S(B)) ≃L[ℂ] S(C)) :=
  V.symm.toContinuousLinearMap.comp (testFunctionToSchwartzCLM (E := C))

local notation "J" => testTensorBack V

include hV in
private theorem testTensor_glue :
    ∃ Q : D(C) →L[ℂ] Cι(D(A), D(B)), ∀ b f, MulT b (J f) = J f →
      Q f = (CutT b).completion (J f) := by
  have hp : PolynormableSpace ℂ Cι(D(A), D(B)) := polynormableSpace_completion
  let : Module ℝ Cι(D(A), D(B)) := Module.compHom Cι(D(A), D(B)) (algebraMap ℝ ℂ)
  let : IsScalarTower ℝ ℂ Cι(D(A), D(B)) := IsScalarTower.of_compHom ℝ ℂ Cι(D(A), D(B))
  let : LocallyConvexSpace ℝ Cι(D(A), D(B)) := (PolynormableSpace.withSeminorms ℂ Cι(D(A), D(B))).toLocallyConvexSpace
  let : ContinuousSMul ℝ Cι(D(A), D(B)) := MulAction.continuousSMul_compHom
    (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal
  exact testFunction_glue_cutoffs J MulT (fun b : D(A) × D(B) ↦ (CutT b).completion) testTensor_comm (fun K ↦ by
    obtain ⟨a, ha⟩ := compactTestOne ⟨_, K.isCompact.image (continuous_fst.comp e.continuous)⟩
    obtain ⟨b, hb⟩ := compactTestOne ⟨_, K.isCompact.image (continuous_snd.comp e.continuous)⟩
    exact ⟨(a, b), fun f hf ↦ testTensor_fix e V hV f (a, b) fun x hx ↦ by
      exact (congrArg₂ (· * ·) (ha _ ⟨x, hf hx, rfl⟩) (hb _ ⟨x, hf hx, rfl⟩)).trans (one_mul _)⟩)

include hV in
private theorem testTensor_fixed (f : D(C)) : ∃ b, MulT b (J f) = J f := by
  obtain ⟨a, ha⟩ := compactTestOne ⟨_, f.hasCompactSupport.image (continuous_fst.comp e.continuous)⟩
  obtain ⟨b, hb⟩ := compactTestOne ⟨_, f.hasCompactSupport.image (continuous_snd.comp e.continuous)⟩
  exact ⟨(a, b), testTensor_fix e V hV f (a, b) fun x hx ↦
    (congrArg₂ (· * ·) (ha _ ⟨x, hx, rfl⟩) (hb _ ⟨x, hx, rfl⟩)).trans (one_mul _)⟩

private theorem schwartzToTestFunctionMulCLM_fixed [FiniteDimensional ℝ E] (f : D(E)) :
    ∃ a : D(E), schwartzToTestFunctionMulCLM a (testFunctionToSchwartzCLM f) = f := by
  obtain ⟨a, ha⟩ := compactTestOne ⟨_, f.hasCompactSupport⟩
  refine ⟨a, TestFunction.ext fun x ↦ ?_⟩
  rw [schwartzToTestFunctionMulCLM_apply]
  change a x * f x = f x
  by_cases h : x ∈ tsupport (f : E → ℂ)
  · rw [ha _ h, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

variable (P : InductiveTensor D(A) D(B) →L[ℂ] D(C)) (Q : D(C) →L[ℂ] Cι(D(A), D(B)))

local notation "H" => ContinuousLinearMap.fromCompletion P

private theorem testTensor_cut_incl_pure (f : D(A)) (g : D(B)) :
    let t : InductiveTensor D(A) D(B) := f ⊗ₜ[ℂ] g
    ∃ b : D(A) × D(B), (CutT b).completion (Completion.coe' (InclT t)) = Completion.coe' t := by
  intro t
  let a := (schwartzToTestFunctionMulCLM_fixed f).choose
  let b := (schwartzToTestFunctionMulCLM_fixed g).choose
  refine ⟨(a, b), ((CutT (a, b)).completion_apply_coe (InclT t)).trans ?_⟩
  exact congrArg (Completion.coe' (α := InductiveTensor D(A) D(B)))
    (congrArg₂ (TensorProduct.tmul ℂ) (schwartzToTestFunctionMulCLM_fixed f).choose_spec
      (schwartzToTestFunctionMulCLM_fixed g).choose_spec)

private theorem testTensor_left
    (hP : ∀ t : InductiveTensor D(A) D(B), testFunctionToSchwartzCLM (P t) = testTensorForward V t)
    (hQ : ∀ (b : D(A) × D(B)) (f : D(C)), MulT b (J f) = J f → Q f = (CutT b).completion (J f)) :
    Q.comp H = ContinuousLinearMap.id ℂ Cι(D(A), D(B)) := by
  refine testCompletedTensor_ext _ _ fun f g ↦ ?_
  let t : InductiveTensor D(A) D(B) := f ⊗ₜ[ℂ] g
  let fixed := testTensor_cut_incl_pure f g
  let b := fixed.choose
  have hJ : J (P t) = Completion.coe' (InclT t) :=
    (congrArg V.symm (hP t)).trans (V.symm_apply_apply _)
  have hR : (CutT b).completion (J (P t)) = Completion.coe' t :=
    (congrArg (CutT b).completion hJ).trans fixed.choose_spec
  have hm : MulT b (J (P t)) = J (P t) :=
    (congrArg (InclT).completion hR).trans (((InclT).completion_apply_coe t).trans hJ.symm)
  exact (congrArg Q (P.fromCompletion_apply_coe t)).trans ((hQ b (P t) hm).trans hR)

private theorem testTensor_intertwines
    (hP : ∀ t : InductiveTensor D(A) D(B), testFunctionToSchwartzCLM (P t) = testTensorForward V t) (z : Cι(D(A), D(B))) :
    V ((InclT).completion z) = testFunctionToSchwartzCLM (H z) := by
  refine DFunLike.congr_fun (testCompletedTensor_ext (V.toContinuousLinearMap.comp (InclT).completion)
    (testFunctionToSchwartzCLM.comp H) ?_) z
  intro a b
  change V ((InclT).completion (Completion.coe' (α := InductiveTensor D(A) D(B)) (a ⊗ₜ[ℂ] b))) =
    testFunctionToSchwartzCLM (P.fromCompletion _)
  erw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.fromCompletion_apply_coe]
  exact (hP _).symm

include hV in
private theorem testTensor_right
    (hP : ∀ t : InductiveTensor D(A) D(B), testFunctionToSchwartzCLM (P t) = testTensorForward V t)
    (hQ : ∀ (b : D(A) × D(B)) (f : D(C)), MulT b (J f) = J f → Q f = (CutT b).completion (J f)) (f : D(C)) :
    H (Q f) = f := by
  let fixed := testTensor_fixed e V hV f
  let b := fixed.choose
  have hb : MulT b (J f) = J f := fixed.choose_spec
  rw [hQ _ _ hb]
  have hi := testTensor_intertwines (V := V) (P := P) (hP := hP) ((CutT b).completion (J f))
  have he := (hi.symm.trans (congrArg V hb)).trans (V.apply_symm_apply _)
  exact TestFunction.ext fun x ↦ congrArg (fun F : S(C) ↦ F x) he

include hV in
private theorem testTensor_seq
    (hP : ∀ t : InductiveTensor D(A) D(B), testFunctionToSchwartzCLM (P t) = testTensorForward V t)
    (hQ : ∀ (b : D(A) × D(B)) (f : D(C)), MulT b (J f) = J f → Q f = (CutT b).completion (J f)) (f : D(C)) :
    ∃ s : ℕ → InductiveTensor D(A) D(B),
    Tendsto (fun n ↦ H (Completion.coe' (s n))) atTop (𝓝 f) := by
  let fixed := testTensor_fixed e V hV f
  let b := fixed.choose
  have hb : MulT b (J f) = J f := fixed.choose_spec
  have hright := testTensor_right (e := e) (V := V) (hV := hV) (P := P) (hP := hP) (Q := Q) (hQ := hQ)
  have hd := V.surjective.denseRange.comp (Completion.denseRange_coe (α := InductiveTensor S(A) S(B))) V.continuous
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp (hd (testFunctionToSchwartzCLM f))
  choose t htval using hs
  have ht' : Filter.Tendsto (fun n ↦ Completion.coe' (t n)) Filter.atTop (𝓝 (J f)) := by
    have ht1 := (V.symm.continuous.tendsto (testFunctionToSchwartzCLM f)).comp ht
    exact ht1.congr fun n ↦ (congrArg V.symm (htval n).symm).trans (V.symm_apply_apply _)
  have ht2 := (((H).continuous.comp (CutT b).completion.continuous).tendsto (J f)).comp ht'
  refine ⟨fun n ↦ CutT b (t n), ?_⟩
  have he : H ((CutT b).completion (J f)) = f := (congrArg H (hQ b f hb).symm).trans (hright f)
  simpa only [Function.comp_def, ContinuousLinearMap.completion_apply_coe, he] using ht2

end TestTensorKernel

private theorem testFunction_tensor_of_schwartz_kernel
    (e : C ≃ₜ A × B) (V : Cι(S(A), S(B)) ≃L[ℂ] S(C))
    (hV : ∀ (a : S(A)) (b : S(B)) x, V (Completion.coe' (α := InductiveTensor S(A) S(B))
        (a ⊗ₜ[ℂ] b)) x = a (e x).1 * b (e x).2) :
    ∃ H : Cι(D(A), D(B)) ≃L[ℂ] D(C),
      (∀ (a : D(A)) (b : D(B)) x, H (Completion.coe' (α := InductiveTensor D(A) D(B))
        (a ⊗ₜ[ℂ] b)) x = a (e x).1 * b (e x).2) ∧
      ∀ f, ∃ s : ℕ → InductiveTensor D(A) D(B), Filter.Tendsto
        (fun n ↦ H (Completion.coe' (s n))) Filter.atTop (𝓝 f) := by
  let : CompleteSpace D(C) := completeSpace_testFunction
  let U := testTensorForward V
  have hU (a : D(A)) (b : D(B)) (x : C) : U (a ⊗ₜ[ℂ] b) x = a (e x).1 * b (e x).2 :=
    hV (testFunctionToSchwartzCLM a) (testFunctionToSchwartzCLM b) x
  let prod := localizedTensor_product e U hU
  let glue := testTensor_glue e V hV
  let P := prod.choose
  let Q := glue.choose
  have hl := testTensor_left (V := V) (P := P) (Q := Q)
    (hP := prod.choose_spec) (hQ := glue.choose_spec)
  have hr := testTensor_right (e := e) (hV := hV) (V := V) (P := P) (Q := Q)
    (hP := prod.choose_spec) (hQ := glue.choose_spec)
  let iso := ContinuousLinearEquiv.equivOfInverse P.fromCompletion Q (fun z ↦ DFunLike.congr_fun hl z) hr
  refine ⟨iso, fun a b x ↦ ?_, testTensor_seq (e := e) (hV := hV) (V := V) (P := P) (Q := Q)
    (hP := prod.choose_spec) (hQ := glue.choose_spec)⟩
  change P.fromCompletion (Completion.coe' (α := InductiveTensor D(A) D(B)) (a ⊗ₜ[ℂ] b)) x = _
  erw [P.fromCompletion_apply_coe]
  exact (congrArg (fun f : S(C) ↦ f x) (prod.choose_spec _)).trans (hU a b x)

/-- Transport the Schwartz–Bruhat kernel along the real vector group presentations. -/
private theorem testTensor_schwartzKernel (e : C ≃L[ℝ] A × B) :
    ∃ V : Cι(S(A), S(B)) ≃L[ℂ] S(C), ∀ (a : S(A)) (b : S(B)) x,
      V (Completion.coe' (α := InductiveTensor S(A) S(B)) (a ⊗ₜ[ℂ] b)) x = a (e x).1 * b (e x).2 := by
  let G := Multiplicative A
  let K := Multiplicative B
  let c : G × K ≃ₜ* Multiplicative C :=
    { toEquiv := e.symm.toEquiv
      map_mul' := fun x y ↦ e.symm.map_add x y
      continuous_toFun := e.symm.continuous, continuous_invFun := e.continuous }
  obtain ⟨Ja, ha⟩ := testTensor_realCoordinates (E := A) (ContinuousMulEquiv.refl G)
  obtain ⟨Jb, hb⟩ := testTensor_realCoordinates (E := B) (ContinuousMulEquiv.refl K)
  obtain ⟨Jc, hc⟩ := testTensor_realCoordinates c
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_eval_t2
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_eval_t2
  let f := testTensorMap Ja.toContinuousLinearMap Jb.toContinuousLinearMap
  let g := testTensorMap Ja.symm.toContinuousLinearMap Jb.symm.toContinuousLinearMap
  have left : g.completion.comp f.completion = ContinuousLinearMap.id ℂ _ := by
    apply testCompletedTensor_ext
    intro x y
    change g.completion (f.completion _) = _
    erw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    change Completion.coe' (α := InductiveTensor S(A) S(B)) (Ja.symm (Ja x) ⊗ₜ[ℂ] Jb.symm (Jb y)) = _
    rw [Ja.symm_apply_apply, Jb.symm_apply_apply]; rfl
  have right : f.completion.comp g.completion = ContinuousLinearMap.id ℂ _ := by
    apply testCompletedTensor_ext
    intro x y
    change f.completion (g.completion _) = _
    erw [ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.completion_apply_coe]
    change Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat K))
      (Ja (Ja.symm x) ⊗ₜ[ℂ] Jb (Jb.symm y)) = _
    rw [Ja.apply_symm_apply, Jb.apply_symm_apply]; rfl
  let t := ContinuousLinearEquiv.equivOfInverse f.completion g.completion
    (fun z ↦ DFunLike.congr_fun left z) (fun z ↦ DFunLike.congr_fun right z)
  obtain ⟨V, hV⟩ := schwartzBruhat_kernel_equiv (G := G) (H := K)
  refine ⟨(t.trans V).trans Jc.symm, fun a b x ↦ ?_⟩
  let z : G × K := (Multiplicative.ofAdd (e x).1, Multiplicative.ofAdd (e x).2)
  have hcoord : (c z).toAdd = x := e.symm_apply_apply x
  have eval (s : SchwartzBruhat (G × K)) : Jc.symm s x = s z := by
    rw [← hcoord, ← hc, Jc.apply_symm_apply]
  change Jc.symm (V (f.completion _)) x = _
  erw [eval, ContinuousLinearMap.completion_apply_coe]
  exact (hV (Ja a) (Jb b) z.1 z.2).trans (congrArg₂ (· * ·) (ha a z.1) (hb b z.2))

private theorem testTensor_euclidean {ι κ : Type*} [Fintype ι] [Fintype κ] :
    let W := InductiveTensor D(EuclideanSpace ℝ ι) D(EuclideanSpace ℝ κ)
    ∃ H : Completion W ≃L[ℂ] D(EuclideanSpace ℝ (ι ⊕ κ)),
      (∀ (a : D(EuclideanSpace ℝ ι)) (b : D(EuclideanSpace ℝ κ)) (x : EuclideanSpace ℝ (ι ⊕ κ)),
          H (Completion.coe' (α := W) (a ⊗ₜ[ℂ] b)) x =
          a (WithLp.toLp 2 (fun i : ι ↦ x (.inl i))) * b (WithLp.toLp 2 (fun j : κ ↦ x (.inr j)))) ∧
        ∀ f, ∃ s : ℕ → W, Filter.Tendsto (fun n ↦ H (s n : Completion W)) Filter.atTop (𝓝 f) := by
  intro W
  let L : EuclideanSpace ℝ (ι ⊕ κ) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :=
    PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : ι ⊕ κ ↦ ℝ)
  let e := WithLp.homeomorphProd 2 (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ)
  let C : EuclideanSpace ℝ (ι ⊕ κ) ≃L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ κ :=
    { L.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ _) with
      continuous_toFun := e.continuous.comp L.continuous
      continuous_invFun := L.symm.continuous.comp e.symm.continuous }
  let h := testTensor_schwartzKernel C
  exact testFunction_tensor_of_schwartz_kernel C.toHomeomorph h.choose h.choose_spec

end TensorProof

end TestFunctionTensor

/-- Paper: Remark 5.3.2.4, p. 246.
Products of test functions define a map from the inductive tensor product with
sequentially dense range. The completed inductive tensor product is isomorphic
to the test space on the product by the same pure tensor formula.
Deviation: The isomorphism uses the completion, as required for the full test space. -/
theorem testFunction_inductiveTensor_equiv :
    let W := InductiveTensor 𝒟(ι) 𝒟(κ)
    letI : ContinuousSMul ℂ W := WithSeminorms.continuousSMul (E := W)
      (withGeneratingSeminorms_spec _ _)
    letI : UniformContinuousConstSMul ℂ W := uniformContinuousConstSMul_of_continuousConstSMul ℂ W
    ∃ e : UniformSpace.Completion W ≃L[ℂ] 𝒟(ι ⊕ κ),
      (∀ (f : 𝒟(ι)) (g : 𝒟(κ)) (x : Eᵣ(ι ⊕ κ)),
        e (UniformSpace.Completion.coe' (α := W) (f ⊗ₜ[ℂ] g)) x = factors(f, g, x)) ∧
      ∀ h : 𝒟(ι ⊕ κ), ∃ s : ℕ → W,
        Tendsto (fun n ↦ e (s n : UniformSpace.Completion W))
          atTop (𝓝 h) := by
  intro W
  exact TestFunctionTensor.testTensor_euclidean (ι := ι) (κ := κ)

/-- Iterated line derivatives are iterated derivatives along the line. -/
private theorem lineDerivPow_apply_eq_iteratedDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℂ)) (y : E) (s : ℝ) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
        →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) φ) (y + s • v) =
      iteratedDeriv k (fun t : ℝ ↦ φ (y + t • v)) s := by
  induction k generalizing φ s with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, iteratedDeriv_succ', ih]
    congr 1
    funext t
    rw [TestFunction.lineDerivOpCLM_eq_lineDerivCLM]
    rw [TestFunction.lineDerivCLM_apply_of_le (𝕜 := ℂ) (n := ⊤) (k := ⊤) le_rfl, lineDeriv]
    have h : (fun u : ℝ ↦ φ (y + t • v + u • v)) = fun u ↦ (fun w : ℝ ↦ φ (y + w • v)) (u + t) := by
      funext u; congr 1; rw [add_smul, add_assoc, add_comm (u • v)]
    rw [h]
    exact (deriv_comp_add_const (f := fun w : ℝ ↦ φ (y + w • v)) (a := t)
        (x := 0)).trans (by rw [zero_add])

private theorem lineDerivPow_apply_eq_iteratedDeriv_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (k : ℕ) (φ : 𝓓((⊤ : Opens E), ℂ)) (y : E) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
        →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) φ) y =
      iteratedDeriv k (fun t : ℝ ↦ φ (y + t • v)) 0 := by
  have h := lineDerivPow_apply_eq_iteratedDeriv v k φ y 0
  rwa [zero_smul, add_zero] at h

/-- `𝓓_K` is not normable: a zero neighbourhood of test functions only controls finitely many
derivatives on the unit ball, so some `∂ₑⁿ δ₀` is unbounded on it. -/
private theorem exists_lineDeriv_unbounded_on_nhds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e : E) (he : e ≠ 0)
    (U : Set 𝓓((⊤ : Opens E), ℂ)) (hU : U ∈ 𝓝 (0 : 𝓓((⊤ : Opens E), ℂ))) :
    ∃ n : ℕ, ∀ M : ℝ, ∃ g ∈ U,
      M ≤ ‖(((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) e : 𝓓((⊤ : Opens E), ℂ)
          →L[ℂ] 𝓓((⊤ : Opens E), ℂ))) ^ n) g 0‖ := by
  classical
  let K : Compacts E := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
  have hK : (K : Set E) ⊆ ((⊤ : Opens E) : Set E) := fun _ _ ↦ trivial
  let ιK : 𝓓_{K}(E, ℂ) →L[ℝ] 𝓓((⊤ : Opens E), ℂ) := TestFunction.ofSupportedInCLM ℝ hK
  have hU' : ιK ⁻¹' U ∈ 𝓝 (0 : 𝓓_{K}(E, ℂ)) := by
    apply ιK.continuous.continuousAt.preimage_mem_nhds
    rw [map_zero]; exact hU
  obtain ⟨s, r, hr, hsub⟩ :=
    ((ContDiffMapSupportedIn.withSeminorms' ℝ E ℂ ⊤ K).mem_nhds_iff 0 _).mp hU'
  set N := s.sup id
  have hmem : ∀ g : 𝓓_{K}(E, ℂ),
      (∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ r / 2) → ιK g ∈ U := by
    intro g hg
    apply hsub
    rw [Seminorm.mem_ball, sub_zero]
    refine lt_of_le_of_lt (Seminorm.finset_sup_apply_le (a := r / 2) (by positivity) fun j hj ↦ ?_)
      (by linarith)
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦ ?_
    rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (by positivity)]
    intro x _
    exact hg i ((Finset.mem_Iic.mp hi).trans (Finset.le_sup (f := id) hj)) x
  -- the profile `g₀ y = χ y * ⟪e, y⟫ ^ (N + 1)`
  let χ : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let ψ : E → ℂ := fun y ↦ ((χ y * (inner ℝ e y) ^ (N + 1) : ℝ) : ℂ)
  have hψ : ContDiff ℝ (∞) ψ :=
    Complex.ofRealCLM.contDiff.comp (χ.contDiff.mul ((contDiff_const.inner ℝ contDiff_id).pow _))
  have hψ0 : ∀ y : E, 1 ≤ ‖y‖ → ψ y = 0 := fun y hy ↦ by
    have : χ y = 0 := χ.zero_of_le_dist (by simpa using hy)
    simp [ψ, this]
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) 1) fun y hy ↦ by
      have h1 : ¬ ‖y‖ ≤ 1 := by simpa using hy
      exact hψ0 y (le_of_lt (not_le.mp h1))
  have hb : ∀ i : ℕ, ∃ C, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ C := fun i ↦
    Continuous.bounded_above_of_compact_support
      (hψ.continuous_iteratedFDeriv (by exact_mod_cast le_top)) (hψc.iteratedFDeriv i)
  choose C hC using hb
  set B : ℝ := 1 + ∑ i ∈ Finset.range (N + 1), |C i| with hB
  have hB0 : 0 < B := by positivity
  have hCB : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ B := fun i hi y ↦ by
    refine (hC i y).trans ((le_abs_self _).trans ?_)
    have := Finset.single_le_sum (f := fun i ↦ |C i|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    linarith
  -- its `(N+1)`-th derivative along `e` at `0`
  set d : ℂ := iteratedDeriv (N + 1) (fun t : ℝ ↦ ψ (t • e)) 0 with hd
  have hd0 : d ≠ 0 := by
    have hev : (fun t : ℝ ↦ ψ (t • e)) =ᶠ[𝓝 0]
        fun t : ℝ ↦ t ^ (N + 1) • ((‖e‖ ^ 2) ^ (N + 1) : ℂ) := by
      have hc : Tendsto (fun t : ℝ ↦ t • e) (𝓝 0) (𝓝 0) := by
        have := (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const e
        rwa [zero_smul] at this
      filter_upwards [hc.eventually (χ.eventuallyEq_one)] with t ht
      simp only [Pi.one_apply] at ht
      simp only [ψ, ht, one_mul, real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hd, hev.iteratedDeriv_eq, iteratedDeriv_smul_const (by fun_prop),
      iteratedDeriv_fun_pow_zero]
    have : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
    simp [this, Nat.factorial_ne_zero]
  refine ⟨N + 1, fun M ↦ ?_⟩
  -- scaled copies `a • g₀ (λ • y)`
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  set lam : ℝ := max 1 (M * B / (r / 2 * ‖d‖)) with hlam
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlam0 : 0 < lam := by linarith
  set a : ℝ := r / 2 / (B * lam ^ N) with ha
  have ha0 : 0 < a := by positivity
  let G : E → ℂ := fun y ↦ a • ψ (lam • y)
  have hψl : ContDiff ℝ (∞) (fun y : E ↦ ψ (lam • y)) := hψ.comp (contDiff_const_smul lam)
  have hG : ContDiff ℝ (∞) G := hψl.const_smul a
  have hGs : support G ⊆ (K : Set E) := by
    intro y hy
    by_contra hyK
    apply hy
    have h1 : 1 < ‖y‖ := by simpa [K] using hyK
    have : 1 ≤ ‖lam • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hlam0.le]; nlinarith
    simp [G, hψ0 _ this]
  let gK : 𝓓_{K}(E, ℂ) := ContDiffMapSupportedIn.of_support_subset hG hGs
  refine ⟨ιK gK, hmem gK fun i hi y ↦ ?_, ?_⟩
  · change ‖iteratedFDeriv ℝ i G y‖ ≤ r / 2
    rw [iteratedFDeriv_const_smul_apply' (f := fun y : E ↦ ψ (lam • y)) (hψl.contDiffAt.of_le
      (by exact_mod_cast le_top)), iteratedFDeriv_comp_const_smul lam (hψ.of_le
      (by exact_mod_cast le_top)), norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg ha0.le,
      Real.norm_of_nonneg hlam0.le]
    calc a * (lam ^ i * ‖iteratedFDeriv ℝ i ψ (lam • y)‖) ≤ a * (lam ^ N * B) := by
          gcongr
          exact hCB i hi _
      _ = r / 2 := by rw [ha]; field_simp
  · have hl : ContDiff ℝ (N + 1 : ℕ) (fun t : ℝ ↦ ψ (t • e)) :=
      (hψ.comp (contDiff_id.smul contDiff_const)).of_le (by exact_mod_cast le_top)
    have hfun : (fun t : ℝ ↦ (ιK gK) (0 + t • e)) =
        fun t : ℝ ↦ a • (fun s : ℝ ↦ ψ (s • e)) (lam * t) := by
      funext t
      change a • ψ (lam • (0 + t • e)) = a • ψ ((lam * t) • e)
      rw [zero_add, smul_smul]
    rw [lineDerivPow_apply_eq_iteratedDeriv_zero, hfun, iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_comp_const_smul hl lam]
    beta_reduce
    rw [mul_zero, ← hd, norm_smul, norm_smul, norm_pow,
      Real.norm_of_nonneg ha0.le, Real.norm_of_nonneg hlam0.le]
    have h1 : M * B / (r / 2 * ‖d‖) ≤ lam := le_max_right _ _
    have h2 : M * B ≤ lam * (r / 2 * ‖d‖) := (div_le_iff₀ (by positivity)).mp h1
    have h3 : a * (lam ^ (N + 1) * ‖d‖) = lam * (r / 2 * ‖d‖) / B := by
      rw [ha]; field_simp; ring
    rw [h3, le_div_iff₀ hB0]
    linarith


/-- Line derivatives preserve vanishing on an open set. -/
private theorem lineDerivPow_apply_eq_zero_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (O : Set E) (hO : IsOpen O) (φ : 𝓓((⊤ : Opens E), ℂ))
    (hφ : ∀ z ∈ O, φ z = 0) (k : ℕ) (z : E) (hz : z ∈ O) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
        →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) φ) z = 0 := by
  rw [lineDerivPow_apply_eq_iteratedDeriv_zero]
  have hc : Tendsto (fun t : ℝ ↦ z + t • v) (𝓝 0) (𝓝 z) := by
    have := ((tendsto_id (x := 𝓝 (0 : ℝ))).smul_const v).const_add z
    rwa [zero_smul, add_zero] at this
  have hev : (fun t : ℝ ↦ φ (z + t • v)) =ᶠ[𝓝 0] fun _ ↦ 0 :=
    (hc.eventually (hO.mem_nhds hz)).mono fun t ht ↦ hφ _ ht
  rw [hev.iteratedDeriv_eq]
  simp


/-- `h ↦ ∑ₖ (∂ᵥᵏ h)(pₖ)` is a continuous functional when `‖pₖ‖ ≥ k` (locally finite sum). -/
private theorem exists_finsum_lineDerivPow_CLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (p : ℕ → E) (hp : ∀ k : ℕ, (k : ℝ) ≤ ‖p k‖) :
    ∃ T : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] ℂ, ∀ h : 𝓓((⊤ : Opens E), ℂ),
      T h = ∑ᶠ k, (((LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v : 𝓓((⊤ : Opens E), ℂ)
          →L[ℂ] 𝓓((⊤ : Opens E), ℂ)) ^ k) h) (p k) := by
  set D : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] 𝓓((⊤ : Opens E), ℂ) :=
    LineDeriv.lineDerivOpCLM ℂ 𝓓((⊤ : Opens E), ℂ) v with hD
  let Tk : ℕ → 𝓓((⊤ : Opens E), ℂ) →L[ℂ] ℂ := fun k ↦
    ((BoundedContinuousFunction.evalCLM ℂ (p k)).comp
      (TestFunction.toBoundedContinuousFunctionCLM ℂ)).comp (D ^ k)
  have hTk : ∀ k h, Tk k h = ((D ^ k) h) (p k) := fun _ _ ↦ rfl
  have hvan : ∀ (h : 𝓓((⊤ : Opens E), ℂ)) (R : ℝ), (∀ z, R < ‖z‖ → h z = 0) → ∀ k : ℕ, R < k →
      Tk k h = 0 := by
    intro h R hR k hk
    rw [hTk]
    exact lineDerivPow_apply_eq_zero_of_isOpen v {z | R < ‖z‖}
      (isOpen_lt continuous_const continuous_norm) h hR k (p k) (hk.trans_le (hp k))
  have hsum : ∀ (h : 𝓓((⊤ : Opens E), ℂ)) (R : ℝ), (∀ z, R < ‖z‖ → h z = 0) → ∀ m : ℕ, R < m →
      ∑ᶠ k, Tk k h = ∑ k ∈ Finset.range m, Tk k h := by
    intro h R hR m hm
    apply finsum_eq_sum_of_support_subset
    intro k hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hkm
    push Not at hkm
    exact hk (hvan h R hR k (hm.trans_le (by exact_mod_cast hkm)))
  have hbd : ∀ h : 𝓓((⊤ : Opens E), ℂ), ∃ R : ℝ, ∀ z, R < ‖z‖ → h z = 0 := by
    intro h
    obtain ⟨R, hR⟩ := h.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz ↦ image_eq_zero_of_notMem_tsupport fun hz' ↦ ?_⟩
    have := hR hz'
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hmax : ∀ (h : 𝓓((⊤ : Opens E), ℂ)) (R R' : ℝ), (∀ z, R < ‖z‖ → h z = 0) → R ≤ R' →
      ∀ z, R' < ‖z‖ → h z = 0 := fun h R R' hR hle z hz ↦ hR z (hle.trans_lt hz)
  let Tl : 𝓓((⊤ : Opens E), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ ∑ᶠ k, Tk k h
      map_add' := fun h₁ h₂ ↦ by
        obtain ⟨R₁, h1⟩ := hbd h₁
        obtain ⟨R₂, h2⟩ := hbd h₂
        obtain ⟨m, hm⟩ := exists_nat_gt (max R₁ R₂)
        have h1' := hmax h₁ R₁ (max R₁ R₂) h1 (le_max_left _ _)
        have h2' := hmax h₂ R₂ (max R₁ R₂) h2 (le_max_right _ _)
        have h12 : ∀ z, max R₁ R₂ < ‖z‖ → (h₁ + h₂) z = 0 := fun z hz ↦ by
          rw [IsAddApply.add_apply, h1' z hz, h2' z hz, add_zero]
        rw [hsum _ _ h12 m hm, hsum _ _ h1' m hm, hsum _ _ h2' m hm, ← Finset.sum_add_distrib]
        simp only [map_add]
      map_smul' := fun a h ↦ by
        obtain ⟨R, hR⟩ := hbd h
        obtain ⟨m, hm⟩ := exists_nat_gt R
        have haR : ∀ z, R < ‖z‖ → (a • h) z = 0 := fun z hz ↦ by
          rw [IsSMulApply.smul_apply, hR z hz, smul_zero]
        rw [hsum _ _ haR m hm, hsum h R hR m hm, RingHom.id_apply, Finset.smul_sum]
        simp only [map_smul] }
  have hcont : Continuous Tl := by
    refine (TestFunction.continuous_iff_continuous_comp Tl).mpr fun K hK ↦ ?_
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨m, hm⟩ := exists_nat_gt R
    have hK' : ∀ φ : 𝓓_{K}(E, ℂ), ∀ z, R < ‖z‖ → (TestFunction.ofSupportedIn hK φ) z = 0 := by
      intro φ z hz
      have hzK : z ∉ (K : Set E) := fun hzK ↦ by
        have := hR hzK
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      exact φ.zero_on_compl hzK
    have heq : (Tl ∘ TestFunction.ofSupportedIn hK) =
        fun φ ↦ ∑ k ∈ Finset.range m, Tk k (TestFunction.ofSupportedIn hK φ) :=
      funext fun φ ↦ hsum _ R (hK' φ) m hm
    rw [heq]
    exact continuous_finsetSum _ fun k _ ↦
      (Tk k).continuous.comp (TestFunction.continuous_ofSupportedIn hK)
  exact ⟨⟨Tl, hcont⟩, fun h ↦ rfl⟩

/-- A smooth bump equal to `1` at `x` and vanishing off the ball of radius `1/2`. -/
private theorem exists_bump_testFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) :
    ∃ f : 𝓓((⊤ : Opens E), ℂ), f x = 1 ∧ ∀ y, 1 / 2 ≤ dist y x → f y = 0 := by
  let b : ContDiffBump x := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨⟨fun y ↦ ((b y : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, by simp⟩, ?_, fun y hy ↦ ?_⟩
  · change ((b x : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num)), Complex.ofReal_one]
  · change ((b y : ℝ) : ℂ) = 0
    rw [b.zero_of_le_dist hy, Complex.ofReal_zero]

/-- Pure tensors are jointly continuous at zero for the projective topology (copy of the private
`continuousAt_projectiveTensor_tmul_zero` of AppC Sec2a_part2). -/
private theorem continuousAt_projectiveTensor_tmul_zero' (X Y : Type*)
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] :
    @ContinuousAt (X × Y) (ProjectiveTensor X Y) _ _ (fun v ↦ v.1 ⊗ₜ[ℂ] v.2) 0 := by
  let tmul : X × Y → ProjectiveTensor X Y := fun v ↦ v.1 ⊗ₜ[ℂ] v.2
  have hzero : tmul 0 = 0 := TensorProduct.zero_tmul _ _
  have hws : WithSeminorms (E := ProjectiveTensor X Y) (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      ContinuousAt (fun v : X × Y ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val) := ⟨rfl⟩
  change Tendsto tmul (𝓝 0) (𝓝 (tmul 0))
  rw [hzero, (SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp hws, tendsto_iInf]
  intro p
  rw [tendsto_comap_iff]
  have hp := p.property.tendsto
  change Tendsto (p.val ∘ tmul) (𝓝 0) (𝓝 (p.val (tmul 0))) at hp
  rwa [hzero, show p.val (0 : ProjectiveTensor X Y) = 0 from map_zero p.val] at hp

/-- Soft part: a continuous `L` out of the projective tensor product, a functional `T` and
"coefficient" maps `lam n` with `T (L ((c • fₙ) ⊗ g)) = c * lam n g` cannot coexist if every zero
neighbourhood of `Y` leaves some `lam n` unbounded. -/
private theorem false_of_projectiveTensor_unbounded {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [Module ℝ X] [ContinuousSMul ℝ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (L : ProjectiveTensor X Y →L[ℂ] Z) (T : Z →L[ℂ] ℂ) (lam : ℕ → Y → ℂ)
    (hT : ∀ n : ℕ, ∃ f : X, ∀ (c : ℝ) (g : Y), T (L ((c • f) ⊗ₜ[ℂ] g)) = c * lam n g)
    (hY : ∀ U ∈ 𝓝 (0 : Y), ∃ n : ℕ, ∀ M : ℝ, ∃ g ∈ U, M ≤ ‖lam n g‖) : False := by
  have hβ : ContinuousAt (fun v : X × Y ↦ T (L (v.1 ⊗ₜ[ℂ] v.2))) 0 :=
    (T.continuous.comp L.continuous).continuousAt.comp
      (continuousAt_projectiveTensor_tmul_zero' X Y)
  have hmem : {v : X × Y | ‖T (L (v.1 ⊗ₜ[ℂ] v.2))‖ < 1} ∈ 𝓝 ((0 : X), (0 : Y)) := by
    refine hβ.preimage_mem_nhds (t := {w : ℂ | ‖w‖ < 1}) ?_
    have hz : ((0 : X) ⊗ₜ[ℂ] (0 : Y) : ProjectiveTensor X Y) = (0 : ProjectiveTensor X Y) :=
      TensorProduct.zero_tmul _ _
    have hL0 : L (0 : ProjectiveTensor X Y) = 0 := map_zero L
    have h0 : T (L ((0 : X × Y).1 ⊗ₜ[ℂ] (0 : X × Y).2)) = 0 := by
      change T (L ((0 : X) ⊗ₜ[ℂ] (0 : Y))) = 0
      rw [hz, hL0, map_zero]
    rw [h0]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨n, hn⟩ := hY U₂ hU₂
  obtain ⟨f, hf⟩ := hT n
  have hcont : Continuous (fun c : ℝ ↦ c • f) := continuous_id.smul continuous_const
  have hsmul : Tendsto (fun c : ℝ ↦ c • f) (𝓝 0) (𝓝 0) := by
    have h := hcont.tendsto 0
    rwa [zero_smul] at h
  obtain ⟨c, hcU, hc⟩ := ((hsmul.eventually hU₁).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  have hc0 : (0 : ℝ) < c := hc
  obtain ⟨g, hgU, hg⟩ := hn (1 / c)
  have hlt : ‖T (L ((c • f) ⊗ₜ[ℂ] g))‖ < 1 := hsub (Set.mk_mem_prod hcU hgU)
  rw [hf c g, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at hlt
  have := (div_le_iff₀' hc0).mp hg
  linarith

/-- Normal-direction-free product rule: differentiating a product in a tangential direction. -/
private theorem lineDerivPow_factors [DecidableEq ι] [DecidableEq κ] (j₀ : κ) (f : 𝒟(ι)) (g : 𝒟(κ))
    (h : 𝒟(ι ⊕ κ))
    (hh : ∀ z, h z = factors(f, g, z)) (k : ℕ) (z : Eᵣ(ι ⊕ κ)) :
    (((LineDeriv.lineDerivOpCLM ℂ 𝒟(ι ⊕ κ) (EuclideanSpace.single (Sum.inr j₀ : ι ⊕ κ) (1 : ℝ)) :
      𝒟(ι ⊕ κ) →L[ℂ] 𝒟(ι ⊕ κ)) ^ k) h) z =
      factors(f, ((LineDeriv.lineDerivOpCLM ℂ 𝒟(κ)
          (EuclideanSpace.single j₀ (1 : ℝ) : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ)) ^ k) g, z) := by
  rw [lineDerivPow_apply_eq_iteratedDeriv_zero, lineDerivPow_apply_eq_iteratedDeriv_zero]
  have hfun : (fun t : ℝ ↦ h (z + t • EuclideanSpace.single (Sum.inr j₀ : ι ⊕ κ) (1 : ℝ))) =
      fun t : ℝ ↦ f (WithLp.toLp 2 (fun i : ι ↦ z (Sum.inl i))) *
        g (WithLp.toLp 2 (fun j : κ ↦ z (Sum.inr j)) + t • EuclideanSpace.single j₀ (1 : ℝ)) := by
    funext t
    rw [hh]
    congr 2
    · ext i; simp
    · ext j; simp [PiLp.single_apply]
  rw [hfun, iteratedDeriv_const_mul_field]


/-- An infinite-order distribution `T = ∑ₙ δ_{(xₙ, 0)} ∘ ∂_{(0,e)}ⁿ` (locally finite, `xₙ → ∞`), and
bumps `fₙ` with `fₙ (x_k) = δ_{kn}`: on products `(c • fₙ) ⊗ g` it gives `c * (∂ₑⁿ g) 0`. -/
private theorem exists_infiniteOrder_functional [Nonempty ι] [Nonempty κ] :
    ∃ (T : 𝒟(ι ⊕ κ) →L[ℂ] ℂ) (e : Eᵣ(κ)), e ≠ 0 ∧ ∀ n : ℕ, ∃ f : 𝒟(ι),
      ∀ (c : ℝ) (g : 𝒟(κ)) (h : 𝒟(ι ⊕ κ)), (∀ z, h z = factors(c • f, g, z)) →
        T h = c * ((LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) (e : Eᵣ(κ)) : 𝒟(κ) →L[ℂ] 𝒟(κ)) ^ n) g 0 := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  let p : ℕ → Eᵣ(ι ⊕ κ) := fun k ↦ EuclideanSpace.single (Sum.inl i₀) (k : ℝ)
  obtain ⟨T, hT⟩ := exists_finsum_lineDerivPow_CLM
    (EuclideanSpace.single (Sum.inr j₀ : ι ⊕ κ) (1 : ℝ)) p (fun k ↦ by simp [p])
  refine ⟨T, EuclideanSpace.single j₀ 1, by simp, fun n ↦ ?_⟩
  obtain ⟨f, hf1, hf0⟩ := exists_bump_testFunction (EuclideanSpace.single i₀ (n : ℝ) : Eᵣ(ι))
  refine ⟨f, fun c g h hh ↦ ?_⟩
  have e1 : ∀ k : ℕ, (WithLp.toLp 2 (fun i : ι ↦ p k (Sum.inl i)) : Eᵣ(ι)) =
      EuclideanSpace.single i₀ (k : ℝ) := fun k ↦ by
    ext i; simp [p, PiLp.single_apply]
  have e2 : ∀ k : ℕ, (WithLp.toLp 2 (fun j : κ ↦ p k (Sum.inr j)) : Eᵣ(κ)) = 0 := fun k ↦ by
    ext j; simp [p]
  rw [hT h, finsum_eq_single _ n]
  · rw [lineDerivPow_factors j₀ (c • f) g h hh n (p n), e1, e2, IsSMulApply.smul_apply, hf1]
    simp
  · intro k hk
    rw [lineDerivPow_factors j₀ (c • f) g h hh k (p k), e1, e2, IsSMulApply.smul_apply,
      hf0 _ ?_]
    · simp
    rw [EuclideanSpace.single, EuclideanSpace.single, PiLp.dist_single_same, Real.dist_eq]
    have : (1 : ℤ) ≤ |(k : ℤ) - n| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hk))
    have h' : (1 : ℝ) ≤ |(k : ℝ) - n| := by exact_mod_cast this
    linarith

-- TODO(paper-gap): If the tangential dimension is zero, its test space is ℂ
-- and the projective and inductive tensor products agree.

/-- Paper: Remark 5.3.2.4, p. 246.
In positive dimensions the product of test functions is not represented by a
continuous linear map out of the projective tensor product.
Deviation: The exception of a zero-dimensional factor is excluded explicitly. -/
theorem testFunction_no_projectiveTensor_product [Nonempty ι] [Nonempty κ] :
    ¬ ∃ L : ProjectiveTensor 𝒟(ι) 𝒟(κ) →L[ℂ] 𝒟(ι ⊕ κ),
      ∀ (f : 𝒟(ι)) (g : 𝒟(κ)) (x : Eᵣ(ι ⊕ κ)),
        L (f ⊗ₜ[ℂ] g) x = factors(f, g, x) := by
  rintro ⟨L, hL⟩
  obtain ⟨T, e, he, hT⟩ := exists_infiniteOrder_functional (ι := ι) (κ := κ)
  exact false_of_projectiveTensor_unbounded L T
    (fun n g ↦ (((LineDeriv.lineDerivOpCLM ℂ 𝒟(κ) e : 𝒟(κ) →L[ℂ] 𝒟(κ)) ^ n) g) 0)
    (fun n ↦ (hT n).imp fun f hf c g ↦ hf c g _ (hL (c • f) g))
    (fun U hU ↦ exists_lineDeriv_unbounded_on_nhds e he U hU)

end CoordinatePlane

section ComplexOrigin

open scoped MvPowerSeries.WithPiTopology

local notation "𝒟ℂ" => 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℂ)
local notation "∂x" => LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) (1 : ℂ)
local notation "∂y" => LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) Complex.I

/-- Paper: Theorem 5.3.2.5, p. 246.
The holomorphic Wirtinger operator on Schwartz functions is half of the real
directional derivative minus i times the imaginary directional derivative. -/
def schwartzWirtingerZ : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂x - Complex.I • ∂y)

/-- Paper: Theorem 5.3.2.5, p. 246.
The antiholomorphic Wirtinger operator on Schwartz functions is half of the real
directional derivative plus i times the imaginary directional derivative. -/
def schwartzWirtingerZBar : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
  (2 : ℂ)⁻¹ • (∂x + Complex.I • ∂y)

/-- Paper: Theorem 5.3.2.5, pp. 246–247.
The bundled Schwartz derivatives have the pointwise Wirtinger conventions of §3.3.2. -/
theorem schwartzWirtinger_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZ f z = wirtingerDeriv f z ∧
    schwartzWirtingerZBar f z = wirtingerConjDeriv f z := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a - b) = (a - b) / 2 ∧ (2 : ℂ)⁻¹ * (a + b) = (a + b) / 2
  constructor <;> ring

/-- Paper: Theorem 5.3.2.5, p. 246.
The sum of the Wirtinger derivatives recovers the real directional derivative. -/
theorem schwartzWirtingerZ_add_zBar (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZ f z + schwartzWirtingerZBar f z = fderiv ℝ (f : ℂ → ℂ) z 1 := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a - b) + (2 : ℂ)⁻¹ * (a + b) = a
  ring

/-- Paper: Theorem 5.3.2.5, p. 246.
The difference of the Wirtinger derivatives recovers the imaginary directional derivative
times i. -/
theorem schwartzWirtingerZBar_sub_z (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    schwartzWirtingerZBar f z - schwartzWirtingerZ f z =
      Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I := by
  let a := fderiv ℝ (f : ℂ → ℂ) z 1
  let b := Complex.I * fderiv ℝ (f : ℂ → ℂ) z Complex.I
  change (2 : ℂ)⁻¹ * (a + b) - (2 : ℂ)⁻¹ * (a - b) = b
  ring

/-- Paper: Theorem 5.3.2.5, p. 246.
A mixed Wirtinger derivative of the Dirac distribution at zero uses the negative transpose
of each Wirtinger differentiation on the test space. -/
def complexDiracDerivative (k l : ℕ) : StrongDual ℂ 𝓢(ℂ, ℂ) :=
  (-1 : ℂ)^(k + l) •
    (TemperedDistribution.delta (0 : ℂ)).comp
      ((schwartzWirtingerZ^k).comp (schwartzWirtingerZBar^l))

/-- Paper: Theorem 5.3.2.5, p. 246.
The first holomorphic derivative of the Dirac distribution is minus the test function's
holomorphic Wirtinger derivative at zero. -/
theorem complexDiracDerivative_one_zero (f : 𝓢(ℂ, ℂ)) :
    complexDiracDerivative 1 0 f = -schwartzWirtingerZ f 0 := by
  change (-1 : ℂ) ^ (1 + 0) • ((schwartzWirtingerZ ^ 1) ((schwartzWirtingerZBar ^ 0) f)) 0 = _
  simp

-- TODO(paper-gap): In (5.3.2.15)–(16) only the sum of tangential
-- derivatives for each normal index is determined. For a point support,
-- take both real coordinates normal in Theorem 5.3.2.3, then change basis.

section ComplexPointSupportHelpers


/-- The LF topology makes inclusion of smooth compactly supported tests into Schwartz space continuous. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_test_schwartz_map
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ J : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ →L[ℂ] SchwartzMap E ℂ,
      ∀ f x, J f x = f x := by
  let J : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ →ₗ[ℂ] SchwartzMap E ℂ :=
    { toFun := fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  have hc : Continuous J := by
    refine (TestFunction.continuous_iff_continuous_comp J).mpr fun K hK ↦ ?_
    have he : J ∘ TestFunction.ofSupportedIn hK = (supportedToSchwartzCLM ℂ K) := by
      funext f
      ext x
      rfl
    rw [he]
    exact (supportedToSchwartzCLM ℂ K).continuous
  exact ⟨⟨J, hc⟩, fun _ _ ↦ rfl⟩

private theorem complexTemperedDistribution_eq_sum_diracDerivative_complex_coordinates :
    Nonempty (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0) ≃L[ℝ] ℂ) := by
  let : Unique (EuclideanSpace ℝ (Fin 0)) := uniqueOfSubsingleton 0
  exact ⟨EuclideanSpace.sumEquivProd.trans
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 0))).trans
      Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv)⟩

private theorem complexTemperedDistribution_eq_sum_diracDerivative_support_schwartz_pull
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E ≃L[ℝ] ℂ) (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) :
    Distribution.dsupport (fun f : SchwartzMap E ℂ ↦ T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm f)) ⊆
      D ⁻¹' Distribution.dsupport (⇑T) := by
  intro x hx
  by_contra hn
  obtain ⟨U, hU, hOpen, hxU⟩ := (Distribution.notMem_dsupport_iff _).mp hn
  apply ((Distribution.notMem_dsupport_iff _).mpr ⟨D ⁻¹' U, ?_, hOpen.preimage D.continuous, hxU⟩) hx
  intro f hf
  apply hU
  intro y hy
  change y ∈ tsupport ((f : E → ℂ) ∘ D.symm.toHomeomorph) at hy
  rw [tsupport_comp_eq_preimage _ D.symm.toHomeomorph] at hy
  have hh := hf hy
  change D (D.symm y) ∈ U at hh
  simpa only [D.apply_symm_apply] using hh

private theorem complexTemperedDistribution_eq_sum_diracDerivative_support_test_restrict
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ →L[ℂ] SchwartzMap E ℂ)
    (hJ : ∀ f x, J f x = f x) (T : StrongDual ℂ (SchwartzMap E ℂ)) :
    Distribution.dsupport (fun f ↦ T (J f)) ⊆ Distribution.dsupport (⇑T) := by
  intro x hx
  by_contra hn
  obtain ⟨U, hU, hOpen, hxU⟩ := (Distribution.notMem_dsupport_iff _).mp hn
  apply ((Distribution.notMem_dsupport_iff _).mpr ⟨U, ?_, hOpen, hxU⟩) hx
  intro f hf
  apply hU
  have he : (J f : E → ℂ) = f := funext (hJ f)
  simpa only [he] using hf

/-- A finite Schwartz seminorm bound gives finite derivative order on each compact support. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_tempered_order_finite
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : StrongDual ℂ (SchwartzMap E ℂ)) :
    ∃ N : ℕ, DistributionOrderLE
      (fun f : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ ↦ T (f.hasCompactSupport.toSchwartzMap f.contDiff)) N := by
  let q : Seminorm ℂ (SchwartzMap E ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq
  let N := s.sup Prod.snd
  refine ⟨N, fun K ↦ ?_⟩
  obtain ⟨R, hR0, hR⟩ := K.isCompact.isBounded.exists_pos_norm_le
  refine ⟨(C : ℝ) * ∑ i ∈ s, R ^ i.1, by positivity, fun f hf B hB hderiv ↦ ?_⟩
  let φ := f.hasCompactSupport.toSchwartzMap f.contDiff
  have hsemi (i : ℕ × ℕ) (hi : i ∈ s) : SchwartzMap.seminorm ℂ i.1 i.2 φ ≤ R ^ i.1 * B := by
    apply SchwartzMap.seminorm_le_bound ℂ i.1 i.2 φ (by positivity)
    intro x
    change ‖x‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (f : E → ℂ) x‖ ≤ R ^ i.1 * B
    by_cases hx : x ∈ (K : Set E)
    · have hn : i.2 ≤ N := Finset.le_sup hi
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hR x hx) _) (hderiv i.2 hn x)
        (norm_nonneg _) (pow_nonneg hR0.le _)
    · have hx' : x ∉ tsupport (iteratedFDeriv ℝ i.2 (f : E → ℂ)) :=
        fun h ↦ hx (hf ((tsupport_iteratedFDeriv_subset i.2) h))
      rw [image_eq_zero_of_notMem_tsupport hx', norm_zero, mul_zero]
      positivity
  have ht := hb φ
  simp only [smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul] at ht
  change ‖T φ‖ ≤ (C : ℝ) * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 φ at ht
  calc
    ‖T φ‖ ≤ (C : ℝ) * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 φ := ht
    _ ≤ (C : ℝ) * ∑ i ∈ s, R ^ i.1 * B := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsemi) C.coe_nonneg
    _ = ((C : ℝ) * ∑ i ∈ s, R ^ i.1) * B := by rw [← Finset.sum_mul]; ring


private theorem complexTemperedDistribution_eq_sum_diracDerivative_point_coordinate_distribution
    (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) (hT : TemperedSupportedAtOrigin T) :
    ∃ (D : EuclideanSpace ℝ (Fin 2 ⊕ Fin 0) ≃L[ℝ] ℂ)
      (V : TestFunction (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0))) ℂ ⊤ →L[ℂ] ℂ)
      (N : ℕ), DistributionOrderLE V N ∧ Distribution.dsupport (⇑V) ⊆ {0} ∧
      ∀ f, V f = T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm (f.hasCompactSupport.toSchwartzMap f.contDiff)) := by
  let E := EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)
  obtain ⟨D⟩ := complexTemperedDistribution_eq_sum_diracDerivative_complex_coordinates
  obtain ⟨J, hJ⟩ := complexTemperedDistribution_eq_sum_diracDerivative_test_schwartz_map E
  let U : StrongDual ℂ (SchwartzMap E ℂ) := T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm)
  let V := U.comp J
  have hsU : Distribution.dsupport (⇑U) ⊆ {0} := by
    intro x hx
    have he := hT (complexTemperedDistribution_eq_sum_diracDerivative_support_schwartz_pull E D T hx)
    have hx0 : x = 0 := D.injective ((show D x = 0 from he).trans (map_zero D).symm)
    exact hx0
  have hsV : Distribution.dsupport (⇑V) ⊆ {0} :=
    (complexTemperedDistribution_eq_sum_diracDerivative_support_test_restrict E J hJ U).trans hsU
  have heJ (f) : J f = f.hasCompactSupport.toSchwartzMap f.contDiff := SchwartzMap.ext (hJ f)
  obtain ⟨N, hN⟩ := complexTemperedDistribution_eq_sum_diracDerivative_tempered_order_finite E U
  have hVN : DistributionOrderLE V N := by
    have he : (fun f ↦ V f) = (fun f ↦ U (f.hasCompactSupport.toSchwartzMap f.contDiff)) :=
      funext fun f ↦ congrArg U (heJ f)
    change DistributionOrderLE (fun f ↦ V f) N
    rw [he]
    exact hN
  refine ⟨D, V, N, hVN, hsV, fun f ↦ ?_⟩
  change U (J f) = _
  rw [heJ]
  rfl

private theorem complexTemperedDistribution_eq_sum_diracDerivative_zero_dim_dual
    (T : StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 0)) ℂ)) :
    ∃ c : ℂ, ∀ f, T f = c * f 0 := by
  let E := EuclideanSpace ℝ (Fin 0)
  let one : SchwartzMap E ℂ := (show HasCompactSupport (fun _ : E ↦ (1 : ℂ)) from
    (isClosed_tsupport _).isCompact).toSchwartzMap contDiff_const
  refine ⟨T one, fun f ↦ ?_⟩
  have he : f = (f 0) • one := by
    ext x
    change f x = f 0 * (1 : ℂ)
    rw [Subsingleton.elim x 0, mul_one]
  calc T f = T ((f 0) • one) := congrArg T he
       _ = f 0 * T one := T.map_smul _ _
       _ = T one * f 0 := mul_comm _ _

private theorem complexTemperedDistribution_eq_sum_diracDerivative_single_independent
    (d₁ d₂ : DecidableEq (Fin 2 ⊕ Fin 0)) (i : Fin 2 ⊕ Fin 0) (a : ℝ) :
    @Pi.single (Fin 2 ⊕ Fin 0) (fun _ ↦ ℝ) (fun _ ↦ inferInstance) d₁ i a =
      @Pi.single (Fin 2 ⊕ Fin 0) (fun _ ↦ ℝ) (fun _ ↦ inferInstance) d₂ i a :=
  congrArg (fun d ↦ @Pi.single (Fin 2 ⊕ Fin 0) (fun _ ↦ ℝ) (fun _ ↦ inferInstance) d i a) (Subsingleton.elim d₁ d₂)
open Classical in

/-- Take both real coordinates normal in the coordinate-plane decomposition, then use density. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_point_real_decomposition
    (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) (hT : TemperedSupportedAtOrigin T) :
    ∃ (D : EuclideanSpace ℝ (Fin 2 ⊕ Fin 0) ≃L[ℝ] ℂ) (N : ℕ)
      (c : {α : (Fin 2 ⊕ Fin 0) → Fin (N + 1) // (∑ i, (α i).val) ≤ N} → ℂ),
      ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)) ℂ,
        T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm f) =
          ∑ α, c α * (coordinateDerivative
            (fun i : Fin 2 ⊕ Fin 0 ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)) ℂ)
              (WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)) : _ →L[ℂ] _)) (fun i ↦ (α.val i).val) f) 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)
  obtain ⟨D, V, N, hVN, hsV, hVS⟩ := complexTemperedDistribution_eq_sum_diracDerivative_point_coordinate_distribution T hT
  have hK : IsCompact (Distribution.dsupport (⇑V)) :=
    isCompact_singleton.of_isClosed_subset Distribution.isClosed_dsupport hsV
  have hp : Distribution.dsupport (⇑V) ⊆ Set.range (fun y : EuclideanSpace ℝ (Fin 0) ↦
      (WithLp.toLp 2 (Sum.elim (fun _ : Fin 2 ↦ (0 : ℝ)) (fun j : Fin 0 ↦ y j)) : E)) := by
    intro x hx
    have he : x = 0 := hsV hx
    refine ⟨0, ?_⟩
    rw [he]
    ext i
    cases i <;> rfl
  obtain ⟨A, hA, heA⟩ := distribution_coordinatePlane_decomposition (ι := Fin 2) (κ := Fin 0) V N hVN hK hp
  obtain ⟨U, B, hU, hB, hrep⟩ := distribution_coordinatePlane_decomposition_tempered V A (fun α ↦ (hA α).2) heA
  let W : StrongDual ℂ (SchwartzMap E ℂ) := T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm)
  have heUW : U = W := by
    apply DFunLike.ext'
    apply Continuous.ext_on (SchwartzMap.dense_hasCompactSupport (E := E) (F := ℂ)) U.continuous W.continuous
    intro f hf
    let φ : TestFunction (⊤ : TopologicalSpace.Opens E) ℂ ⊤ := ⟨f, f.smooth ⊤, hf, by simp⟩
    have he : φ.hasCompactSupport.toSchwartzMap φ.contDiff = f := by ext; rfl
    have hu := hU φ
    rw [he] at hu
    exact hu.trans (hVS φ)
  have hz : (WithLp.toLp 2 (Sum.elim (fun _ : Fin 2 ↦ (0 : ℝ)) (fun j : Fin 0 ↦ (0 : EuclideanSpace ℝ (Fin 0)) j)) : E) = 0 := by
    ext i
    cases i <;> rfl
  have hr0 (φ : SchwartzMap E ℂ) :
      (exists_schwartz_coordinatePlaneRestriction (ι := Fin 2) (κ := Fin 0)).choose φ 0 = φ 0 := by
    have hr := (exists_schwartz_coordinatePlaneRestriction (ι := Fin 2) (κ := Fin 0)).choose_spec φ 0
    simpa only [hz] using hr
  choose c hc using fun α ↦ complexTemperedDistribution_eq_sum_diracDerivative_zero_dim_dual (B α)
  refine ⟨D, N, c, fun f ↦ ?_⟩
  change W f = _
  rw [← heUW]
  rw [hrep]
  refine Finset.sum_congr ?_ ?_
  · ext α
    simp
  · intro α hα
    rw [hc, hr0]
    congr 2
    apply congrArg (fun op : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ ↦ op f)
    apply congrArg (fun d ↦ coordinateDerivative d (fun i ↦ (α.val i).val))
    funext i
    apply congrArg (fun v : E ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap E ℂ) v : _ →L[ℂ] _))
    apply congrArg (WithLp.toLp 2)
    exact complexTemperedDistribution_eq_sum_diracDerivative_single_independent _ _ i (1 : ℝ)


private theorem complexTemperedDistribution_eq_sum_diracDerivative_partials_commute
    (v w : ℂ) :
    Commute (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _)
      (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) w : _ →L[ℂ] _) := by
  ext f x
  have hs : IsSymmSndFDerivAt ℝ (f : ℂ → ℂ) x :=
    (f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)
  calc
    _ = iteratedFDeriv ℝ 2 (f : ℂ → ℂ) x ![v, w] :=
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
    _ = iteratedFDeriv ℝ 2 (f : ℂ → ℂ) x ![w, v] := hs.iteratedFDeriv_cons
    _ = _ := SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm

private theorem complexTemperedDistribution_eq_sum_diracDerivative_wirtingers_commute : Commute schwartzWirtingerZ schwartzWirtingerZBar := by
  let X := (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (1 : ℂ) : _ →L[ℂ] _)
  let Y := (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) Complex.I : _ →L[ℂ] _)
  have hXY : Commute X (Complex.I • Y) := (complexTemperedDistribution_eq_sum_diracDerivative_partials_commute 1 Complex.I).smul_right Complex.I
  have hleft : Commute (X - Complex.I • Y) X := (Commute.refl X).sub_left hXY.symm
  have hright : Commute (X - Complex.I • Y) (Complex.I • Y) := hXY.sub_left (Commute.refl _)
  exact ((hleft.add_right hright).smul_left ((2 : ℂ)⁻¹)).smul_right ((2 : ℂ)⁻¹)

private theorem complexTemperedDistribution_eq_sum_diracDerivative_direction_wirtingers
    (v : ℂ) :
    (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _) =
      v • schwartzWirtingerZ + (star v) • schwartzWirtingerZBar := by
  ext f x
  change fderiv ℝ (f : ℂ → ℂ) x v = v * schwartzWirtingerZ f x + star v * schwartzWirtingerZBar f x
  rw [(schwartzWirtinger_apply f x).1, (schwartzWirtinger_apply f x).2]
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by simp [Complex.real_smul, Complex.re_add_im]
  have hm : fderiv ℝ (f : ℂ → ℂ) x v =
      (v.re : ℂ) * fderiv ℝ (f : ℂ → ℂ) x 1 + (v.im : ℂ) * fderiv ℝ (f : ℂ → ℂ) x Complex.I := by
    conv_lhs => rw [hv, map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  rw [hm]
  unfold wirtingerDeriv wirtingerConjDeriv
  conv_rhs => rw [← Complex.re_add_im v]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

/-- Commuting Wirtinger powers span every finite word of real directional derivatives. -/
private theorem complexTemperedDistribution_eq_sum_diracDerivative_coordinate_operator_span
    (ι : Type*) [Fintype ι] (d : ι → ℂ) (α : ι → ℕ) :
    coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (d i) : _ →L[ℂ] _)) α ∈
      Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ schwartzWirtingerZ ^ p.1 * schwartzWirtingerZBar ^ p.2)) := by
  classical
  let A := schwartzWirtingerZ
  let B := schwartzWirtingerZBar
  let W := Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ A ^ p.1 * B ^ p.2))
  have hAB : Commute A B := complexTemperedDistribution_eq_sum_diracDerivative_wirtingers_commute
  have hA (q) (hq : q ∈ W) : A * q ∈ W := by
    refine Submodule.span_induction (p := fun q _ ↦ A * q ∈ W) ?_ ?_ ?_ ?_ hq
    · rintro q ⟨⟨k, l⟩, rfl⟩
      have he : A * (A ^ k * B ^ l) = A ^ (k + 1) * B ^ l := by rw [pow_succ']; simp only [mul_assoc]
      rw [he]
      exact Submodule.subset_span ⟨(k + 1, l), rfl⟩
    · simpa only [mul_zero] using W.zero_mem
    · intro q r _ _ hq hr
      simpa only [mul_add] using W.add_mem hq hr
    · intro c q _ hq
      simpa only [mul_smul_comm] using W.smul_mem c hq
  have hB (q) (hq : q ∈ W) : B * q ∈ W := by
    refine Submodule.span_induction (p := fun q _ ↦ B * q ∈ W) ?_ ?_ ?_ ?_ hq
    · rintro q ⟨⟨k, l⟩, rfl⟩
      have he : B * (A ^ k * B ^ l) = A ^ k * B ^ (l + 1) := by
        rw [← mul_assoc, (hAB.symm.pow_right k).eq, mul_assoc, ← pow_succ']
      rw [he]
      exact Submodule.subset_span ⟨(k, l + 1), rfl⟩
    · simpa only [mul_zero] using W.zero_mem
    · intro q r _ _ hq hr
      simpa only [mul_add] using W.add_mem hq hr
    · intro c q _ hq
      simpa only [mul_smul_comm] using W.smul_mem c hq
  have hv (v : ℂ) (q) (hq : q ∈ W) :
      (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _) * q ∈ W := by
    rw [complexTemperedDistribution_eq_sum_diracDerivative_direction_wirtingers, add_mul, smul_mul_assoc, smul_mul_assoc]
    exact W.add_mem (W.smul_mem v (hA q hq)) (W.smul_mem (star v) (hB q hq))
  have hpow (v : ℂ) (n : ℕ) (q) (hq : q ∈ W) :
      (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) v : _ →L[ℂ] _) ^ n * q ∈ W := by
    induction n with
    | zero => simpa only [pow_zero, one_mul] using hq
    | succ n ih => rw [pow_succ', mul_assoc]; exact hv v _ ih
  have h1 : (1 : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ) ∈ W := by
    change A ^ 0 * B ^ 0 ∈ W
    exact Submodule.subset_span ⟨(0, 0), rfl⟩
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l with
  | nil => exact h1
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact hpow (d i) (α i) _ ih

private theorem complexTemperedDistribution_eq_sum_diracDerivative_coordinate_functional_span
    (ι : Type*) [Fintype ι] (d : ι → ℂ) (α : ι → ℕ) :
    (TemperedDistribution.delta (0 : ℂ)).comp
      (coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (d i) : _ →L[ℂ] _)) α) ∈
      Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ complexDiracDerivative p.1 p.2)) := by
  let A := schwartzWirtingerZ
  let B := schwartzWirtingerZBar
  let W := Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ A ^ p.1 * B ^ p.2))
  let S := Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ complexDiracDerivative p.1 p.2))
  let Φ : (SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ) →ₗ[ℂ] StrongDual ℂ (SchwartzMap ℂ ℂ) :=
    { toFun := fun op ↦ (TemperedDistribution.delta (0 : ℂ)).comp op
      map_add' := fun op op' ↦ by
        ext f
        change (TemperedDistribution.delta (0 : ℂ)) (op f + op' f) = _
        exact map_add (TemperedDistribution.delta (0 : ℂ)) _ _
      map_smul' := fun c op ↦ by
        ext f
        change (TemperedDistribution.delta (0 : ℂ)) (c • op f) = c • (TemperedDistribution.delta (0 : ℂ)) (op f)
        exact map_smul (TemperedDistribution.delta (0 : ℂ)) _ _ }
  have hgen (k l : ℕ) : Φ (A ^ k * B ^ l) = (-1 : ℂ) ^ (k + l) • complexDiracDerivative k l := by
    ext f
    change ((A ^ k) ((B ^ l) f)) 0 = (-1 : ℂ) ^ (k + l) * ((-1 : ℂ) ^ (k + l) * ((A ^ k) ((B ^ l) f)) 0)
    have hs : (-1 : ℂ) ^ (k + l) * (-1) ^ (k + l) = 1 := by rw [← mul_pow]; norm_num
    rw [← mul_assoc, hs, one_mul]
  have hmap (op) (hop : op ∈ W) : Φ op ∈ S := by
    refine Submodule.span_induction (p := fun op _ ↦ Φ op ∈ S) ?_ ?_ ?_ ?_ hop
    · rintro op ⟨⟨k, l⟩, rfl⟩
      rw [hgen]
      exact S.smul_mem _ (Submodule.subset_span ⟨(k, l), rfl⟩)
    · simpa only [map_zero] using S.zero_mem
    · intro q r _ _ hq hr
      simpa only [map_add] using S.add_mem hq hr
    · intro c q _ hq
      simpa only [map_smul] using S.smul_mem c hq
  exact hmap _ (complexTemperedDistribution_eq_sum_diracDerivative_coordinate_operator_span ι d α)

private theorem complexTemperedDistribution_eq_sum_diracDerivative_coordinate_pull
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ι : Type*) [Fintype ι] (D : E ≃L[ℝ] ℂ) (d : ι → E) (α : ι → ℕ)
    (f : SchwartzMap ℂ ℂ) :
    coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap E ℂ) (d i) : _ →L[ℂ] _)) α
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f) =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D
      (coordinateDerivative (fun i ↦ (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (D (d i)) : _ →L[ℂ] _)) α f) := by
  have hp (i : ι) (k : ℕ) (f : SchwartzMap ℂ ℂ) :
      ((LineDeriv.lineDerivOpCLM ℂ (SchwartzMap E ℂ) (d i) : _ →L[ℂ] _) ^ k)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D
        (((LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (D (d i)) : _ →L[ℂ] _) ^ k) f) := by
    induction k generalizing f with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih]
      exact SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℂ _ D _
  unfold coordinateDerivative
  generalize (Finset.univ.toList : List ι) = l
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [ih, hp]


private theorem complexTemperedDistribution_eq_sum_diracDerivative_point_complex_span
    (T : StrongDual ℂ (SchwartzMap ℂ ℂ)) (hT : TemperedSupportedAtOrigin T) :
    T ∈ Submodule.span ℂ (Set.range (fun p : ℕ × ℕ ↦ complexDiracDerivative p.1 p.2)) := by
  classical
  obtain ⟨D, N, c, hrep⟩ := complexTemperedDistribution_eq_sum_diracDerivative_point_real_decomposition T hT
  let E := EuclideanSpace ℝ (Fin 2 ⊕ Fin 0)
  let I := {α : (Fin 2 ⊕ Fin 0) → Fin (N + 1) // (∑ i, (α i).val) ≤ N}
  let d : Fin 2 ⊕ Fin 0 → E := fun i ↦ WithLp.toLp 2 (Pi.single i (1 : ℝ))
  let Q (α : I) := coordinateDerivative (fun i ↦
    (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℂ ℂ) (D (d i)) : _ →L[ℂ] _)) (fun i ↦ (α.val i).val)
  let V (α : I) := (TemperedDistribution.delta (0 : ℂ)).comp (Q α)
  have he : T = ∑ α : I, c α • V α := by
    ext f
    have hh := hrep (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f)
    have hi : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D.symm
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D f) = f := by
      ext z
      change f (D (D.symm z)) = f z
      rw [D.apply_symm_apply]
    rw [hi] at hh
    rw [hh]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro α hα
    change c α * _ = c α * (Q α f) 0
    congr 1
    have hp := congrArg (fun φ : SchwartzMap E ℂ ↦ φ 0)
      (complexTemperedDistribution_eq_sum_diracDerivative_coordinate_pull E (Fin 2 ⊕ Fin 0) D d (fun i ↦ (α.val i).val) f)
    change _ = (Q α f) (D 0) at hp
    simpa only [map_zero] using hp
  rw [he]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  exact complexTemperedDistribution_eq_sum_diracDerivative_coordinate_functional_span (Fin 2 ⊕ Fin 0) (fun i ↦ D (d i)) (fun i ↦ (α.val i).val)
end ComplexPointSupportHelpers

/-- Paper: Theorem 5.3.2.5, p. 246.
Every complex tempered distribution supported at zero is a finite linear combination of
mixed Wirtinger derivatives of the Dirac distribution. -/
theorem complexTemperedDistribution_eq_sum_diracDerivative (T : StrongDual ℂ 𝓢(ℂ, ℂ))
    (hT : TemperedSupportedAtOrigin T) :
    ∃ (N : ℕ) (c : (k : Fin (N + 1)) → Fin (N + 1 - k.val) → ℂ),
      T = ∑ k : Fin (N + 1), ∑ l : Fin (N + 1 - k.val),
        c k l • complexDiracDerivative k.val l.val := by
  classical
  obtain ⟨a,ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (complexTemperedDistribution_eq_sum_diracDerivative_point_complex_span T hT)
  let N := a.support.sup (fun p ↦ p.1+p.2)
  let I := (k : Fin (N+1)) × Fin (N+1-k.val)
  let e : I ↪ ℕ × ℕ :=
    { toFun := fun u ↦ (u.1.val, u.2.val)
      inj' := by
        rintro ⟨k,l⟩ ⟨k',l'⟩ h
        have hk : k = k' := Fin.ext (congrArg Prod.fst h)
        subst k'
        congr
        exact Fin.ext (congrArg Prod.snd h) }
  have hs : a.support ⊆ Finset.univ.map e := by
    rintro ⟨k,l⟩ hp
    have hb : k+l ≤ N := Finset.le_sup (f := fun p : ℕ × ℕ ↦ p.1+p.2) hp
    let u : I := ⟨⟨k, by omega⟩, ⟨l, by change l < N+1-k; omega⟩⟩
    exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, rfl⟩
  refine ⟨N, fun k l ↦ a (k.val,l.val), ?_⟩
  rw [← ha, a.sum_of_support_subset hs _ (by intro p hp; simp), Finset.sum_map]
  exact Fintype.sum_sigma' (fun (k : Fin (N+1)) (l : Fin (N+1-k.val)) ↦ a (k.val,l.val) • complexDiracDerivative k.val l.val)

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The flat complex Schwartz subspace is the common kernel of the mixed Dirac derivatives. -/
def complexSchwartzFlatAtOrigin : Submodule ℂ 𝓢(ℂ, ℂ) :=
  ⨅ k : ℕ, ⨅ l : ℕ, LinearMap.ker (complexDiracDerivative k l).toLinearMap

/-- Paper: Theorem 5.3.2.5(1), p. 246.
Membership in the flat complex subspace means all mixed Wirtinger derivatives vanish at zero. -/
theorem mem_complexSchwartzFlatAtOrigin_iff (f : 𝓢(ℂ, ℂ)) :
    f ∈ complexSchwartzFlatAtOrigin ↔
      ∀ k l : ℕ, (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) f) 0 = 0 := by
  simp only [complexSchwartzFlatAtOrigin, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall₂_congr fun k l ↦ ?_
  change (-1 : ℂ) ^ (k + l) • ((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) 0 = 0 ↔ _
  rw [smul_eq_zero]
  exact or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Paper: Theorem 5.3.2.5(1), p. 246.
The flat complex Schwartz subspace is closed. -/
theorem complexSchwartzFlatAtOrigin_isClosed :
    IsClosed (complexSchwartzFlatAtOrigin : Set 𝓢(ℂ, ℂ)) := by
  simp only [complexSchwartzFlatAtOrigin, Submodule.coe_iInf]
  exact isClosed_iInter fun k ↦ isClosed_iInter fun l ↦ (complexDiracDerivative k l).isClosed_ker

-- TODO(paper-gap): Under ordinary coefficient pairing the adjoint on p. 249
-- has a sign for each odd total degree and includes all degrees. The positive
-- Taylor map below differs from that adjoint by (X,Y) ↦ (-X,-Y).

/-- the first Wirtinger derivatives of a mixed monomial. -/
private theorem complexSchwartzTaylor_equiv_monomial_deriv (c : ℂ) (k l : ℕ) (z : ℂ) :
    wirtingerDeriv (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z =
      c * (k : ℂ) * z ^ (k - 1) * (star z) ^ l ∧
    wirtingerConjDeriv (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z =
      c * (l : ℂ) * z ^ k * (star z) ^ (l - 1) := by
  have hi := (hasFDerivAt_id (𝕜 := ℝ) z).pow k
  have hb := (Complex.conjCLE.hasFDerivAt (x := z)).pow l
  have h := (hi.mul hb).const_mul c
  simp only [Pi.mul_apply, id_eq, Complex.conjCLE_apply, ← Complex.star_def] at h
  change (fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z 1 -
    Complex.I * fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z Complex.I) / 2 = _ ∧
    (fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z 1 +
    Complex.I * fderiv ℝ (fun w : ℂ ↦ c * (w ^ k * (star w) ^ l)) z Complex.I) / 2 = _
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, Complex.conjCLE_apply, smul_eq_mul, map_one,
    Complex.star_def, Complex.conj_I, nsmul_eq_mul,
    ContinuousLinearEquiv.coe_coe]
  constructor
  · linear_combination (c * (l : ℂ) * z ^ k * ((starRingEnd ℂ) z) ^ (l - 1) -
      c * (k : ℂ) * z ^ (k - 1) * ((starRingEnd ℂ) z) ^ l) * Complex.I_sq / 2
  · linear_combination (c * (k : ℂ) * z ^ (k - 1) * ((starRingEnd ℂ) z) ^ l -
      c * (l : ℂ) * z ^ k * ((starRingEnd ℂ) z) ^ (l - 1)) * Complex.I_sq / 2

/-- Wirtinger differentiation preserves equality with a monomial near zero. -/
private theorem complexSchwartzTaylor_equiv_germ (f : 𝓢(ℂ, ℂ))
    (c : ℂ) (k l : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * (z ^ k * (star z) ^ l)) :
    (schwartzWirtingerZ f : ℂ → ℂ) =ᶠ[𝓝 0]
      (fun z ↦ (c * k) * (z ^ (k - 1) * (star z) ^ l)) ∧
    (schwartzWirtingerZBar f : ℂ → ℂ) =ᶠ[𝓝 0]
      (fun z ↦ (c * l) * (z ^ k * (star z) ^ (l - 1))) := by
  have hd := hf.fderiv (𝕜 := ℝ)
  constructor
  · filter_upwards [hd] with z hz
    rw [(schwartzWirtinger_apply f z).1, wirtingerDeriv, hz]
    have h := (complexSchwartzTaylor_equiv_monomial_deriv c k l z).1
    dsimp only [wirtingerDeriv] at h
    rw [h]
    ring
  · filter_upwards [hd] with z hz
    rw [(schwartzWirtinger_apply f z).2, wirtingerConjDeriv, hz]
    have h := (complexSchwartzTaylor_equiv_monomial_deriv c k l z).2
    dsimp only [wirtingerConjDeriv] at h
    rw [h]
    ring

/-- iterated mixed derivatives of a monomial germ have descending-factorial coefficients. -/
private theorem complexSchwartzTaylor_equiv_germ_pow (f : 𝓢(ℂ, ℂ))
    (c : ℂ) (k l : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ c * (z ^ k * (star z) ^ l)) (u v : ℕ) :
    ((schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) f) : ℂ → ℂ) =ᶠ[𝓝 0]
      fun z ↦ (c * (l.descFactorial v : ℂ) * (k.descFactorial u : ℂ)) *
        (z ^ (k - u) * (star z) ^ (l - v)) := by
  have hb (v : ℕ) : ((schwartzWirtingerZBar ^ v) f : ℂ → ℂ) =ᶠ[𝓝 0]
      fun z ↦ (c * (l.descFactorial v : ℂ)) * (z ^ k * (star z) ^ (l - v)) := by
    induction v with
    | zero => simpa using hf
    | succ v ih =>
      have h := (complexSchwartzTaylor_equiv_germ _ _ _ _ ih).2
      rw [pow_succ']
      filter_upwards [h] with z hz
      change schwartzWirtingerZBar ((schwartzWirtingerZBar ^ v) f) z = _
      rw [hz, Nat.descFactorial_succ, Nat.sub_sub]
      push_cast
      ring
  induction u with
  | zero => simpa using hb v
  | succ u ih =>
    have h := (complexSchwartzTaylor_equiv_germ _ _ _ _ ih).1
    rw [pow_succ']
    filter_upwards [h] with z hz
    change schwartzWirtingerZ ((schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) f)) z = _
    rw [hz, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/-- a mixed monomial germ has exactly one nonzero mixed derivative at zero. -/
private theorem complexSchwartzTaylor_equiv_germ_zero (f : 𝓢(ℂ, ℂ)) (k l : ℕ)
    (hf : (f : ℂ → ℂ) =ᶠ[𝓝 0] fun z ↦ z ^ k * (star z) ^ l) (u v : ℕ) :
    (schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) f) 0 =
      if u = k ∧ v = l then (k.factorial * l.factorial : ℂ) else 0 := by
  have h := (complexSchwartzTaylor_equiv_germ_pow f 1 k l (by simpa using hf) u v).eq_of_nhds
  rw [h]
  rcases lt_trichotomy u k with hu | rfl | hu
  · simp [hu.ne, Nat.sub_ne_zero_of_lt hu]
  · rcases lt_trichotomy v l with hv | rfl | hv
    · simp [hv.ne, Nat.sub_ne_zero_of_lt hv]
    · simp [Nat.descFactorial_self, mul_comm]
    · simp [hv.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hv]
  · simp [hu.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hu]

/-- dilation makes every seminorm below the homogeneous degree arbitrarily small. -/
private theorem complexSchwartzTaylor_equiv_scaled (G ψ : 𝓢(ℂ, ℂ)) (n m k : ℕ)
    (hG : tsupport (G : ℂ → ℂ) ⊆ Metric.closedBall 0 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hmn : m < n)
    (hψ : ∀ z, ψ z = (ε : ℂ) ^ n * G (ε⁻¹ • z)) :
    SchwartzMap.seminorm ℂ k m ψ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by
  have hd (z : ℂ) : iteratedFDeriv ℝ m (ψ : ℂ → ℂ) z =
      (ε : ℂ) ^ n • ((ε⁻¹) ^ m • iteratedFDeriv ℝ m (G : ℂ → ℂ) (ε⁻¹ • z)) := by
    rw [show (ψ : ℂ → ℂ) = fun z ↦ (ε : ℂ) ^ n • G (ε⁻¹ • z) from funext hψ,
      iteratedFDeriv_const_smul_apply']
    · rw [iteratedFDeriv_comp_const_smul ε⁻¹ (G.smooth m)]
    · exact ((G.smooth m).comp (contDiff_id.const_smul ε⁻¹)).contDiffAt
  have hGb (z : ℂ) : ‖iteratedFDeriv ℝ m (G : ℂ → ℂ) z‖ ≤ SchwartzMap.seminorm ℂ 0 m G := by
    simpa using SchwartzMap.le_seminorm ℂ 0 m G z
  have hpow : ε ^ n * (ε⁻¹) ^ m ≤ ε := by
    rw [← pow_sub_mul_pow ε hmn.le, mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow,
      mul_one]
    calc ε ^ (n - m) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by omega)
      _ = ε := pow_one ε
  refine SchwartzMap.seminorm_le_bound ℂ k m _ (by positivity) fun z ↦ ?_
  rw [hd, norm_smul, norm_smul, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos (inv_pos.mpr hε)]
  by_cases hz : ‖z‖ ≤ 1
  · calc ‖z‖ ^ k * (ε ^ n * ((ε⁻¹) ^ m * ‖iteratedFDeriv ℝ m (G : ℂ → ℂ) (ε⁻¹ • z)‖))
        ≤ 1 * ((ε ^ n * (ε⁻¹) ^ m) * SchwartzMap.seminorm ℂ 0 m G) := by
          rw [← mul_assoc (ε ^ n)]
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) hz
          · exact hGb _
      _ ≤ ε * SchwartzMap.seminorm ℂ 0 m G := by rw [one_mul]; gcongr
  · have hout : ε⁻¹ • z ∉ tsupport (G : ℂ → ℂ) := by
      intro h
      have hh := hG h
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hε, inv_mul_le_iff₀ hε] at hh
      exact hz ((by simpa using hh : ‖z‖ ≤ ε).trans hε1)
    have h0 : iteratedFDeriv ℝ m (G : ℂ → ℂ) (ε⁻¹ • z) = 0 := by
      by_contra hne
      exact hout (support_iteratedFDeriv_subset m hne)
    rw [h0, norm_zero, mul_zero, mul_zero, mul_zero]
    positivity

/-- a compactly supported mixed monomial and its dilations realize the same jet. -/
private theorem complexSchwartzTaylor_equiv_bump (k l : ℕ) :
    ∃ G : 𝓢(ℂ, ℂ), tsupport (G : ℂ → ℂ) ⊆ Metric.closedBall 0 1 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ψ : 𝓢(ℂ, ℂ),
        (∀ z, ψ z = (ε : ℂ) ^ (k + l) * G (ε⁻¹ • z)) ∧
        (∀ u v, (schwartzWirtingerZ ^ u) ((schwartzWirtingerZBar ^ v) ψ) 0 =
          if u = k ∧ v = l then (k.factorial * l.factorial : ℂ) else 0) := by
  let χ : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let g : ℂ → ℂ := fun z ↦ (χ z : ℂ) * (z ^ k * (star z) ^ l)
  have hc : HasCompactSupport g :=
    (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hd : ContDiff (ℝ) (∞) g := (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul
    ((contDiff_id.pow k).mul (Complex.conjLIE.contDiff.pow l))
  let G := hc.toSchwartzMap hd
  have hG : tsupport (G : ℂ → ℂ) ⊆ Metric.closedBall 0 1 := by
    change tsupport g ⊆ _
    exact tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero _).trans
      (by rw [χ.tsupport_eq]))
  refine ⟨G, hG, fun ε hε ↦ ?_⟩
  have hsc : HasCompactSupport (fun z : ℂ ↦ (ε : ℂ) ^ (k + l) * G (ε⁻¹ • z)) :=
    (hc.comp_smul (inv_ne_zero hε.ne')).mul_left
  have hsd : ContDiff (ℝ) (∞) (fun z : ℂ ↦ (ε : ℂ) ^ (k + l) * G (ε⁻¹ • z)) :=
    contDiff_const.mul ((G.smooth ⊤).comp (contDiff_id.const_smul ε⁻¹))
  let ψ := hsc.toSchwartzMap hsd
  refine ⟨ψ, fun _ ↦ rfl, fun u v ↦ complexSchwartzTaylor_equiv_germ_zero ψ k l ?_ u v⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (mul_pos hε χ.rIn_pos)] with z hz
  have hb : ε⁻¹ • z ∈ Metric.closedBall (0 : ℂ) χ.rIn := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hε, inv_mul_le_iff₀ hε]
    exact hz.le
  change (ε : ℂ) ^ (k + l) * ((χ (ε⁻¹ • z) : ℂ) * ((ε⁻¹ • z) ^ k * (star (ε⁻¹ • z)) ^ l)) = _
  rw [χ.one_of_mem_closedBall hb]
  simp only [Complex.ofReal_one, one_mul, Complex.real_smul, star_mul',
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, map_inv₀, mul_pow, pow_add]
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hk : (ε : ℂ) ^ k * ((ε : ℂ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ he, one_pow]
  have hl : (ε : ℂ) ^ l * ((ε : ℂ)⁻¹) ^ l = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ he, one_pow]
  calc _ = ((ε : ℂ) ^ k * ((ε : ℂ)⁻¹) ^ k) *
      ((ε : ℂ) ^ l * ((ε : ℂ)⁻¹) ^ l) * (z ^ k * ((starRingEnd ℂ) z) ^ l) := by ring
    _ = _ := by rw [hk, hl]; simp

/-- a normalized jet basis element can be made small in every lower-order seminorm. -/
private theorem complexSchwartzTaylor_equiv_basis (d : Fin 2 →₀ ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : 𝓢(ℂ, ℂ),
      (∀ q : Fin 2 →₀ ℕ,
        (schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) φ) 0 /
          ((q 0).factorial * (q 1).factorial : ℂ) = if q = d then 1 else 0) ∧
      ∀ k m : ℕ, m < d 0 + d 1 → SchwartzMap.seminorm ℂ k m φ ≤ δ := by
  classical
  obtain ⟨G, hG, hψ⟩ := complexSchwartzTaylor_equiv_bump (d 0) (d 1)
  let C : ℝ := ∑ m ∈ Finset.range (d 0 + d 1), SchwartzMap.seminorm ℂ 0 m G + 1
  have hC : 0 < C := by
    have : 0 ≤ ∑ m ∈ Finset.range (d 0 + d 1), SchwartzMap.seminorm ℂ 0 m G :=
      Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
    dsimp [C]; linarith
  let ε := min 1 (δ / C)
  have hε : 0 < ε := lt_min one_pos (div_pos hδ hC)
  obtain ⟨φ, hφ, hj⟩ := hψ ε hε
  refine ⟨φ, fun q ↦ ?_, fun k m hm ↦ ?_⟩
  · rw [hj]
    have he : q 0 = d 0 ∧ q 1 = d 1 ↔ q = d := by
      constructor
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> assumption
      · rintro rfl; exact ⟨rfl, rfl⟩
    simp only [he]
    split_ifs with h
    · subst q
      exact div_self (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d 0))
        (by exact_mod_cast Nat.factorial_ne_zero (d 1)))
    · exact zero_div _
  · have hmc : SchwartzMap.seminorm ℂ 0 m G ≤ C := by
      have h := Finset.single_le_sum (fun j _ ↦ apply_nonneg (SchwartzMap.seminorm ℂ 0 j) G)
        (Finset.mem_range.mpr hm)
      dsimp [C]; linarith
    calc SchwartzMap.seminorm ℂ k m φ ≤ ε * SchwartzMap.seminorm ℂ 0 m G :=
          complexSchwartzTaylor_equiv_scaled G φ (d 0 + d 1) m k hG ε hε (min_le_left _ _) hm hφ
      _ ≤ (δ / C) * C := by
          gcongr
          exact min_le_right _ _
      _ = δ := div_mul_cancel₀ _ hC.ne'

/-- Paper: Theorem 5.3.2.5(2), p. 246.
Finite mixed Wirtinger jets can be realized by Schwartz functions, with a linear bound
on any prescribed finite family of Schwartz seminorms. -/
private theorem complexSchwartzTaylor_equiv_finite
    (s : Finset (ℕ × ℕ)) (t : Finset (Fin 2 →₀ ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : (Fin 2 →₀ ℕ) → ℂ, ∃ f : 𝓢(ℂ, ℂ),
      (∀ d : Fin 2 →₀ ℕ,
        (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
          ((d 0).factorial * (d 1).factorial : ℂ) = if d ∈ t then b d else 0) ∧
      (s.sup (schwartzSeminormFamily ℂ ℂ ℂ)) f ≤ C * ∑ d ∈ t, ‖b d‖ := by
  classical
  choose φ hφ using fun d ↦ complexSchwartzTaylor_equiv_basis d 1 one_pos
  let p := s.sup (schwartzSeminormFamily ℂ ℂ ℂ)
  let C := ∑ d ∈ t, p (φ d) + 1
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun d (_ : d ∈ t) ↦ apply_nonneg p (φ d))
    dsimp [C]; linarith
  refine ⟨C, hC, fun b ↦ ⟨∑ d ∈ t, b d • φ d, fun q ↦ ?_, ?_⟩⟩
  · let a : StrongDual ℂ 𝓢(ℂ, ℂ) :=
      (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ •
        (TemperedDistribution.delta (0 : ℂ)).comp
          ((schwartzWirtingerZ ^ (q 0)).comp (schwartzWirtingerZBar ^ (q 1)))
    have ha (f : 𝓢(ℂ, ℂ)) : a f =
        (schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) f) 0 /
          ((q 0).factorial * (q 1).factorial : ℂ) := by
      change (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ * _ = _; rw [div_eq_mul_inv, mul_comm]; rfl
    have hap (d : Fin 2 →₀ ℕ) : a (φ d) = if q = d then 1 else 0 :=
      (ha _).trans ((hφ d).1 q)
    rw [← ha, map_sum]
    simp [map_smul, hap]
  · calc p (∑ d ∈ t, b d • φ d) ≤ ∑ d ∈ t, p (b d • φ d) :=
          Finset.le_sum_of_subadditive p (map_zero _).le (map_add_le_add _) _ _
      _ ≤ ∑ d ∈ t, C * ‖b d‖ := by
          apply Finset.sum_le_sum
          intro d hd
          rw [map_smul_eq_mul, mul_comm]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have h := Finset.single_le_sum (fun d _ ↦ apply_nonneg p (φ d)) hd
          dsimp [C]; linarith
      _ = C * ∑ d ∈ t, ‖b d‖ := (Finset.mul_sum _ _ _).symm


/-- Paper: Theorem 5.3.2.5(2), p. 246.
For any finite family of Schwartz seminorms, jets vanishing on a sufficiently large
finite set of indices admit realizations arbitrarily small in those seminorms.
This is the tail part of the two-variable Borel construction. -/
private theorem complexSchwartzTaylor_equiv_tail (s : Finset (ℕ × ℕ)) :
    ∃ t : Finset (Fin 2 →₀ ℕ), ∀ b : (Fin 2 →₀ ℕ) → ℂ,
      (∀ d ∈ t, b d = 0) → ∀ r : ℝ, 0 < r → ∃ f : 𝓢(ℂ, ℂ),
        (∀ d : Fin 2 →₀ ℕ,
          (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
            ((d 0).factorial * (d 1).factorial : ℂ) = b d) ∧
        (s.sup (schwartzSeminormFamily ℂ ℂ ℂ)) f < r := by
  classical
  let e : ℕ ≃ (Fin 2 →₀ ℕ) :=
    (Finsupp.equivFunOnFinite.trans ((finTwoArrowEquiv ℕ).trans Nat.pairEquiv)).symm
  have he (n : ℕ) : (e n) 0 = (Nat.unpair n).1 ∧ (e n) 1 = (Nat.unpair n).2 := by
    simp [e, finTwoArrowEquiv, Nat.pairEquiv]
    exact ⟨rfl, rfl⟩
  have hdeg (j n : ℕ) (hn : (j + 1) ^ 2 ≤ n) : j < (e n) 0 + (e n) 1 := by
    by_contra h
    have h0 : (Nat.unpair n).1 ≤ j := by rw [← (he n).1]; omega
    have h1 : (Nat.unpair n).2 ≤ j := by rw [← (he n).2]; omega
    have hp := Nat.pair_lt_max_add_one_sq (Nat.unpair n).1 (Nat.unpair n).2
    rw [Nat.pair_unpair] at hp
    have hmax : max (Nat.unpair n).1 (Nat.unpair n).2 ≤ j := max_le h0 h1
    have hs : (max (Nat.unpair n).1 (Nat.unpair n).2 + 1) ^ 2 ≤ (j + 1) ^ 2 := by gcongr
    omega
  let m := s.sup Prod.snd
  let t := (Finset.range ((m + 1) ^ 2)).image e
  refine ⟨t, fun b hb r hr ↦ ?_⟩
  let w (n : ℕ) : ℝ := r / 4 * (1 / 2) ^ n
  have hw (n : ℕ) : 0 < w n := by positivity
  have hwsum : HasSum w (r / 2) := by
    have h := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (r / 4)
    convert h using 1
    norm_num
    ring
  choose φ hφ using fun n ↦ complexSchwartzTaylor_equiv_basis (e n)
    (w n / (‖b (e n)‖ + 1)) (by have := hw n; positivity)
  have hsmall (n k j : ℕ) (hn : (j + 1) ^ 2 ≤ n) :
      ‖b (e n)‖ * SchwartzMap.seminorm ℂ k j (φ n) ≤ w n := by
    calc ‖b (e n)‖ * SchwartzMap.seminorm ℂ k j (φ n)
        ≤ ‖b (e n)‖ * (w n / (‖b (e n)‖ + 1)) := by
          gcongr
          exact (hφ n).2 k j (hdeg j n hn)
      _ = w n * (‖b (e n)‖ / (‖b (e n)‖ + 1)) := by ring
      _ ≤ w n * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = w n := mul_one _
  let v (i : ℕ × ℕ) (n : ℕ) : ℝ :=
    if n < (i.2 + 1) ^ 2 then ‖b (e n)‖ * SchwartzMap.seminorm ℂ i.1 i.2 (φ n) else 0
  have hv (i : ℕ × ℕ) : Summable (v i) := by
    refine summable_of_ne_finset_zero (s := Finset.range ((i.2 + 1) ^ 2)) fun n hn ↦ ?_
    simp only [Finset.mem_range] at hn
    simp only [v, hn, ↓reduceIte]
  have hx (i : ℕ × ℕ) (n : ℕ) :
      schwartzSeminormFamily ℂ ℂ ℂ i (b (e n) • φ n) ≤ w n + v i n := by
    rw [SchwartzMap.schwartzSeminormFamily_apply, map_smul_eq_mul]
    by_cases hn : n < (i.2 + 1) ^ 2
    · simp only [v, hn, ↓reduceIte]
      linarith [hw n]
    · simp only [v, hn, ↓reduceIte, add_zero]
      exact hsmall n i.1 i.2 (by omega)
  have : CompleteSpace 𝓢(ℂ, ℂ) := completeSpace_schwartzMap
  obtain ⟨hsum, hbound⟩ := realSchwartzFlatQuotient_strongDual_summable
    (schwartz_withSeminorms ℂ ℂ ℂ) (fun n ↦ b (e n) • φ n)
    (fun i n ↦ w n + v i n) (fun i ↦ hwsum.summable.add (hv i)) hx
  refine ⟨∑' n, b (e n) • φ n, fun q ↦ ?_, ?_⟩
  · let a : StrongDual ℂ 𝓢(ℂ, ℂ) :=
      (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ •
        (TemperedDistribution.delta (0 : ℂ)).comp
          ((schwartzWirtingerZ ^ (q 0)).comp (schwartzWirtingerZBar ^ (q 1)))
    have ha (f : 𝓢(ℂ, ℂ)) : a f =
        (schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) f) 0 /
          ((q 0).factorial * (q 1).factorial : ℂ) := by
      change (((q 0).factorial * (q 1).factorial : ℂ))⁻¹ * _ = _
      rw [div_eq_mul_inv, mul_comm]; rfl
    have hap (n : ℕ) : a (φ n) = if q = e n then 1 else 0 := (ha _).trans ((hφ n).1 q)
    rw [← ha, ContinuousLinearMap.map_tsum _ hsum]
    simp only [map_smul, hap, smul_eq_mul]
    rw [tsum_eq_single (e.symm q) fun n hn ↦ ?_]
    · simp
    · have hne : q ≠ e n := fun h ↦ hn (by rw [h, e.symm_apply_apply])
      simp [hne]
  · apply Seminorm.finset_sup_apply_lt hr
    intro i hi
    have him : i.2 ≤ m := Finset.le_sup (f := Prod.snd) hi
    have hv0 : v i = 0 := by
      funext n
      dsimp only [v]
      split_ifs with hn
      · have hnm : n < (m + 1) ^ 2 := hn.trans_le (by gcongr)
        have hb0 := hb (e n) (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hnm, rfl⟩)
        simp [hb0]
      · rfl
    have h := hbound i
    rw [hv0] at h
    simp only [Pi.zero_apply, add_zero, hwsum.tsum_eq] at h
    exact h.trans_lt (by linarith)

/-- A finite jet and an arbitrarily small tail give a quantitative Borel realization. -/
private theorem complexSchwartzTaylor_equiv_bound (s : Finset (ℕ × ℕ)) :
    ∃ t : Finset (Fin 2 →₀ ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ b : (Fin 2 →₀ ℕ) → ℂ, ∀ r : ℝ, 0 < r → ∃ f : 𝓢(ℂ, ℂ),
        (∀ d : Fin 2 →₀ ℕ,
          (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
            ((d 0).factorial * (d 1).factorial : ℂ) = b d) ∧
        (s.sup (schwartzSeminormFamily ℂ ℂ ℂ)) f < C * ∑ d ∈ t, ‖b d‖ + r := by
  classical
  obtain ⟨t, ht⟩ := complexSchwartzTaylor_equiv_tail s
  obtain ⟨C, hC, hfinite⟩ := complexSchwartzTaylor_equiv_finite s t
  refine ⟨t, C, hC, fun b r hr ↦ ?_⟩
  obtain ⟨f, hf, hfb⟩ := hfinite b
  obtain ⟨g, hg, hgb⟩ := ht (fun d ↦ if d ∈ t then 0 else b d)
    (fun d hd ↦ by simp [hd]) r hr
  refine ⟨f + g, fun d ↦ ?_, (map_add_le_add _ f g).trans_lt (add_lt_add_of_le_of_lt hfb hgb)⟩
  simp only [map_add, add_apply, add_div, hf, hg]
  split_ifs <;> simp

/-- Paper: Theorem 5.3.2.5(2), p. 246.
The complex flat quotient is identified with formal power series in two variables by the
mixed Wirtinger Taylor coefficients, with the coefficientwise topology of (5.3.2.13).
Deviation: The Taylor formula takes a Schwartz test as input, as required by the domain. -/
theorem complexSchwartzTaylor_equiv :
    ∃ e : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ,
      ∀ (f : 𝓢(ℂ, ℂ)) (s : Fin 2 →₀ ℕ),
        MvPowerSeries.coeff s (e (complexSchwartzFlatAtOrigin.mkQ f)) =
          (schwartzWirtingerZ^(s 0)) ((schwartzWirtingerZBar^(s 1)) f) 0 /
            ((s 0).factorial * (s 1).factorial : ℂ) := by
  classical
  let a (d : Fin 2 →₀ ℕ) : StrongDual ℂ 𝓢(ℂ, ℂ) :=
    (((d 0).factorial * (d 1).factorial : ℂ))⁻¹ •
      (TemperedDistribution.delta (0 : ℂ)).comp
        ((schwartzWirtingerZ ^ (d 0)).comp (schwartzWirtingerZBar ^ (d 1)))
  have ha (d : Fin 2 →₀ ℕ) (f : 𝓢(ℂ, ℂ)) :
      a d f = (schwartzWirtingerZ ^ (d 0)) ((schwartzWirtingerZBar ^ (d 1)) f) 0 /
        ((d 0).factorial * (d 1).factorial : ℂ) := by
    change (((d 0).factorial * (d 1).factorial : ℂ))⁻¹ * _ = _
    rw [div_eq_mul_inv, mul_comm]
    rfl
  have hfact (d : Fin 2 →₀ ℕ) : ((d 0).factorial * (d 1).factorial : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d 0))
      (by exact_mod_cast Nat.factorial_ne_zero (d 1))
  let T : 𝓢(ℂ, ℂ) →ₗ[ℂ] MvPowerSeries (Fin 2) ℂ :=
    { toFun := fun f d ↦ a d f
      map_add' := fun f g ↦ by ext d; exact map_add (a d) f g
      map_smul' := fun c f ↦ by ext d; exact map_smul (a d) c f }
  have hT (f : 𝓢(ℂ, ℂ)) (d : Fin 2 →₀ ℕ) : MvPowerSeries.coeff d (T f) = a d f := rfl
  have hTc : Continuous T := by
    refine continuous_iff_continuousAt.mpr fun f ↦ ?_
    rw [ContinuousAt, MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    simp only [hT]
    exact (a d).continuous.tendsto f
  let TL : 𝓢(ℂ, ℂ) →L[ℂ] MvPowerSeries (Fin 2) ℂ := ⟨T, hTc⟩
  have hTL (f : 𝓢(ℂ, ℂ)) (d : Fin 2 →₀ ℕ) : MvPowerSeries.coeff d (TL f) = a d f := rfl
  have hmem (f : 𝓢(ℂ, ℂ)) : f ∈ complexSchwartzFlatAtOrigin ↔ TL f = 0 := by
    rw [mem_complexSchwartzFlatAtOrigin_iff, MvPowerSeries.ext_iff]
    simp only [hTL, ha, map_zero, div_eq_zero_iff, hfact, or_false]
    constructor
    · intro h d
      exact h (d 0) (d 1)
    · intro h k l
      let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![k, l]
      simpa [d] using h d
  have hle : complexSchwartzFlatAtOrigin ≤ TL.ker := fun f hf ↦ (hmem f).mp hf
  let E := complexSchwartzFlatAtOrigin.liftQL TL hle
  have hE (f : 𝓢(ℂ, ℂ)) : E (complexSchwartzFlatAtOrigin.mkQ f) = TL f := rfl
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).mpr fun y hy ↦ ?_
    obtain ⟨f, rfl⟩ := complexSchwartzFlatAtOrigin.mkQ_surjective y
    rw [hE] at hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((hmem f).mpr hy)
  have hsurj : Function.Surjective E := by
    intro p
    obtain ⟨t, C, hC, hb⟩ := complexSchwartzTaylor_equiv_bound ∅
    obtain ⟨f, hf, -⟩ := hb (fun d ↦ MvPowerSeries.coeff d p) 1 one_pos
    refine ⟨complexSchwartzFlatAtOrigin.mkQ f, ?_⟩
    ext d
    rw [hE, hTL, ha, hf]
  let e : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃ₗ[ℂ] MvPowerSeries (Fin 2) ℂ :=
    LinearEquiv.ofBijective E.toLinearMap ⟨hinj, hsurj⟩
  have he (y : 𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) : e y = E y := rfl
  have hsymm : Continuous e.symm := by
    refine continuous_of_continuousAt_zero e.symm ?_
    rw [ContinuousAt, map_zero]
    intro V hV
    have hq : complexSchwartzFlatAtOrigin.mkQ ⁻¹' V ∈ 𝓝 (0 : 𝓢(ℂ, ℂ)) :=
      complexSchwartzFlatAtOrigin.mkQL.continuous.continuousAt.preimage_mem_nhds
        (by simpa using hV)
    obtain ⟨⟨s, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ ℂ ℂ).hasBasis_zero_ball.mem_iff.mp hq
    obtain ⟨t, C, hC, hb⟩ := complexSchwartzTaylor_equiv_bound s
    have hcont : Continuous (fun p : MvPowerSeries (Fin 2) ℂ ↦
        C * ∑ d ∈ t, ‖MvPowerSeries.coeff d p‖) := by
      fun_prop
    have hW : ∀ᶠ p in 𝓝 (0 : MvPowerSeries (Fin 2) ℂ),
        C * ∑ d ∈ t, ‖MvPowerSeries.coeff d p‖ < r / 2 := by
      have h := hcont.tendsto 0
      have hz : C * ∑ d ∈ t, ‖MvPowerSeries.coeff d (0 : MvPowerSeries (Fin 2) ℂ)‖ = 0 := by simp
      rw [hz] at h
      exact h.eventually (gt_mem_nhds (by linarith))
    rw [Filter.mem_map]
    filter_upwards [hW] with p hp
    obtain ⟨f, hf, hfb⟩ := hb (fun d ↦ MvPowerSeries.coeff d p) (r / 2) (by linarith)
    have hp' : e.symm p = complexSchwartzFlatAtOrigin.mkQ f := by
      rw [LinearEquiv.symm_apply_eq, he, hE]
      ext d
      rw [hTL, ha, hf]
    rw [Set.mem_preimage, hp']
    apply hsub
    apply (Seminorm.mem_ball_zero _).mpr
    linarith
  let eL : (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ :=
    { e with
      continuous_toFun := E.continuous
      continuous_invFun := hsymm }
  refine ⟨eL, fun f d ↦ ?_⟩
  change MvPowerSeries.coeff d (TL f) = _
  rw [hTL, ha]


/-- Paper: Theorem 5.3.2.5(1), p. 246.
The quotient adjoint identifies the strong dual of the complex flat quotient with
the annihilator in the strong dual of the complex Schwartz space. -/
theorem complexSchwartzFlatQuotient_strongDual :
    let pull := fun T : StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ↦
      T.comp complexSchwartzFlatAtOrigin.mkQL
    IsEmbedding pull ∧ Set.range pull =
      {T : StrongDual ℂ 𝓢(ℂ, ℂ) | ∀ f ∈ complexSchwartzFlatAtOrigin, T f = 0} := by
  intro pull
  refine ⟨realSchwartzFlatQuotient_strongDual_isEmbedding _ ?_, ?_⟩
  · let K := complexSchwartzFlatAtOrigin
    let I := Fin 2 →₀ ℕ
    let e := complexSchwartzTaylor_equiv.choose
    let coeff : MvPowerSeries (Fin 2) ℂ →L[ℂ] (I → ℂ) :=
      ContinuousLinearMap.pi fun i ↦ ⟨MvPowerSeries.coeff i, MvPowerSeries.WithPiTopology.continuous_coeff ℂ i⟩
    let T := coeff.comp e.toContinuousLinearMap
    have hback : Continuous (fun p : I → ℂ ↦ e.symm p) := e.symm.continuous
    have hN : IsNuclearTVS.{0} (I → ℂ) :=
      isNuclearTVS_pi (X := fun _ : I ↦ ℂ) (fun _ ↦ isNuclearTVS_of_finiteDimensional ℂ)
    let : PolynormableSpace ℂ (I → ℂ) := hN.2.1
    have : IsClosed (K : Set 𝓢(ℂ, ℂ)) := complexSchwartzFlatAtOrigin_isClosed
    let : CompleteSpace 𝓢(ℂ, ℂ) := completeSpace_schwartzMap
    have : (uniformity 𝓢(ℂ, ℂ)).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero]
      infer_instance
    let := UniformSpace.pseudoMetricSpace 𝓢(ℂ, ℂ)
    intro B hB
    have hc := isCompact_closure_of_isNuclearTVS (I → ℂ) hN (hB.image T)
    obtain ⟨A, hA, heq⟩ := exists_isCompact_image_eq_of_isOpenQuotientMap K.isOpenQuotientMap_mkQL
      (hc.image hback)
    refine ⟨A, hA.isVonNBounded ℂ, ?_⟩
    intro y hy
    change y ∈ K.mkQL '' A
    rw [heq]
    exact ⟨T y, subset_closure ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  · change Set.range (fun T : StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin) ↦
      T.comp complexSchwartzFlatAtOrigin.mkQL) = _
    rw [range_transpose_mkQL]
    ext T
    simp [Set.mem_iInter]

section ComplexPolynomialDualHelpers


/-- A continuous functional on coefficientwise formal power series has finite coefficient support. -/
private theorem complexDiracDerivatives_polynomialEquiv_poly_finite
    (L : MvPowerSeries (Fin 2) ℂ →L[ℂ] ℂ) :
    ∃ N : ℕ, ∀ s : MvPowerSeries (Fin 2) ℂ,
      (∀ d : Fin 2 →₀ ℕ, d 0 + d 1 ≤ N → MvPowerSeries.coeff d s = 0) → L s = 0 := by
  by_contra h
  push Not at h
  choose s hs0 hs using h
  let t (N : ℕ) : MvPowerSeries (Fin 2) ℂ := (L (s N))⁻¹ • s N
  have ht : Tendsto t atTop (𝓝 0) := by
    rw [MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    rw [map_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (d 0 + d 1)] with N hN
    simp [t, hs0 N d hN]
  have h1 := (L.continuous.tendsto 0).comp ht
  rw [map_zero] at h1
  have h2 : ⇑L ∘ t = fun _ ↦ 1 := by
    funext N
    simp [t, inv_mul_cancel₀ (hs N)]
  rw [h2] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

private theorem complexDiracDerivatives_polynomialEquiv_poly_box
    (N : ℕ) :
    ∃ t : Finset (Fin 2 →₀ ℕ), ∀ d : Fin 2 →₀ ℕ, d 0 + d 1 ≤ N → d ∈ t := by
  classical
  refine ⟨((Finset.range (N + 1)).product (Finset.range (N + 1))).image
    (fun p ↦ Finsupp.equivFunOnFinite.symm ![p.1, p.2]), fun d hd ↦ ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(d 0, d 1), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

private theorem complexDiracDerivatives_polynomialEquiv_poly_bounded
    (w : (Fin 2 →₀ ℕ) → ℝ) :
    Bornology.IsVonNBounded ℂ {b : MvPowerSeries (Fin 2) ℂ | ∀ d, ‖MvPowerSeries.coeff d b‖ ≤ w d} := by
  change Bornology.IsVonNBounded ℂ {b : (Fin 2 →₀ ℕ) → ℂ | ∀ d, ‖b d‖ ≤ w d}
  rw [Bornology.isVonNBounded_pi_iff]
  intro d
  apply (NormedSpace.isVonNBounded_iff ℂ).mpr
  apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := w d)).subset
  rintro z ⟨b, hb, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb d

private theorem complexDiracDerivatives_polynomialEquiv_poly_algebra :
    ∃ e : MvPolynomial (Fin 2) ℂ ≃ₗ[ℂ] StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
      ∀ (p : MvPolynomial (Fin 2) ℂ) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
        e p y = ∑ d ∈ p.support, p.coeff d * (-1 : ℂ) ^ (d 0 + d 1) *
          MvPowerSeries.coeff d (complexSchwartzTaylor_equiv.choose y) := by
  classical
  let τ := complexSchwartzTaylor_equiv.choose
  let cf (d : Fin 2 →₀ ℕ) : MvPowerSeries (Fin 2) ℂ →L[ℂ] ℂ :=
    ⟨MvPowerSeries.coeff d, MvPowerSeries.WithPiTopology.continuous_coeff ℂ d⟩
  let c (d : Fin 2 →₀ ℕ) : StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    (-1 : ℂ) ^ (d 0 + d 1) • (cf d).comp τ.toContinuousLinearMap
  have hc (d) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :
      c d y = (-1 : ℂ) ^ (d 0 + d 1) * MvPowerSeries.coeff d (τ y) := rfl
  let Φ : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    (Finsupp.linearCombination ℂ c).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  have hΦ (p : MvPolynomial (Fin 2) ℂ) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :
      Φ p y = ∑ d ∈ p.support, p.coeff d * c d y := by
    simp [Φ, Finsupp.linearCombination_apply, Finsupp.sum, sum_apply]
    rfl
  have hΦm (d : Fin 2 →₀ ℕ) (a : ℂ) : Φ (MvPolynomial.monomial d a) = a • c d := by
    simp [Φ, MvPolynomial.monomial, Finsupp.linearCombination_apply]
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).mpr fun p hp ↦ ?_
    ext n
    have h := congrArg (fun T : StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) ↦
      T (τ.symm (MvPowerSeries.monomial n 1))) hp
    simp only [hΦ, hc, ContinuousLinearEquiv.apply_symm_apply, MvPowerSeries.coeff_monomial,
      zero_apply] at h
    rw [Finset.sum_eq_single n (fun d _ hd ↦ by simp [hd])
      (fun hn ↦ by simp [MvPolynomial.notMem_support_iff.mp hn])] at h
    simpa using h
  have hsurj : Function.Surjective Φ := by
    intro T
    let L : MvPowerSeries (Fin 2) ℂ →L[ℂ] ℂ := T.comp τ.symm.toContinuousLinearMap
    obtain ⟨N, hN⟩ := complexDiracDerivatives_polynomialEquiv_poly_finite L
    obtain ⟨t, ht⟩ := complexDiracDerivatives_polynomialEquiv_poly_box N
    refine ⟨∑ d ∈ t, MvPolynomial.monomial d ((-1 : ℂ) ^ (d 0 + d 1) * L (MvPowerSeries.monomial d 1)), ?_⟩
    ext y
    rw [map_sum]
    simp only [hΦm, sum_apply, smul_apply, hc, smul_eq_mul]
    have hy : T y = L (τ y) := by simp [L]
    have hs : L (τ y - ∑ d ∈ t, MvPowerSeries.coeff d (τ y) • MvPowerSeries.monomial d 1) = 0 := by
      apply hN
      intro m hm
      rw [map_sub, map_sum]
      simp [MvPowerSeries.coeff_monomial, ht m hm, Finset.sum_ite_eq]
    rw [map_sub, map_sum, sub_eq_zero] at hs
    rw [hy, hs]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [map_smul, smul_eq_mul]
    have he : (-1 : ℂ) ^ (d 0 + d 1) * (-1) ^ (d 0 + d 1) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (L (MvPowerSeries.monomial d 1) * MvPowerSeries.coeff d (τ y)) * he
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun p y ↦ ?_⟩
  change Φ p y = _
  rw [hΦ]
  simp only [hc, mul_assoc]
  rfl

/-- Bounded coefficient polydiscs control every seminorm of the inverse strong-dual map. -/
private theorem complexDiracDerivatives_polynomialEquiv_poly_topology :
    ∃ e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
        StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
      ∀ (p : MvPolynomial (Fin 2) ℂ) (y : SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin),
        e p y = ∑ d ∈ p.support, p.coeff d * (-1 : ℂ) ^ (d 0 + d 1) *
          MvPowerSeries.coeff d (complexSchwartzTaylor_equiv.choose y) := by
  classical
  obtain ⟨e₀, he₀⟩ := complexDiracDerivatives_polynomialEquiv_poly_algebra
  let τ := complexSchwartzTaylor_equiv.choose
  let e₁ : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃ₗ[ℂ]
      StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) := e₀
  have : IsClosed (complexSchwartzFlatAtOrigin : Set (SchwartzMap ℂ ℂ)) := complexSchwartzFlatAtOrigin_isClosed
  let : UniformSpace (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) :=
    isUniformAddGroup_of_addCommGroup
  let : PolynormableSpace ℂ (StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin)) :=
    uniformConvergenceCLM_polynormable (F := ℂ)
      {B : Set (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin) | Bornology.IsVonNBounded ℂ B}
      (fun _ h ↦ h)
      (by rw [Bornology.sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  have hcont : Continuous e₁ := continuous_of_finestLocallyConvex _ e₁.toLinearMap
  have hsymm : Continuous e₁.symm := by
    refine (finestLocallyConvex_withSeminorms (MvPolynomial (Fin 2) ℂ)).continuous_of_continuous_comp
      e₁.symm.toLinearMap fun p ↦ ?_
    refine Seminorm.continuous (r := 1) ?_
    let w (d : Fin 2 →₀ ℕ) : ℝ := p (MvPolynomial.monomial d 1)
    let B : Set (MvPowerSeries (Fin 2) ℂ) := {b | ∀ d, ‖MvPowerSeries.coeff d b‖ ≤ w d}
    have hB := (complexDiracDerivatives_polynomialEquiv_poly_bounded w).image τ.symm.toContinuousLinearMap
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo hB
      (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with T hT
    rw [Seminorm.mem_ball_zero]
    change p (e₁.symm T) < 1
    let q : MvPolynomial (Fin 2) ℂ := e₁.symm T
    have hTq : T = e₀ q := by exact (e₁.apply_symm_apply T).symm
    let b : MvPowerSeries (Fin 2) ℂ := fun d ↦
      (-1 : ℂ) ^ (d 0 + d 1) * (w d : ℂ) * (star (q.coeff d) / (‖q.coeff d‖ : ℂ))
    have hb : b ∈ B := by
      intro d
      have hw : 0 ≤ w d := apply_nonneg _ _
      have hu : ‖star (q.coeff d) / (‖q.coeff d‖ : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
        exact div_self_le_one _
      change ‖(-1 : ℂ) ^ (d 0 + d 1) * (w d : ℂ) * _‖ ≤ w d
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_of_nonneg hw, mul_one] using mul_le_mul_of_nonneg_left hu hw
    have hval : T (τ.symm b) = ((∑ d ∈ q.support, w d * ‖q.coeff d‖ : ℝ) : ℂ) := by
      rw [hTq, he₀]
      simp only [τ, ContinuousLinearEquiv.apply_symm_apply]
      push_cast
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hz : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hn : (‖q.coeff d‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      have hs : (-1 : ℂ) ^ (d 0 + d 1) * (-1) ^ (d 0 + d 1) = 1 := by rw [← mul_pow]; norm_num
      change q.coeff d * (-1 : ℂ) ^ (d 0 + d 1) *
        ((-1 : ℂ) ^ (d 0 + d 1) * (w d : ℂ) * (star (q.coeff d) / (‖q.coeff d‖ : ℂ))) = _
      calc
        _ = ((-1 : ℂ) ^ (d 0 + d 1) * (-1) ^ (d 0 + d 1)) * (w d : ℂ) *
            (q.coeff d * star (q.coeff d)) / (‖q.coeff d‖ : ℂ) := by ring
        _ = _ := by rw [hs, Complex.star_def, Complex.mul_conj']; field_simp
    have hle : p q ≤ ∑ d ∈ q.support, w d * ‖q.coeff d‖ := by
      conv_lhs => rw [q.as_sum]
      refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans
        (Finset.sum_le_sum fun d _ ↦ ?_)
      rw [show MvPolynomial.monomial d (q.coeff d) = q.coeff d • MvPolynomial.monomial d 1 by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul_eq_mul, mul_comm]
    have hlt := hT ⟨b, hb, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hlt
    change ‖T (τ.symm b)‖ < 1 at hlt
    rw [hval, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun d _ ↦ mul_nonneg (apply_nonneg _ _) (norm_nonneg _))] at hlt
    exact hle.trans_lt hlt
  refine ⟨{e₁ with continuous_toFun := hcont, continuous_invFun := hsymm}, ?_⟩
  exact he₀

private theorem complexDiracDerivatives_polynomialEquiv_dir_norm
    (v x : ℂ) (f : SchwartzMap ℂ ℂ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (LineDeriv.lineDerivOp v f : ℂ → ℂ) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖ := by
  have hf : ContDiff ℝ (n : ℕ∞ω) (fderiv ℝ (f : ℂ → ℂ)) :=
    (f.smooth (n + 1)).fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) hf.contDiffAt le_rfl
  have he : (LineDeriv.lineDerivOp v f : ℂ → ℂ) = fun y ↦ fderiv ℝ (f : ℂ → ℂ) y v :=
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv v f)
  rw [he]
  simpa only [norm_iteratedFDeriv_fderiv] using h

private theorem complexDiracDerivatives_polynomialEquiv_wirt_norm
    (f : SchwartzMap ℂ ℂ) (n : ℕ) (x : ℂ) :
    ‖iteratedFDeriv ℝ n (schwartzWirtingerZ f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖ ∧
    ‖iteratedFDeriv ℝ n (schwartzWirtingerZBar f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖ := by
  have h1 := complexDiracDerivatives_polynomialEquiv_dir_norm 1 x f n
  have hI := complexDiracDerivatives_polynomialEquiv_dir_norm Complex.I x f n
  simp only [norm_one, Complex.norm_I, one_mul] at h1 hI
  have hd (g : SchwartzMap ℂ ℂ) (c : ℂ) :
      iteratedFDeriv ℝ n (c • g : SchwartzMap ℂ ℂ) x = c • iteratedFDeriv ℝ n (g : ℂ → ℂ) x :=
    by
      change iteratedFDeriv ℝ n (fun z ↦ c • g z) x = _
      exact iteratedFDeriv_const_smul_apply' (a := c) (g.smooth n).contDiffAt
  have hsub (g h : SchwartzMap ℂ ℂ) :
      iteratedFDeriv ℝ n (g - h : SchwartzMap ℂ ℂ) x =
        iteratedFDeriv ℝ n (g : ℂ → ℂ) x - iteratedFDeriv ℝ n (h : ℂ → ℂ) x := by
    change iteratedFDeriv ℝ n ((g : ℂ → ℂ) - (h : ℂ → ℂ)) x = _
    exact iteratedFDeriv_sub_apply (g.smooth n).contDiffAt (h.smooth n).contDiffAt
  have hadd (g h : SchwartzMap ℂ ℂ) :
      iteratedFDeriv ℝ n (g + h : SchwartzMap ℂ ℂ) x =
        iteratedFDeriv ℝ n (g : ℂ → ℂ) x + iteratedFDeriv ℝ n (h : ℂ → ℂ) x := by
    change iteratedFDeriv ℝ n ((g : ℂ → ℂ) + (h : ℂ → ℂ)) x = _
    exact iteratedFDeriv_add_apply (g.smooth n).contDiffAt (h.smooth n).contDiffAt
  constructor
  · change ‖iteratedFDeriv ℝ n (((2 : ℂ)⁻¹ • (LineDeriv.lineDerivOp (1 : ℂ) f -
      Complex.I • LineDeriv.lineDerivOp Complex.I f)) : SchwartzMap ℂ ℂ) x‖ ≤ _
    rw [hd, hsub, hd, norm_smul, show ‖(2 : ℂ)⁻¹‖ = (1/2 : ℝ) by norm_num]
    refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith
  · change ‖iteratedFDeriv ℝ n (((2 : ℂ)⁻¹ • (LineDeriv.lineDerivOp (1 : ℂ) f +
      Complex.I • LineDeriv.lineDerivOp Complex.I f)) : SchwartzMap ℂ ℂ) x‖ ≤ _
    rw [hd, hadd, hd, norm_smul, show ‖(2 : ℂ)⁻¹‖ = (1/2 : ℝ) by norm_num]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith

private theorem complexDiracDerivatives_polynomialEquiv_mixed_norm
    (f : SchwartzMap ℂ ℂ) (k l : ℕ) (x : ℂ) :
    ‖((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) x‖ ≤
      ‖iteratedFDeriv ℝ (k + l) (f : ℂ → ℂ) x‖ := by
  have hp (op : SchwartzMap ℂ ℂ →L[ℂ] SchwartzMap ℂ ℂ)
      (ho : ∀ (f : SchwartzMap ℂ ℂ) (n : ℕ), ‖iteratedFDeriv ℝ n (op f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) x‖)
      (m n : ℕ) (f : SchwartzMap ℂ ℂ) :
      ‖iteratedFDeriv ℝ n ((op ^ m) f : ℂ → ℂ) x‖ ≤
        ‖iteratedFDeriv ℝ (n + m) (f : ℂ → ℂ) x‖ := by
    induction m generalizing n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', mul_apply_eq_comp]
      have h := (ho ((op ^ m) f) n).trans (ih (n + 1))
      rw [show n + 1 + m = n + (m + 1) by omega] at h
      exact h
  have hz := hp schwartzWirtingerZ (fun f n ↦ (complexDiracDerivatives_polynomialEquiv_wirt_norm f n x).1) k 0 ((schwartzWirtingerZBar ^ l) f)
  have hb := hp schwartzWirtingerZBar (fun f n ↦ (complexDiracDerivatives_polynomialEquiv_wirt_norm f n x).2) l k f
  rw [zero_add, norm_iteratedFDeriv_zero] at hz
  exact hz.trans hb

private theorem complexDiracDerivatives_polynomialEquiv_dirac_bound
    (f : SchwartzMap ℂ ℂ) (k l : ℕ) :
    ‖complexDiracDerivative k l f / ((k.factorial * l.factorial : ℂ))‖ ≤
      ‖iteratedFDeriv ℝ (k + l) (f : ℂ → ℂ) 0‖ := by
  change ‖((-1 : ℂ) ^ (k + l) * ((schwartzWirtingerZ ^ k) ((schwartzWirtingerZBar ^ l) f)) 0) /
    ((k.factorial * l.factorial : ℂ))‖ ≤ _
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hf : (1 : ℝ) ≤ (k.factorial : ℝ) * (l.factorial : ℝ) := by
    have hk : (1 : ℝ) ≤ k.factorial := mod_cast k.factorial_pos
    have hl : (1 : ℝ) ≤ l.factorial := mod_cast l.factorial_pos
    nlinarith
  exact (div_le_self (norm_nonneg _) hf).trans (complexDiracDerivatives_polynomialEquiv_mixed_norm f k l 0)

private theorem complexDiracDerivatives_polynomialEquiv_poly_weight
    (d : Fin 2 →₀ ℕ) : d.sum (fun _ n ↦ n) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl), Fin.sum_univ_two]

private theorem complexDiracDerivatives_polynomialEquiv_poly_upper
    (e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
      StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin))
    (hev : ∀ (p : MvPolynomial (Fin 2) ℂ) (g : SchwartzMap ℂ ℂ), e p (complexSchwartzFlatAtOrigin.mkQ g) =
      ∑ d ∈ p.support, p.coeff d * (complexDiracDerivative (d 0) (d 1) g /
        ((d 0).factorial * (d 1).factorial : ℂ)))
    (p : MvPolynomial (Fin 2) ℂ) (N : ℕ) (hdeg : p.totalDegree ≤ N) :
    DistributionOrderLE (fun f : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ ↦
      e p (complexSchwartzFlatAtOrigin.mkQ (f.hasCompactSupport.toSchwartzMap f.contDiff))) N := by
  intro K
  refine ⟨∑ d ∈ p.support, ‖p.coeff d‖, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, fun f _ B _ hf ↦ ?_⟩
  beta_reduce
  rw [hev, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd ↦ ?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hdN : d 0 + d 1 ≤ N := by
    have h := (MvPolynomial.le_totalDegree hd).trans hdeg
    simpa only [complexDiracDerivatives_polynomialEquiv_poly_weight] using h
  exact (complexDiracDerivatives_polynomialEquiv_dirac_bound _ _ _).trans (hf _ hdN 0)

/-- Shrinking mixed-monomial bumps isolate a coefficient while all lower-order derivatives vanish in norm. -/
private theorem complexDiracDerivatives_polynomialEquiv_poly_lower
    (e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
      StrongDual ℂ (SchwartzMap ℂ ℂ ⧸ complexSchwartzFlatAtOrigin))
    (hev : ∀ (p : MvPolynomial (Fin 2) ℂ) (g : SchwartzMap ℂ ℂ), e p (complexSchwartzFlatAtOrigin.mkQ g) =
      ∑ d ∈ p.support, p.coeff d * (complexDiracDerivative (d 0) (d 1) g /
        ((d 0).factorial * (d 1).factorial : ℂ)))
    (p : MvPolynomial (Fin 2) ℂ) (N : ℕ)
    (hord : DistributionOrderLE (fun f : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ ↦
      e p (complexSchwartzFlatAtOrigin.mkQ (f.hasCompactSupport.toSchwartzMap f.contDiff))) N) :
    p.totalDegree ≤ N := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro d hd
  rw [complexDiracDerivatives_polynomialEquiv_poly_weight]
  by_contra hdn
  have hn : N < d 0 + d 1 := by omega
  have hpd : p.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hpd' : 0 < ‖p.coeff d‖ := norm_pos_iff.mpr hpd
  let K0 : Compacts ℂ := ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩
  obtain ⟨C, hC0, hC⟩ := hord K0
  obtain ⟨G, hG, hscale⟩ := complexSchwartzTaylor_equiv_bump (d 0) (d 1)
  let A : ℝ := ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j G
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  let ε : ℝ := min 1 (‖p.coeff d‖ / (2 * (C * A + 1)))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (2 * (C * A + 1)) ≤ ‖p.coeff d‖ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨ψ, hψ, hjets⟩ := hscale ε hε
  have hψsupp : tsupport (ψ : ℂ → ℂ) ⊆ Metric.closedBall 0 1 := by
    refine closure_minimal (fun z hz ↦ ?_) Metric.isClosed_closedBall
    rw [mem_support, hψ] at hz
    have hzG : ε⁻¹ • z ∈ tsupport (G : ℂ → ℂ) := subset_tsupport _ (right_ne_zero_of_mul hz)
    have hb := hG hzG
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hε, inv_mul_le_iff₀ hε, mul_one] at hb
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hb.trans hε1
  have hψc : HasCompactSupport (ψ : ℂ → ℂ) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _) hψsupp
  let φ : TestFunction (⊤ : TopologicalSpace.Opens ℂ) ℂ ⊤ := ⟨ψ, ψ.smooth ⊤, hψc, by simp⟩
  have hφ : φ.hasCompactSupport.toSchwartzMap φ.contDiff = ψ := by ext; rfl
  have hbound := hC φ hψsupp (ε * A) (by positivity) fun j hj z ↦ by
    change ‖iteratedFDeriv ℝ j (ψ : ℂ → ℂ) z‖ ≤ ε * A
    have h1 : ‖iteratedFDeriv ℝ j (ψ : ℂ → ℂ) z‖ ≤ SchwartzMap.seminorm ℂ 0 j ψ := by
      simpa using SchwartzMap.le_seminorm ℂ 0 j ψ z
    have h2 := complexSchwartzTaylor_equiv_scaled G ψ (d 0 + d 1) j 0 hG ε hε hε1 (by omega) hψ
    have h3 : SchwartzMap.seminorm ℂ 0 j G ≤ A :=
      Finset.single_le_sum (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hε.le))
  beta_reduce at hbound
  rw [hφ, hev] at hbound
  have hjet (q : Fin 2 →₀ ℕ) : complexDiracDerivative (q 0) (q 1) ψ /
      ((q 0).factorial * (q 1).factorial : ℂ) = if q = d then (-1 : ℂ) ^ (d 0 + d 1) else 0 := by
    change ((-1 : ℂ) ^ (q 0 + q 1) * ((schwartzWirtingerZ ^ (q 0)) ((schwartzWirtingerZBar ^ (q 1)) ψ)) 0) / _ = _
    rw [hjets]
    by_cases h : q = d
    · subst q
      simp only [↓reduceIte, and_self]
      rw [mul_div_assoc, div_self (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (d 0))
        (by exact_mod_cast Nat.factorial_ne_zero (d 1))), mul_one]
    · have he : ¬ (q 0 = d 0 ∧ q 1 = d 1) := by
        rintro ⟨h0, h1⟩
        apply h
        ext i
        fin_cases i <;> assumption
      simp [he, h]
  have hsum : ∑ q ∈ p.support, p.coeff q * (complexDiracDerivative (q 0) (q 1) ψ /
      ((q 0).factorial * (q 1).factorial : ℂ)) = p.coeff d * (-1 : ℂ) ^ (d 0 + d 1) := by
    simp_rw [hjet]
    rw [Finset.sum_eq_single d]
    · simp
    · intro q hq hqd
      simp [hqd]
    · exact fun h ↦ False.elim (h hd)
  rw [hsum, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one] at hbound
  have hCA : 0 ≤ C * (ε * A) := by positivity
  nlinarith
end ComplexPolynomialDualHelpers

-- TODO(paper-gap): The coefficient seminorms in (5.3.2.12) give the coefficientwise
-- topology on the whole polynomial space and do not give its finest locally convex topology.

/-- Paper: Theorem 5.3.2.5(1), p. 246.
Polynomials in two variables with the finest locally convex topology identify with the strong
dual of the complex flat quotient through factorial-normalized mixed Dirac derivatives.
The least order bound of the distribution is the polynomial's total degree.
Deviation: Uses the finest locally convex topology and omits the false equivalence in
(5.3.2.12). -/
theorem complexDiracDerivatives_polynomialEquiv :
    ∃ e : FinestLocallyConvex (MvPolynomial (Fin 2) ℂ) ≃L[ℂ]
        StrongDual ℂ (𝓢(ℂ, ℂ) ⧸ complexSchwartzFlatAtOrigin),
      (∀ s : Fin 2 →₀ ℕ, ∀ f : 𝓢(ℂ, ℂ),
        e (MvPolynomial.monomial s 1) (complexSchwartzFlatAtOrigin.mkQ f) =
          complexDiracDerivative (s 0) (s 1) f /
            ((s 0).factorial * (s 1).factorial : ℂ)) ∧
      ∀ (p : MvPolynomial (Fin 2) ℂ) (N : ℕ),
        DistributionOrderLE
          (fun f : 𝒟ℂ ↦ e p (complexSchwartzFlatAtOrigin.mkQ
            (f.hasCompactSupport.toSchwartzMap f.contDiff))) N ↔ p.totalDegree ≤ N := by
  obtain ⟨e,he⟩ := complexDiracDerivatives_polynomialEquiv_poly_topology
  have hcf (d : Fin 2 →₀ ℕ) (f : SchwartzMap ℂ ℂ) :
      (-1 : ℂ)^(d 0+d 1) * MvPowerSeries.coeff d
        (complexSchwartzTaylor_equiv.choose (complexSchwartzFlatAtOrigin.mkQ f)) =
      complexDiracDerivative (d 0) (d 1) f / ((d 0).factorial * (d 1).factorial : ℂ) := by
    rw [complexSchwartzTaylor_equiv.choose_spec]
    change (-1 : ℂ)^(d 0+d 1) *
      (((schwartzWirtingerZ^(d 0)) ((schwartzWirtingerZBar^(d 1)) f)) 0 /
        ((d 0).factorial * (d 1).factorial : ℂ)) =
      ((-1 : ℂ)^(d 0+d 1) * ((schwartzWirtingerZ^(d 0)) ((schwartzWirtingerZBar^(d 1)) f)) 0) /
        ((d 0).factorial * (d 1).factorial : ℂ)
    ring
  have hev (p : MvPolynomial (Fin 2) ℂ) (f : SchwartzMap ℂ ℂ) :
      e p (complexSchwartzFlatAtOrigin.mkQ f) =
      ∑ d ∈ p.support, p.coeff d * (complexDiracDerivative (d 0) (d 1) f /
        ((d 0).factorial * (d 1).factorial : ℂ)) := by
    rw [he]
    exact Finset.sum_congr rfl fun d _ ↦ by rw [mul_assoc, hcf]
  refine ⟨e, ?_, fun p N ↦ ⟨complexDiracDerivatives_polynomialEquiv_poly_lower e hev p N, complexDiracDerivatives_polynomialEquiv_poly_upper e hev p N⟩⟩
  intro s f
  rw [hev]
  simp [MvPolynomial.support_monomial, MvPolynomial.coeff_monomial]

end ComplexOrigin

end RiemannMasullo
